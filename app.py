"""
Smart Marg - IndianOil Route Management System
Clean Production Version - No AI Dependencies
"""

from flask import Flask, render_template, request, session, redirect, url_for, send_from_directory, make_response, jsonify
import googlemaps
import polyline
import folium
from datetime import datetime, timedelta
from flask_session import Session
import os
import pandas as pd
import json
import glob
from database import init_database, save_route_map, get_route_map_by_sap, get_all_route_maps
import math
from geopy.distance import geodesic
from functools import wraps
from uuid import uuid4

# Database imports
from database import (
    init_database, 
    save_route_map, 
    get_route_map_by_sap, 
    get_all_route_maps, 
    delete_route_map
)

# ============================================================================
# FLASK APP CONFIGURATION
# ============================================================================

app = Flask(__name__)
app.secret_key = os.environ.get('SECRET_KEY', 'your-secret-key-change-in-production')
app.config['SESSION_TYPE'] = 'filesystem'
app.config['SESSION_PERMANENT'] = True
app.config['PERMANENT_SESSION_LIFETIME'] = timedelta(hours=24)
Session(app)

# Initialize database
init_database()

# Google Maps API
API_KEY = os.environ.get("API_KEY")
gmaps = googlemaps.Client(key=API_KEY)

# ============================================================================
# LOGIN CREDENTIALS
# ============================================================================

LOGIN_CREDENTIALS = {
    "terminal": "terminal123",
    "admin": "admin123",
    "Vadinar": "Vadinar@123"
}

# ============================================================================
# TRUCK TANKER SPECIFICATIONS
# ============================================================================

TT_SPECIFICATIONS = {
    "12-16KL": {
        "capacity_range": "12-16 KL",
        "avg_capacity_liters": 14000,
        "product_weight": 12600,
        "tare_weight": 8500,
        "gross_weight": 21100,
        "axle_load": 10.5,
        "risk_multiplier": 1.0,
        "max_speed": 60,
        "turn_sensitivity": 1.0,
        "cg_height": 2.3,
        "track_width": 2.0,
        "stability_factor": 1.0
    },
    "16-20KL": {
        "capacity_range": "16-20 KL",
        "avg_capacity_liters": 18000,
        "product_weight": 16200,
        "tare_weight": 9500,
        "gross_weight": 25700,
        "axle_load": 12.85,
        "risk_multiplier": 1.2,
        "max_speed": 55,
        "turn_sensitivity": 1.15,
        "cg_height": 2.4,
        "track_width": 2.0,
        "stability_factor": 0.95
    },
    "20-24KL": {
        "capacity_range": "20-24 KL",
        "avg_capacity_liters": 22000,
        "product_weight": 19800,
        "tare_weight": 10500,
        "gross_weight": 30300,
        "axle_load": 15.15,
        "risk_multiplier": 1.4,
        "max_speed": 50,
        "turn_sensitivity": 1.3,
        "cg_height": 2.5,
        "track_width": 2.0,
        "stability_factor": 0.88
    },
    "24-30KL": {
        "capacity_range": "24-30 KL",
        "avg_capacity_liters": 27000,
        "product_weight": 24300,
        "tare_weight": 11500,
        "gross_weight": 35800,
        "axle_load": 17.9,
        "risk_multiplier": 1.6,
        "max_speed": 45,
        "turn_sensitivity": 1.5,
        "cg_height": 2.6,
        "track_width": 2.0,
        "stability_factor": 0.80
    },
    "30KL+": {
        "capacity_range": "30+ KL",
        "avg_capacity_liters": 35000,
        "product_weight": 31500,
        "tare_weight": 13000,
        "gross_weight": 44500,
        "axle_load": 22.25,
        "risk_multiplier": 2.0,
        "max_speed": 40,
        "turn_sensitivity": 1.8,
        "cg_height": 2.8,
        "track_width": 2.0,
        "stability_factor": 0.70
    }
}

PRACTICAL_SPEED_MATRIX = {
    "12-16KL": {'critical': 12, 'high': 20, 'moderate': 28, 'low': 40},
    "16-20KL": {'critical': 10, 'high': 18, 'moderate': 25, 'low': 35},
    "20-24KL": {'critical': 8, 'high': 15, 'moderate': 22, 'low': 32},
    "24-30KL": {'critical': 8, 'high': 12, 'moderate': 20, 'low': 30},
    "30KL+": {'critical': 5, 'high': 10, 'moderate': 18, 'low': 28}
}

# ============================================================================
# UTILITY FUNCTIONS
# ============================================================================

def login_required(f):
    """Decorator to require login"""
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if not session.get('logged_in'):
            return redirect(url_for('login'))
        return f(*args, **kwargs)
    return decorated_function

def get_tt_specs(tt_type):
    """Get truck tanker specifications"""
    return TT_SPECIFICATIONS.get(tt_type, TT_SPECIFICATIONS["16-20KL"])

def load_ro_data():
    """Load consignee data from Excel file"""
    try:
        df_ro = pd.read_excel("IOCL_Plant_data.xlsx")
        ro_data = {}
        
        for _, row in df_ro.iterrows():
            try:
                state_code = str(row['State code']).strip().upper() if pd.notna(row['State code']) else None
                # Convert SAP code and remove .0 if it's a float
                if pd.notna(row['SAP Code']):
                    sap_raw = row['SAP Code']
                    # If it's a number (float/int), convert to int first to remove decimals
                    if isinstance(sap_raw, (int, float)):
                        sap_code = str(int(sap_raw))
                    else:
                        sap_code = str(sap_raw).strip()
                        # Also handle string "333938.0" cases
                        if '.' in sap_code and sap_code.replace('.', '').isdigit():
                            sap_code = str(int(float(sap_code)))
                else:
                    sap_code = None
                consignee = str(row['Consignee']).strip() if pd.notna(row['Consignee']) else None
                district = str(row['District']).strip() if pd.notna(row.get('District')) else 'Unknown'
                region = str(row['Region']).strip() if pd.notna(row.get('Region')) else 'Retail'
                lat = float(row['Latitude']) if pd.notna(row['Latitude']) else None
                lng = float(row['Longitude']) if pd.notna(row['Longitude']) else None
                
                if all([state_code, sap_code, consignee, lat, lng]):
                    if state_code not in ro_data:
                        ro_data[state_code] = {}
                    
                    ro_data[state_code][sap_code] = {
                        'name': consignee,
                        'district': district,
                        'region': region,
                        'lat': lat,
                        'lng': lng
                    }
            except:
                continue
        
        print(f"✅ Loaded {sum(len(state_ros) for state_ros in ro_data.values())} consignees")
        return ro_data
    except Exception as e:
        print(f"❌ Error loading consignee data: {e}")
        return {}

# ============================================================================
# ROUTE ANALYSIS FUNCTIONS
# ============================================================================

def calculate_precise_bearing(lat1, lng1, lat2, lng2):
    """Calculate bearing between two points"""
    try:
        lat1_rad, lng1_rad = math.radians(lat1), math.radians(lng1)
        lat2_rad, lng2_rad = math.radians(lat2), math.radians(lng2)
        
        dlng = lng2_rad - lng1_rad
        y = math.sin(dlng) * math.cos(lat2_rad)
        x = (math.cos(lat1_rad) * math.sin(lat2_rad) - 
             math.sin(lat1_rad) * math.cos(lat2_rad) * math.cos(dlng))
        
        bearing = math.atan2(y, x)
        return (math.degrees(bearing) + 360) % 360
    except:
        return 0

def calculate_turn_angle_precise(bearing1, bearing2):
    """Calculate turn angle with wrap-around"""
    diff = bearing2 - bearing1
    if diff > 180:
        diff -= 360
    elif diff < -180:
        diff += 360
    return abs(diff)

def interpolate_route_for_accuracy(coords, target_points_per_km=50):
    """Interpolate route for better analysis"""
    if len(coords) < 2:
        return coords
    
    try:
        interpolated = [coords[0]]
        
        for i in range(1, len(coords)):
            start = coords[i-1]
            end = coords[i]
            
            distance_km = geodesic(start, end).kilometers
            
            if distance_km > (1.0 / target_points_per_km):
                num_intermediate = int(distance_km * target_points_per_km)
                
                for j in range(1, num_intermediate + 1):
                    ratio = j / (num_intermediate + 1)
                    lat = start[0] + (end[0] - start[0]) * ratio
                    lng = start[1] + (end[1] - start[1]) * ratio
                    interpolated.append((lat, lng))
            
            interpolated.append(end)
        
        return interpolated
    except:
        return coords

def detect_practical_hazards(coords, min_turn_angle=25, sample_distance=5, tt_specs=None):
    """Detect hazards along route"""
    coords = interpolate_route_for_accuracy(coords, target_points_per_km=50)
    
    sharp_turns = []
    curves = []
    
    if len(coords) < sample_distance * 2:
        return sharp_turns, curves
    
    if not tt_specs:
        tt_specs = TT_SPECIFICATIONS["16-20KL"]
    
    for i in range(sample_distance, len(coords) - sample_distance):
        try:
            bearing_in = calculate_precise_bearing(
                coords[i - sample_distance][0], coords[i - sample_distance][1],
                coords[i][0], coords[i][1]
            )
            bearing_out = calculate_precise_bearing(
                coords[i][0], coords[i][1],
                coords[i + sample_distance][0], coords[i + sample_distance][1]
            )
            
            turn_angle = calculate_turn_angle_precise(bearing_in, bearing_out)
            
            if turn_angle >= min_turn_angle:
                bearing_diff = bearing_out - bearing_in
                if bearing_diff > 180:
                    bearing_diff -= 360
                elif bearing_diff < -180:
                    bearing_diff += 360
                turn_direction = "right" if bearing_diff > 0 else "left"
                
                if turn_angle >= 90:
                    severity = 'critical'
                    risk_category = 'U-Turn/Roundabout'
                elif turn_angle >= 65:
                    severity = 'high'
                    risk_category = 'Highway Ramp'
                elif turn_angle >= 45:
                    severity = 'moderate'
                    risk_category = 'Intersection'
                else:
                    severity = 'low'
                    risk_category = 'Highway Curve'
                
                hazard = {
                    'location': coords[i],
                    'turn_angle': turn_angle,
                    'direction': turn_direction,
                    'severity': severity,
                    'risk_category': risk_category
                }
                
                if turn_angle >= 45:
                    sharp_turns.append(hazard)
                else:
                    curves.append(hazard)
        except:
            continue
    
    return sharp_turns, curves

# ============================================================================
# AUTHENTICATION ROUTES
# ============================================================================

@app.route('/login', methods=['GET', 'POST'])
def login():
    """Login page"""
    if request.method == 'POST':
        try:
            username = request.form['username'].strip()
            password = request.form['password']
            
            if username in LOGIN_CREDENTIALS and LOGIN_CREDENTIALS[username] == password:
                session['logged_in'] = True
                session['username'] = username
                session['login_time'] = datetime.now().isoformat()
                session.modified = True
                
                return redirect(url_for('dashboard'))
            else:
                return render_template('login.html', error='Invalid credentials')
        except Exception as e:
            return render_template('login.html', error='Login failed')
    
    return render_template('login.html')

@app.route('/logout')
def logout():
    """Logout"""
    session.clear()
    return redirect(url_for('login'))

@app.route('/dashboard')
@login_required
def dashboard():
    """Main dashboard after login"""
    try:
        username = session.get('username', 'User')
        
        # Get statistics
        saved_maps = get_all_route_maps(limit=1000)
        saved_maps_count = len(saved_maps)
        
        # Count landmarks
        landmarks_count = 0
        try:
            df_iocl = pd.read_excel("IOCL_Landmark_Details.xlsx")
            landmarks_count = len(df_iocl)
        except:
            landmarks_count = 0
        
        # Count consignees
        ro_data = load_ro_data()
        consignees_count = sum(len(state_ros) for state_ros in ro_data.values())
        
        return render_template('dashboard.html',
                             username=username,
                             saved_maps_count=saved_maps_count,
                             landmarks_count=landmarks_count,
                             consignees_count=consignees_count)
    except Exception as e:
        print(f"❌ Dashboard error: {e}")
        return f"Error loading dashboard: {str(e)}"

# ============================================================================
# MAIN ROUTES
# ============================================================================

@app.route('/')
@login_required
def home():
    """Main route form page"""
    try:
        username = session.get('username', 'User')
        
        # Load landmarks
        landmarks = []
        try:
            df_iocl = pd.read_excel("IOCL_Landmark_Details.xlsx")
            for _, row in df_iocl.iterrows():
                try:
                    lat = float(row['Latitude']) if pd.notna(row['Latitude']) else None
                    lng = float(row['Longitude']) if pd.notna(row['Longitude']) else None
                    name = str(row['Landmark Name']).strip() if pd.notna(row['Landmark Name']) else None
                    
                    if lat and lng and name:
                        landmarks.append({'name': name, 'lat': lat, 'lng': lng})
                except:
                    continue
        except:
            landmarks = []
        
        # Load consignee data
        ro_data = load_ro_data()
        
        return render_template(
            "route_form_professional.html",
            landmarks=landmarks,
            ro_data=ro_data,
            tt_specifications=TT_SPECIFICATIONS,
            username=username
        )
    except Exception as e:
        print(f"❌ Error: {e}")
        return f"Error: {str(e)}"

@app.route('/fetch_routes', methods=['POST'])
@login_required
def fetch_routes():
    """Generate routes from form input"""
    try:
        # Clear old session data
        username = session.get('username')
        login_time = session.get('login_time')
        logged_in = session.get('logged_in')
        
        session.clear()
        session['logged_in'] = logged_in
        session['username'] = username
        session['login_time'] = login_time
        
        # Get form data
        source = request.form['source'].strip()
        destination = request.form['destination'].strip()
        tt_type = request.form['tt_type']
        
        # Try to get additional form data (SAP code, terminal, consignee)
        sap_code = request.form.get('sap_code', '').strip()
        # Clean SAP code - remove .0 if present
        if sap_code and '.' in sap_code:
            try:
                sap_code = str(int(float(sap_code)))
            except:
                pass  # Keep original if conversion fails
        terminal_name = request.form.get('terminal_name', '').strip()
        consignee_name = request.form.get('consignee_name', '').strip()
        
        tt_specs = get_tt_specs(tt_type)
        
        # Add additional info to tt_specs for later use
        tt_specs['sap_code'] = sap_code
        tt_specs['terminal'] = terminal_name
        tt_specs['consignee'] = consignee_name
        tt_specs['tt_type'] = tt_type
        
        # Extract capacity from TT_SPECIFICATIONS
        if tt_type in TT_SPECIFICATIONS:
            tt_specs['capacity'] = TT_SPECIFICATIONS[tt_type]['avg_capacity_liters'] / 1000  # Convert to KL
            tt_specs['weight'] = TT_SPECIFICATIONS[tt_type]['gross_weight'] / 1000  # Convert to MT
            tt_specs['axles'] = '3-4'  # Standard for tankers
        
        # Parse coordinates
        source_coords = tuple(map(float, source.split(',')))
        dest_coords = tuple(map(float, destination.split(',')))
        
        # Get routes from Google Maps
        directions = gmaps.directions(
            source_coords, dest_coords,
            mode="driving",
            alternatives=True,
            departure_time=datetime.now()
        )
        
        if not directions:
            return "No routes found"
        
        # Store in session
        session['directions'] = directions
        session['source'] = source_coords
        session['destination'] = dest_coords
        session['tt_type'] = tt_type
        session['tt_specs'] = tt_specs
        session.modified = True
        
        # Process routes
        routes = []
        for i, route in enumerate(directions):
            try:
                coords = polyline.decode(route['overview_polyline']['points'])
                distance = route['legs'][0]['distance']['text']
                duration = route['legs'][0]['duration']['text']
                
                # Create preview map
                unique_id = uuid4().hex
                preview_file = f"route_preview_{i}_{unique_id}.html"
                m = folium.Map(location=coords[len(coords)//2], zoom_start=12)
                
                folium.PolyLine(coords, color='blue', weight=5).add_to(m)
                m.save(f"templates/{preview_file}")
                
                routes.append({
                    'index': i,
                    'distance': distance,
                    'duration': duration,
                    'summary': route.get('summary', f"Route {i+1}"),
                    'preview_file': preview_file,
                    'coords': coords  # Add coords for editor
                })
            except:
                continue
        
        # Prepare route data JSON for advanced editor (use first route)
        if routes:
            first_route = routes[0]
            route_data_json = json.dumps({
                'source': list(source_coords),
                'destination': list(dest_coords),
                'coords': first_route['coords'],
                'distance': first_route['distance'],
                'duration': first_route['duration']
            })
            
            # Create a route object for the template
            route = {
                'summary': first_route['summary'],
                'distance': first_route['distance'],
                'duration': first_route['duration'],
                'index': first_route['index']
            }
        else:
            route_data_json = json.dumps({
                'source': list(source_coords),
                'destination': list(dest_coords),
                'coords': [],
                'distance': 'N/A',
                'duration': 'N/A'
            })
            route = {
                'summary': 'Route 1',
                'distance': 'N/A',
                'duration': 'N/A',
                'index': 0
            }
        
        return render_template("advanced_route_editor.html", 
                             route=route,
                             routes=routes, 
                             tt_specs=tt_specs, 
                             username=username,
                             route_data_json=route_data_json)
    except Exception as e:
        print(f"❌ Error: {e}")
        return f"Error: {str(e)}"

@app.route('/analyze_route', methods=['POST'])
@login_required
def analyze_route():
    """Analyze selected route"""
    try:
        directions = session.get('directions')
        tt_specs = session.get('tt_specs')
        username = session.get('username', 'User')
        index = int(request.form['route_index'])
        
        if not directions or not tt_specs:
            return "Session expired"
        
        selected = directions[index]
        coords = polyline.decode(selected['overview_polyline']['points'])
        source = session['source']
        destination = session['destination']
        
        total_distance = selected['legs'][0]['distance']['text']
        total_duration = selected['legs'][0]['duration']['text']
        
        # Detect hazards
        sharp_turns, curves = detect_practical_hazards(coords, min_turn_angle=25, sample_distance=2, tt_specs=tt_specs)
        
        # Get POIs
        all_pois = []
        sample_coords = coords[::25] if len(coords) > 25 else coords[:3]
        
        for keyword in ['hospital', 'police', 'fuel']:
            for lat, lng in sample_coords:
                try:
                    places = gmaps.places_nearby(location=(lat, lng), radius=1500, keyword=keyword)
                    for place in places.get('results', [])[:2]:
                        all_pois.append({
                            'name': place.get('name', 'Unknown'),
                            'location': (place['geometry']['location']['lat'], place['geometry']['location']['lng']),
                            'type': keyword
                        })
                except:
                    continue
        
        # Create map
        center_lat = sum(coord[0] for coord in coords) / len(coords)
        center_lng = sum(coord[1] for coord in coords) / len(coords)
        
        m = folium.Map(location=(center_lat, center_lng), zoom_start=12)
        
        # Draw route
        folium.PolyLine(coords, color='#007cba', weight=6, opacity=0.8).add_to(m)
        
        # Add hazard markers
        for i, turn in enumerate(sharp_turns):
            lat, lng = turn['location']
            color = 'darkred' if turn['turn_angle'] >= 90 else 'red' if turn['turn_angle'] >= 65 else 'orange'
            
            folium.Marker(
                location=(lat, lng),
                icon=folium.Icon(color=color, icon='exclamation-triangle', prefix='fa'),
                popup=f"Hazard {i+1}: {turn['turn_angle']:.1f}° {turn['direction']}"
            ).add_to(m)
        
        # Add POI markers
        for poi in all_pois:
            color = 'red' if 'hospital' in poi['type'] else 'blue' if 'police' in poi['type'] else 'orange'
            folium.Marker(
                location=poi['location'],
                icon=folium.Icon(color=color, icon='info', prefix='fa'),
                popup=poi['name']
            ).add_to(m)
        
        # Add start/end
        folium.Marker(source, popup='START', icon=folium.Icon(color='green', icon='play', prefix='fa')).add_to(m)
        folium.Marker(destination, popup='END', icon=folium.Icon(color='blue', icon='stop', prefix='fa')).add_to(m)
        
        # Save map
        unique_id = uuid4().hex
        html_name = f"route_map_{unique_id}.html"
        m.save(f"templates/{html_name}")
        
        # Store in session
        session['coords'] = coords
        session['sharp_turns'] = sharp_turns
        session['curves'] = curves
        session['all_pois'] = all_pois
        session['html_file'] = html_name
        session['total_distance'] = total_distance
        session['total_duration'] = total_duration
        session.modified = True
        
        # Create report
        route_report = {
            'total_distance': total_distance,
            'total_duration': total_duration,
            'tt_specifications': tt_specs,
            'hazards': {
                'critical': len([t for t in sharp_turns if t['turn_angle'] >= 90]),
                'high': len([t for t in sharp_turns if 65 <= t['turn_angle'] < 90]),
                'moderate': len([t for t in sharp_turns if 45 <= t['turn_angle'] < 65])
            },
            'facilities': {
                'hospitals': len([p for p in all_pois if 'hospital' in p['type']]),
                'police': len([p for p in all_pois if 'police' in p['type']]),
                'fuel': len([p for p in all_pois if 'fuel' in p['type']])
            }
        }
        
        return render_template("route_analysis_improved.html",
                             html_file=html_name,
                             route_report=route_report,
                             sharp_turns=sharp_turns,
                             curves=curves,
                             all_pois=all_pois,
                             tt_specs=tt_specs,
                             username=username)
    except Exception as e:
        print(f"❌ Error: {e}")
        return f"Error: {str(e)}"

@app.route('/analyze_edited_route', methods=['POST'])
@login_required
def analyze_edited_route():
    """Analyze route with custom waypoints from advanced editor"""
    try:
        # Get edited route data from form
        edited_data = json.loads(request.form.get('edited_route_data', '{}'))
        
        tt_specs = session.get('tt_specs')
        username = session.get('username', 'User')
        
        if not edited_data or not tt_specs:
            return "Session expired or invalid data"
        
        # Extract waypoints
        waypoints = edited_data.get('waypoints', [])
        if len(waypoints) < 2:
            return "Invalid route data"
        
        # Get route from Google Maps with custom waypoints
        origin = (waypoints[0]['lat'], waypoints[0]['lng'])
        destination = (waypoints[-1]['lat'], waypoints[-1]['lng'])
        
        # Prepare intermediate waypoints if any
        via_waypoints = []
        if len(waypoints) > 2:
            via_waypoints = [(wp['lat'], wp['lng']) for wp in waypoints[1:-1]]
        
        # Get directions with waypoints
        if via_waypoints:
            directions = gmaps.directions(
                origin, destination,
                waypoints=via_waypoints,
                mode="driving",
                optimize_waypoints=False
            )
        else:
            directions = gmaps.directions(origin, destination, mode="driving")
        
        if not directions:
            return "Unable to calculate route with specified waypoints"
        
        # Process the route
        selected = directions[0]
        coords = polyline.decode(selected['overview_polyline']['points'])
        
        total_distance = selected['legs'][0]['distance']['text']
        total_duration = selected['legs'][0]['duration']['text']
        
        # Detect hazards
        sharp_turns, curves = detect_practical_hazards(coords, min_turn_angle=25, sample_distance=2, tt_specs=tt_specs)
        
        # Get POIs
        all_pois = []
        sample_coords = coords[::25] if len(coords) > 25 else coords[:3]
        
        for keyword in ['hospital', 'police', 'fuel']:
            for lat, lng in sample_coords:
                try:
                    places = gmaps.places_nearby(location=(lat, lng), radius=1500, keyword=keyword)
                    for place in places.get('results', [])[:2]:
                        all_pois.append({
                            'name': place.get('name', 'Unknown'),
                            'location': (place['geometry']['location']['lat'], place['geometry']['location']['lng']),
                            'type': keyword
                        })
                except:
                    continue
        
        # Create map
        center_lat = sum(coord[0] for coord in coords) / len(coords)
        center_lng = sum(coord[1] for coord in coords) / len(coords)
        
        m = folium.Map(location=(center_lat, center_lng), zoom_start=12)
        
        # Draw route
        folium.PolyLine(coords, color='#007cba', weight=6, opacity=0.8).add_to(m)
        
        # Add custom waypoint markers
        for i, wp in enumerate(waypoints):
            if i == 0:
                folium.Marker(
                    (wp['lat'], wp['lng']),
                    popup='START',
                    icon=folium.Icon(color='green', icon='play', prefix='fa')
                ).add_to(m)
            elif i == len(waypoints) - 1:
                folium.Marker(
                    (wp['lat'], wp['lng']),
                    popup='END',
                    icon=folium.Icon(color='blue', icon='stop', prefix='fa')
                ).add_to(m)
            else:
                folium.Marker(
                    (wp['lat'], wp['lng']),
                    popup=f"Waypoint {i}: {wp.get('name', 'Custom Stop')}",
                    icon=folium.Icon(color='purple', icon='map-pin', prefix='fa')
                ).add_to(m)
        
        # Add hazard markers
        for i, turn in enumerate(sharp_turns):
            lat, lng = turn['location']
            color = 'darkred' if turn['turn_angle'] >= 90 else 'red' if turn['turn_angle'] >= 65 else 'orange'
            
            folium.Marker(
                location=(lat, lng),
                icon=folium.Icon(color=color, icon='exclamation-triangle', prefix='fa'),
                popup=f"Hazard {i+1}: {turn['turn_angle']:.1f}° {turn['direction']}"
            ).add_to(m)
        
        # Add POI markers
        for poi in all_pois:
            color = 'red' if 'hospital' in poi['type'] else 'blue' if 'police' in poi['type'] else 'orange'
            folium.Marker(
                location=poi['location'],
                icon=folium.Icon(color=color, icon='info', prefix='fa'),
                popup=poi['name']
            ).add_to(m)
        
        # Save map
        unique_id = uuid4().hex
        html_name = f"route_map_edited_{unique_id}.html"
        m.save(f"templates/{html_name}")
        
        # Store in session
        session['coords'] = coords
        session['sharp_turns'] = sharp_turns
        session['curves'] = curves
        session['all_pois'] = all_pois
        session['html_file'] = html_name
        session['total_distance'] = total_distance
        session['total_duration'] = total_duration
        session.modified = True
        
        # Create report
        route_report = {
            'total_distance': total_distance,
            'total_duration': total_duration,
            'tt_specifications': tt_specs,
            'custom_waypoints': len(waypoints) - 2,
            'hazards': {
                'critical': len([t for t in sharp_turns if t['turn_angle'] >= 90]),
                'high': len([t for t in sharp_turns if 65 <= t['turn_angle'] < 90]),
                'moderate': len([t for t in sharp_turns if 45 <= t['turn_angle'] < 65])
            },
            'facilities': {
                'hospitals': len([p for p in all_pois if 'hospital' in p['type']]),
                'police': len([p for p in all_pois if 'police' in p['type']]),
                'fuel': len([p for p in all_pois if 'fuel' in p['type']])
            }
        }
        
        return render_template("route_analysis_improved.html",
                             html_file=html_name,
                             route_report=route_report,
                             sharp_turns=sharp_turns,
                             curves=curves,
                             all_pois=all_pois,
                             tt_specs=tt_specs,
                             username=username)
    except Exception as e:
        print(f"❌ Error: {e}")
        return f"Error: {str(e)}"

@app.route('/detailed_report')
@login_required
def detailed_report():
    """Generate detailed PDF-style report"""
    try:
        # Get data from session
        coords = session.get('coords', [])
        sharp_turns = session.get('sharp_turns', [])
        curves = session.get('curves', [])
        all_pois = session.get('all_pois', [])
        tt_specs = session.get('tt_specs', {})
        username = session.get('username', 'User')
        source = session.get('source', (0, 0))
        destination = session.get('destination', (0, 0))
        
        # Calculate totals
        critical_turns = len([t for t in sharp_turns if t.get('turn_angle', 0) >= 90])
        high_turns = len([t for t in sharp_turns if 65 <= t.get('turn_angle', 0) < 90])
        moderate_turns = len([t for t in sharp_turns if 45 <= t.get('turn_angle', 0) < 65])
        
        # Create report data
        route_report = {
            'total_distance': session.get('total_distance', 'N/A'),
            'total_duration': session.get('total_duration', 'N/A'),
            'tt_specifications': tt_specs
        }
        
        # For now, render the same analysis template with a print-friendly flag
        # In production, you'd create a separate PDF template
        return render_template("route_analysis_improved.html",
                             html_file=session.get('html_file', ''),
                             route_report=route_report,
                             sharp_turns=sharp_turns,
                             curves=curves,
                             all_pois=all_pois,
                             tt_specs=tt_specs,
                             username=username,
                             source=source,
                             destination=destination,
                             critical_turns=critical_turns,
                             high_turns=high_turns,
                             moderate_turns=moderate_turns,
                             print_mode=True)
    except Exception as e:
        print(f"❌ Error: {e}")
        return f"Error generating report: {str(e)}"

@app.route('/save_map_to_database', methods=['POST'])
@login_required
def save_map_to_database():
    """Save analyzed route map to database"""
    try:
        # Get data from session
        tt_specs = session.get('tt_specs', {})
        html_file = session.get('html_file', '')
        total_distance = session.get('total_distance', 'N/A')
        total_duration = session.get('total_duration', 'N/A')
        source = session.get('source', (0, 0))
        destination = session.get('destination', (0, 0))
        username = session.get('username', 'Terminal Operator')
        
        # Extract data from tt_specs
        sap_code = tt_specs.get('sap_code', '')
        terminal_name = tt_specs.get('terminal', '')
        consignee_name = tt_specs.get('consignee', '')
        tt_type = tt_specs.get('tt_type', '')
        tt_capacity = tt_specs.get('capacity', 0)
        
        if not sap_code:
            return jsonify({'success': False, 'message': 'SAP code not found in session'})
        
        # Prepare data for database
        map_data = {
            'sap_code': sap_code,
            'terminal_name': terminal_name,
            'terminal_coords': f"{source[0]},{source[1]}",
            'consignee_name': consignee_name,
            'consignee_coords': f"{destination[0]},{destination[1]}",
            'tt_type': tt_type,
            'tt_capacity': tt_capacity,
            'route_distance': total_distance,
            'route_duration': total_duration,
            'map_file': html_file,
            'created_by': username
        }
        
        # Save to database
        success, message = save_route_map(map_data)
        
        return jsonify({'success': success, 'message': message})
    
    except Exception as e:
        print(f"❌ Error saving to database: {e}")
        return jsonify({'success': False, 'message': f'Error: {str(e)}'})

# ============================================================================
# TERMINAL ROUTES
# ============================================================================

@app.route('/terminal')
def terminal_dashboard():
    """Terminal operator dashboard"""
    try:
        landmarks = []
        try:
            df_iocl = pd.read_excel("IOCL_Landmark_Details.xlsx")
            for _, row in df_iocl.iterrows():
                try:
                    lat = float(row['Latitude']) if pd.notna(row['Latitude']) else None
                    lng = float(row['Longitude']) if pd.notna(row['Longitude']) else None
                    name = str(row['Landmark Name']).strip() if pd.notna(row['Landmark Name']) else None
                    
                    if lat and lng and name:
                        landmarks.append({'name': name, 'lat': lat, 'lng': lng})
                except:
                    continue
        except:
            pass
        
        ro_data = load_ro_data()
        
        # Get saved route maps
        saved_maps = get_all_route_maps(limit=50)
        
        username = session.get('username', 'User')
        
        return render_template('terminal_dashboard_pro.html',
                             landmarks=landmarks,
                             ro_data=ro_data,
                             tt_specifications=TT_SPECIFICATIONS,
                             saved_maps=saved_maps,
                             username=username)
    except Exception as e:
        return f"Error: {str(e)}"

# ============================================================================
# DRIVER ROUTES
# ============================================================================

@app.route('/driver/scan')
def driver_scan():
    """Driver QR scanner page"""
    return render_template('driver_scan.html')

@app.route('/driver/view-map', methods=['POST'])
def driver_view_map():
    """Driver view map after QR scan"""
    try:
        data = request.get_json()
        sap_code = data.get('sap_code')
        
        if not sap_code:
            return jsonify({'error': 'SAP code required'}), 400
        
        route_map = get_route_map_by_sap(sap_code)
        if not route_map:
            return jsonify({'error': 'Route not found'}), 404
        
        return jsonify({'success': True, 'redirect': f'/driver/map/{sap_code}'})
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/driver/map/<sap_code>')
def driver_map_view(sap_code):
    """Display map to driver"""
    try:
        route_map = get_route_map_by_sap(sap_code)
        if not route_map:
            return "Route not found", 404
        
        return render_template('driver_view_map.html', map_data=route_map)
    except Exception as e:
        return f"Error: {str(e)}", 500

# ============================================================================
# API ROUTES
# ============================================================================

@app.route('/api/get_saved_maps')
def api_get_saved_maps():
    """Get all saved maps"""
    try:
        maps = get_all_route_maps(limit=100)
        return jsonify({'success': True, 'maps': maps, 'count': len(maps)})
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)})

@app.route('/api/delete_map/<sap_code>', methods=['DELETE'])
def api_delete_map(sap_code):
    """Delete a map"""
    try:
        success, message = delete_route_map(sap_code)
        return jsonify({'success': success, 'message': message})
    except Exception as e:
        return jsonify({'success': False, 'message': str(e)})

@app.route('/admin/migrate-sap-codes')
@login_required
def migrate_sap_codes():
    """Admin endpoint to clean SAP codes in database"""
    try:
        import sqlite3
        
        conn = sqlite3.connect('route_maps.db')
        cursor = conn.cursor()
        
        # Get all records
        cursor.execute('SELECT id, sap_code FROM route_maps')
        records = cursor.fetchall()
        
        results = []
        updated = 0
        
        for record_id, sap_code in records:
            # Check if SAP has .0
            if '.' in str(sap_code):
                try:
                    # Convert to int to remove decimal
                    clean_sap = str(int(float(sap_code)))
                    
                    # Update the record
                    cursor.execute('UPDATE route_maps SET sap_code = ? WHERE id = ?', 
                                 (clean_sap, record_id))
                    updated += 1
                    results.append(f"✅ Updated: {sap_code} → {clean_sap}")
                except Exception as e:
                    results.append(f"⚠️ Could not clean {sap_code}: {e}")
        
        conn.commit()
        conn.close()
        
        results.append(f"\n✅ Migration complete! Updated {updated} SAP codes.")
        
        return "<pre>" + "\n".join(results) + "</pre>"
        
    except Exception as e:
        return f"<pre>❌ Migration failed: {e}</pre>"

# ============================================================================
# UTILITY ROUTES
# ============================================================================

@app.route('/map/<filename>')
def view_map(filename):
    """View map file"""
    return render_template(filename)

@app.route('/health')
def health():
    """Health check"""
    return {"status": "OK", "message": "App is running"}

# ============================================================================
# ERROR HANDLERS
# ============================================================================

@app.errorhandler(404)
def not_found(e):
    return "Page not found", 404

@app.errorhandler(500)
def server_error(e):
    return "Internal server error", 500

# ============================================================================
# RUN APP
# ============================================================================

if __name__ == '__main__':
    try:
        if not os.path.exists("templates"):
            os.makedirs("templates")
        
        if not os.path.exists("flask_session"):
            os.makedirs("flask_session")
        
        print("=" * 60)
        print("Smart Marg - IndianOil Route Management System")
        print("=" * 60)
        print("Login Credentials:")
        for username, password in LOGIN_CREDENTIALS.items():
            print(f"  {username} : {password}")
        print("=" * 60)
        
        app.run(debug=True, host='0.0.0.0', port=5000)
    except Exception as e:
        print(f"❌ Error starting app: {e}")
