from flask import Flask, render_template, request, session, redirect, url_for, send_from_directory, make_response
import googlemaps
import polyline
import folium
from datetime import datetime, timedelta
from flask_session import Session
from branca.element import Template, MacroElement
import os
import pandas as pd
import json
import glob
from uuid import uuid4
import math
import numpy as np
from geopy.distance import geodesic
import time
from functools import wraps

app = Flask(__name__)
app.secret_key = 'your_secret_key_here'
app.config['SESSION_TYPE'] = 'filesystem'
Session(app)

API_KEY = os.environ.get("API_KEY")  # Secure access
gmaps = googlemaps.Client(key=API_KEY)

# Login credentials - modify these as needed
LOGIN_CREDENTIALS = {
    "Vadinar": "Vadinar@123",
    "Afra": "Afra@123",
    "Ahmedabad": "Ahmedabad@123",
    "Allahabad": "Allahabad@123",
    "Aurangabad": "Aurangabad@123",
    "Baidyabati": "Baidyabati@123",
    "Balitaipur": "Balitaipur@123",
    "Bangalore": "Bangalore@123",
    "Barauni": "Barauni@123",
    "Belgaum": "Belgaum@123",
    "Bhatinda": "Bhatinda@123",
    "Bhubaneswar": "Bhubaneswar@123",
    "Bijwasan": "Bijwasan@123",
    "Bina": "Bina@123",
    "Bolangir": "Bolangir@123",
    "Bondamunda": "Bondamunda@123",
    "RILBHOI": "RILBHOI@123",
    "RILBHOL-BHOL-BHOURI": "RILBHOL-BHOL-BHOURI@123",
    "Chaksu": "Chaksu@123",
    "Chennai": "Chennai@123",
    "Manali": "Manali@123",
    "Tondiarpet": "Tondiarpet@123",
    "Cochin": "Cochin@123",
    "Cuttack": "Cuttack@123",
    "Delhi": "Delhi@123",
    "Deoli": "Deoli@123",
    "Dewas": "Dewas@123",
    "Digboi": "Digboi@123",
    "Dumdum": "Dumdum@123",
    "Ernakulam": "Ernakulam@123",
    "Gandhar": "Gandhar@123",
    "Goabari": "Goabari@123",
    "Gulbarga": "Gulbarga@123",
    "Guntakal": "Guntakal@123",
    "Guwahati": "Guwahati@123",
    "Haldia": "Haldia@123",
    "Hassarm": "Hassarm@123",
    "Hassaram": "Hassaram@123",
    "Hazarimal": "Hazarimal@123",
    "Hyderabad": "Hyderabad@123",
    "VISHAKAPATNAM": "VISHAKAPATNAM@123",
    "ITDCMBL": "ITDCMBL@123",
    "Mumbai": "Mumbai@123",
    "Jabalpur": "Jabalpur@123",
    "Jajapur": "Jajapur@123",
    "Jalandhar": "Jalandhar@123",
    "Jalgaon": "Jalgaon@123",
    "Jammu": "Jammu@123",
    "Jasidih": "Jasidih@123",
    "Jodhpur": "Jodhpur@123",
    "Jothpur": "Jothpur@123",
    "Jharsuguda": "Jharsuguda@123",
    "Jhumri": "Jhumri@123",
    "Kandla": "Kandla@123",
    "Kandi": "Kandi@123",
    "Karna": "Karna@123",
    "Karnal": "Karnal@123",
    "Kareil": "Kareil@123",
    "Khairabad": "Khairabad@123",
    "Kol": "Kol@123",
    "KORBA": "KORBA@123",
    "Kottayam": "Kottayam@123",
    "Kozhikode": "Kozhikode@123",
    "LAKHOLI": "LAKHOLI@123",
    "Loni": "Loni@123",
    "Lumdning": "Lumdning@123",
    "Madurai": "Madurai@123",
    "Mahakal": "Mahakal@123",
    "Malkapur": "Malkapur@123",
    "Mangalore": "Mangalore@123",
    "Mathura": "Mathura@123",
    "Mayapur": "Mayapur@123",
    "Miraj": "Miraj@123",
    "Mithapur": "Mithapur@123",
    "Muzzafarpur": "Muzzafarpur@123",
    "Mysore": "Mysore@123",
    "Nagothane": "Nagothane@123",
    "Jaipur": "Jaipur@123",
    "Panipat": "Panipat@123",
    "Paradeep": "Paradeep@123",
    "Patna": "Patna@123",
    "Pipelines": "Pipelines@123",
    "Pune": "Pune@123",
    "Rajahmundry": "Rajahmundry@123",
    "Rajbandh": "Rajbandh@123",
    "Ramgarh": "Ramgarh@123",
    "Ramagundam": "Ramagundam@123",
    "Ranchi": "Ranchi@123",
    "RANINAGAR": "RANINAGAR@123",
    "Raxaul": "Raxaul@123",
    "Rourkela": "Rourkela@123",
    "Sangrur": "Sangrur@123",
    "Shillong": "Shillong@123",
    "Silchar": "Silchar@123",
    "Srinagar": "Srinagar@123",
    "Tanar": "Tanar@123",
    "Tinsukia": "Tinsukia@123",
    "Trichy": "Trichy@123",
    "Vedaranyan": "Vedaranyan@123",
    "Vapi": "Vapi@123",
    "Vadodara": "Vadodara@123",
    "Vijayawada": "Vijayawada@123",
    "Visakhapatnam": "Visakhapatnam@123",
    "Viyayawada": "Viyayawada@123",
    "Warangal": "Warangal@123",
    "Wellington": "Wellington@123"
}

# Truck Tanker (TT) Specifications with Indian standards
TT_SPECIFICATIONS = {
    "12-16KL": {
        "capacity_range": "12-16 KL",
        "avg_capacity_liters": 14000,  # Average of 12-16KL
        "product_weight": 12600,  # 14000L * 0.9 density
        "tare_weight": 8500,  # Empty truck weight (Indian standard)
        "gross_weight": 21100,  # Total weight
        "axle_load": 10.5,  # Per axle in tonnes
        "risk_multiplier": 1.0,  # Base risk
        "max_speed": 60,  # kmph
        "turn_sensitivity": 1.0
    },
    "16-20KL": {
        "capacity_range": "16-20 KL",
        "avg_capacity_liters": 18000,
        "product_weight": 16200,  # 18000L * 0.9
        "tare_weight": 9500,
        "gross_weight": 25700,
        "axle_load": 12.85,
        "risk_multiplier": 1.2,
        "max_speed": 55,
        "turn_sensitivity": 1.15
    },
    "20-24KL": {
        "capacity_range": "20-24 KL",
        "avg_capacity_liters": 22000,
        "product_weight": 19800,  # 22000L * 0.9
        "tare_weight": 10500,
        "gross_weight": 30300,
        "axle_load": 15.15,
        "risk_multiplier": 1.4,
        "max_speed": 50,
        "turn_sensitivity": 1.3
    },
    "24-30KL": {
        "capacity_range": "24-30 KL",
        "avg_capacity_liters": 27000,
        "product_weight": 24300,  # 27000L * 0.9
        "tare_weight": 11500,
        "gross_weight": 35800,
        "axle_load": 17.9,
        "risk_multiplier": 1.6,
        "max_speed": 45,
        "turn_sensitivity": 1.5
    },
    "30KL+": {
        "capacity_range": "30+ KL",
        "avg_capacity_liters": 35000,
        "product_weight": 31500,  # 35000L * 0.9
        "tare_weight": 13000,
        "gross_weight": 44500,
        "axle_load": 22.25,
        "risk_multiplier": 2.0,
        "max_speed": 40,
        "turn_sensitivity": 1.8
    }
}

# Default values (will be updated based on TT selection)
TRUCK_WEIGHT = 25.0  # Will be dynamically set
MAX_SPEED_LIMIT = 50  # Will be dynamically set
SAFE_TURN_ANGLE = 130  # degrees
DANGEROUS_TURN_ANGLE = 30  # degrees

def login_required(f):
    """Decorator to require login for protected routes"""
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if not session.get('logged_in'):
            return redirect(url_for('login'))
        return f(*args, **kwargs)
    return decorated_function

def get_tt_specs(tt_type):
    """Get truck tanker specifications"""
    return TT_SPECIFICATIONS.get(tt_type, TT_SPECIFICATIONS["16-20KL"])

def calculate_bearing(lat1, lng1, lat2, lng2):
    """Calculate bearing between two points"""
    try:
        lat1, lng1, lat2, lng2 = map(math.radians, [lat1, lng1, lat2, lng2])
        dlng = lng2 - lng1
        y = math.sin(dlng) * math.cos(lat2)
        x = math.cos(lat1) * math.sin(lat2) - math.sin(lat1) * math.cos(lat2) * math.cos(dlng)
        bearing = math.atan2(y, x)
        return (math.degrees(bearing) + 360) % 360
    except:
        return 0

def calculate_turn_angle(prev_bearing, curr_bearing):
    """Calculate turn angle between two bearings"""
    try:
        angle = abs(curr_bearing - prev_bearing)
        return min(angle, 360 - angle)
    except:
        return 0

def get_recommended_speed(turn_angle, tt_specs, road_type="urban"):
    """Calculate recommended speed based on turn angle, TT specs, and road type"""
    try:
        base_speed = 35 if road_type == "urban" else 45
        max_speed = tt_specs["max_speed"]
        turn_sensitivity = tt_specs["turn_sensitivity"]
        
        # Adjust base speed for truck weight and capacity
        if tt_specs["gross_weight"] > 35000:  # Heavy TT
            base_speed -= 5
        elif tt_specs["gross_weight"] > 25000:  # Medium TT
            base_speed -= 2
        
        # Calculate speed based on turn angle with sensitivity
        adjusted_turn_angle = turn_angle * turn_sensitivity
        
        if adjusted_turn_angle < 10:  # Straight/slight curve
            recommended_speed = min(max_speed, base_speed + 10)
        elif adjusted_turn_angle < 25:  # Moderate turn
            recommended_speed = min(max_speed, base_speed)
        elif adjusted_turn_angle < 40:  # Sharp turn
            recommended_speed = min(35, base_speed - 8)
        elif adjusted_turn_angle < 70:  # Very sharp turn
            recommended_speed = min(25, base_speed - 15)
        else:  # U-turn or extreme turn
            recommended_speed = 12
        
        # Additional safety margin for heavier trucks
        if tt_specs["gross_weight"] > 30000:
            recommended_speed = max(10, recommended_speed - 5)
            
        return int(recommended_speed)
    except:
        return 25  # Default safe speed

def interpolate_route_points(coords, points_per_km=10):
    """Interpolate route to get more points per kilometer"""
    if len(coords) < 2:
        return coords
    
    try:
        interpolated = [coords[0]]
        
        for i in range(1, len(coords)):
            start = coords[i-1]
            end = coords[i]
            
            # Calculate distance between points
            distance_km = geodesic(start, end).kilometers
            
            if distance_km > 1/points_per_km:  # If points are far apart
                # Calculate number of intermediate points needed
                num_points = int(distance_km * points_per_km)
                
                # Interpolate points
                for j in range(1, num_points + 1):
                    ratio = j / (num_points + 1)
                    lat = start[0] + (end[0] - start[0]) * ratio
                    lng = start[1] + (end[1] - start[1]) * ratio
                    interpolated.append((lat, lng))
            
            interpolated.append(end)
        
        return interpolated
    except Exception as e:
        print(f"Error in interpolation: {e}")
        return coords

def get_traffic_data(coords):
    """Get traffic data for route coordinates"""
    traffic_data = []
    
    try:
        # Sample every 5th point to avoid API limits
        sample_coords = coords[::5] if len(coords) > 5 else coords
        
        for lat, lng in sample_coords:
            try:
                # Get traffic data using simulation (replace with actual API in production)
                traffic_level = np.random.choice(['light', 'moderate', 'heavy'], p=[0.4, 0.4, 0.2])
                traffic_data.append({
                    'location': (lat, lng),
                    'traffic_level': traffic_level,
                    'delay_factor': {'light': 1.0, 'moderate': 1.3, 'heavy': 1.8}[traffic_level]
                })
            except:
                continue
    except Exception as e:
        print(f"Error getting traffic data: {e}")
    
    return traffic_data

def identify_high_risk_zones(coords, pois, tt_specs):
    """Identify high-risk zones based on various factors including TT specifications"""
    risk_zones = []
    risk_multiplier = tt_specs["risk_multiplier"]
    
    try:
        for i, (lat, lng) in enumerate(coords):
            risk_score = 0
            risk_factors = []
            
            # Check proximity to hospitals (accident-prone areas)
            try:
                hospital_count = sum(1 for poi in pois if poi['type'] == 'hospital' 
                               and geodesic((lat, lng), poi['location']).meters < 500)
                if hospital_count > 0:
                    base_risk = hospital_count * 2
                    risk_score += base_risk * risk_multiplier
                    risk_factors.append(f"{hospital_count} hospital(s) nearby - TT Risk: {risk_multiplier}x")
            except:
                pass
            
            # Check for intersections with TT-specific sensitivity
            if i % 10 == 0 and i > 0 and i < len(coords) - 1:
                try:
                    prev_bearing = calculate_bearing(coords[i-10][0], coords[i-10][1], lat, lng)
                    next_bearing = calculate_bearing(lat, lng, coords[i+10][0], coords[i+10][1])
                    turn_angle = calculate_turn_angle(prev_bearing, next_bearing)
                    
                    if turn_angle > 30:
                        base_risk = 3
                        adjusted_risk = base_risk * risk_multiplier * tt_specs["turn_sensitivity"]
                        risk_score += adjusted_risk
                        risk_factors.append(f"Sharp turn/intersection ({turn_angle:.1f}°) - TT Sensitivity: {tt_specs['turn_sensitivity']}x")
                except:
                    pass
            
            # Weight-based risk factors
            if tt_specs["gross_weight"] > 35000:
                if np.random.random() < 0.08:  # Higher chance for heavy TT
                    risk_score += 6
                    risk_factors.append(f"Heavy TT zone - {tt_specs['gross_weight']/1000:.1f}T gross weight")
            
            # Crowded zones with TT risk multiplier
            try:
                if np.random.random() < 0.05:  # 5% chance
                    base_risk = 4
                    risk_score += base_risk * risk_multiplier
                    risk_factors.append(f"Crowded zone - TT capacity: {tt_specs['capacity_range']}")
                
                if np.random.random() < 0.03:  # 3% chance
                    base_risk = 5
                    risk_score += base_risk * risk_multiplier
                    risk_factors.append(f"Construction zone - Axle load: {tt_specs['axle_load']:.1f}T")
            except:
                pass
            
            # Bridge/overpass restrictions for heavy TT
            if tt_specs["gross_weight"] > 30000 and np.random.random() < 0.02:
                risk_score += 8
                risk_factors.append(f"Bridge weight restriction - Current: {tt_specs['gross_weight']/1000:.1f}T")
            
            if risk_score >= 3:
                risk_level = 'Critical' if risk_score >= 10 else 'High' if risk_score >= 6 else 'Medium'
                risk_zones.append({
                    'location': (lat, lng),
                    'risk_score': min(risk_score, 10),  # Cap at 10
                    'risk_factors': risk_factors,
                    'risk_level': risk_level,
                    'tt_impact': risk_multiplier
                })
    except Exception as e:
        print(f"Error identifying risk zones: {e}")
    
    return risk_zones

def generate_route_report(coords, pois, risk_zones, traffic_data, total_distance, total_duration, tt_specs):
    """Generate a detailed route analysis report with TT specifications"""
    try:
        # Extract numeric value from distance string
        distance_value = 1
        try:
            if total_distance:
                distance_parts = total_distance.split()
                if distance_parts:
                    distance_value = float(distance_parts[0])
        except:
            distance_value = 1
        
        report = {
            'total_distance': total_distance,
            'total_duration': total_duration,
            'tt_specifications': {
                'capacity_range': tt_specs['capacity_range'],
                'fuel_capacity': f"{tt_specs['avg_capacity_liters']:,} L",
                'product_weight': f"{tt_specs['product_weight']/1000:.1f} T",
                'tare_weight': f"{tt_specs['tare_weight']/1000:.1f} T",
                'gross_weight': f"{tt_specs['gross_weight']/1000:.1f} T",
                'axle_load': f"{tt_specs['axle_load']:.1f} T per axle",
                'max_speed': f"{tt_specs['max_speed']} kmph",
                'risk_multiplier': f"{tt_specs['risk_multiplier']}x"
            },
            'route_analysis': {
                'total_points': len(coords),
                'points_per_km': len(coords) / distance_value,
                'critical_risk_zones': len([z for z in risk_zones if z['risk_level'] == 'Critical']),
                'high_risk_zones': len([z for z in risk_zones if z['risk_level'] == 'High']),
                'medium_risk_zones': len([z for z in risk_zones if z['risk_level'] == 'Medium']),
                'hospitals_along_route': len([p for p in pois if p['type'] == 'hospital']),
                'fuel_stations': len([p for p in pois if p['type'] == 'fuel']),
                'police_stations': len([p for p in pois if p['type'] == 'police'])
            },
            'traffic_analysis': {
                'light_traffic_segments': len([t for t in traffic_data if t['traffic_level'] == 'light']),
                'moderate_traffic_segments': len([t for t in traffic_data if t['traffic_level'] == 'moderate']),
                'heavy_traffic_segments': len([t for t in traffic_data if t['traffic_level'] == 'heavy']),
                'average_delay_factor': np.mean([t['delay_factor'] for t in traffic_data]) if traffic_data else 1.0
            },
            'safety_recommendations': [
                f"Maximum speed: {tt_specs['max_speed']} kmph for {tt_specs['capacity_range']} TT",
                f"Gross weight {tt_specs['gross_weight']/1000:.1f}T - Check bridge weight limits",
                f"Axle load {tt_specs['axle_load']:.1f}T - Ensure road compliance",
                f"Extra caution at {len([z for z in risk_zones if z['risk_level'] in ['Critical', 'High']])} high-risk zones",
                f"Reduce speed to 10-25 kmph at sharp turns (sensitivity: {tt_specs['turn_sensitivity']}x)",
                "Plan fuel stops considering tanker capacity and weight distribution",
                "Emergency contacts ready - carrying hazardous petroleum products",
                f"Risk multiplier {tt_specs['risk_multiplier']}x applies to all hazard assessments"
            ]
        }
        
        return report
    except Exception as e:
        print(f"Error generating report: {e}")
        return {
            'total_distance': total_distance or "N/A",
            'total_duration': total_duration or "N/A",
            'tt_specifications': tt_specs,
            'route_analysis': {
                'total_points': len(coords),
                'points_per_km': 1,
                'critical_risk_zones': 0,
                'high_risk_zones': 0,
                'medium_risk_zones': 0,
                'hospitals_along_route': 0,
                'fuel_stations': 0,
                'police_stations': 0
            },
            'traffic_analysis': {
                'light_traffic_segments': 0,
                'moderate_traffic_segments': 0,
                'heavy_traffic_segments': 0,
                'average_delay_factor': 1.0
            },
            'safety_recommendations': [
                f"Maximum speed: {tt_specs['max_speed']} kmph for {tt_specs['capacity_range']} TT"
            ]
        }

# Session timeout check
@app.before_request
def check_session_timeout():
    """Check if session has expired (24 hours)"""
    if session.get('logged_in'):
        login_time = session.get('login_time')
        if login_time:
            try:
                login_datetime = datetime.fromisoformat(login_time)
                if datetime.now() - login_datetime > timedelta(hours=24):
                    session.clear()
                    return redirect(url_for('login', error='Session expired. Please login again.'))
            except:
                pass

@app.route('/login', methods=['GET', 'POST'])
def login():
    """Login page and authentication"""
    if request.method == 'POST':
        try:
            username = request.form['username'].strip()
            password = request.form['password']
            
            # Check credentials
            if username in LOGIN_CREDENTIALS and LOGIN_CREDENTIALS[username] == password:
                session['logged_in'] = True
                session['username'] = username
                session['login_time'] = datetime.now().isoformat()
                session.modified = True
                
                return redirect(url_for('home'))
            else:
                return redirect(url_for('login', error='Invalid username or password'))
                
        except Exception as e:
            print(f"Login error: {e}")
            return redirect(url_for('login', error='Login failed. Please try again.'))
    
    # GET request - show login form
    return render_template('login.html')

@app.route('/logout')
def logout():
    """Logout and clear session"""
    session.clear()
    return redirect(url_for('login', success='Successfully logged out'))

@app.route('/user_info')
@login_required
def user_info():
    """Display current user information"""
    username = session.get('username', 'Unknown')
    login_time = session.get('login_time', 'Unknown')
    
    try:
        login_datetime = datetime.fromisoformat(login_time)
        login_formatted = login_datetime.strftime("%Y-%m-%d %H:%M:%S")
    except:
        login_formatted = login_time
    
    return {
        'username': username,
        'login_time': login_formatted,
        'session_active': True
    }

@app.route('/health')
def health():
    """Simple health check endpoint"""
    return {"status": "OK", "message": "App is running"}

@app.route('/test')
def test():
    """Simple test page"""
    return "<h1>Flask App is Working!</h1><p>If you see this, the basic Flask setup is fine.</p>"

@app.route('/')
@login_required
def home():
    """Main route form page - requires login"""
    try:
        # Add username to template context
        username = session.get('username', 'User')
        
        # Load IOCL Landmarks with data validation
        landmarks = []
        
        # Try to load from Excel file, but handle gracefully if it doesn't exist
        try:
            df_iocl = pd.read_excel("IOCL_Landmark_Details.xlsx")
            
            for _, row in df_iocl.iterrows():
                try:
                    # Validate and convert coordinates
                    lat = float(row['Latitude']) if pd.notna(row['Latitude']) else None
                    lng = float(row['Longitude']) if pd.notna(row['Longitude']) else None
                    name = str(row['Landmark Name']).strip() if pd.notna(row['Landmark Name']) else None
                    
                    if lat is not None and lng is not None and name:
                        landmarks.append({
                            'name': name,
                            'lat': lat,
                            'lng': lng
                        })
                except (ValueError, TypeError) as e:
                    print(f"Skipping invalid landmark row: {e}")
                    continue
                    
            print(f"Loaded {len(landmarks)} landmarks from Excel file")
            
        except FileNotFoundError:
            print("IOCL_Landmark_Details.xlsx not found, using sample landmarks")
            # Provide some sample landmarks if file doesn't exist
            landmarks = [
                {'name': 'Delhi Terminal', 'lat': 28.6139, 'lng': 77.2090},
                {'name': 'Mumbai Terminal', 'lat': 19.0760, 'lng': 72.8777},
                {'name': 'Bangalore Terminal', 'lat': 12.9716, 'lng': 77.5946},
                {'name': 'Chennai Terminal', 'lat': 13.0827, 'lng': 80.2707},
                {'name': 'Kolkata Terminal', 'lat': 22.5726, 'lng': 88.3639}
            ]
        except Exception as e:
            print(f"Error loading Excel file: {e}")
            landmarks = []

        # Pass landmarks, TT specifications, and username to template
        return render_template(
            "route_form.html",
            landmarks=landmarks,
            tt_specifications=TT_SPECIFICATIONS,
            username=username
        )
        
    except Exception as e:
        print(f"Error loading data: {e}")
        import traceback
        traceback.print_exc()
        # Return a simple fallback page if everything fails
        username = session.get('username', 'User')
        tt_options = ""
        for tt_key, tt_data in TT_SPECIFICATIONS.items():
            tt_options += f'<option value="{tt_key}">{tt_data["capacity_range"]} ({tt_data["gross_weight"]/1000:.1f}T)</option>'
        
        return f"""
        <html><body>
        <h2>IndianOil Smart Marg - Truck Tanker Navigation</h2>
        <p>Welcome, {username}! <a href="/logout">Logout</a></p>
        <p>Basic form (landmarks unavailable)</p>
        <form method="POST" action="/fetch_routes">
            <p>Source: <input type="text" name="source" placeholder="lat,lng" required></p>
            <p>Destination: <input type="text" name="destination" placeholder="lat,lng" required></p>
            <p>Truck Tanker Type: 
                <select name="tt_type" required>
                    <option value="">Choose TT Capacity</option>
                    {tt_options}
                </select>
            </p>
            <button type="submit">Generate Routes</button>
        </form>
        <p>Error: {str(e)}</p>
        </body></html>
        """

@app.route('/fetch_routes', methods=['POST'])
@login_required
def fetch_routes():
    """Generate routes based on form input"""
    try:
        # Clear session and old route files
        old_directions = session.get('directions')
        old_route_report = session.get('route_report')
        username = session.get('username')
        login_time = session.get('login_time')
        logged_in = session.get('logged_in')
        
        session.clear()
        
        # Restore login session
        session['logged_in'] = logged_in
        session['username'] = username
        session['login_time'] = login_time
        
        for f in glob.glob("templates/route_preview_*.html"):
            try:
                os.remove(f)
            except:
                pass
        for f in glob.glob("templates/route_map_*.html"):
            try:
                os.remove(f)
            except:
                pass

        # Get form data
        source = request.form['source'].strip()
        destination = request.form['destination'].strip()
        tt_type = request.form['tt_type']

        # Get TT specifications
        tt_specs = get_tt_specs(tt_type)

        # Validate coordinates
        try:
            source_coords = tuple(map(float, source.split(',')))
            dest_coords = tuple(map(float, destination.split(',')))
        except ValueError:
            return "Invalid coordinates format. Please use: latitude,longitude"

        # Get routes from Google Maps - always use driving for trucks
        directions = gmaps.directions(
            source_coords, dest_coords,
            mode="driving",
            alternatives=True,
            departure_time=datetime.now(),
            avoid=["tolls"] if tt_specs["gross_weight"] > 35000 else []  # Avoid tolls for very heavy TT
        )

        if not directions:
            return "No routes found between the specified locations."

        # Store in session
        session['directions'] = directions
        session['source'] = source_coords
        session['destination'] = dest_coords
        session['tt_type'] = tt_type
        session['tt_specs'] = tt_specs
        session.modified = True

        # Process routes for selection
        routes = []
        for i, route in enumerate(directions):
            try:
                coords = polyline.decode(route['overview_polyline']['points'])
                distance = route['legs'][0]['distance']['text']
                duration = route['legs'][0]['duration']['text']
                summary = route.get('summary', f"Route {i+1}")

                # Create preview map with TT info
                unique_id = uuid4().hex
                preview_file = f"route_preview_{i}_{unique_id}.html"
                m = folium.Map(location=coords[len(coords)//2], zoom_start=12)
                
                # Add route with weight-based color
                route_color = 'red' if tt_specs["gross_weight"] > 35000 else 'orange' if tt_specs["gross_weight"] > 25000 else 'blue'
                folium.PolyLine(coords, color=route_color, weight=5, 
                              popup=f"TT {tt_specs['capacity_range']} - {tt_specs['gross_weight']/1000:.1f}T").add_to(m)
                
                m.save(f"templates/{preview_file}")

                routes.append({
                    'index': i,
                    'distance': distance,
                    'duration': duration,
                    'summary': summary,
                    'preview_file': preview_file,
                    'tt_info': f"TT {tt_specs['capacity_range']} - {tt_specs['gross_weight']/1000:.1f}T"
                })
            except Exception as e:
                print(f"Error processing route {i}: {e}")
                continue

        return render_template("route_select.html", routes=routes, tt_specs=tt_specs, username=username)
    
    except Exception as e:
        print(f"Error in fetch_routes: {e}")
        import traceback
        traceback.print_exc()
        return f"Error processing route request: {str(e)}"

# Replace the existing analyze_route function with this enhanced version
@app.route('/analyze_route', methods=['POST'])
@login_required
def analyze_route():
    """Enhanced route analysis with realistic hazard detection"""
    try:
        directions = session.get('directions')
        tt_specs = session.get('tt_specs')
        username = session.get('username', 'User')
        index = int(request.form['route_index'])

        if not directions or index >= len(directions) or not tt_specs:
            return "Invalid route selected or session data expired. Please start over."

        selected = directions[index]
        steps = selected['legs'][0]['steps']
        coords = polyline.decode(selected['overview_polyline']['points'])
        source = session['source']
        destination = session['destination']
        
        # Get route details
        total_distance = selected['legs'][0]['distance']['text']
        total_duration = selected['legs'][0]['duration']['text']

        # Enhanced route interpolation based on truck weight
        points_per_km = 25 if tt_specs["gross_weight"] > 35000 else 20 if tt_specs["gross_weight"] > 25000 else 15
        detailed_coords = interpolate_route_points(coords, points_per_km=points_per_km)
        
        print(f"Route analysis: {len(coords)} original points, {len(detailed_coords)} detailed points")
        
        # Get elevation profile for realistic gradient analysis
        elevations, gradients = [], []
        try:
            # Sample coordinates for elevation data
            elevation_sample = detailed_coords[::max(1, len(detailed_coords)//50)]  # Max 50 elevation points
            elevation_result = gmaps.elevation(elevation_sample)
            elevations = [point['elevation'] for point in elevation_result]
            
            # Calculate gradients
            for i in range(1, len(elevations)):
                if i < len(elevation_sample):
                    distance_m = geodesic(elevation_sample[i-1], elevation_sample[i]).meters
                    if distance_m > 0:
                        elevation_diff = elevations[i] - elevations[i-1]
                        gradient = (elevation_diff / distance_m) * 100
                        gradients.append(gradient)
                    else:
                        gradients.append(0)
        except Exception as e:
            print(f"Elevation data unavailable: {e}")
            elevations = [100] * len(detailed_coords)
            gradients = [0] * (len(detailed_coords) - 1)
        
        # Enhanced POI collection with better categorization
        def get_enhanced_pois():
            all_pois = []
            poi_types = [
                ('hospital', 'health'),
                ('school', 'education'), 
                ('gas_station', 'fuel'),
                ('police', 'safety'),
                ('shopping_mall', 'commercial'),
                ('place_of_worship', 'religious')
            ]
            
            # Use strategic sampling points
            sample_coords = detailed_coords[::max(1, len(detailed_coords)//15)]  # 15 sample points max
            
            for poi_type, category in poi_types:
                for lat, lng in sample_coords:
                    try:
                        places_result = gmaps.places_nearby(
                            location=(lat, lng), 
                            radius=400,  # Larger radius for better coverage
                            type=poi_type
                        )
                        
                        for place in places_result.get('results', [])[:3]:  # Limit to top 3 per location
                            all_pois.append({
                                'name': place['name'],
                                'location': (
                                    place['geometry']['location']['lat'],
                                    place['geometry']['location']['lng']
                                ),
                                'type': category,
                                'rating': place.get('rating', 3.0),
                                'place_id': place.get('place_id', '')
                            })
                        
                        time.sleep(0.05)  # Rate limiting
                        
                    except Exception as e:
                        print(f"Error getting {poi_type} POIs: {e}")
                        continue
            
            # Remove duplicates based on location proximity
            unique_pois = []
            for poi in all_pois:
                is_duplicate = False
                for existing in unique_pois:
                    if geodesic(poi['location'], existing['location']).meters < 100:
                        is_duplicate = True
                        break
                if not is_duplicate:
                    unique_pois.append(poi)
            
            return unique_pois
        
        all_pois = get_enhanced_pois()
        print(f"Collected {len(all_pois)} POIs")
        
        # Realistic traffic analysis
        traffic_data = get_realistic_traffic_data(detailed_coords, gmaps)
        print(f"Traffic analysis: {len(traffic_data)} data points")
        
        # Enhanced hazard zone identification
        hazard_zones = identify_realistic_poi_hazards(detailed_coords, all_pois, tt_specs)
        print(f"Identified {len(hazard_zones)} hazard zones")
        
        # Precise turn analysis with physics
        turns = calculate_precise_turn_analysis(detailed_coords, tt_specs)
        print(f"Analyzed {len(turns)} significant turns")
        
        # Braking distance calculations
        braking_points = calculate_braking_distances(detailed_coords, tt_specs, elevations, gradients)
        print(f"Calculated braking distances for {len(braking_points)} points")
        
        # Generate comprehensive report
        route_report = generate_enhanced_route_report(
            detailed_coords, all_pois, hazard_zones, traffic_data, turns, 
            braking_points, total_distance, total_duration, tt_specs, elevations, gradients
        )

        # Create enhanced visualization map
        m = folium.Map(location=source, zoom_start=12)
        
        # Add start and end markers with truck-specific info
        start_popup = f"""
        <div style='font-family: Arial; text-align: center;'>
            <h4>🚩 DEPARTURE</h4>
            <p><strong>TT Specs:</strong> {tt_specs['capacity_range']}<br>
            <strong>Gross Weight:</strong> {tt_specs['gross_weight']/1000:.1f}T<br>
            <strong>Cargo:</strong> {tt_specs['avg_capacity_liters']:,}L Petroleum</p>
        </div>
        """
        folium.Marker(source, popup=start_popup, 
                     icon=folium.Icon(color='green', icon='play', prefix='fa')).add_to(m)
        
        end_popup = f"""
        <div style='font-family: Arial; text-align: center;'>
            <h4>🏁 DESTINATION</h4>
            <p><strong>Distance:</strong> {total_distance}<br>
            <strong>Duration:</strong> {total_duration}<br>
            <strong>Complexity:</strong> {route_report['route_overview']['complexity_rating']}</p>
        </div>
        """
        folium.Marker(destination, popup=end_popup,
                     icon=folium.Icon(color='red', icon='stop', prefix='fa')).add_to(m)
        
        # Main route with weight-based styling
        if tt_specs["gross_weight"] > 35000:
            route_color, route_weight = '#8B0000', 6  # Dark red, thick for heavy TT
        elif tt_specs["gross_weight"] > 25000:
            route_color, route_weight = '#FF4500', 5  # Orange red, medium
        else:
            route_color, route_weight = '#0066CC', 4  # Blue, normal
            
        folium.PolyLine(
            detailed_coords, 
            color=route_color, 
            weight=route_weight, 
            opacity=0.8,
            popup=f"TT Route: {tt_specs['capacity_range']} - {tt_specs['gross_weight']/1000:.1f}T"
        ).add_to(m)

        # Add critical turns with detailed physics information
        for turn in turns[:15]:  # Limit to top 15 critical turns
            if turn.get('severity') in ['critical', 'high']:
                severity_colors = {'critical': '#8B0000', 'high': '#FF4500', 'moderate': '#FFD700'}
                color = severity_colors.get(turn['severity'], '#FFD700')
                
                turn_popup = f"""
                <div style='font-family: Arial; max-width: 300px;'>
                    <h4 style='color: {color}; margin: 5px 0;'>⚠️ {turn['severity'].title()} Turn</h4>
                    <table style='font-size: 11px; width: 100%;'>
                        <tr><td><strong>Turn Angle:</strong></td><td>{turn['turn_angle']:.1f}°</td></tr>
                        <tr><td><strong>Radius:</strong></td><td>{turn['radius']:.1f}m</td></tr>
                        <tr><td><strong>Safe Speed:</strong></td><td style='color: red; font-weight: bold;'>{turn['recommended_speed']} kmph</td></tr>
                        <tr><td><strong>Rollover Speed:</strong></td><td>{turn['rollover_speed']} kmph</td></tr>
                        <tr><td><strong>Lateral G-Force:</strong></td><td>{turn['physics_factors']['lateral_g_force']}g</td></tr>
                        <tr><td><strong>Brake Distance:</strong></td><td>{turn['deceleration_distance']}m</td></tr>
                    </table>
                    <p style='color: red; font-weight: bold; margin: 8px 0;'>{turn['warning']}</p>
                    <div style='background: #f0f0f0; padding: 5px; border-radius: 3px; font-size: 10px;'>
                        <strong>Physics Factors:</strong><br>
                        • Weight penalty: {turn['physics_factors']['weight_penalty']:.1%}<br>
                        • Liquid slosh risk: {turn['physics_factors']['slosh_factor']:.1%}<br>
                        • Safety margin: {turn['physics_factors']['safety_margin']:.1%}
                    </div>
                </div>
                """
                
                # Turn severity icon
                icon_html = f"""
                <div style='text-align: center;'>
                    <div style='background: {color}; color: white; border-radius: 50%; width: 30px; height: 30px; 
                                line-height: 30px; font-weight: bold; font-size: 12px;'>
                        {turn['recommended_speed']}
                    </div>
                    <div style='font-size: 8px; margin-top: 2px;'>km/h</div>
                </div>
                """
                
                folium.Marker(
                    location=turn['location'],
                    popup=turn_popup,
                    icon=folium.DivIcon(html=icon_html, icon_size=(35, 40), icon_anchor=(17, 35))
                ).add_to(m)

        # Add hazard zones with realistic risk visualization
        hazard_colors = {
            'Critical': '#8B0000',
            'High': '#DC143C', 
            'Medium': '#FF6347'
        }
        
        for zone in hazard_zones[:20]:  # Limit to top 20 hazard zones
            color = hazard_colors.get(zone['risk_level'], '#FF6347')
            
            hazard_popup = f"""
            <div style='font-family: Arial; max-width: 350px;'>
                <h4 style='color: {color}; margin: 5px 0;'>🚨 {zone['risk_level']} Risk Zone</h4>
                <p><strong>Risk Score:</strong> {zone['risk_score']:.1f}/10</p>
                <p><strong>Hazard Count:</strong> {zone['hazard_count']}</p>
                
                <div style='background: #fff3cd; padding: 8px; border-radius: 4px; margin: 5px 0;'>
                    <strong>Primary Hazards:</strong><br>
                    {"<br>".join([f"• {h['name']} ({h['distance']:.0f}m)" for h in zone['primary_hazards'][:3]])}
                </div>
                
                <div style='background: #f8d7da; padding: 8px; border-radius: 4px; margin: 5px 0;'>
                    <strong>TT Specific Risks:</strong><br>
                    {"<br>".join([f"• {rec}" for rec in zone.get('tt_specific_recommendations', [])][:3])}
                </div>
                
                <div style='background: #e2e3e5; padding: 6px; border-radius: 4px; font-size: 10px;'>
                    <strong>Tanker Info:</strong> {tt_specs['capacity_range']} | 
                    {tt_specs['gross_weight']/1000:.1f}T | Class 3 Flammable
                </div>
            </div>
            """
            
            radius = min(50, max(15, zone['risk_score'] * 5))
            folium.CircleMarker(
                location=zone['location'],
                radius=radius,
                popup=hazard_popup,
                color=color,
                fillColor=color,
                fillOpacity=0.3,
                weight=3
            ).add_to(m)

        # Add POIs with truck-relevant categorization
        poi_styles = {
            'fuel': {'color': 'orange', 'icon': 'gas-pump'},
            'health': {'color': 'red', 'icon': 'plus-square'},
            'safety': {'color': 'blue', 'icon': 'shield-alt'},
            'education': {'color': 'purple', 'icon': 'graduation-cap'},
            'commercial': {'color': 'green', 'icon': 'shopping-cart'},
            'religious': {'color': 'darkpurple', 'icon': 'place-of-worship'}
        }

        for poi in all_pois[:50]:  # Limit POI display
            try:
                poi_type = poi.get('type', 'other')
                style = poi_styles.get(poi_type, {'color': 'gray', 'icon': 'info'})
                
                # Special handling for fuel stations (extreme hazard for petroleum tankers)
                if poi_type == 'fuel':
                    poi_popup = f"""
                    <div style='font-family: Arial; text-align: center;'>
                        <h4 style='color: red;'>⛽ EXTREME HAZARD</h4>
                        <p><strong>{poi['name']}</strong></p>
                        <div style='background: #ffcccc; padding: 5px; border-radius: 3px;'>
                            <strong>PETROLEUM TANKER WARNING</strong><br>
                            • Reduce speed to 20 kmph<br>
                            • No smoking/ignition sources<br>
                            • Emergency protocols ready
                        </div>
                    </div>
                    """
                else:
                    poi_popup = f"""
                    <div style='font-family: Arial; text-align: center;'>
                        <h4>{poi['name']}</h4>
                        <p><strong>Type:</strong> {poi_type.title()}<br>
                        <strong>Rating:</strong> {poi.get('rating', 'N/A')}/5</p>
                    </div>
                    """
                
                folium.Marker(
                    location=poi['location'],
                    popup=poi_popup,
                    icon=folium.Icon(color=style['color'], icon=style['icon'], prefix='fa')
                ).add_to(m)
                
            except Exception as e:
                continue

        # Add traffic visualization with truck-specific impact
        for traffic in traffic_data[:30]:  # Limit traffic points
            try:
                traffic_colors = {'light': 'green', 'moderate': 'yellow', 'heavy': 'red'}
                color = traffic_colors.get(traffic['traffic_level'], 'gray')
                
                # Calculate truck-specific impact
                base_delay = traffic['delay_factor']
                truck_impact = base_delay * (1 + (tt_specs['gross_weight'] / 50000))  # Heavier trucks affected more
                
                traffic_popup = f"""
                <div style='font-family: Arial; max-width: 200px;'>
                    <h4>🚦 Traffic Conditions</h4>
                    <p><strong>Level:</strong> {traffic['traffic_level'].title()}<br>
                    <strong>Delay Factor:</strong> {traffic['delay_factor']:.1f}x<br>
                    <strong>TT Impact:</strong> {truck_impact:.1f}x<br>
                    <strong>Data Source:</strong> {'Real-time' if traffic.get('realistic') else 'Estimated'}</p>
                </div>
                """
                
                folium.CircleMarker(
                    location=traffic['location'],
                    radius=8,
                    popup=traffic_popup,
                    color=color,
                    fillColor=color,
                    fillOpacity=0.6
                ).add_to(m)
                
            except Exception as e:
                continue

        # Add braking distance indicators
        for braking in braking_points[:10]:  # Show top 10 critical braking zones
            try:
                if braking['total_distance'] > 60:  # Only show extended braking distances
                    braking_popup = f"""
                    <div style='font-family: Arial; max-width: 250px;'>
                        <h4>🛑 Extended Braking Zone</h4>
                        <table style='font-size: 11px; width: 100%;'>
                            <tr><td><strong>Speed:</strong></td><td>{braking['speed_kmph']} kmph</td></tr>
                            <tr><td><strong>Total Distance:</strong></td><td style='color: red; font-weight: bold;'>{braking['total_distance']}m</td></tr>
                            <tr><td><strong>Reaction:</strong></td><td>{braking['reaction_distance']}m</td></tr>
                            <tr><td><strong>Physics:</strong></td><td>{braking['physics_distance']}m</td></tr>
                            <tr><td><strong>Weight Factor:</strong></td><td>{braking['weight_factor']}x</td></tr>
                            <tr><td><strong>Gradient:</strong></td><td>{braking['gradient']:.1f}%</td></tr>
                        </table>
                        <p style='color: red; font-size: 10px; font-weight: bold; margin: 5px 0;'>
                            Maintain {int(braking['total_distance'] * 1.2)}m following distance
                        </p>
                    </div>
                    """
                    
                    folium.Marker(
                        location=braking['location'],
                        popup=braking_popup,
                        icon=folium.Icon(color='darkred', icon='hand-paper', prefix='fa')
                    ).add_to(m)
                    
            except Exception as e:
                continue

        # Enhanced legend with comprehensive truck tanker information
        legend_html = f"""
        {{% macro html(this, kwargs) %}}
        <div style="
            position: fixed;
            bottom: 50px;
            left: 50px;
            width: 400px;
            background-color: white;
            border: 2px solid #333;
            border-radius: 10px;
            z-index: 9999;
            padding: 15px;
            font-size: 11px;
            box-shadow: 0 6px 12px rgba(0,0,0,0.15);
            max-height: 70vh;
            overflow-y: auto;
        ">
            <h3 style='margin-top: 0; color: #333; text-align: center;'>🚛 Truck Tanker Navigation System</h3>
            
            <div style='background: linear-gradient(90deg, #f0f0f0, #e0e0e0); padding: 10px; border-radius: 6px; margin: 10px 0;'>
                <div style='display: grid; grid-template-columns: 1fr 1fr; gap: 8px; font-size: 10px;'>
                    <div><strong>Capacity:</strong> {tt_specs['capacity_range']}</div>
                    <div><strong>Fuel:</strong> {tt_specs['avg_capacity_liters']:,}L</div>
                    <div><strong>Gross Weight:</strong> {tt_specs['gross_weight']/1000:.1f}T</div>
                    <div><strong>Max Speed:</strong> {tt_specs['max_speed']} kmph</div>
                    <div><strong>Axle Load:</strong> {tt_specs['axle_load']:.1f}T</div>
                    <div><strong>Risk Class:</strong> 3 (Flammable)</div>
                </div>
                <div style='text-align: center; margin-top: 5px; color: #666; font-size: 9px;'>
                    User: {username} | Complexity: {route_report['route_overview']['complexity_rating']}
                </div>
            </div>
            
            <div style='margin: 8px 0;'>
                <div style='font-weight: bold; margin-bottom: 5px;'>🎯 Turn Speed Indicators:</div>
                <div style='margin: 3px 0;'>🔴 <span style='background: #8B0000; color: white; padding: 1px 4px; border-radius: 2px; font-size: 9px;'>&lt;25</span> Critical Turn</div>
                <div style='margin: 3px 0;'>🟠 <span style='background: #FF4500; color: white; padding: 1px 4px; border-radius: 2px; font-size: 9px;'>25-35</span> High Risk Turn</div>
                <div style='margin: 3px 0;'>🟡 <span style='background: #FFD700; color: black; padding: 1px 4px; border-radius: 2px; font-size: 9px;'>35+</span> Moderate Turn</div>
            </div>
            
            <div style='margin: 8px 0;'>
                <div style='font-weight: bold; margin-bottom: 5px;'>🚨 Hazard Zones:</div>
                <div style='margin: 3px 0;'>⚫ Critical Risk (Score 8-10)</div>
                <div style='margin: 3px 0;'>🔴 High Risk (Score 6-8)</div>
                <div style='margin: 3px 0;'>🟡 Medium Risk (Score 4-6)</div>
            </div>
            
            <div style='margin: 8px 0;'>
                <div style='font-weight: bold; margin-bottom: 5px;'>📍 Points of Interest:</div>
                <div style='display: grid; grid-template-columns: 1fr 1fr; gap: 2px; font-size: 10px;'>
                    <div>⛽ Fuel Station (EXTREME HAZARD)</div>
                    <div>🏥 Hospital</div>
                    <div>🎓 School/Education</div>
                    <div>🛡️ Police Station</div>
                    <div>🛒 Shopping Center</div>
                    <div>🕊️ Religious Site</div>
                </div>
            </div>
            
            <div style='margin: 8px 0;'>
                <div style='font-weight: bold; margin-bottom: 5px;'>🚦 Traffic Levels:</div>
                <div style='margin: 3px 0;'>● <span style='color: green; font-weight: bold;'>Light</span> (Delay: 1.0-1.2x)</div>
                <div style='margin: 3px 0;'>● <span style='color: orange; font-weight: bold;'>Moderate</span> (Delay: 1.3-1.7x)</div>
                <div style='margin: 3px 0;'>● <span style='color: red; font-weight: bold;'>Heavy</span> (Delay: 1.8x+)</div>
            </div>
            
            <div style='margin: 8px 0;'>
                <div style='font-weight: bold; margin-bottom: 5px;'>🛑 Special Indicators:</div>
                <div style='margin: 3px 0; font-size: 10px;'>✋ Extended Braking Zone (&gt;60m)</div>
                <div style='margin: 3px 0; font-size: 10px;'>🚩 Start/End Points</div>
            </div>
            
            <hr style='margin: 8px 0; border: none; border-top: 1px solid #ccc;'>
            <div style='text-align: center; font-size: 9px; color: #666;'>
                Route Statistics: {len(turns)} turns • {len(hazard_zones)} hazards<br>
                Max Braking: {max([b.get('total_distance', 45) for b in braking_points]) if braking_points else 45}m
            </div>
        </div>
        {{% endmacro %}}
        """
        
        legend = MacroElement()
        legend._template = Template(legend_html)
        m.get_root().add_child(legend)

        # Save enhanced map
        unique_map_id = uuid4().hex
        html_name = f"route_map_{unique_map_id}.html"
        m.save(f"templates/{html_name}")

        # Store comprehensive data in session
        session['route_report'] = route_report
        session['hazard_zones'] = hazard_zones
        session['turns'] = turns
        session['braking_points'] = braking_points
        session.modified = True

        # Return enhanced analysis page
        return render_template("route_analysis.html",
                               mode="Enhanced TT Navigation",
                               turns=len(turns),
                               critical_turns=len([t for t in turns if t.get('severity') == 'critical']),
                               poi_count=len(all_pois),
                               html_file=html_name,
                               route_report=route_report,
                               risk_zones=len(hazard_zones),
                               high_risk_zones=len([z for z in hazard_zones if z['risk_level'] in ['Critical', 'High']]),
                               critical_hazards=len([z for z in hazard_zones if z['risk_level'] == 'Critical']),
                               max_braking_distance=max([b.get('total_distance', 45) for b in braking_points]) if braking_points else 45,
                               tt_specs=tt_specs,
                               username=username,
                               complexity_rating=route_report['route_overview']['complexity_rating'])

    except Exception as e:
        print(f"Error in enhanced analyze_route: {e}")
        import traceback
        traceback.print_exc()
        return f"Error analyzing route: {str(e)}. Please try again or contact support."

# Updated detailed report function
@app.route('/detailed_report')
@login_required
def detailed_report():
    """Show comprehensive route analysis report"""
    try:
        report = session.get('route_report')
        tt_specs = session.get('tt_specs')
        hazard_zones = session.get('hazard_zones', [])
        turns = session.get('turns', [])
        braking_points = session.get('braking_points', [])
        username = session.get('username', 'User')
        
        if not report or not tt_specs:
            return "No route analysis data found. Please analyze a route first."
        
        # Prepare additional analysis data
        analysis_data = {
            'critical_hazards': [h for h in hazard_zones if h.get('risk_level') == 'Critical'],
            'critical_turns': [t for t in turns if t.get('severity') == 'critical'],
            'extreme_braking_zones': [b for b in braking_points if b.get('total_distance', 0) > 70],
            'fuel_station_hazards': [h for h in hazard_zones if any('fuel' in str(f).lower() for f in h.get('risk_factors', []))],
            'school_zone_hazards': [h for h in hazard_zones if any('school' in str(f).lower() for f in h.get('risk_factors', []))]
        }
        
        return render_template("enhanced_detailed_report.html", 
                             report=report, 
                             tt_specs=tt_specs,
                             analysis_data=analysis_data,
                             username=username)
        
    except Exception as e:
        print(f"Error in detailed_report: {e}")
        return f"Error generating detailed report: {str(e)}"

@app.route('/view_map/<filename>')
@login_required
def view_map(filename):
    try:
        path = os.path.join("templates", filename)
        if not os.path.exists(path):
            return "Map file not found", 404
        response = make_response(render_template(filename))
        response.headers['Cache-Control'] = 'no-store'
        return response
    except Exception as e:
        print(f"Error viewing map: {e}")
        return f"Error displaying map: {str(e)}", 500

@app.route('/download/<filename>')
@login_required
def download_map(filename):
    try:
        return send_from_directory(directory='templates', path=filename, as_attachment=True)
    except Exception as e:
        print(f"Error downloading map: {e}")
        return f"Error downloading file: {str(e)}", 500

@app.route('/preview/<filename>')
@login_required
def view_preview(filename):
    try:
        path = os.path.join("templates", filename)
        if not os.path.exists(path):
            return "Preview not found.", 404
        response = make_response(render_template(filename))
        response.headers['Cache-Control'] = 'no-store'
        return response
    except Exception as e:
        print(f"Error viewing preview: {e}")
        return f"Error displaying preview: {str(e)}", 500

@app.route('/tt_specs/<tt_type>')
@login_required
def get_tt_specifications(tt_type):
    """API endpoint to get TT specifications"""
    try:
        specs = get_tt_specs(tt_type)
        return {
            'success': True,
            'specifications': specs
        }
    except Exception as e:
        return {
            'success': False,
            'error': str(e)
        }

# Additional utility routes
@app.route('/dashboard')
@login_required
def dashboard():
    """User dashboard with system overview"""
    username = session.get('username', 'User')
    login_time = session.get('login_time', 'Unknown')
    
    try:
        login_datetime = datetime.fromisoformat(login_time)
        login_formatted = login_datetime.strftime("%Y-%m-%d %H:%M:%S")
        session_duration = str(datetime.now() - login_datetime).split('.')[0]
    except:
        login_formatted = login_time
        session_duration = "Unknown"
    
    # Get recent activity (if you want to track route analyses)
    recent_routes = session.get('recent_routes', [])
    
    dashboard_data = {
        'username': username,
        'login_time': login_formatted,
        'session_duration': session_duration,
        'total_routes_analyzed': len(recent_routes),
        'tt_specifications': TT_SPECIFICATIONS,
        'system_status': 'Online',
        'api_status': 'Connected' if API_KEY else 'Disconnected'
    }
    
    return render_template("dashboard.html", data=dashboard_data)

@app.route('/change_password', methods=['GET', 'POST'])
@login_required
def change_password():
    """Change user password"""
    username = session.get('username')
    
    if request.method == 'POST':
        try:
            current_password = request.form['current_password']
            new_password = request.form['new_password']
            confirm_password = request.form['confirm_password']
            
            # Verify current password
            if LOGIN_CREDENTIALS.get(username) != current_password:
                return redirect(url_for('change_password', error='Current password is incorrect'))
            
            # Check new password confirmation
            if new_password != confirm_password:
                return redirect(url_for('change_password', error='New passwords do not match'))
            
            # Validate new password strength
            if len(new_password) < 6:
                return redirect(url_for('change_password', error='New password must be at least 6 characters'))
            
            # Update password (Note: In production, use proper password hashing)
            LOGIN_CREDENTIALS[username] = new_password
            
            return redirect(url_for('dashboard', success='Password changed successfully'))
            
        except Exception as e:
            print(f"Password change error: {e}")
            return redirect(url_for('change_password', error='Failed to change password'))
    
    return render_template('change_password.html', username=username)

@app.route('/system_status')
@login_required
def system_status():
    """System status and diagnostics"""
    try:
        # Check various system components
        status = {
            'flask_app': 'Running',
            'google_maps_api': 'Connected' if API_KEY else 'Not Configured',
            'session_system': 'Active',
            'templates_directory': 'Available' if os.path.exists('templates') else 'Missing',
            'landmarks_file': 'Available' if os.path.exists('IOCL_Landmark_Details.xlsx') else 'Missing',
            'total_users': len(LOGIN_CREDENTIALS),
            'active_sessions': 1,  # Current user
            'server_time': datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            'app_version': '2.0',
            'last_restart': 'Unknown'  # You can track this if needed
        }
        
        return {
            'system_status': status,
            'tt_specifications_count': len(TT_SPECIFICATIONS),
            'supported_tt_types': list(TT_SPECIFICATIONS.keys())
        }
        
    except Exception as e:
        return {
            'error': str(e),
            'system_status': 'Error retrieving status'
        }

@app.errorhandler(500)
def internal_error(error):
    print(f"Internal server error: {error}")
    return "Internal server error occurred. Please check the logs.", 500

@app.errorhandler(404)
def not_found_error(error):
    return "Page not found.", 404

@app.errorhandler(403)
def forbidden_error(error):
    return redirect(url_for('login', error='Access denied. Please login.'))

if __name__ == '__main__':
    try:
        if not os.path.exists("templates"):
            os.makedirs("templates")
        
        # Create session directory if it doesn't exist
        if not os.path.exists("flask_session"):
            os.makedirs("flask_session")
        
        print("IndianOil Smart Marg - Truck Tanker Navigation System")
        print("=" * 50)
        print("Available login credentials:")
        for username, password in LOGIN_CREDENTIALS.items():
            print(f"Username: {username} | Password: {password}")
        print("=" * 50)
        print("Starting Flask application...")
        
        app.run(debug=True, host='0.0.0.0', port=5000)
        
    except Exception as e:
        print(f"Error starting application: {e}")
        import traceback
        traceback.print_exc()

