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
import re

app = Flask(__name__)
app.secret_key = os.environ.get('SECRET_KEY', 'your_secret_key_here')
app.config['SESSION_TYPE'] = 'filesystem'
Session(app)

# Initialize Google Maps client with proper error handling
Maps_API_KEY = os.environ.get('Maps_API_KEY')
API_KEY = os.environ.get("API_KEY")  # Backup variable name

# Use whichever API key is available
api_key = Maps_API_KEY or API_KEY

if api_key and api_key != 'YOUR_Maps_API_KEY':
    try:
        gmaps = googlemaps.Client(key=api_key)
        print("Google Maps client initialized successfully")
    except Exception as e:
        print(f"Error initializing Google Maps client: {e}")
        gmaps = None
else:
    print("WARNING: No valid Google Maps API key found in environment variables")
    gmaps = None

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
            if i % 10 == 0 and i > 0 and i < len(coords) - 10:
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
        distance_value = extract_distance_km(total_distance)
        
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
                'points_per_km': len(coords) / max(distance_value, 1),
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
            'safety_recommendations': generate_tt_recommendations(risk_zones, traffic_data, tt_specs)
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

def generate_tt_recommendations(risk_zones, traffic_data, tt_specs):
    """Generate specific recommendations for truck tanker operation"""
    recommendations = []
    
    recommendations.append(f"Maximum speed: {tt_specs['max_speed']} kmph for {tt_specs['capacity_range']} TT")
    recommendations.append(f"Gross weight {tt_specs['gross_weight']/1000:.1f}T - Check bridge weight limits")
    recommendations.append(f"Axle load {tt_specs['axle_load']:.1f}T - Ensure road compliance")
    
    critical_zones = [z for z in risk_zones if z['risk_level'] == 'Critical']
    if critical_zones:
        recommendations.append(f"Extra caution at {len(critical_zones)} critical zones")
        recommendations.append(f"Reduce speed to 10-25 kmph at sharp turns (sensitivity: {tt_specs['turn_sensitivity']}x)")
    
    if tt_specs['gross_weight'] > 35000:
        recommendations.append("Heavy TT: Maintain maximum 50 km/h on highways")
        recommendations.append("Use engine braking on downhill sections")
    
    heavy_traffic = [t for t in traffic_data if t['traffic_level'] == 'heavy']
    if len(heavy_traffic) > 3:
        recommendations.append("Consider alternate timing - heavy traffic detected")
    
    if tt_specs['turn_sensitivity'] > 1.5:
        recommendations.append("Take wide turns - high center of gravity vehicle")
        recommendations.append("Check mirrors frequently for trailer swing")
    
    recommendations.append("Plan fuel stops considering tanker capacity and weight distribution")
    recommendations.append("Emergency contacts ready - carrying hazardous petroleum products")
    recommendations.append(f"Risk multiplier {tt_specs['risk_multiplier']}x applies to all hazard assessments")
    recommendations.append("Maintain emergency kit: fire extinguisher, spill containment")
    recommendations.append("Monitor tire pressure - heavy load affects handling")
    
    return recommendations

def extract_distance_km(distance_text):
    """Extract distance in kilometers from Google Maps distance text"""
    try:
        if not distance_text:
            return 1
        
        # Handle different formats: "123 km", "1,234 km", "12.5 km"
        distance_text = distance_text.lower().replace(',', '').strip()
        
        if 'km' in distance_text:
            # Extract number before 'km'
            km_value = distance_text.split('km')[0].strip()
            return float(km_value)
        elif 'm' in distance_text and 'km' not in distance_text:
            # Handle meters: "500 m" -> 0.5 km
            m_value = distance_text.split('m')[0].strip()
            return float(m_value) / 1000
        else:
            # Try to extract any number
            numbers = re.findall(r'\d+\.?\d*', distance_text)
            if numbers:
                return float(numbers[0])
            return 1
    except (ValueError, AttributeError, IndexError):
        return 1

@app.route('/health')
def health():
    """Simple health check endpoint"""
    return {"status": "OK", "message": "App is running", "gmaps_available": gmaps is not None}

@app.route('/test')
def test():
    """Simple test page"""
    return f"<h1>Flask App is Working!</h1><p>Google Maps Available: {gmaps is not None}</p>"

@app.route('/')
def home():
    """Main route form page"""
    try:
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

        # Pass landmarks and TT specifications to template
        return render_template(
            "route_form.html",
            landmarks=landmarks,
            tt_specifications=TT_SPECIFICATIONS,
            gmaps_available=gmaps is not None
        )
        
    except Exception as e:
        print(f"Error loading data: {e}")
        import traceback
        traceback.print_exc()
        # Return a simple fallback page if everything fails
        tt_options = ""
        for tt_key, tt_data in TT_SPECIFICATIONS.items():
            tt_options += f'<option value="{tt_key}">{tt_data["capacity_range"]} ({tt_data["gross_weight"]/1000:.1f}T)</option>'
        
        gmaps_status = "✓ Available" if gmaps else "✗ Not Available (Check API Key)"
        
        return f"""
        <html><body>
        <h2>IndianOil Smart Marg - Truck Tanker Navigation</h2>
        <p>Status: Google Maps {gmaps_status}</p>
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
        <p>Note: {str(e)}</p>
        </body></html>
        """

@app.route('/fetch_routes', methods=['POST'])
def fetch_routes():
    """Generate routes based on form input with validation"""
    try:
        # Check if Google Maps is available
        if not gmaps:
            return render_template("error_page.html",
                                   error="Service unavailable",
                                   message="Google Maps service is not available. Please check the API key configuration.",
                                   back_url=url_for('home'))

        # Clear session and old route files
        session.clear()
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
            
            # Basic coordinate validation
            if not (-90 <= source_coords[0] <= 90 and -180 <= source_coords[1] <= 180):
                return render_template("error_page.html",
                                       error="Invalid source coordinates",
                                       message="Source latitude must be between -90 and 90, longitude between -180 and 180",
                                       back_url=url_for('home'))
            
            if not (-90 <= dest_coords[0] <= 90 and -180 <= dest_coords[1] <= 180):
                return render_template("error_page.html",
                                       error="Invalid destination coordinates",
                                       message="Destination latitude must be between -90 and 90, longitude between -180 and 180",
                                       back_url=url_for('home'))
                                       
        except ValueError:
            return render_template("error_page.html",
                                   error="Invalid coordinate format",
                                   message="Please use the format: latitude,longitude (e.g., 28.6139,77.2090)",
                                   back_url=url_for('home'))

        # Get routes from Google Maps
        print(f"Requesting routes from {source_coords} to {dest_coords}")
        
        try:
            directions = gmaps.directions(
                source_coords, dest_coords,
                mode="driving",
                alternatives=True,
                departure_time=datetime.now(),
                avoid=["tolls"] if tt_specs["gross_weight"] > 35000 else []
            )
        except Exception as api_error:
            print(f"Google Maps API error: {api_error}")
            return render_template("error_page.html",
                                   error="Route service error",
                                   message="Unable to fetch routes from Google Maps. Please check your internet connection and try again.",
                                   back_url=url_for('home'))

        if not directions:
            return render_template("error_page.html",
                                   error="No routes found",
                                   message="No driving routes could be found between the specified locations.",
                                   back_url=url_for('home'))

        print(f"Found {len(directions)} routes")

        # Validate route distances
        valid_routes = []
        for i, route in enumerate(directions):
            try:
                distance_text = route['legs'][0]['distance']['text']
                distance_km = extract_distance_km(distance_text)
                
                # Check distance limit for safety
                if distance_km > 500:
                    print(f"Route {i+1} exceeds 500km limit: {distance_text}")
                    continue
                
                valid_routes.append((i, route, distance_km))
            except Exception as e:
                print(f"Error processing route {i}: {e}")
                continue

        if not valid_routes:
            return render_template("error_page.html",
                                   error="No suitable routes",
                                   message="All available routes exceed the 500 km safety limit for truck tanker operations.",
                                   back_url=url_for('home'))

        # Store in session
        session['directions'] = directions
        session['source'] = source_coords
        session['destination'] = dest_coords
        session['tt_type'] = tt_type
        session['tt_specs'] = tt_specs
        session['valid_route_indices'] = [route[0] for route in valid_routes]
        session.modified = True

        # Process routes for selection
        routes = []
        for original_index, route, distance_km in valid_routes:
            try:
                coords = polyline.decode(route['overview_polyline']['points'])
                distance = route['legs'][0]['distance']['text']
                duration = route['legs'][0]['duration']['text']
                summary = route.get('summary', f"Route {len(routes)+1}")

                # Create preview map
                unique_id = uuid4().hex
                preview_file = f"route_preview_{original_index}_{unique_id}.html"
                m = folium.Map(location=coords[len(coords)//2], zoom_start=10)
                
                # Add route with weight-based color
                route_color = 'red' if tt_specs["gross_weight"] > 35000 else 'orange' if tt_specs["gross_weight"] > 25000 else 'blue'
                folium.PolyLine(coords, color=route_color, weight=5,
                                 popup=f"TT {tt_specs['capacity_range']} - {tt_specs['gross_weight']/1000:.1f}T").add_to(m)
                
                # Add markers
                folium.Marker(source_coords, popup='Start',
                                 icon=folium.Icon(color='green', icon='play')).add_to(m)
                folium.Marker(dest_coords, popup='End',
                                 icon=folium.Icon(color='red', icon='stop')).add_to(m)
                
                m.save(f"templates/{preview_file}")

                routes.append({
                    'index': original_index,
                    'distance': distance,
                    'duration': duration,
                    'summary': summary,
                    'preview_file': preview_file,
                    'tt_info': f"TT {tt_specs['capacity_range']} - {tt_specs['gross_weight']/1000:.1f}T",
                    'distance_km': distance_km
                })
            except Exception as e:
                print(f"Error processing route {original_index}: {e}")
                continue

        if not routes:
            return render_template("error_page.html",
                                   error="Route processing failed",
                                   message="Routes were found but could not be processed. Please try again.",
                                   back_url=url_for('home'))

        return render_template("route_selection.html", routes=routes, tt_info=f"{tt_specs['capacity_range']} ({tt_specs['gross_weight']/1000:.1f}T)")
        
    except Exception as e:
        import traceback
        traceback.print_exc()
        return render_template("error_page.html",
                               error="An unexpected error occurred",
                               message=str(e),
                               back_url=url_for('home'))

@app.route('/analyze_route/<int:route_index>')
def analyze_route(route_index):
    """Analyze a selected route and display detailed map and report"""
    directions = session.get('directions')
    tt_specs = session.get('tt_specs')
    source_coords = session.get('source')
    dest_coords = session.get('destination')
    valid_route_indices = session.get('valid_route_indices')

    if not directions or not tt_specs or route_index not in valid_route_indices:
        return render_template("error_page.html",
                               error="Invalid route",
                               message="The selected route is no longer available or an error occurred.",
                               back_url=url_for('home'))
                               
    try:
        selected_route = directions[route_index]
        route_coords = polyline.decode(selected_route['overview_polyline']['points'])
        total_distance = selected_route['legs'][0]['distance']['text']
        total_duration = selected_route['legs'][0]['duration']['text']

        # Get relevant POIs along the route
        # Using a simulated list for this example
        pois = [
            {'location': (28.6139, 77.2090), 'type': 'hospital', 'name': 'Delhi Hospital'},
            {'location': (28.625, 77.215), 'type': 'fuel', 'name': 'IOCL Fuel Pump'},
            {'location': (28.59, 77.19), 'type': 'police', 'name': 'Delhi Police Station'},
            # Add more simulated POIs as needed
        ]
        
        # Interpolate coordinates for finer analysis
        interpolated_coords = interpolate_route_points(route_coords)
        
        # Analyze route for risks, traffic, and speed
        risk_zones = identify_high_risk_zones(interpolated_coords, pois, tt_specs)
        traffic_data = get_traffic_data(interpolated_coords)
        
        # Create final map with all data layers
        m = folium.Map(location=source_coords, zoom_start=10)

        # Add route line
        route_color = 'red' if tt_specs["gross_weight"] > 35000 else 'orange' if tt_specs["gross_weight"] > 25000 else 'blue'
        folium.PolyLine(interpolated_coords, color=route_color, weight=5, opacity=0.7).add_to(m)

        # Add start and end markers
        folium.Marker(source_coords, popup=f"Source: {source_coords}", icon=folium.Icon(color='green', icon='play')).add_to(m)
        folium.Marker(dest_coords, popup=f"Destination: {dest_coords}", icon=folium.Icon(color='red', icon='stop')).add_to(m)
        
        # Add risk zones with custom icons and popups
        for zone in risk_zones:
            folium.CircleMarker(
                location=zone['location'],
                radius=10,
                color='red',
                fill=True,
                fill_color='red',
                fill_opacity=0.6,
                popup=f"<b>Risk Level: {zone['risk_level']}</b><br>"
                      f"Score: {zone['risk_score']:.1f}<br>"
                      f"Factors: {', '.join(zone['risk_factors'])}<br>"
                      f"TT Impact: {zone['tt_impact']}x"
            ).add_to(m)
            
        # Add traffic data as colored circles
        for traffic in traffic_data:
            color = 'green' if traffic['traffic_level'] == 'light' else 'orange' if traffic['traffic_level'] == 'moderate' else 'red'
            folium.CircleMarker(
                location=traffic['location'],
                radius=5,
                color=color,
                fill=True,
                fill_color=color,
                fill_opacity=0.4,
                popup=f"Traffic: {traffic['traffic_level']}"
            ).add_to(m)

        # Generate report
        report = generate_route_report(interpolated_coords, pois, risk_zones, traffic_data, total_distance, total_duration, tt_specs)

        # Save the map to a temporary file
        map_file = f"route_map_{uuid4().hex}.html"
        m.save(f"templates/{map_file}")
        
        return render_template("route_detail.html",
                               report=report,
                               map_file=map_file,
                               tt_type=tt_specs['capacity_range'])

    except Exception as e:
        print(f"Error during route analysis: {e}")
        import traceback
        traceback.print_exc()
        return render_template("error_page.html",
                               error="Analysis Failed",
                               message="An error occurred while analyzing the route. Please try a different route.",
                               back_url=url_for('home'))

@app.route('/uploads/<path:filename>')
def serve_file(filename):
    """Serve temporary map files"""
    return send_from_directory('templates', filename)

if __name__ == '__main__':
    app.run(debug=True, host='0.0.0.0', port=5000)
