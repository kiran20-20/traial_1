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

app = Flask(__name__)
app.secret_key = 'your_secret_key_here'
app.config['SESSION_TYPE'] = 'filesystem'
Session(app)

API_KEY = os.environ.get("API_KEY")  # Secure access
gmaps = googlemaps.Client(key=API_KEY)

# Constants for truck navigation
TRUCK_WEIGHT = 37.5  # Average of 30-45 tonnes
MAX_SPEED_LIMIT = 60  # kmph
SAFE_TURN_ANGLE = 130  # degrees
DANGEROUS_TURN_ANGLE = 30  # degrees

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

def get_recommended_speed(turn_angle, road_type="urban"):
    """Calculate recommended speed based on turn angle and road type"""
    try:
        base_speed = 40 if road_type == "urban" else 50
        
        if turn_angle < 15:  # Straight/slight curve
            return min(MAX_SPEED_LIMIT, base_speed + 10)
        elif turn_angle < 30:  # Moderate turn
            return min(MAX_SPEED_LIMIT, base_speed)
        elif turn_angle < 45:  # Sharp turn
            return min(40, base_speed - 10)
        elif turn_angle < 90:  # Very sharp turn
            return min(30, base_speed - 20)
        else:  # U-turn or extreme turn
            return 15
    except:
        return 30  # Default safe speed

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

def identify_high_risk_zones(coords, pois):
    """Identify high-risk zones based on various factors"""
    risk_zones = []
    
    try:
        for i, (lat, lng) in enumerate(coords):
            risk_score = 0
            risk_factors = []
            
            # Check proximity to hospitals (accident-prone areas)
            try:
                hospital_count = sum(1 for poi in pois if poi['type'] == 'hospital' 
                               and geodesic((lat, lng), poi['location']).meters < 500)
                if hospital_count > 0:
                    risk_score += hospital_count * 2
                    risk_factors.append(f"{hospital_count} hospital(s) nearby")
            except:
                pass
            
            # Check for intersections (every 10th point approximation)
            if i % 10 == 0 and i > 0 and i < len(coords) - 10:
                try:
                    # Simplified intersection detection based on bearing changes
                    prev_bearing = calculate_bearing(coords[i-10][0], coords[i-10][1], lat, lng)
                    next_bearing = calculate_bearing(lat, lng, coords[i+10][0], coords[i+10][1])
                    turn_angle = calculate_turn_angle(prev_bearing, next_bearing)
                    
                    if turn_angle > 30:
                        risk_score += 3
                        risk_factors.append("Sharp turn/intersection")
                except:
                    pass
            
            # Add random factors for demonstration (Crowded zones, construction, etc.)
            try:
                if np.random.random() < 0.05:  # 5% chance
                    risk_score += 4
                    risk_factors.append("Crowded zone")
                
                if np.random.random() < 0.03:  # 3% chance
                    risk_score += 5
                    risk_factors.append("Construction zone")
            except:
                pass
            
            if risk_score >= 3:
                risk_zones.append({
                    'location': (lat, lng),
                    'risk_score': risk_score,
                    'risk_factors': risk_factors,
                    'risk_level': 'High' if risk_score >= 6 else 'Medium'
                })
    except Exception as e:
        print(f"Error identifying risk zones: {e}")
    
    return risk_zones

def generate_route_report(coords, pois, risk_zones, traffic_data, total_distance, total_duration):
    """Generate a detailed route analysis report"""
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
            'truck_weight': TRUCK_WEIGHT,
            'max_speed_limit': MAX_SPEED_LIMIT,
            'route_analysis': {
                'total_points': len(coords),
                'points_per_km': len(coords) / distance_value,
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
                f"Maintain speed below {MAX_SPEED_LIMIT} kmph at all times",
                f"Extra caution required at {len([z for z in risk_zones if z['risk_level'] == 'High'])} high-risk zones",
                "Reduce speed to 15-30 kmph at sharp turns",
                "Plan for fuel stops at marked stations",
                "Keep emergency contacts handy for police/hospital locations"
            ]
        }
        
        return report
    except Exception as e:
        print(f"Error generating report: {e}")
        return {
            'total_distance': total_distance or "N/A",
            'total_duration': total_duration or "N/A",
            'truck_weight': TRUCK_WEIGHT,
            'max_speed_limit': MAX_SPEED_LIMIT,
            'route_analysis': {
                'total_points': len(coords),
                'points_per_km': 1,
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
                f"Maintain speed below {MAX_SPEED_LIMIT} kmph at all times"
            ]
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
def home():
    """Main route form page - no login required"""
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

        # Create the route_form.html content and save it to templates folder
        route_form_content = '''<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <title>IndianOil Smart Marg</title>
  <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
  <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.4.0/css/all.min.css">
  <style>
    body {
      margin: 0;
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Oxygen;
      background: linear-gradient(to right, #f8f9fa, #e0e0e0);
      min-height: 100vh;
      display: flex;
      align-items: center;
      justify-content: center;
      padding: 20px;
    }
    .form-box {
      background-color: white;
      padding: 40px;
      border-radius: 16px;
      box-shadow: 0 0 30px rgba(0,0,0,0.1);
      width: 100%;
      max-width: 480px;
      position: relative;
      text-align: center;
    }
    .heading-container {
      position: relative;
      display: inline-block;
      margin-bottom: 30px;
      padding: 20px 40px;
      border: 2px solid #0057b7;
      border-radius: 10px;
      box-shadow: 0 0 15px rgba(0, 87, 183, 0.2);
    }
    .heading-container h2 {
      font-size: 1.8em;
      font-weight: bold;
      color: #0057b7;
      margin: 0;
      position: relative;
      z-index: 2;
    }
    .rectangle-path {
      position: absolute;
      top: 0;
      left: 0;
      width: 100%;
      height: 100%;
      z-index: 1;
      pointer-events: none;
    }
    .orbit-dot {
      position: absolute;
      width: 20px;
      height: 12px;
      background-color: orange;
      border-radius: 4px;
      box-shadow: 0 0 10px orange;
      animation: moveRect 4s linear infinite;
    }
    @keyframes moveRect {
      0%   { top: 0; left: 0; }
      25%  { top: 0; left: calc(100% - 20px); }
      50%  { top: calc(100% - 12px); left: calc(100% - 20px); }
      75%  { top: calc(100% - 12px); left: 0; }
      100% { top: 0; left: 0; }
    }
    label {
      font-weight: 600;
      margin-top: 10px;
      display: block;
      text-align: left;
    }
    input, select {
      width: 100%;
      padding: 12px;
      margin: 10px 0;
      font-size: 1rem;
      border: 1px solid #ccc;
      border-radius: 8px;
      box-sizing: border-box;
    }
    button {
      width: 100%;
      padding: 14px;
      font-size: 1rem;
      background-color: #0071e3;
      border: none;
      color: white;
      border-radius: 8px;
      cursor: pointer;
      margin-top: 20px;
    }
    button:hover {
      background-color: #005bb5;
    }
    .footer {
      margin-top: 20px;
      font-size: 0.9rem;
      text-align: center;
      color: #888;
    }
    datalist option {
      padding: 10px;
    }
    .section-divider {
      margin: 30px 0;
      border-top: 2px solid #e0e0e0;
      padding-top: 20px;
    }
    .section-title {
      font-size: 1.2em;
      font-weight: bold;
      color: #0057b7;
      margin-bottom: 15px;
      text-align: left;
    }
    .coord-helper {
      font-size: 0.8em;
      color: #666;
      margin-top: 5px;
    }
  </style>
</head>
<body>

  <form class="form-box" method="POST" action="{{ url_for('fetch_routes') }}">
    <div class="heading-container">
      <h2>IndianOil Smart Marg</h2>
      <div class="rectangle-path">
        <div class="orbit-dot"></div>
      </div>
    </div>

    <!-- Source Location Section -->
    <div class="section-title">📍 Terminal Location</div>
    
    <label for="landmark_name">IOCL Terminal (Optional)</label>
    <input type="text" id="landmark_name" list="landmarkList" placeholder="Start typing landmark name...">
    <datalist id="landmarkList">
      {% for lm in landmarks %}
        <option value="{{ lm['name'] }}">
      {% endfor %}
    </datalist>

    <label for="source">Terminal Coordinates</label>
    <input type="text" name="source" id="source" placeholder="Enter coordinates (lat, lng) or select landmark above" required>
    <div class="coord-helper">Example: 28.6139, 77.2090 (New Delhi)</div>

    <!-- Destination Section -->
    <div class="section-divider">
      <div class="section-title">🎯 RO Location</div>

      <label for="destination">Destination Coordinates</label>
      <input type="text" name="destination" id="destination" placeholder="Enter coordinates manually (lat, lng)" required>
      <div class="coord-helper">Example: 19.0760, 72.8777 (Mumbai)</div>
    </div>

    <!-- Vehicle Type Section -->
    <div class="section-divider">
      <div class="section-title">🚛 Vehicle Type</div>
      
      <label for="vehicle">Select Vehicle Mode</label>
      <select id="vehicle" name="vehicle" required>
        <option value="">Choose Vehicle Type</option>
        <option value="driving">🚛 Truck (Driving)</option>
        <option value="walking">🚶 Walking</option>
        <option value="transit">🚌 Public Transit</option>
      </select>
    </div>

    <button type="submit"><i class="fa-solid fa-route"></i> Generate Routes</button>
    <div class="footer">© 2025 IndianOil Corporation Ltd.</div>
  </form>

  <script>
    // IOCL Landmark autofill for SOURCE only
    const landmarkData = {{ landmarks | tojson }};
    
    document.getElementById('landmark_name').addEventListener('input', function () {
      const name = this.value;
      const match = landmarkData.find(item => item.name === name);
      const sourceInput = document.getElementById('source');
      if (match) {
        sourceInput.value = `${match.lat}, ${match.lng}`;
      } else if (name === "") {
        sourceInput.value = "";
      }
    });

    // Allow manual coordinate entry for source
    document.getElementById('source').addEventListener('focus', function() {
      this.placeholder = "Enter coordinates manually (lat, lng)";
    });
  </script>
</body>
</html>'''

        # Ensure templates directory exists
        if not os.path.exists("templates"):
            os.makedirs("templates")
            
        # Save the route_form.html template
        with open("templates/route_form.html", "w", encoding="utf-8") as f:
            f.write(route_form_content)

        # Pass landmarks to template
        return render_template(
            "route_form.html",
            landmarks=landmarks
        )
        
    except Exception as e:
        print(f"Error loading data: {e}")
        import traceback
        traceback.print_exc()
        # Return a simple fallback page if everything fails
        return f"""
        <html><body>
        <h2>IndianOil Smart Marg</h2>
        <p>Basic form (landmarks unavailable)</p>
        <form method="POST" action="/fetch_routes">
            <p>Source: <input type="text" name="source" placeholder="lat,lng" required></p>
            <p>Destination: <input type="text" name="destination" placeholder="lat,lng" required></p>
            <p>Vehicle: 
                <select name="vehicle" required>
                    <option value="">Choose</option>
                    <option value="driving">Driving</option>
                    <option value="walking">Walking</option>
                    <option value="transit">Transit</option>
                </select>
            </p>
            <button type="submit">Generate Routes</button>
        </form>
        <p>Error: {str(e)}</p>
        </body></html>
        """

@app.route('/fetch_routes', methods=['POST'])
def fetch_routes():
    """Generate routes based on form input"""
    try:
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
        vehicle = request.form['vehicle']

        # Validate coordinates
        try:
            source_coords = tuple(map(float, source.split(',')))
            dest_coords = tuple(map(float, destination.split(',')))
        except ValueError:
            return "Invalid coordinates format. Please use: latitude,longitude"

        # Get routes from Google Maps
        directions = gmaps.directions(
            source_coords, dest_coords,
            mode=vehicle,
            alternatives=True,
            departure_time=datetime.now()
        )

        if not directions:
            return "No routes found between the specified locations."

        # Store in session
        session['directions'] = directions
        session['source'] = source_coords
        session['destination'] = dest_coords
        session['vehicle'] = vehicle
        session.modified = True

        # Create route_select.html template if it doesn't exist
        route_select_content = '''<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <title>Select Route - IndianOil Smart Marg</title>
    <style>
        body {
            font-family: Arial, sans-serif;
            margin: 20px;
            background: linear-gradient(to right, #f8f9fa, #e0e0e0);
        }
        .container {
            max-width: 800px;
            margin: 0 auto;
            background: white;
            padding: 20px;
            border-radius: 10px;
            box-shadow: 0 0 20px rgba(0,0,0,0.1);
        }
        h1 {
            color: #0057b7;
            text-align: center;
        }
        .route-option {
            border: 1px solid #ddd;
            margin: 15px 0;
            padding: 20px;
            border-radius: 8px;
            background: #f9f9f9;
        }
        .route-option h3 {
            color: #0057b7;
            margin-top: 0;
        }
        .route-info {
            display: flex;
            justify-content: space-between;
            margin: 10px 0;
        }
        .route-info span {
            font-weight: bold;
        }
        button {
            background-color: #0071e3;
            color: white;
            border: none;
            padding: 10px 20px;
            border-radius: 5px;
            cursor: pointer;
            font-size: 16px;
        }
        button:hover {
            background-color: #005bb5;
        }
        .preview {
            margin: 10px 0;
            height: 200px;
            border: 1px solid #ccc;
            border-radius: 5px;
        }
    </style>
</head>
<body>
    <div class="container">
        <h1>🚛 Select Your Route</h1>
        
        {% for route in routes %}
        <div class="route-option">
            <h3>Route {{ route.index + 1 }}: {{ route.summary }}</h3>
            <div class="route-info">
                <span>Distance: {{ route.distance }}</span>
                <span>Duration: {{ route.duration }}</span>
            </div>
            
            {% if route.preview_file %}
            <iframe src="{{ url_for('view_preview', filename=route.preview_file) }}" 
                    class="preview" frameborder="0"></iframe>
            {% endif %}
            
            <form method="POST" action="{{ url_for('analyze_route') }}" style="margin-top: 15px;">
                <input type="hidden" name="route_index" value="{{ route.index }}">
                <button type="submit">🔍 Analyze This Route</button>
            </form>
        </div>
        {% endfor %}
        
        <div style="text-align: center; margin-top: 30px;">
            <a href="{{ url_for('home') }}" style="text-decoration: none;">
                <button>🏠 Start Over</button>
            </a>
        </div>
    </div>
</body>
</html>'''

        with open("templates/route_select.html", "w", encoding="utf-8") as f:
            f.write(route_select_content)

        # Process routes for selection
        routes = []
        for i, route in enumerate(directions):
            try:
                coords = polyline.decode(route['overview_polyline']['points'])
                distance = route['legs'][0]['distance']['text']
                duration = route['legs'][0]['duration']['text']
                summary = route.get('summary', f"Route {i+1}")

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
                    'summary': summary,
                    'preview_file': preview_file
                })
            except Exception as e:
                print(f"Error processing route {i}: {e}")
                continue

        return render_template("route_select.html", routes=routes)
    
    except Exception as e:
        print(f"Error in fetch_routes: {e}")
        import traceback
        traceback.print_exc()
        return f"Error processing route request: {str(e)}"

@app.route('/analyze_route', methods=['POST'])
def analyze_route():
    """Analyze the selected route"""
    try:
        directions = session.get('directions')
        index = int(request.form['route_index'])

        if not directions or index >= len(directions):
            return "Invalid route selected or session data expired. Please start over."

        selected = directions[index]
        steps = selected['legs'][0]['steps']
        coords = polyline.decode(selected['overview_polyline']['points'])
        source = session['source']
        destination = session['destination']
        
        # Get route details
        total_distance = selected['legs'][0]['distance']['text']
        total_duration = selected['legs'][0]['duration']['text']

        # Interpolate route for more precise mapping (10 points per km)
        detailed_coords = interpolate_route_points(coords, points_per_km=10)
        
        def get_pois(keyword):
            pois = []
            try:
                # Use detailed coords for more precise POI detection
                sample_coords = detailed_coords[::20] if len(detailed_coords) > 20 else detailed_coords
                for lat, lng in sample_coords:
                    try:
                        places = gmaps.places_nearby(location=(lat, lng), radius=300, keyword=keyword)
                        for place in places.get('results', []):
                            pois.append({
                                'name': place['name'],
                                'location': (
                                    place['geometry']['location']['lat'],
                                    place['geometry']['location']['lng']
                                ),
                                'type': keyword
                            })
                    except Exception as e:
                        print(f"Error getting places for {keyword}: {e}")
                        continue
            except Exception as e:
                print(f"Error in get_pois for {keyword}: {e}")
            return pois

        all_pois = []
        for keyword in ['hospital', 'police', 'fuel']:
            all_pois.extend(get_pois(keyword))

        # Get traffic data
        traffic_data = get_traffic_data(detailed_coords)
        
        # Identify high-risk zones
        risk_zones = identify_high_risk_zones(detailed_coords, all_pois)
        
        # Generate detailed report
        route_report = generate_route_report(detailed_coords, all_pois, risk_zones, 
                                           traffic_data, total_distance, total_duration)

        # Create enhanced map
        m = folium.Map(location=source, zoom_start=13)
        
        # Add start and end markers
        folium.Marker(source, popup='Start', 
                     icon=folium.Icon(color='green', icon='flag', prefix='fa')).add_to(m)
        folium.Marker(destination, popup='End', 
                     icon=folium.Icon(color='black', icon='flag-checkered', prefix='fa')).add_to(m)
        
        # Add main route with speed indicators
        for i, (lat, lng) in enumerate(detailed_coords):
            if i > 0 and i < len(detailed_coords) - 1 and i % 50 == 0:
                try:
                    # Calculate turn angle for speed recommendation
                    prev_coord = detailed_coords[i-1]
                    next_coord = detailed_coords[i+1]
                    
                    prev_bearing = calculate_bearing(prev_coord[0], prev_coord[1], lat, lng)
                    next_bearing = calculate_bearing(lat, lng, next_coord[0], next_coord[1])
                    turn_angle = calculate_turn_angle(prev_bearing, next_bearing)
                    
                    recommended_speed = get_recommended_speed(turn_angle)
                    
                    # Add truck icon with speed popup
                    truck_html = f"""
                    <div style='text-align: center; font-family: Arial;'>
                        <div style='font-size: 20px;'>🚛</div>
                        <div style='background-color: {"red" if recommended_speed < 30 else "orange" if recommended_speed < 45 else "green"}; 
                                    color: white; padding: 2px 5px; border-radius: 3px; font-weight: bold;'>
                            {recommended_speed} km/h
                        </div>
                        <div style='font-size: 10px; margin-top: 2px;'>
                            Turn: {turn_angle:.1f}° | Weight: {TRUCK_WEIGHT}T
                        </div>
                    </div>
                    """
                    
                    folium.Marker(
                        location=(lat, lng),
                        popup=truck_html,
                        icon=folium.DivIcon(html=truck_html, icon_size=(60, 60), icon_anchor=(30, 30))
                    ).add_to(m)
                except Exception as e:
                    print(f"Error adding truck marker: {e}")
                    continue

        # Add route polyline
        folium.PolyLine(detailed_coords, color='blue', weight=4, opacity=0.8).add_to(m)

        # Add POIs with enhanced icons
        marker_styles = {
            'hospital': {'color': 'red', 'icon': 'plus'},
            'police': {'color': 'blue', 'icon': 'shield'},
            'fuel': {'color': 'orange', 'icon': 'gas-pump'}
        }

        for poi in all_pois:
            try:
                props = marker_styles.get(poi['type'], {'color': 'gray', 'icon': 'info-circle'})
                icon = folium.Icon(color=props['color'], icon=props['icon'], prefix='fa')
                folium.Marker(
                    location=poi['location'],
                    popup=f"{poi['type'].capitalize()}: {poi['name']}",
                    icon=icon
                ).add_to(m)
            except Exception as e:
                print(f"Error adding POI marker: {e}")
                continue

        # Add high-risk zones
        for zone in risk_zones:
            try:
                color = 'red' if zone['risk_level'] == 'High' else 'orange'
                risk_popup = f"""
                <div style='font-family: Arial; max-width: 200px;'>
                    <h4 style='color: {color};'>⚠️ {zone['risk_level']} Risk Zone</h4>
                    <p><strong>Risk Score:</strong> {zone['risk_score']}/10</p>
                    <p><strong>Factors:</strong><br>{'<br>'.join(zone['risk_factors'])}</p>
                </div>
                """
                
                folium.CircleMarker(
                    location=zone['location'],
                    radius=15,
                    popup=risk_popup,
                    color=color,
                    fillColor=color,
                    fillOpacity=0.3,
                    weight=3
                ).add_to(m)
            except Exception as e:
                print(f"Error adding risk zone: {e}")
                continue

        # Add traffic indicators
        for traffic in traffic_data:
            try:
                color = {'light': 'green', 'moderate': 'yellow', 'heavy': 'red'}[traffic['traffic_level']]
                folium.CircleMarker(
                    location=traffic['location'],
                    radius=5,
                    popup=f"Traffic: {traffic['traffic_level'].title()}<br>Delay Factor: {traffic['delay_factor']:.1f}x",
                    color=color,
                    fillColor=color,
                    fillOpacity=0.6
                ).add_to(m)
            except Exception as e:
                print(f"Error adding traffic indicator: {e}")
                continue

        # Fixed legend HTML
        legend_html = f"""
        {{% macro html(this, kwargs) %}}
        <div style="
            position: fixed;
            bottom: 50px;
            left: 50px;
            width: 280px;
            background-color: white;
            border: 2px solid grey;
            border-radius: 8px;
            z-index: 9999;
            padding: 15px;
            font-size: 12px;
            box-shadow: 0 4px 8px rgba(0,0,0,0.1);
        ">
            <h4 style='margin-top: 0; color: #333;'>🚛 Truck Navigation Legend</h4>
            <div style='margin: 5px 0;'><i class="fa fa-plus fa-lg" style="color:red"></i> Hospital</div>
            <div style='margin: 5px 0;'><i class="fa fa-shield fa-lg" style="color:blue"></i> Police</div>
            <div style='margin: 5px 0;'><i class="fa fa-gas-pump fa-lg" style="color:orange"></i> Fuel Station</div>
            <div style='margin: 5px 0;'>🚛 <span style='background: green; color: white; padding: 1px 3px;'>50+</span> Safe Speed</div>
            <div style='margin: 5px 0;'>🚛 <span style='background: orange; color: white; padding: 1px 3px;'>30-45</span> Caution Speed</div>
            <div style='margin: 5px 0;'>🚛 <span style='background: red; color: white; padding: 1px 3px;'>&lt;30</span> Slow Speed</div>
            <div style='margin: 5px 0;'>🔴 High Risk Zone</div>
            <div style='margin: 5px 0;'>🟡 Medium Risk Zone</div>
            <div style='margin: 5px 0;'>● Traffic: <span style='color: green;'>Light</span> <span style='color: orange;'>Moderate</span> <span style='color: red;'>Heavy</span></div>
            <hr style='margin: 10px 0;'>
            <div style='font-size: 10px; color: #666;'>
                Max Weight: {TRUCK_WEIGHT}T | Speed Limit: {MAX_SPEED_LIMIT} km/h
            </div>
        </div>
        {{% endmacro %}}
        """
        
        legend = MacroElement()
        legend._template = Template(legend_html)
        m.get_root().add_child(legend)

        # Save map
        unique_map_id = uuid4().hex
        html_name = f"route_map_{unique_map_id}.html"
        m.save(f"templates/{html_name}")

        # Store report in session for detailed view
        session['route_report'] = route_report
        session.modified = True

        # Create route_analysis.html template if it doesn't exist
        route_analysis_content = '''<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <title>Route Analysis - IndianOil Smart Marg</title>
    <style>
        body {
            font-family: Arial, sans-serif;
            margin: 0;
            background: linear-gradient(to right, #f8f9fa, #e0e0e0);
            min-height: 100vh;
        }
        .container {
            max-width: 1200px;
            margin: 0 auto;
            padding: 20px;
        }
        .header {
            background: white;
            padding: 20px;
            border-radius: 10px;
            margin-bottom: 20px;
            box-shadow: 0 2px 10px rgba(0,0,0,0.1);
            text-align: center;
        }
        .header h1 {
            color: #0057b7;
            margin: 0;
        }
        .stats-grid {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(250px, 1fr));
            gap: 20px;
            margin-bottom: 20px;
        }
        .stat-card {
            background: white;
            padding: 20px;
            border-radius: 10px;
            box-shadow: 0 2px 10px rgba(0,0,0,0.1);
            text-align: center;
        }
        .stat-card h3 {
            color: #0057b7;
            margin-top: 0;
        }
        .stat-value {
            font-size: 2em;
            font-weight: bold;
            color: #333;
            margin: 10px 0;
        }
        .map-container {
            background: white;
            padding: 20px;
            border-radius: 10px;
            box-shadow: 0 2px 10px rgba(0,0,0,0.1);
            margin-bottom: 20px;
        }
        .map-frame {
            width: 100%;
            height: 600px;
            border: none;
            border-radius: 8px;
        }
        .actions {
            text-align: center;
            margin: 20px 0;
        }
        .btn {
            display: inline-block;
            background-color: #0071e3;
            color: white;
            text-decoration: none;
            padding: 12px 24px;
            border-radius: 6px;
            margin: 0 10px;
            font-weight: bold;
        }
        .btn:hover {
            background-color: #005bb5;
        }
        .btn-secondary {
            background-color: #6c757d;
        }
        .btn-secondary:hover {
            background-color: #545b62;
        }
        .alert {
            padding: 15px;
            margin: 15px 0;
            border-radius: 8px;
            border-left: 4px solid #ffc107;
            background-color: #fff3cd;
            color: #856404;
        }
        .recommendations {
            background: white;
            padding: 20px;
            border-radius: 10px;
            box-shadow: 0 2px 10px rgba(0,0,0,0.1);
        }
        .recommendations h3 {
            color: #0057b7;
        }
        .recommendations ul {
            padding-left: 20px;
        }
        .recommendations li {
            margin: 10px 0;
        }
    </style>
</head>
<body>
    <div class="container">
        <div class="header">
            <h1>🚛 Route Analysis Complete</h1>
            <p>Vehicle Mode: {{ mode|title }} | Analysis Generated</p>
        </div>

        <div class="stats-grid">
            <div class="stat-card">
                <h3>📏 Total Distance</h3>
                <div class="stat-value">{{ route_report.total_distance }}</div>
            </div>
            <div class="stat-card">
                <h3>⏱️ Estimated Duration</h3>
                <div class="stat-value">{{ route_report.total_duration }}</div>
            </div>
            <div class="stat-card">
                <h3>⚠️ Risk Zones</h3>
                <div class="stat-value">{{ high_risk_zones }}</div>
                <small>High Risk Areas</small>
            </div>
            <div class="stat-card">
                <h3>🏥 POIs Found</h3>
                <div class="stat-value">{{ poi_count }}</div>
                <small>Hospitals, Police, Fuel</small>
            </div>
        </div>

        {% if high_risk_zones > 0 %}
        <div class="alert">
            <strong>⚠️ Caution Required:</strong> This route contains {{ high_risk_zones }} high-risk zones. 
            Please review the detailed map below and exercise extra caution in marked areas.
        </div>
        {% endif %}

        <div class="map-container">
            <h3>🗺️ Interactive Route Map</h3>
            <iframe src="{{ url_for('view_map', filename=html_file) }}" 
                    class="map-frame"></iframe>
        </div>

        <div class="recommendations">
            <h3>🛡️ Safety Recommendations</h3>
            <ul>
                {% for recommendation in route_report.safety_recommendations %}
                <li>{{ recommendation }}</li>
                {% endfor %}
            </ul>
        </div>

        <div class="actions">
            <a href="{{ url_for('detailed_report') }}" class="btn">📊 View Detailed Report</a>
            <a href="{{ url_for('download_map', filename=html_file) }}" class="btn btn-secondary">💾 Download Map</a>
            <a href="{{ url_for('home') }}" class="btn btn-secondary">🏠 Start Over</a>
        </div>
    </div>
</body>
</html>'''

        with open("templates/route_analysis.html", "w", encoding="utf-8") as f:
            f.write(route_analysis_content)

        return render_template("route_analysis.html",
                               mode=session['vehicle'],
                               turns=sum("turn" in s['html_instructions'].lower() for s in steps),
                               poi_count=len(all_pois),
                               html_file=html_name,
                               route_report=route_report,
                               risk_zones=len(risk_zones),
                               high_risk_zones=len([z for z in risk_zones if z['risk_level'] == 'High']))

    except Exception as e:
        print(f"Error in analyze_route: {e}")
        import traceback
        traceback.print_exc()
        return f"Error analyzing route: {str(e)}. Please try again."

@app.route('/detailed_report')
def detailed_report():
    """Show detailed route analysis report"""
    try:
        report = session.get('route_report')
        if not report:
            return "No route analysis data found. Please analyze a route first."
        
        # Create detailed_report.html template if it doesn't exist
        detailed_report_content = '''<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <title>Detailed Route Report - IndianOil Smart Marg</title>
    <style>
        body {
            font-family: Arial, sans-serif;
            margin: 0;
            background: linear-gradient(to right, #f8f9fa, #e0e0e0);
            min-height: 100vh;
            padding: 20px;
        }
        .container {
            max-width: 900px;
            margin: 0 auto;
            background: white;
            border-radius: 10px;
            box-shadow: 0 4px 20px rgba(0,0,0,0.1);
            overflow: hidden;
        }
        .header {
            background: linear-gradient(135deg, #0057b7, #0071e3);
            color: white;
            padding: 30px;
            text-align: center;
        }
        .header h1 {
            margin: 0;
            font-size: 2.5em;
        }
        .content {
            padding: 30px;
        }
        .section {
            margin-bottom: 30px;
            padding: 20px;
            border-left: 4px solid #0071e3;
            background: #f8f9fa;
            border-radius: 0 8px 8px 0;
        }
        .section h2 {
            color: #0057b7;
            margin-top: 0;
            display: flex;
            align-items: center;
        }
        .section h2 i {
            margin-right: 10px;
        }
        .info-grid {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
            gap: 15px;
            margin: 15px 0;
        }
        .info-item {
            background: white;
            padding: 15px;
            border-radius: 8px;
            border: 1px solid #e0e0e0;
        }
        .info-item strong {
            color: #0057b7;
            display: block;
            margin-bottom: 5px;
        }
        .info-value {
            font-size: 1.2em;
            font-weight: bold;
            color: #333;
        }
        .recommendations {
            background: #fff3cd;
            border: 1px solid #ffeaa7;
            border-radius: 8px;
            padding: 20px;
            margin: 20px 0;
        }
        .recommendations h3 {
            color: #856404;
            margin-top: 0;
        }
        .recommendations ul {
            margin: 0;
            padding-left: 20px;
        }
        .recommendations li {
            margin: 8px 0;
        }
        .actions {
            text-align: center;
            margin: 30px 0;
            padding-top: 20px;
            border-top: 1px solid #e0e0e0;
        }
        .btn {
            display: inline-block;
            background-color: #0071e3;
            color: white;
            text-decoration: none;
            padding: 12px 24px;
            border-radius: 6px;
            margin: 0 10px;
            font-weight: bold;
        }
        .btn:hover {
            background-color: #005bb5;
        }
        .btn-secondary {
            background-color: #6c757d;
        }
        .btn-secondary:hover {
            background-color: #545b62;
        }
        .truck-specs {
            background: linear-gradient(135deg, #ff9500, #ffa726);
            color: white;
            padding: 20px;
            border-radius: 8px;
            margin: 20px 0;
        }
        .truck-specs h3 {
            margin-top: 0;
        }
        .progress-bar {
            background: #e0e0e0;
            border-radius: 10px;
            overflow: hidden;
            margin: 10px 0;
        }
        .progress-fill {
            height: 20px;
            background: linear-gradient(90deg, #28a745, #20c997);
            text-align: center;
            color: white;
            font-size: 12px;
            line-height: 20px;
            font-weight: bold;
        }
    </style>
</head>
<body>
    <div class="container">
        <div class="header">
            <h1>📊 Detailed Route Analysis Report</h1>
            <p>IndianOil Smart Marg - Comprehensive Truck Navigation Analysis</p>
        </div>

        <div class="content">
            <!-- Route Overview -->
            <div class="section">
                <h2>🛣️ Route Overview</h2>
                <div class="info-grid">
                    <div class="info-item">
                        <strong>Total Distance</strong>
                        <div class="info-value">{{ report.total_distance }}</div>
                    </div>
                    <div class="info-item">
                        <strong>Estimated Duration</strong>
                        <div class="info-value">{{ report.total_duration }}</div>
                    </div>
                    <div class="info-item">
                        <strong>Route Points</strong>
                        <div class="info-value">{{ report.route_analysis.total_points }}</div>
                    </div>
                    <div class="info-item">
                        <strong>Points per KM</strong>
                        <div class="info-value">{{ "%.1f"|format(report.route_analysis.points_per_km) }}</div>
                    </div>
                </div>
            </div>

            <!-- Truck Specifications -->
            <div class="truck-specs">
                <h3>🚛 Truck Specifications</h3>
                <div class="info-grid">
                    <div style="color: white;">
                        <strong>Maximum Weight:</strong> {{ report.truck_weight }} tonnes
                    </div>
                    <div style="color: white;">
                        <strong>Speed Limit:</strong> {{ report.max_speed_limit }} km/h
                    </div>
                </div>
            </div>

            <!-- Risk Analysis -->
            <div class="section">
                <h2>⚠️ Risk Zone Analysis</h2>
                <div class="info-grid">
                    <div class="info-item">
                        <strong>High Risk Zones</strong>
                        <div class="info-value" style="color: #dc3545;">{{ report.route_analysis.high_risk_zones }}</div>
                    </div>
                    <div class="info-item">
                        <strong>Medium Risk Zones</strong>
                        <div class="info-value" style="color: #fd7e14;">{{ report.route_analysis.medium_risk_zones }}</div>
                    </div>
                </div>
            </div>

            <!-- Points of Interest -->
            <div class="section">
                <h2>📍 Points of Interest Along Route</h2>
                <div class="info-grid">
                    <div class="info-item">
                        <strong>🏥 Hospitals</strong>
                        <div class="info-value">{{ report.route_analysis.hospitals_along_route }}</div>
                    </div>
                    <div class="info-item">
                        <strong>👮 Police Stations</strong>
                        <div class="info-value">{{ report.route_analysis.police_stations }}</div>
                    </div>
                    <div class="info-item">
                        <strong>⛽ Fuel Stations</strong>
                        <div class="info-value">{{ report.route_analysis.fuel_stations }}</div>
                    </div>
                </div>
            </div>

            <!-- Traffic Analysis -->
            <div class="section">
                <h2>🚦 Traffic Analysis</h2>
                <div class="info-grid">
                    <div class="info-item">
                        <strong>Light Traffic Segments</strong>
                        <div class="info-value" style="color: #28a745;">{{ report.traffic_analysis.light_traffic_segments }}</div>
                    </div>
                    <div class="info-item">
                        <strong>Moderate Traffic Segments</strong>
                        <div class="info-value" style="color: #ffc107;">{{ report.traffic_analysis.moderate_traffic_segments }}</div>
                    </div>
                    <div class="info-item">
                        <strong>Heavy Traffic Segments</strong>
                        <div class="info-value" style="color: #dc3545;">{{ report.traffic_analysis.heavy_traffic_segments }}</div>
                    </div>
                    <div class="info-item">
                        <strong>Average Delay Factor</strong>
                        <div class="info-value">{{ "%.1fx"|format(report.traffic_analysis.average_delay_factor) }}</div>
                    </div>
                </div>

                <!-- Traffic Distribution Progress Bar -->
                <div style="margin-top: 20px;">
                    <strong>Traffic Distribution:</strong>
                    <div class="progress-bar">
                        {% set total_segments = report.traffic_analysis.light_traffic_segments + report.traffic_analysis.moderate_traffic_segments + report.traffic_analysis.heavy_traffic_segments %}
                        {% if total_segments > 0 %}
                        {% set light_percent = (report.traffic_analysis.light_traffic_segments / total_segments * 100)|int %}
                        <div class="progress-fill" style="width: {{ light_percent }}%;">
                            {{ light_percent }}% Light Traffic
                        </div>
                        {% endif %}
                    </div>
                </div>
            </div>

            <!-- Safety Recommendations -->
            <div class="recommendations">
                <h3>🛡️ Safety Recommendations</h3>
                <ul>
                    {% for recommendation in report.safety_recommendations %}
                    <li>{{ recommendation }}</li>
                    {% endfor %}
                </ul>
            </div>

            <!-- Actions -->
            <div class="actions">
                <a href="javascript:window.history.back();" class="btn">⬅️ Back to Map</a>
                <a href="{{ url_for('home') }}" class="btn btn-secondary">🏠 New Route</a>
                <button onclick="window.print()" class="btn btn-secondary">🖨️ Print Report</button>
            </div>
        </div>
    </div>

    <script>
        // Print styles
        window.addEventListener('beforeprint', function() {
            document.body.style.background = 'white';
        });
    </script>
</body>
</html>'''

        with open("templates/detailed_report.html", "w", encoding="utf-8") as f:
            f.write(detailed_report_content)
        
        return render_template("detailed_report.html", report=report)
        
    except Exception as e:
        print(f"Error in detailed_report: {e}")
        return f"Error generating detailed report: {str(e)}"

@app.route('/view_map/<filename>')
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
def download_map(filename):
    try:
        return send_from_directory(directory='templates', path=filename, as_attachment=True)
    except Exception as e:
        print(f"Error downloading map: {e}")
        return f"Error downloading file: {str(e)}", 500

@app.route('/preview/<filename>')
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

@app.errorhandler(500)
def internal_error(error):
    print(f"Internal server error: {error}")
    return "Internal server error occurred. Please check the logs.", 500

@app.errorhandler(404)
def not_found_error(error):
    return "Page not found.", 404

if __name__ == '__main__':
    try:
        if not os.path.exists("templates"):
            os.makedirs("templates")
        app.run(debug=True)
    except Exception as e:
        print(f"Error starting application: {e}")
