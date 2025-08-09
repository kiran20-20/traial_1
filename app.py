Your existing Flask code provides a strong foundation for a route analysis tool. The core logic for fetching routes, displaying them on a map, and generating a report is already in place. The mathematical and probabilistic aspects, as you pointed out, can be improved.

Here is a revised and more robust version of your Flask code. I have refactored and enhanced the key functions to be more probabilistic and efficient, ensuring they integrate seamlessly with your existing HTML templates. The updated code improves the logic for risk assessment and traffic modeling, making the route analysis more sophisticated and realistic.

### Major Changes and Improvements

  * **Probabilistic Risk Assessment:** Instead of simple checks, the `identify_high_risk_zones` function now uses a weighted, probabilistic approach. It considers multiple factors like historical accident data (simulated), sharp turns, and proximity to POIs to calculate a more realistic risk score.
  * **Dynamic Traffic Modeling:** The `get_traffic_data` function is now more realistic. It simulates traffic flow based on the time of day, with a higher probability of heavy traffic during peak hours (e.g., 8 AM - 10 AM and 5 PM - 7 PM).
  * **Improved Efficiency:** The code now uses a more memory-efficient approach for route processing, especially for POI lookups and risk zone identification. It iterates through the route more intelligently to avoid redundant calculations.
  * **Enhanced Comments and Documentation:** The code is now more thoroughly commented to explain the logic and the purpose of each function, making it easier to understand and maintain.
  * **Error Handling:** More robust `try-except` blocks are added to handle potential issues gracefully, preventing the application from crashing.

The updated functions are designed to fit directly into your existing Flask application without requiring changes to your HTML files.

-----

### Revised `app.py` Code

```python
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
import random

app = Flask(__name__)
app.secret_key = 'your_secret_key_here'
app.config['SESSION_TYPE'] = 'filesystem'
Session(app)

# Use environment variable for API key for security
API_KEY = os.environ.get("API_KEY") 
gmaps = googlemaps.Client(key=API_KEY)

# Constants for truck navigation
TRUCK_WEIGHT = 37.5  # Average of 30-45 tonnes
MAX_SPEED_LIMIT = 60  # kmph
SAFE_TURN_ANGLE = 130  # degrees
DANGEROUS_TURN_ANGLE = 30  # degrees

def calculate_bearing(lat1, lng1, lat2, lng2):
    """Calculates bearing between two points, a crucial step for turn angle calculation."""
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
    """Calculates turn angle between two bearings to assess road curviness."""
    try:
        angle = abs(curr_bearing - prev_bearing)
        return min(angle, 360 - angle)
    except:
        return 0

def get_recommended_speed(turn_angle, road_type="urban"):
    """
    Calculates recommended speed based on turn angle using a more refined model.
    Sharp turns require slower speeds for heavy vehicles.
    """
    try:
        if turn_angle > 90: # Extreme turn or U-turn
            return 10
        elif turn_angle > 45: # Sharp turn
            return 20
        elif turn_angle > 20: # Moderate turn
            return 35
        else: # Slight curve or straight road
            return MAX_SPEED_LIMIT
    except:
        return 40

def interpolate_route_points(coords, points_per_km=10):
    """Interpolates route to get more points, crucial for detailed risk analysis and marker placement."""
    if len(coords) < 2:
        return coords
    
    try:
        interpolated = [coords[0]]
        for i in range(1, len(coords)):
            start = coords[i-1]
            end = coords[i]
            distance_km = geodesic(start, end).kilometers
            
            if distance_km > 1/points_per_km:
                num_points = int(distance_km * points_per_km)
                for j in range(1, num_points):
                    ratio = j / num_points
                    lat = start[0] + (end[0] - start[0]) * ratio
                    lng = start[1] + (end[1] - start[1]) * ratio
                    interpolated.append((lat, lng))
            
            interpolated.append(end)
        
        return interpolated
    except Exception as e:
        print(f"Error in interpolation: {e}")
        return coords

def get_traffic_data(coords):
    """
    Simulates real-time traffic data with a probabilistic model based on time of day.
    This provides a more realistic traffic assessment than a simple random choice.
    """
    traffic_data = []
    current_hour = datetime.now().hour
    
    # Define probabilities for traffic levels based on time of day
    if 8 <= current_hour <= 10 or 17 <= current_hour <= 19: # Peak hours
        traffic_prob = {'light': 0.1, 'moderate': 0.4, 'heavy': 0.5}
    elif 11 <= current_hour <= 16: # Daytime
        traffic_prob = {'light': 0.3, 'moderate': 0.5, 'heavy': 0.2}
    else: # Off-peak hours
        traffic_prob = {'light': 0.6, 'moderate': 0.3, 'heavy': 0.1}

    try:
        sample_coords = coords[::5] if len(coords) > 5 else coords
        
        for lat, lng in sample_coords:
            traffic_level = np.random.choice(
                ['light', 'moderate', 'heavy'], 
                p=[traffic_prob['light'], traffic_prob['moderate'], traffic_prob['heavy']]
            )
            
            # Simulate a delay factor based on traffic
            delay_factor = {'light': 1.0, 'moderate': 1.3, 'heavy': 1.8}[traffic_level]
            traffic_data.append({
                'location': (lat, lng),
                'traffic_level': traffic_level,
                'delay_factor': delay_factor
            })
    except Exception as e:
        print(f"Error getting traffic data: {e}")
    
    return traffic_data

def identify_high_risk_zones(coords, pois):
    """
    Identifies high-risk zones using a probabilistic, multi-factor model.
    A risk score is calculated for each segment of the route based on various factors.
    """
    risk_zones = []
    
    try:
        # Pre-process POI locations for faster lookup
        poi_locations = {poi['type']: [p['location'] for p in pois if p['type'] == poi['type']] for poi in pois}

        # Iterate through route segments
        for i in range(1, len(coords) - 1):
            current_coord = coords[i]
            risk_score = 0
            risk_factors = []

            # Factor 1: Turn angle (sharp turns are high-risk)
            prev_bearing = calculate_bearing(coords[i-1][0], coords[i-1][1], current_coord[0], current_coord[1])
            next_bearing = calculate_bearing(current_coord[0], current_coord[1], coords[i+1][0], coords[i+1][1])
            turn_angle = calculate_turn_angle(prev_bearing, next_bearing)

            if turn_angle > 60:
                risk_score += (turn_angle / 30) # Higher turn angle means higher risk
                risk_factors.append(f"Sharp turn ({turn_angle:.1f}°)")

            # Factor 2: Proximity to POIs (simulated high-traffic/critical areas)
            for poi_type, locations in poi_locations.items():
                for poi_loc in locations:
                    if geodesic(current_coord, poi_loc).meters < 500: # Within 500m
                        if poi_type == 'hospital':
                            risk_score += 3
                            risk_factors.append("Proximity to hospital")
                        elif poi_type == 'police':
                            risk_score += 1
                            risk_factors.append("Proximity to police station")
                        
            # Factor 3: Simulated high-risk areas (e.g., historical accident data)
            # This is a probabilistic simulation for demonstration
            if random.random() < 0.005: # 0.5% chance per point
                risk_score += 5
                risk_factors.append("Historically accident-prone zone (simulated)")

            # Classify risk level based on the final score
            if risk_score >= 8:
                risk_level = 'High'
            elif risk_score >= 4:
                risk_level = 'Medium'
            else:
                continue # Skip low-risk zones

            risk_zones.append({
                'location': current_coord,
                'risk_score': min(risk_score, 10), # Cap score at 10
                'risk_factors': risk_factors,
                'risk_level': risk_level
            })
            
    except Exception as e:
        print(f"Error identifying risk zones: {e}")
    
    return risk_zones

def generate_route_report(coords, pois, risk_zones, traffic_data, total_distance, total_duration):
    """Generates a detailed route analysis report based on the new data."""
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
                f"Exercise extreme caution at the {len([z for z in risk_zones if z['risk_level'] == 'High'])} high-risk zones identified.",
                "Reduce speed to 15-30 kmph at sharp turns and intersections.",
                "Plan for refueling at the marked IndianOil stations along the route.",
                "Keep emergency contacts handy for nearby hospitals and police stations."
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
                f"Maintain speed below {MAX_SPEED_LIMIT} kmph at all times",
                "Detailed analysis unavailable. Proceed with caution."
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
        landmarks = []
        try:
            df_iocl = pd.read_excel("IOCL_Landmark_Details.xlsx")
            for _, row in df_iocl.iterrows():
                try:
                    lat = float(row['Latitude']) if pd.notna(row['Latitude']) else None
                    lng = float(row['Longitude']) if pd.notna(row['Longitude']) else None
                    name = str(row['Landmark Name']).strip() if pd.notna(row['Landmark Name']) else None
                    if lat is not None and lng is not None and name:
                        landmarks.append({'name': name, 'lat': lat, 'lng': lng})
                except (ValueError, TypeError) as e:
                    continue
        except FileNotFoundError:
            print("IOCL_Landmark_Details.xlsx not found, using sample landmarks")
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

        return render_template("route_form.html", landmarks=landmarks)
    except Exception as e:
        print(f"Error loading data: {e}")
        import traceback
        traceback.print_exc()
        return f"<html><body><h2>IndianOil Smart Marg</h2><p>Error: {str(e)}</p></body></html>"

@app.route('/fetch_routes', methods=['POST'])
def fetch_routes():
    """Generates and displays alternative routes for user selection."""
    try:
        session.clear()
        for f in glob.glob("templates/route_preview_*.html"): os.remove(f)
        for f in glob.glob("templates/route_map_*.html"): os.remove(f)

        source = request.form['source'].strip()
        destination = request.form['destination'].strip()
        vehicle = request.form['vehicle']

        try:
            source_coords = tuple(map(float, source.split(',')))
            dest_coords = tuple(map(float, destination.split(',')))
        except ValueError:
            return "Invalid coordinates format. Please use: latitude,longitude"

        directions = gmaps.directions(
            source_coords, dest_coords,
            mode=vehicle,
            alternatives=True,
            departure_time=datetime.now()
        )

        if not directions:
            return "No routes found between the specified locations."

        session['directions'] = directions
        session['source'] = source_coords
        session['destination'] = dest_coords
        session['vehicle'] = vehicle
        session.modified = True

        routes = []
        for i, route in enumerate(directions):
            try:
                coords = polyline.decode(route['overview_polyline']['points'])
                distance = route['legs'][0]['distance']['text']
                duration = route['legs'][0]['duration']['text']
                summary = route.get('summary', f"Route {i+1}")

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
    """Analyzes the selected route using enhanced probabilistic and safety models."""
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
        
        total_distance = selected['legs'][0]['distance']['text']
        total_duration = selected['legs'][0]['duration']['text']

        # Interpolate route for more precise mapping and analysis (10 points per km)
        detailed_coords = interpolate_route_points(coords, points_per_km=10)
        
        def get_pois(keyword):
            pois = []
            try:
                # Use a more efficient POI search by checking points along the route
                for lat, lng in detailed_coords[::20]: # Sample every 20th point
                    places = gmaps.places_nearby(location=(lat, lng), radius=300, keyword=keyword)
                    for place in places.get('results', []):
                        pois.append({
                            'name': place['name'],
                            'location': (place['geometry']['location']['lat'], place['geometry']['location']['lng']),
                            'type': keyword
                        })
            except Exception as e:
                print(f"Error getting places for {keyword}: {e}")
            return pois

        all_pois = []
        for keyword in ['hospital', 'police', 'fuel']:
            all_pois.extend(get_pois(keyword))

        traffic_data = get_traffic_data(detailed_coords)
        risk_zones = identify_high_risk_zones(detailed_coords, all_pois)
        route_report = generate_route_report(detailed_coords, all_pois, risk_zones, traffic_data, total_distance, total_duration)

        # Create enhanced map with all the new data points
        m = folium.Map(location=source, zoom_start=13)
        
        folium.Marker(source, popup='Start', icon=folium.Icon(color='green', icon='flag', prefix='fa')).add_to(m)
        folium.Marker(destination, popup='End', icon=folium.Icon(color='black', icon='flag-checkered', prefix='fa')).add_to(m)
        
        # Add speed markers and POIs
        for i, (lat, lng) in enumerate(detailed_coords):
            if i % 50 == 0 and i > 0 and i < len(detailed_coords) - 1:
                try:
                    prev_coord = detailed_coords[i-1]
                    next_coord = detailed_coords[i+1]
                    prev_bearing = calculate_bearing(prev_coord[0], prev_coord[1], lat, lng)
                    next_bearing = calculate_bearing(lat, lng, next_coord[0], next_coord[1])
                    turn_angle = calculate_turn_angle(prev_bearing, next_bearing)
                    recommended_speed = get_recommended_speed(turn_angle)
                    
                    # Enhanced truck marker HTML
                    truck_html = f"""
                    <div style='text-align: center; font-family: Arial;'>
                        <div style='font-size: 20px;'>🚛</div>
                        <div style='background-color: {"red" if recommended_speed < 30 else "orange" if recommended_speed < 45 else "green"}; 
                                    color: white; padding: 2px 5px; border-radius: 3px; font-weight: bold;'>
                            {recommended_speed} km/h
                        </div>
                        <div style='font-size: 10px; margin-top: 2px;'>
                            Turn: {turn_angle:.1f}°
                        </div>
                    </div>
                    """
                    folium.Marker(
                        location=(lat, lng),
                        popup=folium.IFrame(truck_html, width=120, height=80),
                        icon=folium.DivIcon(html=truck_html, icon_size=(60, 60), icon_anchor=(30, 30))
                    ).add_to(m)
                except Exception as e:
                    print(f"Error adding truck marker at {i}: {e}")

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
                folium.Marker(location=poi['location'], popup=f"<b>{poi['name']}</b><br>{poi['type'].capitalize()}", icon=icon).add_to(m)
            except Exception as e:
                print(f"Error adding POI marker: {e}")

        # Add high-risk zones
        for zone in risk_zones:
            try:
                color = 'red' if zone['risk_level'] == 'High' else 'orange'
                risk_popup = f"""
                <div style='font-family: Arial; max-width: 200px;'>
                    <h4 style='color: {color};'>⚠️ {zone['risk_level']} Risk Zone</h4>
                    <p><b>Risk Score:</b> {zone['risk_score']:.1f}/10</p>
                    <p><b>Factors:</b><br>{'<br>'.join(zone['risk_factors'])}</p>
                </div>
                """
                folium.CircleMarker(
                    location=zone['location'],
                    radius=15,
                    popup=folium.IFrame(risk_popup, width=200, height=120),
                    color=color,
                    fillColor=color,
                    fillOpacity=0.4
                ).add_to(m)
            except Exception as e:
                print(f"Error adding risk zone: {e}")

        # Add traffic indicators
        for traffic in traffic_data:
            try:
                color = {'light': 'green', 'moderate': 'yellow', 'heavy': 'red'}[traffic['traffic_level']]
                folium.Circle(
                    location=traffic['location'],
                    radius=100, # Circle radius in meters
                    color=color,
                    fill=True,
                    fillColor=color,
                    fillOpacity=0.2,
                    popup=f"Traffic: {traffic['traffic_level'].title()}<br>Delay: {traffic['delay_factor']:.1f}x"
                ).add_to(m)
            except Exception as e:
                print(f"Error adding traffic indicator: {e}")

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
    """Shows detailed route analysis report from the session."""
    try:
        report = session.get('route_report')
        if not report:
            return "No route analysis data found. Please analyze a route first."
        
        return render_template("detailed_report.html", report=report)
        
    except Exception as e:
        print(f"Error in detailed_report: {e}")
        return f"Error generating detailed report: {str(e)}"

@app.route('/view_map/<filename>')
def view_map(filename):
    """Serves the generated map HTML files."""
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
    """Allows users to download the map HTML."""
    try:
        return send_from_directory(directory='templates', path=filename, as_attachment=True)
    except Exception as e:
        print(f"Error downloading map: {e}")
        return f"Error downloading file: {str(e)}", 500

@app.route('/preview/<filename>')
def view_preview(filename):
    """Serves the smaller preview maps."""
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
        # Consider using a more robust server for production
        app.run(debug=True)
    except Exception as e:
        print(f"Error starting application: {e}")
```
