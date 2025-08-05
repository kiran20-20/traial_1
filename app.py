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
SAFE_TURN_ANGLE = 45  # degrees
DANGEROUS_TURN_ANGLE = 30  # degrees

def calculate_bearing(lat1, lng1, lat2, lng2):
    """Calculate bearing between two points"""
    lat1, lng1, lat2, lng2 = map(math.radians, [lat1, lng1, lat2, lng2])
    dlng = lng2 - lng1
    y = math.sin(dlng) * math.cos(lat2)
    x = math.cos(lat1) * math.sin(lat2) - math.sin(lat1) * math.cos(lat2) * math.cos(dlng)
    bearing = math.atan2(y, x)
    return (math.degrees(bearing) + 360) % 360

def calculate_turn_angle(prev_bearing, curr_bearing):
    """Calculate turn angle between two bearings"""
    angle = abs(curr_bearing - prev_bearing)
    return min(angle, 360 - angle)

def get_recommended_speed(turn_angle, road_type="urban"):
    """Calculate recommended speed based on turn angle and road type"""
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

def interpolate_route_points(coords, points_per_km=10):
    """Interpolate route to get more points per kilometer"""
    if len(coords) < 2:
        return coords
    
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

def get_traffic_data(coords):
    """Get traffic data for route coordinates"""
    traffic_data = []
    
    # Sample every 5th point to avoid API limits
    sample_coords = coords[::5]
    
    for lat, lng in sample_coords:
        try:
            # Get traffic data using Google Roads API (simplified)
            # In real implementation, you'd use traffic APIs
            traffic_level = np.random.choice(['light', 'moderate', 'heavy'], p=[0.4, 0.4, 0.2])
            traffic_data.append({
                'location': (lat, lng),
                'traffic_level': traffic_level,
                'delay_factor': {'light': 1.0, 'moderate': 1.3, 'heavy': 1.8}[traffic_level]
            })
        except:
            continue
    
    return traffic_data

def identify_high_risk_zones(coords, pois):
    """Identify high-risk zones based on various factors"""
    risk_zones = []
    
    for i, (lat, lng) in enumerate(coords):
        risk_score = 0
        risk_factors = []
        
        # Check proximity to hospitals (accident-prone areas)
        hospital_count = sum(1 for poi in pois if poi['type'] == 'hospital' 
                           and geodesic((lat, lng), poi['location']).meters < 500)
        if hospital_count > 0:
            risk_score += hospital_count * 2
            risk_factors.append(f"{hospital_count} hospital(s) nearby")
        
        # Check for intersections (every 10th point approximation)
        if i % 10 == 0 and i > 0 and i < len(coords) - 10:
            # Simplified intersection detection based on bearing changes
            prev_bearing = calculate_bearing(coords[i-10][0], coords[i-10][1], lat, lng)
            next_bearing = calculate_bearing(lat, lng, coords[i+10][0], coords[i+10][1])
            turn_angle = calculate_turn_angle(prev_bearing, next_bearing)
            
            if turn_angle > 30:
                risk_score += 3
                risk_factors.append("Sharp turn/intersection")
        
        # Add random factors for demonstration (school zones, construction, etc.)
        if np.random.random() < 0.05:  # 5% chance
            risk_score += 4
            risk_factors.append("School zone")
        
        if np.random.random() < 0.03:  # 3% chance
            risk_score += 5
            risk_factors.append("Construction zone")
        
        if risk_score >= 3:
            risk_zones.append({
                'location': (lat, lng),
                'risk_score': risk_score,
                'risk_factors': risk_factors,
                'risk_level': 'High' if risk_score >= 6 else 'Medium'
            })
    
    return risk_zones

def generate_route_report(coords, pois, risk_zones, traffic_data, total_distance, total_duration):
    """Generate a detailed route analysis report"""
    report = {
        'total_distance': total_distance,
        'total_duration': total_duration,
        'truck_weight': TRUCK_WEIGHT,
        'max_speed_limit': MAX_SPEED_LIMIT,
        'route_analysis': {
            'total_points': len(coords),
            'points_per_km': len(coords) / (float(total_distance.split()[0]) if total_distance else 1),
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

@app.route('/')
def home():
    df = pd.read_excel("IOCL_Landmark_Details.xlsx")
    landmarks = [
        {'name': row['Landmark Name'], 'lat': row['Latitude'], 'lng': row['Longitude']}
        for _, row in df.iterrows()
    ]
    return render_template("route_form.html", landmarks=landmarks)

@app.route('/fetch_routes', methods=['POST'])
def fetch_routes():
    # Clear session and old route files
    session.clear()
    for f in glob.glob("templates/route_preview_*.html"):
        os.remove(f)
    for f in glob.glob("templates/route_map_*.html"):
        os.remove(f)

    source = request.form['source']
    destination = request.form['destination']
    vehicle = request.form['vehicle']

    try:
        source_coords = tuple(map(float, source.split(',')))
        dest_coords = tuple(map(float, destination.split(',')))
    except ValueError:
        return "Invalid coordinates"

    directions = gmaps.directions(
        source_coords, dest_coords,
        mode=vehicle,
        alternatives=True,
        departure_time=datetime.now()
    )

    if not directions:
        return "No routes found."

    session['directions'] = directions
    session['source'] = source_coords
    session['destination'] = dest_coords
    session['vehicle'] = vehicle
    session.modified = True

    routes = []
    for i, route in enumerate(directions):
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

    return render_template("route_select.html", routes=routes)

@app.route('/analyze_route', methods=['POST'])
def analyze_route():
    directions = session.get('directions')
    index = int(request.form['route_index'])

    if not directions or index >= len(directions):
        return "Invalid route selected or data expired."

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
        # Use detailed coords for more precise POI detection
        for lat, lng in detailed_coords[::20]:  # Sample every 20th point
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
            except:
                continue
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
    route_points_with_speed = []
    for i, (lat, lng) in enumerate(detailed_coords):
        if i > 0 and i < len(detailed_coords) - 1:
            # Calculate turn angle for speed recommendation
            prev_coord = detailed_coords[i-1]
            next_coord = detailed_coords[i+1]
            
            prev_bearing = calculate_bearing(prev_coord[0], prev_coord[1], lat, lng)
            next_bearing = calculate_bearing(lat, lng, next_coord[0], next_coord[1])
            turn_angle = calculate_turn_angle(prev_bearing, next_bearing)
            
            recommended_speed = get_recommended_speed(turn_angle)
            
            # Add truck icon with speed popup every 50th point
            if i % 50 == 0:
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

    # Add route polyline with color coding for speed
    folium.PolyLine(detailed_coords, color='blue', weight=4, opacity=0.8).add_to(m)

    # Add POIs with enhanced icons
    marker_styles = {
        'hospital': {'color': 'red', 'icon': 'plus'},
        'police': {'color': 'blue', 'icon': 'shield'},
        'fuel': {'color': 'orange', 'icon': 'gas-pump'}
    }

    for poi in all_pois:
        props = marker_styles.get(poi['type'], {'color': 'gray', 'icon': 'info-circle'})
        icon = folium.Icon(color=props['color'], icon=props['icon'], prefix='fa')
        folium.Marker(
            location=poi['location'],
            popup=f"{poi['type'].capitalize()}: {poi['name']}",
            icon=icon
        ).add_to(m)

    # Add high-risk zones
    for zone in risk_zones:
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

    # Add traffic indicators
    for traffic in traffic_data:
        color = {'light': 'green', 'moderate': 'yellow', 'heavy': 'red'}[traffic['traffic_level']]
        folium.CircleMarker(
            location=traffic['location'],
            radius=5,
            popup=f"Traffic: {traffic['traffic_level'].title()}<br>Delay Factor: {traffic['delay_factor']:.1f}x",
            color=color,
            fillColor=color,
            fillOpacity=0.6
        ).add_to(m)

    # Enhanced legend
    legend_html = """
    {% macro html(this, kwargs) %}
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
    {% endmacro %}
    """.format(TRUCK_WEIGHT=TRUCK_WEIGHT, MAX_SPEED_LIMIT=MAX_SPEED_LIMIT)
    
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

@app.route('/detailed_report')
def detailed_report():
    """Show detailed route analysis report"""
    report = session.get('route_report')
    if not report:
        return "No route analysis data found. Please analyze a route first."
    
    return render_template("detailed_report.html", report=report)

@app.route('/view_map/<filename>')
def view_map(filename):
    path = os.path.join("templates", filename)
    if not os.path.exists(path):
        return "Map file not found", 404
    response = make_response(render_template(filename))
    response.headers['Cache-Control'] = 'no-store'
    return response

@app.route('/download/<filename>')
def download_map(filename):
    return send_from_directory(directory='templates', path=filename, as_attachment=True)

@app.route('/preview/<filename>')
def view_preview(filename):
    path = os.path.join("templates", filename)
    if not os.path.exists(path):
        return "Preview not found.", 404
    response = make_response(render_template(filename))
    response.headers['Cache-Control'] = 'no-store'
    return response

if __name__ == '__main__':
    if not os.path.exists("templates"):
        os.makedirs("templates")
    app.run(debug=True)
