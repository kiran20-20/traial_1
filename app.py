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

@app.route('/')
def home():
    """Main route form page - no login required"""
    try:
        # Load IOCL Landmarks with data validation
        df_iocl = pd.read_excel("IOCL_Landmark_Details.xlsx")
        landmarks = []
        
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
        
        # Load SAP Codes with data validation
        df_sap = pd.read_excel("IOCL_Plant_data.xlsx")
        sap_codes = []
        valid_states = set()
        
        for _, row in df_sap.iterrows():
            try:
                # Validate and convert data
                state = str(row['State code']).strip() if pd.notna(row['State code']) else None
                sap_code = str(row['Sap Code']).strip() if pd.notna(row['Sap Code']) else None
                lat = float(row['Latitude']) if pd.notna(row['Latitude']) else None
                lng = float(row['Longitude']) if pd.notna(row['Longitude']) else None
                
                if state and sap_code and lat is not None and lng is not None:
                    sap_codes.append({
                        'state': state,
                        'sap_code': sap_code,
                        'lat': lat,
                        'lng': lng
                    })
                    valid_states.add(state)
            except (ValueError, TypeError) as e:
                print(f"Skipping invalid SAP row: {e}")
                continue
        
        # Sort states safely (all should be strings now)
        sap_states = sorted(list(valid_states))

        print(f"Loaded {len(landmarks)} landmarks and {len(sap_codes)} SAP codes from {len(sap_states)} states")

        # Pass both to template
        return render_template(
            "route_form.html",
            landmarks=landmarks,
            sap_codes=sap_codes,
            sap_states=sap_states
        )
    except Exception as e:
        print(f"Error loading data: {e}")
        import traceback
        traceback.print_exc()
        return render_template("route_form.html", landmarks=[], sap_codes=[], sap_states=[])

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
        source = request.form['source']
        destination = request.form['destination']  # Changed from 'destination' to match form
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

        # Fixed legend HTML - removed the problematic duplicate section
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
        return f"Error analyzing route: {str(e)}. Please try again."

@app.route('/detailed_report')
def detailed_report():
    """Show detailed route analysis report"""
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
