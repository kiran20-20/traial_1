from flask import Flask, render_template, request, session, url_for
import googlemaps
import folium
from folium import plugins
from folium.plugins import MarkerCluster
import polyline
import os
import glob
from datetime import datetime
from uuid import uuid4
from jinja2 import Template
from branca.element import MacroElement
import math
import re

# Initialize Flask app
app = Flask(__name__)
app.secret_key = os.environ.get('SECRET_KEY', 'dev-key-change-in-production')

# Initialize Google Maps client with environment variable
GOOGLE_MAPS_API_KEY = os.environ.get('GOOGLE_MAPS_API_KEY')
if not GOOGLE_MAPS_API_KEY:
    print("WARNING: GOOGLE_MAPS_API_KEY environment variable not set!")
    gmaps = None
else:
    gmaps = googlemaps.Client(key=GOOGLE_MAPS_API_KEY)

# TT (Truck Tanker) specifications
def get_tt_specs(tt_type):
    """Get truck tanker specifications based on type"""
    specs = {
        'small_tt': {
            'capacity_range': '5,000-10,000L',
            'avg_capacity_liters': 7500,
            'gross_weight': 15000,  # kg
            'axle_load': 7.5,  # tonnes
            'max_speed': 60,  # km/h
            'turn_sensitivity': 1.2,
            'risk_multiplier': 1.5,
            'product_weight': 6750  # kg (0.9 density for petroleum)
        },
        'medium_tt': {
            'capacity_range': '10,000-20,000L',
            'avg_capacity_liters': 15000,
            'gross_weight': 25000,  # kg
            'axle_load': 12.5,  # tonnes
            'max_speed': 55,  # km/h
            'turn_sensitivity': 1.5,
            'risk_multiplier': 2.0,
            'product_weight': 13500  # kg
        },
        'large_tt': {
            'capacity_range': '20,000-35,000L',
            'avg_capacity_liters': 27500,
            'gross_weight': 40000,  # kg
            'axle_load': 20.0,  # tonnes
            'max_speed': 50,  # km/h
            'turn_sensitivity': 2.0,
            'risk_multiplier': 2.5,
            'product_weight': 24750  # kg
        }
    }
    return specs.get(tt_type, specs['medium_tt'])

def calculate_bearing(lat1, lon1, lat2, lon2):
    """Calculate bearing between two coordinates"""
    lat1 = math.radians(lat1)
    lat2 = math.radians(lat2)
    diff_long = math.radians(lon2 - lon1)
    
    x = math.sin(diff_long) * math.cos(lat2)
    y = math.cos(lat1) * math.sin(lat2) - (math.sin(lat1) * math.cos(lat2) * math.cos(diff_long))
    
    initial_bearing = math.atan2(x, y)
    initial_bearing = math.degrees(initial_bearing)
    compass_bearing = (initial_bearing + 360) % 360
    
    return compass_bearing

def calculate_turn_angle(prev_bearing, next_bearing):
    """Calculate turn angle between two bearings"""
    angle_diff = next_bearing - prev_bearing
    if angle_diff > 180:
        angle_diff -= 360
    elif angle_diff < -180:
        angle_diff += 360
    return abs(angle_diff)

def get_recommended_speed(turn_angle, tt_specs):
    """Get recommended speed based on turn angle and TT specs"""
    base_speed = tt_specs['max_speed']
    
    if turn_angle > 45:  # Sharp turn
        return int(base_speed * 0.3)  # 30% of max speed
    elif turn_angle > 20:  # Moderate turn
        return int(base_speed * 0.6)  # 60% of max speed
    else:  # Gentle turn or straight
        return base_speed

def interpolate_route_points(coords, points_per_km=10):
    """Interpolate additional points along the route for better precision"""
    if len(coords) < 2:
        return coords
    
    detailed_coords = []
    
    for i in range(len(coords) - 1):
        lat1, lon1 = coords[i]
        lat2, lon2 = coords[i + 1]
        
        # Calculate distance between points
        distance = math.sqrt((lat2 - lat1)**2 + (lon2 - lon1)**2) * 111  # Rough km conversion
        
        # Determine number of interpolation points
        num_points = max(1, int(distance * points_per_km))
        
        # Add original point
        detailed_coords.append((lat1, lon1))
        
        # Add interpolated points
        for j in range(1, num_points):
            ratio = j / num_points
            interp_lat = lat1 + (lat2 - lat1) * ratio
            interp_lon = lon1 + (lon2 - lon1) * ratio
            detailed_coords.append((interp_lat, interp_lon))
    
    # Add final point
    detailed_coords.append(coords[-1])
    
    return detailed_coords

def get_traffic_data(coords):
    """Simulate traffic data for route points"""
    import random
    traffic_data = []
    
    # Sample every 10th coordinate for traffic data
    sample_coords = coords[::10] if len(coords) > 10 else coords
    
    for i, (lat, lng) in enumerate(sample_coords):
        # Simulate traffic levels
        traffic_level = random.choice(['light', 'moderate', 'heavy'])
        delay_factor = {'light': 1.0, 'moderate': 1.3, 'heavy': 1.8}[traffic_level]
        
        traffic_data.append({
            'location': (lat, lng),
            'traffic_level': traffic_level,
            'delay_factor': delay_factor
        })
    
    return traffic_data

def identify_high_risk_zones(coords, pois, tt_specs):
    """Identify high-risk zones for truck tankers"""
    risk_zones = []
    
    # Check each coordinate for risk factors
    for i, (lat, lng) in enumerate(coords[::20]):  # Sample every 20th point
        risk_score = 0
        risk_factors = []
        
        # Check proximity to POIs
        for poi in pois:
            poi_lat, poi_lng = poi['location']
            distance = math.sqrt((lat - poi_lat)**2 + (lng - poi_lng)**2) * 111  # km
            
            if distance < 0.5:  # Within 500m
                if poi['type'] == 'hospital':
                    risk_score += 3
                    risk_factors.append("Near hospital - high pedestrian traffic")
                elif poi['type'] == 'police':
                    risk_score += 1
                    risk_factors.append("Police station nearby")
                elif poi['type'] == 'fuel':
                    risk_score += 2
                    risk_factors.append("Fuel station - fire hazard zone")
        
        # Check for turns (simplified)
        if i > 0 and i < len(coords[::20]) - 1:
            prev_coord = coords[::20][i-1]
            next_coord = coords[::20][i+1]
            
            prev_bearing = calculate_bearing(prev_coord[0], prev_coord[1], lat, lng)
            next_bearing = calculate_bearing(lat, lng, next_coord[0], next_coord[1])
            turn_angle = calculate_turn_angle(prev_bearing, next_bearing)
            
            if turn_angle > 45:
                risk_score += 2 * tt_specs['turn_sensitivity']
                risk_factors.append(f"Sharp turn ({turn_angle:.1f}°)")
            elif turn_angle > 20:
                risk_score += 1 * tt_specs['turn_sensitivity']
                risk_factors.append(f"Moderate turn ({turn_angle:.1f}°)")
        
        # Apply TT-specific risk multiplier
        risk_score *= tt_specs['risk_multiplier']
        
        if risk_score > 2:
            risk_level = 'Critical' if risk_score > 6 else 'High' if risk_score > 4 else 'Medium'
            risk_zones.append({
                'location': (lat, lng),
                'risk_score': risk_score,
                'risk_level': risk_level,
                'risk_factors': risk_factors,
                'tt_impact': tt_specs['risk_multiplier']
            })
    
    return risk_zones

def generate_route_report(coords, pois, risk_zones, traffic_data, total_distance, total_duration, tt_specs):
    """Generate comprehensive route report for truck tankers"""
    
    # Calculate statistics
    total_pois = len(pois)
    hospitals = len([p for p in pois if p['type'] == 'hospital'])
    police = len([p for p in pois if p['type'] == 'police'])
    fuel_stations = len([p for p in pois if p['type'] == 'fuel'])
    
    critical_zones = len([z for z in risk_zones if z['risk_level'] == 'Critical'])
    high_zones = len([z for z in risk_zones if z['risk_level'] == 'High'])
    
    heavy_traffic_points = len([t for t in traffic_data if t['traffic_level'] == 'heavy'])
    
    # Calculate safety score
    base_score = 100
    base_score -= critical_zones * 20
    base_score -= high_zones * 10
    base_score -= heavy_traffic_points * 5
    
    # Apply TT-specific penalties
    if tt_specs['gross_weight'] > 30000:
        base_score -= 10  # Heavy TT penalty
    
    safety_score = max(0, base_score)
    safety_grade = 'A' if safety_score >= 90 else 'B' if safety_score >= 80 else 'C' if safety_score >= 70 else 'D' if safety_score >= 60 else 'F'
    
    return {
        'total_distance': total_distance,
        'total_duration': total_duration,
        'safety_score': safety_score,
        'safety_grade': safety_grade,
        'total_pois': total_pois,
        'hospitals': hospitals,
        'police_stations': police,
        'fuel_stations': fuel_stations,
        'critical_zones': critical_zones,
        'high_risk_zones': high_zones,
        'heavy_traffic_points': heavy_traffic_points,
        'tt_specs': tt_specs,
        'recommendations': generate_tt_recommendations(risk_zones, traffic_data, tt_specs)
    }

def generate_tt_recommendations(risk_zones, traffic_data, tt_specs):
    """Generate specific recommendations for truck tanker operation"""
    recommendations = []
    
    if tt_specs['gross_weight'] > 35000:
        recommendations.append("Heavy TT: Maintain maximum 50 km/h on highways")
        recommendations.append("Use engine braking on downhill sections")
    
    critical_zones = [z for z in risk_zones if z['risk_level'] == 'Critical']
    if critical_zones:
        recommendations.append(f"Reduce speed by 50% in {len(critical_zones)} critical zones")
        recommendations.append("Increase following distance to 6+ seconds")
    
    heavy_traffic = [t for t in traffic_data if t['traffic_level'] == 'heavy']
    if len(heavy_traffic) > 3:
        recommendations.append("Consider alternate timing - heavy traffic detected")
    
    if tt_specs['turn_sensitivity'] > 1.5:
        recommendations.append("Take wide turns - high center of gravity vehicle")
        recommendations.append("Check mirrors frequently for trailer swing")
    
    recommendations.append("Maintain emergency kit: fire extinguisher, spill containment")
    recommendations.append("Monitor tire pressure - heavy load affects handling")
    
    return recommendations

def extract_distance_km(distance_text):
    """Extract distance in kilometers from Google Maps distance text"""
    try:
        if not distance_text:
            return 0
        
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
            import re
            numbers = re.findall(r'\d+\.?\d*', distance_text)
            if numbers:
                return float(numbers[0])
            return 0
    except (ValueError, AttributeError, IndexError):
        return 0

@app.route('/')
def home():
    """Home page with TT route planning form"""
    return render_template('index.html')

@app.route('/fetch_routes', methods=['POST'])
def fetch_routes():
    """Generate routes based on form input with validation"""
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

        # Check if Google Maps client is available
        if not gmaps:
            return render_template("error_page.html", 
                                 error="Service configuration error", 
                                 message="Google Maps service is not properly configured. Please contact support.",
                                 back_url=url_for('home'))

        # Get routes from Google Maps - always use driving for trucks
        print(f"Requesting routes from {source_coords} to {dest_coords}")
        
        try:
            directions = gmaps.directions(
                source_coords, dest_coords,
                mode="driving",
                alternatives=True,
                departure_time=datetime.now(),
                avoid=["tolls"] if tt_specs["gross_weight"] > 35000 else []  # Avoid tolls for very heavy TT
            )
        except Exception as api_error:
            print(f"Google Maps API error: {api_error}")
            return render_template("error_page.html", 
                                 error="Route service unavailable", 
                                 message="Unable to connect to route service. Please check your internet connection and try again.",
                                 back_url=url_for('home'))

        # Check if any routes were found
        if not directions:
            return render_template("error_page.html", 
                                 error="No routes found", 
                                 message="No driving routes could be found between the specified locations. Please check your coordinates and try different locations.",
                                 back_url=url_for('home'))

        print(f"Found {len(directions)} routes")

        # Validate route distances and filter valid routes
        valid_routes = []
        invalid_reasons = []
        
        for i, route in enumerate(directions):
            try:
                distance_text = route['legs'][0]['distance']['text']
                distance_km = extract_distance_km(distance_text)
                
                print(f"Route {i+1}: {distance_text} -> {distance_km} km")
                
                # Check if route exceeds 500 km limit
                if distance_km > 500:
                    invalid_reasons.append(f"Route {i+1}: {distance_text} (exceeds 500 km limit)")
                    continue
                
                # Check if route is too short (less than 1 km might be an error)
                if distance_km < 1:
                    invalid_reasons.append(f"Route {i+1}: {distance_text} (route too short, possible error)")
                    continue
                
                valid_routes.append((i, route, distance_km))
                
            except Exception as e:
                print(f"Error processing route {i}: {e}")
                invalid_reasons.append(f"Route {i+1}: Error processing route data")
                continue

        # Check if we have any valid routes after filtering
        if not valid_routes:
            error_details = "All routes were filtered out for the following reasons:\n" + "\n".join(invalid_reasons)
            return render_template("error_page.html", 
                                 error="No suitable routes found", 
                                 message="All available routes exceed the 500 km distance limit for truck tanker operations or have other issues.",
                                 details=error_details,
                                 back_url=url_for('home'))

        print(f"Valid routes after filtering: {len(valid_routes)}")

        # Store in session
        session['directions'] = directions
        session['source'] = source_coords
        session['destination'] = dest_coords
        session['tt_type'] = tt_type
        session['tt_specs'] = tt_specs
        session['valid_route_indices'] = [route[0] for route in valid_routes]
        session.modified = True

        # Process valid routes for selection
        routes = []
        for original_index, route, distance_km in valid_routes:
            try:
                coords = polyline.decode(route['overview_polyline']['points'])
                distance = route['legs'][0]['distance']['text']
                duration = route['legs'][0]['duration']['text']
                summary = route.get('summary', f"Route {len(routes)+1}")

                # Add distance validation info to summary
                if distance_km > 400:
                    summary += " (Long Route)"
                elif distance_km > 200:
                    summary += " (Medium Route)"
                else:
                    summary += " (Short Route)"

                # Create preview map with TT info
                unique_id = uuid4().hex
                preview_file = f"route_preview_{original_index}_{unique_id}.html"
                m = folium.Map(location=coords[len(coords)//2], zoom_start=10)
                
                # Add route with weight-based color and distance info
                route_color = 'red' if tt_specs["gross_weight"] > 35000 else 'orange' if tt_specs["gross_weight"] > 25000 else 'blue'
                folium.PolyLine(coords, color=route_color, weight=5, 
                              popup=f"TT {tt_specs['capacity_range']} - {tt_specs['gross_weight']/1000:.1f}T<br>Distance: {distance} ({distance_km:.1f} km)").add_to(m)
                
                # Add start and end markers
                folium.Marker(source_coords, popup='Start', 
                             icon=folium.Icon(color='green', icon='play')).add_to(m)
                folium.Marker(dest_coords, popup='End', 
                             icon=folium.Icon(color='red', icon='stop')).add_to(m)
                
                m.save(f"templates/{preview_file}")

                # Ensure distance_km is a valid number
                if distance_km is None or distance_km <= 0:
                    distance_km = extract_distance_km(distance)  # Try to extract again
                    if distance_km <= 0:
                        distance_km = 1  # Default fallback

                print(f"Processing route {original_index}: distance={distance}, distance_km={distance_km}")

                routes.append({
                    'index': original_index,  # Keep original index for backend processing
                    'distance': distance,
                    'duration': duration,
                    'summary': summary,
                    'preview_file': preview_file,
                    'tt_info': f"TT {tt_specs['capacity_range']} - {tt_specs['gross_weight']/1000:.1f}T"
                })
            except Exception as e:
                print(f"Error processing valid route {original_index}: {e}")
                continue

        # Final check - ensure we have processable routes
        if not routes:
            return render_template("error_page.html", 
                                 error="Route processing failed", 
                                 message="Valid routes were found but could not be processed for display. Please try again.",
                                 back_url=url_for('home'))

        return render_template("route_select.html", 
                             routes=routes, 
                             tt_specs=tt_specs)
    
    except Exception as e:
        print(f"Error in fetch_routes: {e}")
        import traceback
        traceback.print_exc()
        return render_template("error_page.html", 
                             error="System error", 
                             message=f"An unexpected error occurred while processing your request: {str(e)}",
                             back_url=url_for('home'))

@app.route('/analyze_route', methods=['POST'])
def analyze_route():
    """Analyze the selected route with additional validation"""
    try:
        directions = session.get('directions')
        tt_specs = session.get('tt_specs')
        valid_indices = session.get('valid_route_indices', [])
        index = int(request.form['route_index'])

        if not directions or not tt_specs:
            return render_template("error_page.html", 
                                 error="Session expired", 
                                 message="Your session has expired. Please start over with a new route request.",
                                 back_url=url_for('home'))

        if index >= len(directions):
            return render_template("error_page.html", 
                                 error="Invalid route selection", 
                                 message="The selected route is no longer available. Please select a different route.",
                                 back_url=url_for('fetch_routes'))

        # Double-check if the selected route was marked as valid
        if index not in valid_indices:
            return render_template("error_page.html", 
                                 error="Invalid route selected", 
                                 message="The selected route does not meet safety requirements (distance > 500km or other issues). Please select a different route.",
                                 back_url=url_for('fetch_routes'))

        # Validate route distance again before analysis
        selected = directions[index]
        distance_text = selected['legs'][0]['distance']['text']
        distance_km = extract_distance_km(distance_text)
        
        if distance_km > 500:
            return render_template("error_page.html", 
                                 error="Route too long", 
                                 message=f"The selected route ({distance_text}) exceeds the 500 km safety limit for truck tanker operations.",
                                 back_url=url_for('fetch_routes'))

        # Continue with existing analysis code...
        steps = selected['legs'][0]['steps']
        coords = polyline.decode(selected['overview_polyline']['points'])
        source = session['source']
        destination = session['destination']
        
        # Get route details
        total_distance = selected['legs'][0]['distance']['text']
        total_duration = selected['legs'][0]['duration']['text']

        # Interpolate route for more precise mapping (adjusted for TT weight)
        points_per_km = 15 if tt_specs["gross_weight"] > 30000 else 10  # More points for heavier TT
        detailed_coords = interpolate_route_points(coords, points_per_km=points_per_km)
        
        def get_pois(keyword):
            pois = []
            if not gmaps:
                return pois
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
        
        # Identify high-risk zones with TT specifications
        risk_zones = identify_high_risk_zones(detailed_coords, all_pois, tt_specs)
        
        # Generate detailed report with TT specs
        route_report = generate_route_report(detailed_coords, all_pois, risk_zones, 
                                           traffic_data, total_distance, total_duration, tt_specs)

        # Create enhanced map with TT-specific visualization
        m = folium.Map(location=source, zoom_start=13)
        
        # Add start and end markers
        folium.Marker(source, popup='Start', 
                     icon=folium.Icon(color='green', icon='flag', prefix='fa')).add_to(m)
        folium.Marker(destination, popup='End', 
                     icon=folium.Icon(color='black', icon='flag-checkered', prefix='fa')).add_to(m)
        
        # Add main route with TT-specific speed indicators
        for i, (lat, lng) in enumerate(detailed_coords):
            if i > 0 and i < len(detailed_coords) - 1 and i % 50 == 0:
                try:
                    # Calculate turn angle for speed recommendation
                    prev_coord = detailed_coords[i-1]
                    next_coord = detailed_coords[i+1]
                    
                    prev_bearing = calculate_bearing(prev_coord[0], prev_coord[1], lat, lng)
                    next_bearing = calculate_bearing(lat, lng, next_coord[0], next_coord[1])
                    turn_angle = calculate_turn_angle(prev_bearing, next_bearing)
                    
                    recommended_speed = get_recommended_speed(turn_angle, tt_specs)
                    
                    # Add truck tanker icon with speed popup
                    truck_html = f"""
                    <div style='text-align: center; font-family: Arial;'>
                        <div style='font-size: 20px;'>🚛</div>
                        <div style='background-color: {"red" if recommended_speed < 20 else "orange" if recommended_speed < 35 else "green"}; 
                                    color: white; padding: 2px 5px; border-radius: 3px; font-weight: bold; font-size: 11px;'>
                            {recommended_speed} km/h
                        </div>
                        <div style='font-size: 9px; margin-top: 2px;'>
                            TT: {tt_specs['capacity_range']}<br>
                            Weight: {tt_specs['gross_weight']/1000:.1f}T<br>
                            Turn: {turn_angle:.1f}°
                        </div>
                    </div>
                    """
                    
                    folium.Marker(
                        location=(lat, lng),
                        popup=truck_html,
                        icon=folium.DivIcon(html=truck_html, icon_size=(70, 70), icon_anchor=(35, 35))
                    ).add_to(m)
                except Exception as e:
                    print(f"Error adding truck marker: {e}")
                    continue

        # Add route polyline with TT-appropriate color
        route_color = 'red' if tt_specs["gross_weight"] > 35000 else 'orange' if tt_specs["gross_weight"] > 25000 else 'blue'
        folium.PolyLine(detailed_coords, color=route_color, weight=4, opacity=0.8).add_to(m)

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

        # Add high-risk zones with TT-specific risk visualization
        for zone in risk_zones:
            try:
                color = 'darkred' if zone['risk_level'] == 'Critical' else 'red' if zone['risk_level'] == 'High' else 'orange'
                risk_popup = f"""
                <div style='font-family: Arial; max-width: 250px;'>
                    <h4 style='color: {color}; margin: 5px 0;'>⚠️ {zone['risk_level']} Risk Zone</h4>
                    <p><strong>Risk Score:</strong> {zone['risk_score']:.1f}/10</p>
                    <p><strong>TT Impact:</strong> {zone['tt_impact']}x multiplier</p>
                    <p><strong>TT Type:</strong> {tt_specs['capacity_range']} ({tt_specs['gross_weight']/1000:.1f}T)</p>
                    <p><strong>Risk Factors:</strong><br>{'<br>'.join(zone['risk_factors'])}</p>
                    <p style='color: red; font-weight: bold;'>Recommended: Reduce speed by 50%</p>
                </div>
                """
                
                radius = 20 if zone['risk_level'] == 'Critical' else 15 if zone['risk_level'] == 'High' else 10
                folium.CircleMarker(
                    location=zone['location'],
                    radius=radius,
                    popup=risk_popup,
                    color=color,
                    fillColor=color,
                    fillOpacity=0.4,
                    weight=3
                ).add_to(m)
            except Exception as e:
                print(f"Error adding risk zone: {e}")
                continue

        # Add traffic indicators with TT-specific impact
        for traffic in traffic_data:
            try:
                color = {'light': 'green', 'moderate': 'yellow', 'heavy': 'red'}[traffic['traffic_level']]
                tt_impact = "High impact" if tt_specs["gross_weight"] > 30000 and traffic['traffic_level'] == 'heavy' else "Moderate impact"
                folium.CircleMarker(
                    location=traffic['location'],
                    radius=6,
                    popup=f"Traffic: {traffic['traffic_level'].title()}<br>Delay Factor: {traffic['delay_factor']:.1f}x<br>TT Impact: {tt_impact}",
                    color=color,
                    fillColor=color,
                    fillOpacity=0.6
                ).add_to(m)
            except Exception as e:
                print(f"Error adding traffic indicator: {e}")
                continue

        # Enhanced legend HTML with TT specifications
        legend_html = f"""
        {{% macro html(this, kwargs) %}}
        <div style="
            position: fixed;
            bottom: 50px;
            left: 50px;
            width: 320px;
            background-color: white;
            border: 2px solid grey;
            border-radius: 8px;
            z-index: 9999;
            padding: 15px;
            font-size: 11px;
            box-shadow: 0 4px 8px rgba(0,0,0,0.1);
        ">
            <h4 style='margin-top: 0; color: #333;'>🚛 Truck Tanker Navigation Legend</h4>
            <div style='background: #f0f0f0; padding: 8px; border-radius: 4px; margin: 8px 0;'>
                <strong>TT Specs: {tt_specs['capacity_range']}</strong><br>
                Capacity: {tt_specs['avg_capacity_liters']:,}L | Weight: {tt_specs['gross_weight']/1000:.1f}T<br>
                Max Speed: {tt_specs['max_speed']} km/h | Risk: {tt_specs['risk_multiplier']}x
            </div>
            <div style='margin: 5px 0;'><i class="fa fa-plus fa-lg" style="color:red"></i> Hospital</div>
            <div style='margin: 5px 0;'><i class="fa fa-shield fa-lg" style="color:blue"></i> Police</div>
            <div style='margin: 5px 0;'><i class="fa fa-gas-pump fa-lg" style="color:orange"></i> Fuel Station</div>
            <div style='margin: 5px 0;'>🚛 <span style='background: green; color: white; padding: 1px 3px;'>35+</span> Safe Speed</div>
            <div style='margin: 5px 0;'>🚛 <span style='background: orange; color: white; padding: 1px 3px;'>20-35</span> Caution Speed</div>
            <div style='margin: 5px 0;'>🚛 <span style='background: red; color: white; padding: 1px 3px;'>&lt;20</span> Slow Speed</div>
            <div style='margin: 5px 0;'>⚫ Critical Risk Zone (TT Sensitive)</div>
            <div style='margin: 5px 0;'>🔴 High Risk Zone</div>
            <div style='margin: 5px 0;'>🟡 Medium Risk Zone</div>
            <div style='margin: 5px 0;'>● Traffic: <span style='color: green;'>Light</span> <span style='color: orange;'>Moderate</span> <span style='color: red;'>Heavy</span></div>
            <hr style='margin: 8px 0;'>
            <div style='font-size: 9px; color: #666;'>
                Axle Load: {tt_specs['axle_load']:.1f}T | Turn Sensitivity: {tt_specs['turn_sensitivity']}x<br>
                Product: Petroleum ({tt_specs['product_weight']/1000:.1f}T) | Density: 0.9 kg/L<br>
                Distance: {total_distance} | Valid Route ✓
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
                               mode="TT Navigation",
                               turns=sum("turn" in s['html_instructions'].lower() for s in steps),
                               poi_count=len(all_pois),
                               html_file=html_name,
                               route_report=route_report,
                               risk_zones=len(risk_zones),
                               high_risk_zones=len([z for z in risk_zones if z['risk_level'] in ['Critical', 'High']]),
                               tt_specs=tt_specs,
                               distance_km=distance_km,
                               is_valid_distance=True)

    except Exception as e:
        print(f"Error in analyze_route: {e}")
        import traceback
        traceback.print_exc()
        return render_template("error_page.html", 
                             error="Analysis error", 
                             message=f"Error analyzing route: {str(e)}. Please try selecting a different route.",
                             back_url=url_for('fetch_routes'))

@app.route('/detailed_report')
def detailed_report():
    """Show detailed route report"""
    route_report = session.get('route_report')
    if not route_report:
        return render_template("error_page.html", 
                             error="No report available", 
                             message="No route analysis report found. Please analyze a route first.",
                             back_url=url_for('home'))
    
    return render_template("detailed_report.html", report=route_report)

@app.errorhandler(404)
def not_found_error(error):
    return render_template('error_page.html', 
                          error="Page not found",
                          message="The requested page could not be found.",
                          back_url=url_for('home')), 404

@app.errorhandler(500)
def internal_error(error):
    return render_template('error_page.html',
                          error="Internal server error",
                          message="An internal server error occurred. Please try again later.",
                          back_url=url_for('home')), 500

if __name__ == '__main__':
    # Create templates directory if it doesn't exist
    if not os.path.exists('templates'):
        os.makedirs('templates')
    
    # Run the application
    app.run(debug=True, host='0.0.0.0', port=10000)
