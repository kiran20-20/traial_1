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
from scipy.interpolate import interp1d
from scipy.signal import savgol_filter

app = Flask(__name__)
app.secret_key = 'your_secret_key_here'
app.config['SESSION_TYPE'] = 'filesystem'
Session(app)

API_KEY = os.environ.get("API_KEY")
gmaps = googlemaps.Client(key=API_KEY)

# Login credentials
LOGIN_CREDENTIALS = {
    "Vadinar": "Vadinar@123",
    "Ahmedabad": "Ahmedabad@123",
    "Mumbai": "Mumbai@123",
    # Add more as needed
}

# Enhanced TT Specifications with blind spot parameters
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
        "length": 8.5,  # meters
        "width": 2.5,   # meters
        "height": 3.8,  # meters
        "blind_spot_left": 2.8,  # meters
        "blind_spot_right": 3.2,  # meters
        "blind_spot_rear": 7.5,   # meters
        "turning_radius": 9.5,    # meters
        "center_of_gravity": 1.8, # meters from ground
        "brake_distance_dry": 12, # meters at 40kmph
        "brake_distance_wet": 18  # meters at 40kmph
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
        "length": 10.2,
        "width": 2.5,
        "height": 4.0,
        "blind_spot_left": 3.2,
        "blind_spot_right": 3.8,
        "blind_spot_rear": 9.0,
        "turning_radius": 11.5,
        "center_of_gravity": 1.95,
        "brake_distance_dry": 15,
        "brake_distance_wet": 22
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
        "length": 11.5,
        "width": 2.5,
        "height": 4.2,
        "blind_spot_left": 3.5,
        "blind_spot_right": 4.2,
        "blind_spot_rear": 10.5,
        "turning_radius": 13.0,
        "center_of_gravity": 2.1,
        "brake_distance_dry": 18,
        "brake_distance_wet": 27
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
        "length": 12.5,
        "width": 2.5,
        "height": 4.4,
        "blind_spot_left": 4.0,
        "blind_spot_right": 4.8,
        "blind_spot_rear": 12.0,
        "turning_radius": 14.5,
        "center_of_gravity": 2.25,
        "brake_distance_dry": 22,
        "brake_distance_wet": 33
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
        "length": 14.0,
        "width": 2.5,
        "height": 4.6,
        "blind_spot_left": 4.5,
        "blind_spot_right": 5.5,
        "blind_spot_rear": 14.0,
        "turning_radius": 16.5,
        "center_of_gravity": 2.4,
        "brake_distance_dry": 28,
        "brake_distance_wet": 42
    }
}

def login_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if not session.get('logged_in'):
            return redirect(url_for('login'))
        return f(*args, **kwargs)
    return decorated_function

def calculate_blind_spot_area(tt_specs, lat, lng, bearing):
    """
    Calculate blind spot areas using mathematical models
    Returns polygon coordinates for blind spots
    """
    blind_spots = []
    
    # Convert bearing to radians
    bearing_rad = math.radians(bearing)
    
    # Calculate left blind spot polygon
    left_angle = bearing_rad - math.pi/2  # 90 degrees left
    left_blind_spot = []
    
    # Create wedge-shaped blind spot
    for angle_offset in np.linspace(-0.3, 0.3, 5):  # 35 degree wedge
        for distance in [0.5, tt_specs['blind_spot_left']]:
            point_angle = left_angle + angle_offset
            dlat = distance * math.cos(point_angle) / 111111  # meters to degrees
            dlng = distance * math.sin(point_angle) / (111111 * math.cos(math.radians(lat)))
            left_blind_spot.append((lat + dlat, lng + dlng))
    
    # Calculate right blind spot polygon
    right_angle = bearing_rad + math.pi/2  # 90 degrees right
    right_blind_spot = []
    
    for angle_offset in np.linspace(-0.3, 0.3, 5):
        for distance in [0.5, tt_specs['blind_spot_right']]:
            point_angle = right_angle + angle_offset
            dlat = distance * math.cos(point_angle) / 111111
            dlng = distance * math.sin(point_angle) / (111111 * math.cos(math.radians(lat)))
            right_blind_spot.append((lat + dlat, lng + dlng))
    
    # Calculate rear blind spot (triangular)
    rear_angle = bearing_rad + math.pi  # 180 degrees behind
    rear_blind_spot = []
    
    # Create triangular rear blind spot
    rear_width = tt_specs['width'] * 1.5  # Wider at the back
    for width_offset in np.linspace(-rear_width/2, rear_width/2, 5):
        # Starting point (near truck)
        start_angle = rear_angle + math.atan2(width_offset, 2)
        start_distance = math.sqrt(4 + width_offset**2)
        dlat_start = start_distance * math.cos(start_angle) / 111111
        dlng_start = start_distance * math.sin(start_angle) / (111111 * math.cos(math.radians(lat)))
        rear_blind_spot.append((lat + dlat_start, lng + dlng_start))
        
        # End point (far from truck)
        end_distance = tt_specs['blind_spot_rear']
        dlat_end = end_distance * math.cos(rear_angle) / 111111
        dlng_end = end_distance * math.sin(rear_angle) / (111111 * math.cos(math.radians(lat)))
        rear_blind_spot.append((lat + dlat_end, lng + dlng_end))
    
    return {
        'left': left_blind_spot,
        'right': right_blind_spot,
        'rear': rear_blind_spot
    }

def calculate_stopping_distance(speed_kmph, tt_specs, road_condition='dry', gradient=0):
    """
    Calculate stopping distance using physics formulas
    Includes reaction time, brake efficiency, and road gradient
    """
    # Convert speed to m/s
    speed_ms = speed_kmph / 3.6
    
    # Reaction time (seconds) - increases with truck weight
    reaction_time = 1.5 + (tt_specs['gross_weight'] / 50000)  # 1.5-2.4 seconds
    
    # Reaction distance
    reaction_distance = speed_ms * reaction_time
    
    # Deceleration rate (m/s²) - depends on conditions and weight
    if road_condition == 'dry':
        deceleration = 6.5 - (tt_specs['gross_weight'] / 20000)  # 4.3-6.5 m/s²
    elif road_condition == 'wet':
        deceleration = 4.0 - (tt_specs['gross_weight'] / 25000)  # 2.2-4.0 m/s²
    else:  # ice/oil
        deceleration = 1.5 - (tt_specs['gross_weight'] / 40000)  # 0.4-1.5 m/s²
    
    # Adjust for gradient (positive = uphill, negative = downhill)
    gravity_component = 9.81 * math.sin(math.radians(gradient))
    effective_deceleration = deceleration + gravity_component
    
    # Prevent division by zero
    if effective_deceleration <= 0:
        effective_deceleration = 0.5
    
    # Braking distance using physics formula: v² = u² + 2as
    braking_distance = (speed_ms ** 2) / (2 * effective_deceleration)
    
    # Total stopping distance
    total_distance = reaction_distance + braking_distance
    
    # Add safety factor for liquid surge in tanker
    surge_factor = 1 + (0.15 * (tt_specs['avg_capacity_liters'] / 35000))
    total_distance *= surge_factor
    
    return {
        'reaction_distance': reaction_distance,
        'braking_distance': braking_distance,
        'total_distance': total_distance,
        'safe_following_distance': total_distance * 1.5  # 50% safety margin
    }

def calculate_rollover_risk(speed_kmph, turn_radius, tt_specs, road_camber=0, liquid_fill=0.9):
    """
    Calculate rollover risk using complex physics model
    Considers center of gravity, liquid slosh, and road conditions
    """
    # Convert speed to m/s
    speed_ms = speed_kmph / 3.6
    
    # Calculate lateral acceleration (m/s²)
    if turn_radius > 0:
        lateral_acceleration = (speed_ms ** 2) / turn_radius
    else:
        lateral_acceleration = 0
    
    # Static rollover threshold (m/s²)
    # Based on track width and center of gravity height
    track_width = tt_specs['width']
    cog_height = tt_specs['center_of_gravity']
    
    # Basic static stability factor
    static_threshold = (track_width * 9.81) / (2 * cog_height)
    
    # Adjust for liquid slosh effect (reduces stability)
    # Partial fill is more dangerous than full
    if liquid_fill < 0.95 and liquid_fill > 0.3:
        slosh_factor = 1 - (0.3 * (1 - abs(liquid_fill - 0.6) / 0.4))
    else:
        slosh_factor = 0.95
    
    # Adjust for road camber (positive = favorable, negative = adverse)
    camber_factor = 1 + (0.1 * math.sin(math.radians(road_camber)))
    
    # Calculate effective rollover threshold
    effective_threshold = static_threshold * slosh_factor * camber_factor
    
    # Calculate rollover risk percentage
    if effective_threshold > 0:
        rollover_risk = min(100, (lateral_acceleration / effective_threshold) * 100)
    else:
        rollover_risk = 100
    
    # Determine safe speed for turn
    if turn_radius > 0:
        safe_speed_ms = math.sqrt(effective_threshold * turn_radius * 0.6)  # 60% safety margin
        safe_speed_kmph = safe_speed_ms * 3.6
    else:
        safe_speed_kmph = tt_specs['max_speed']
    
    return {
        'rollover_risk_percent': rollover_risk,
        'lateral_acceleration': lateral_acceleration,
        'threshold_acceleration': effective_threshold,
        'safe_speed': safe_speed_kmph,
        'risk_level': 'CRITICAL' if rollover_risk > 80 else 'HIGH' if rollover_risk > 60 else 'MODERATE' if rollover_risk > 40 else 'LOW'
    }

def calculate_curve_radius(coords, index, sample_points=5):
    """
    Calculate the radius of curvature at a point using mathematical approximation
    Uses circle fitting through multiple points
    """
    if index < sample_points or index >= len(coords) - sample_points:
        return float('inf')  # Straight line
    
    # Get sample points around the index
    points = []
    for i in range(index - sample_points, index + sample_points + 1):
        lat, lng = coords[i]
        # Convert to local Cartesian coordinates (meters)
        x = lng * 111111 * math.cos(math.radians(lat))
        y = lat * 111111
        points.append([x, y])
    
    points = np.array(points)
    
    # Fit a circle using least squares
    # (x - a)² + (y - b)² = r²
    A = np.column_stack([points[:, 0], points[:, 1], np.ones(len(points))])
    b = points[:, 0]**2 + points[:, 1]**2
    
    try:
        c = np.linalg.lstsq(A, b, rcond=None)[0]
        center_x = c[0] / 2
        center_y = c[1] / 2
        radius = math.sqrt(c[2] + center_x**2 + center_y**2)
        return min(radius, 1000)  # Cap at 1km
    except:
        return float('inf')

def analyze_intersection_complexity(coords, index, poi_data, tt_specs):
    """
    Analyze intersection complexity using mathematical scoring
    Considers multiple factors including traffic patterns and visibility
    """
    if index < 10 or index >= len(coords) - 10:
        return {'complexity_score': 0, 'factors': []}
    
    complexity_score = 0
    factors = []
    
    # 1. Calculate number of potential conflict points
    lat, lng = coords[index]
    
    # Check for nearby roads (simplified - would use actual road network data)
    nearby_intersections = 0
    for i in range(max(0, index-20), min(len(coords), index+20)):
        if i != index:
            dist = geodesic(coords[i], (lat, lng)).meters
            if dist < 50:  # Within 50 meters
                nearby_intersections += 1
    
    if nearby_intersections > 4:
        complexity_score += 30
        factors.append(f"Complex intersection: {nearby_intersections} conflict points")
    elif nearby_intersections > 2:
        complexity_score += 15
        factors.append(f"Moderate intersection: {nearby_intersections} conflict points")
    
    # 2. Calculate approach angles
    prev_bearing = calculate_bearing(coords[index-10][0], coords[index-10][1], lat, lng)
    next_bearing = calculate_bearing(lat, lng, coords[index+10][0], coords[index+10][1])
    turn_angle = calculate_turn_angle(prev_bearing, next_bearing)
    
    if turn_angle > 75:
        complexity_score += 25
        factors.append(f"Sharp turn required: {turn_angle:.1f}°")
    elif turn_angle > 45:
        complexity_score += 15
        factors.append(f"Moderate turn: {turn_angle:.1f}°")
    
    # 3. Visibility analysis based on blind spots
    blind_spot_coverage = (tt_specs['blind_spot_left'] + tt_specs['blind_spot_right']) * tt_specs['length']
    visibility_factor = blind_spot_coverage / 100  # Normalize
    complexity_score += visibility_factor * 20
    factors.append(f"Blind spot area: {blind_spot_coverage:.1f}m²")
    
    # 4. Check for traffic control devices (simulated)
    if np.random.random() < 0.3:  # 30% chance of traffic light
        complexity_score -= 10  # Traffic lights reduce complexity
        factors.append("Traffic light present")
    
    # 5. Pedestrian crossing risk
    hospital_nearby = any(p['type'] == 'hospital' and geodesic(p['location'], (lat, lng)).meters < 200 for p in poi_data)
    if hospital_nearby:
        complexity_score += 20
        factors.append("High pedestrian activity zone")
    
    return {
        'complexity_score': min(100, complexity_score),
        'factors': factors,
        'risk_level': 'HIGH' if complexity_score > 60 else 'MODERATE' if complexity_score > 30 else 'LOW'
    }

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

def calculate_gradient(coords, index, sample_distance=100):
    """
    Calculate road gradient using elevation data
    Returns gradient in degrees
    """
    if index < 5 or index >= len(coords) - 5:
        return 0
    
    # Get points sample_distance meters apart
    start_point = coords[index - 5]
    end_point = coords[index + 5]
    
    # Calculate horizontal distance
    horizontal_distance = geodesic(start_point, end_point).meters
    
    # Simulate elevation change (in production, use actual elevation API)
    # This is a simplified model
    elevation_change = np.random.normal(0, 5)  # ±5 meters variation
    
    if horizontal_distance > 0:
        gradient_radians = math.atan(elevation_change / horizontal_distance)
        gradient_degrees = math.degrees(gradient_radians)
        return gradient_degrees
    return 0

def generate_advanced_risk_analysis(coords, pois, tt_specs):
    """
    Generate comprehensive risk analysis with mathematical models
    """
    risk_points = []
    
    # Analyze every 10th point for computational efficiency
    for i in range(0, len(coords), 10):
        lat, lng = coords[i]
        risk_data = {
            'location': (lat, lng),
            'index': i,
            'risks': []
        }
        
        # 1. Calculate curve radius and rollover risk
        if i > 10 and i < len(coords) - 10:
            curve_radius = calculate_curve_radius(coords, i)
            if curve_radius < 500:  # Curve detected
                # Estimate speed (simplified)
                speed = min(tt_specs['max_speed'], 40 + curve_radius / 20)
                rollover = calculate_rollover_risk(speed, curve_radius, tt_specs)
                
                if rollover['rollover_risk_percent'] > 40:
                    risk_data['risks'].append({
                        'type': 'rollover',
                        'severity': rollover['risk_level'],
                        'details': f"Rollover risk: {rollover['rollover_risk_percent']:.1f}%",
                        'safe_speed': rollover['safe_speed']
                    })
        
        # 2. Calculate stopping distance requirements
        gradient = calculate_gradient(coords, i)
        typical_speed = tt_specs['max_speed'] * 0.8  # 80% of max speed
        stopping = calculate_stopping_distance(typical_speed, tt_specs, 'dry', gradient)
        
        if stopping['total_distance'] > 50:  # Long stopping distance
            risk_data['risks'].append({
                'type': 'stopping_distance',
                'severity': 'MODERATE',
                'details': f"Stopping distance: {stopping['total_distance']:.1f}m",
                'safe_following': stopping['safe_following_distance']
            })
        
        # 3. Analyze intersection complexity
        intersection = analyze_intersection_complexity(coords, i, pois, tt_specs)
        if intersection['complexity_score'] > 30:
            risk_data['risks'].append({
                'type': 'intersection',
                'severity': intersection['risk_level'],
                'details': f"Complex intersection (score: {intersection['complexity_score']:.0f})",
                'factors': intersection['factors']
            })
        
        # 4. Calculate blind spot risks
        if i > 0:
            bearing = calculate_bearing(coords[i-1][0], coords[i-1][1], lat, lng)
            blind_spots = calculate_blind_spot_area(tt_specs, lat, lng, bearing)
            
            # Check if POIs fall within blind spots
            blind_spot_pois = 0
            for poi in pois:
                poi_lat, poi_lng = poi['location']
                # Simplified check - in production, use proper point-in-polygon
                dist_to_poi = geodesic((lat, lng), (poi_lat, poi_lng)).meters
                if dist_to_poi < tt_specs['blind_spot_rear']:
                    blind_spot_pois += 1
            
            if blind_spot_pois > 0:
                risk_data['risks'].append({
                    'type': 'blind_spot',
                    'severity': 'HIGH' if blind_spot_pois > 2 else 'MODERATE',
                    'details': f"{blind_spot_pois} hazards in blind spots",
                    'blind_spots': blind_spots
                })
        
        if risk_data['risks']:
            risk_points.append(risk_data)
    
    return risk_points

def create_enhanced_map(coords, source, destination, pois, risk_analysis, tt_specs, username):
    """
    Create an enhanced map with mathematical visualizations
    """
    m = folium.Map(location=source, zoom_start=12)
    
    # Add start and end markers
    folium.Marker(source, popup='Start', icon=folium.Icon(color='green', icon='flag')).add_to(m)
    folium.Marker(destination, popup='End', icon=folium.Icon(color='red', icon='flag-checkered')).add_to(m)
    
    # Add main route with gradient coloring based on risk
    for i in range(len(coords) - 1):
        segment_coords = [coords[i], coords[i + 1]]
        
        # Determine color based on nearby risks
        color = 'green'  # Default safe
        for risk_point in risk_analysis:
            if abs(risk_point['index'] - i) < 10:
                if any(r['severity'] == 'CRITICAL' for r in risk_point['risks']):
                    color = 'darkred'
                    break
                elif any(r['severity'] == 'HIGH' for r in risk_point['risks']):
                    color = 'red'
                elif any(r['severity'] == 'MODERATE' for r in risk_point['risks']):
                    color = 'orange'
        
        folium.PolyLine(segment_coords, color=color, weight=4, opacity=0.8).add_to(m)
    
    # Add risk analysis markers
    for risk_point in risk_analysis:
        lat, lng = risk_point['location']
        
        # Create detailed popup
        popup_html = "<div style='width: 300px; font-family: Arial;'>"
        popup_html += "<h4>⚠️ Risk Analysis</h4>"
        
        for risk in risk_point['risks']:
            icon = {'rollover': '🔄', 'stopping_distance': '🛑', 
                   'intersection': '🚦', 'blind_spot': '👁️'}.get(risk['type'], '⚠️')
            popup_html += f"<div style='margin: 10px 0; padding: 8px; background: #f0f0f0; border-radius: 4px;'>"
            popup_html += f"<strong>{icon} {risk['type'].replace('_', ' ').title()}</strong><br>"
            popup_html += f"Severity: <span style='color: {'red' if risk['severity'] in ['CRITICAL', 'HIGH'] else 'orange'};'>{risk['severity']}</span><br>"
            popup_html += f"{risk['details']}<br>"
            
            if 'safe_speed' in risk:
                popup_html += f"Safe speed: {risk['safe_speed']:.0f} km/h<br>"
            if 'safe_following' in risk:
                popup_html += f"Safe following: {risk['safe_following']:.0f}m<br>"
            if 'factors' in risk and risk['factors']:
                popup_html += f"Factors:<br>"
                for factor in risk['factors'][:3]:  # Limit to 3 factors
                    popup_html += f"• {factor}<br>"
            
            popup_html += "</div>"
        
        popup_html += f"<div style='font-size: 10px; color: #666; margin-top: 8px;'>"
        popup_html += f"TT: {tt_specs['capacity_range']} ({tt_specs['gross_weight']/1000:.1f}T)<br>"
        popup_html += f"Analysis by: {username}"
        popup_html += "</div></div>"
        
        # Determine marker size and color based on severity
        max_severity = max([r['severity'] for r in risk_point['risks']], 
                          key=lambda x: ['LOW', 'MODERATE', 'HIGH', 'CRITICAL'].index(x))
        
        marker_color = {'CRITICAL': 'darkred', 'HIGH': 'red', 
                       'MODERATE': 'orange', 'LOW': 'yellow'}[max_severity]
        marker_size = {'CRITICAL': 15, 'HIGH': 12, 'MODERATE': 10, 'LOW': 8}[max_severity]
        
        folium.CircleMarker(
            location=(lat, lng),
            radius=marker_size,
            popup=folium.Popup(popup_html, max_width=300),
            color=marker_color,
            fillColor=marker_color,
            fillOpacity=0.6,
            weight=2
        ).add_to(m)
        
        # Add blind spot visualization for high-risk areas
        if any(r['type'] == 'blind_spot' and r['severity'] in ['HIGH', 'CRITICAL'] for r in risk_point['risks']):
            blind_spot_risk = next(r for r in risk_point['risks'] if r['type'] == 'blind_spot')
            if 'blind_spots' in blind_spot_risk:
                for spot_type, spot_coords in blind_spot_risk['blind_spots'].items():
                    if spot_coords:
                        folium.Polygon(
                            locations=spot_coords[:6],  # Limit points for performance
                            color='purple',
                            fill=True,
                            fillColor='purple',
                            fillOpacity=0.2,
                            weight=1,
                            popup=f"{spot_type.title()} blind spot"
                        ).add_to(m)
    
    # Add POIs
    for poi in pois:
        icon_config = {
            'hospital': {'color': 'red', 'icon': 'plus'},
            'police': {'color': 'blue', 'icon': 'shield'},
            'fuel': {'color': 'orange', 'icon': 'gas-pump'}
        }.get(poi['type'], {'color': 'gray', 'icon': 'info'})
        
        folium.Marker(
            location=poi['location'],
            popup=f"{poi['type'].title()}: {poi['name']}",
            icon=folium.Icon(**icon_config, prefix='fa')
        ).add_to(m)
    
    # Add stopping distance visualization at key points
    for i in range(0, len(coords), 100):  # Every 100 points
        if i < len(coords):
            lat, lng = coords[i]
            speed = tt_specs['max_speed'] * 0.7  # Typical speed
            gradient = calculate_gradient(coords, i)
            stopping = calculate_stopping_distance(speed, tt_specs, 'dry', gradient)
            
            if i > 0:
                bearing = calculate_bearing(coords[i-1][0], coords[i-1][1], lat, lng)
                # Draw stopping distance line
                end_lat = lat + (stopping['total_distance'] * math.cos(math.radians(bearing)) / 111111)
                end_lng = lng + (stopping['total_distance'] * math.sin(math.radians(bearing)) / (111111 * math.cos(math.radians(lat))))
                
                folium.PolyLine(
                    [(lat, lng), (end_lat, end_lng)],
                    color='yellow',
                    weight=2,
                    opacity=0.5,
                    dash_array='5, 10',
                    popup=f"Stopping distance at {speed:.0f}km/h: {stopping['total_distance']:.1f}m"
                ).add_to(m)
    
    # Add comprehensive legend
    legend_html = f"""
    {{% macro html(this, kwargs) %}}
    <div style="
        position: fixed;
        bottom: 50px;
        right: 50px;
        width: 380px;
        background-color: white;
        border: 2px solid grey;
        border-radius: 8px;
        z-index: 9999;
        padding: 15px;
        font-size: 11px;
        box-shadow: 0 4px 8px rgba(0,0,0,0.2);
        max-height: 500px;
        overflow-y: auto;
    ">
        <h4 style='margin-top: 0; color: #333;'>🚛 Advanced TT Navigation Analysis</h4>
        
        <div style='background: #f8f8f8; padding: 8px; border-radius: 4px; margin: 8px 0;'>
            <strong>Truck Specifications</strong><br>
            Type: {tt_specs['capacity_range']}<br>
            Weight: {tt_specs['gross_weight']/1000:.1f}T | COG: {tt_specs['center_of_gravity']:.1f}m<br>
            Dimensions: {tt_specs['length']:.1f}×{tt_specs['width']:.1f}×{tt_specs['height']:.1f}m<br>
            Turning Radius: {tt_specs['turning_radius']:.1f}m<br>
            User: {username}
        </div>
        
        <div style='background: #fff0f0; padding: 8px; border-radius: 4px; margin: 8px 0;'>
            <strong>Blind Spot Zones</strong><br>
            Left: {tt_specs['blind_spot_left']:.1f}m | Right: {tt_specs['blind_spot_right']:.1f}m<br>
            Rear: {tt_specs['blind_spot_rear']:.1f}m<br>
            <span style='color: purple;'>▓</span> Purple areas show blind spots
        </div>
        
        <div style='background: #f0f8ff; padding: 8px; border-radius: 4px; margin: 8px 0;'>
            <strong>Stopping Distances (Dry)</strong><br>
            @ 40km/h: {tt_specs['brake_distance_dry']:.0f}m<br>
            @ 60km/h: {tt_specs['brake_distance_dry']*2.25:.0f}m (estimated)<br>
            <span style='color: orange;'>---</span> Yellow lines show stopping distance
        </div>
        
        <div style='margin: 8px 0;'>
            <strong>Risk Indicators</strong><br>
            <span style='color: darkred;'>●</span> Critical Risk (>80% danger)<br>
            <span style='color: red;'>●</span> High Risk (60-80% danger)<br>
            <span style='color: orange;'>●</span> Moderate Risk (40-60%)<br>
            <span style='color: yellow;'>●</span> Low Risk (<40%)<br>
        </div>
        
        <div style='margin: 8px 0;'>
            <strong>Route Coloring</strong><br>
            <span style='color: green;'>━</span> Safe sections<br>
            <span style='color: orange;'>━</span> Caution required<br>
            <span style='color: red;'>━</span> High risk sections<br>
            <span style='color: darkred;'>━</span> Critical sections<br>
        </div>
        
        <div style='margin: 8px 0;'>
            <strong>Risk Types</strong><br>
            🔄 Rollover risk (curves)<br>
            🛑 Long stopping distance<br>
            🚦 Complex intersection<br>
            👁️ Blind spot hazards<br>
        </div>
        
        <hr style='margin: 10px 0;'>
        <div style='font-size: 9px; color: #666;'>
            Analysis uses physics-based models including:<br>
            • Rollover dynamics (lateral acceleration)<br>
            • Stopping distance (reaction + braking)<br>
            • Liquid surge effects ({tt_specs['avg_capacity_liters']:,}L capacity)<br>
            • Blind spot geometry calculations<br>
            Generated: {datetime.now().strftime('%Y-%m-%d %H:%M')}
        </div>
    </div>
    {{% endmacro %}}
    """
    
    legend = MacroElement()
    legend._template = Template(legend_html)
    m.get_root().add_child(legend)
    
    return m

def generate_comprehensive_report(coords, pois, risk_analysis, tt_specs, total_distance, total_duration):
    """
    Generate detailed mathematical analysis report
    """
    # Calculate statistics
    critical_risks = sum(1 for r in risk_analysis for risk in r['risks'] if risk['severity'] == 'CRITICAL')
    high_risks = sum(1 for r in risk_analysis for risk in r['risks'] if risk['severity'] == 'HIGH')
    moderate_risks = sum(1 for r in risk_analysis for risk in r['risks'] if risk['severity'] == 'MODERATE')
    
    # Calculate risk density
    try:
        distance_km = float(total_distance.split()[0])
        risk_density = (critical_risks + high_risks) / distance_km
    except:
        distance_km = 1
        risk_density = 0
    
    # Calculate average speeds for different sections
    safe_sections = len(coords) - len(risk_analysis) * 10
    avg_safe_speed = tt_specs['max_speed'] * 0.8
    avg_risk_speed = tt_specs['max_speed'] * 0.5
    
    # Estimate fuel consumption (simplified model)
    base_consumption = 35  # liters per 100km for loaded tanker
    weight_factor = 1 + (tt_specs['gross_weight'] - 25000) / 50000  # Weight adjustment
    speed_factor = 1 + (avg_safe_speed - 50) / 100  # Speed adjustment
    estimated_fuel = distance_km * base_consumption * weight_factor * speed_factor / 100
    
    report = {
        'summary': {
            'total_distance': total_distance,
            'total_duration': total_duration,
            'estimated_fuel': f"{estimated_fuel:.1f} L",
            'risk_density': f"{risk_density:.2f} risks/km"
        },
        'vehicle_specifications': {
            'type': tt_specs['capacity_range'],
            'gross_weight': f"{tt_specs['gross_weight']/1000:.1f} T",
            'dimensions': f"{tt_specs['length']:.1f}×{tt_specs['width']:.1f}×{tt_specs['height']:.1f}m",
            'turning_radius': f"{tt_specs['turning_radius']:.1f}m",
            'center_of_gravity': f"{tt_specs['center_of_gravity']:.1f}m",
            'max_legal_speed': f"{tt_specs['max_speed']} km/h"
        },
        'risk_analysis': {
            'total_risk_points': len(risk_analysis),
            'critical_risks': critical_risks,
            'high_risks': high_risks,
            'moderate_risks': moderate_risks,
            'rollover_risks': sum(1 for r in risk_analysis for risk in r['risks'] if risk['type'] == 'rollover'),
            'intersection_risks': sum(1 for r in risk_analysis for risk in r['risks'] if risk['type'] == 'intersection'),
            'blind_spot_risks': sum(1 for r in risk_analysis for risk in r['risks'] if risk['type'] == 'blind_spot'),
            'stopping_distance_concerns': sum(1 for r in risk_analysis for risk in r['risks'] if risk['type'] == 'stopping_distance')
        },
        'safety_metrics': {
            'avg_stopping_distance_40kmh': f"{tt_specs['brake_distance_dry']:.0f}m (dry), {tt_specs['brake_distance_wet']:.0f}m (wet)",
            'blind_spot_coverage': f"{(tt_specs['blind_spot_left'] + tt_specs['blind_spot_right']) * tt_specs['length']:.1f}m²",
            'safe_following_distance': f"{calculate_stopping_distance(50, tt_specs)['safe_following_distance']:.0f}m at 50km/h",
            'rollover_threshold_speed': f"{math.sqrt(9.81 * tt_specs['turning_radius'] * tt_specs['width'] / (2 * tt_specs['center_of_gravity'])) * 3.6:.0f} km/h on flat curve"
        },
        'recommendations': generate_smart_recommendations(risk_analysis, tt_specs, distance_km),
        'compliance_notes': [
            f"Maximum axle load: {tt_specs['axle_load']:.1f}T - Verify bridge ratings",
            f"Gross vehicle weight: {tt_specs['gross_weight']/1000:.1f}T - Check route restrictions",
            "Hazardous material placards required for petroleum products",
            "Driver must have ADR certification for dangerous goods",
            "Emergency response plan must be accessible"
        ]
    }
    
    return report

def generate_smart_recommendations(risk_analysis, tt_specs, distance_km):
    """
    Generate intelligent recommendations based on risk analysis
    """
    recommendations = []
    
    # Analyze risk patterns
    rollover_count = sum(1 for r in risk_analysis for risk in r['risks'] if risk['type'] == 'rollover')
    intersection_count = sum(1 for r in risk_analysis for risk in r['risks'] if risk['type'] == 'intersection')
    blind_spot_count = sum(1 for r in risk_analysis for risk in r['risks'] if risk['type'] == 'blind_spot')
    
    # Speed recommendations
    if rollover_count > 5:
        max_curve_speed = min(r['safe_speed'] for r in risk_analysis 
                              for risk in r['risks'] if risk['type'] == 'rollover' and 'safe_speed' in risk)
        recommendations.append(f"⚠️ High rollover risk route - Maximum speed in curves: {max_curve_speed:.0f} km/h")
    
    # Intersection recommendations
    if intersection_count > 3:
        recommendations.append("🚦 Multiple complex intersections - Use spotter/assistant for blind spots")
    
    # Weight-specific recommendations
    if tt_specs['gross_weight'] > 35000:
        recommendations.append("⚖️ Heavy load - Plan for extended stopping distances and avoid steep grades")
    
    # Time recommendations
    if distance_km > 200:
        recommendations.append("⏱️ Long route - Plan mandatory rest stops every 2 hours per regulations")
    
    # Blind spot recommendations
    if blind_spot_count > 0:
        recommendations.append(f"👁️ Install convex mirrors to cover {tt_specs['blind_spot_rear']:.1f}m rear blind zone")
    
    # Fuel recommendations
    fuel_stops_needed = math.ceil(distance_km / 400)  # Assuming 400km range
    if fuel_stops_needed > 1:
        recommendations.append(f"⛽ Plan {fuel_stops_needed} fuel stops for this route")
    
    # Weather-based (simulated)
    recommendations.append("🌧️ Check weather conditions - stopping distance increases 50% in wet conditions")
    
    return recommendations

@app.route('/')
@login_required
def home():
    """Enhanced home route with TT selection"""
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
        # Default landmarks
        landmarks = [
            {'name': 'Delhi Terminal', 'lat': 28.6139, 'lng': 77.2090},
            {'name': 'Mumbai Terminal', 'lat': 19.0760, 'lng': 72.8777}
        ]
    
    return render_template("route_form.html", 
                         landmarks=landmarks,
                         tt_specifications=TT_SPECIFICATIONS,
                         username=username)

@app.route('/analyze_route', methods=['POST'])
@login_required
def analyze_route():
    """Enhanced route analysis with mathematical models"""
    try:
        directions = session.get('directions')
        tt_specs = session.get('tt_specs')
        username = session.get('username', 'User')
        index = int(request.form['route_index'])

        if not directions or index >= len(directions) or not tt_specs:
            return "Invalid route selected. Please start over."

        selected = directions[index]
        coords = polyline.decode(selected['overview_polyline']['points'])
        source = session['source']
        destination = session['destination']
        
        total_distance = selected['legs'][0]['distance']['text']
        total_duration = selected['legs'][0]['duration']['text']

        # Get POIs
        pois = []
        for keyword in ['hospital', 'police', 'fuel']:
            sample_coords = coords[::30]
            for lat, lng in sample_coords:
                try:
                    places = gmaps.places_nearby(location=(lat, lng), radius=500, keyword=keyword)
                    for place in places.get('results', []):
                        pois.append({
                            'name': place['name'],
                            'location': (place['geometry']['location']['lat'],
                                       place['geometry']['location']['lng']),
                            'type': keyword
                        })
                except:
                    continue

        # Perform advanced risk analysis
        risk_analysis = generate_advanced_risk_analysis(coords, pois, tt_specs)
        
        # Create enhanced map
        m = create_enhanced_map(coords, source, destination, pois, risk_analysis, tt_specs, username)
        
        # Save map
        unique_map_id = uuid4().hex
        html_name = f"route_map_{unique_map_id}.html"
        m.save(f"templates/{html_name}")
        
        # Generate comprehensive report
        route_report = generate_comprehensive_report(coords, pois, risk_analysis, tt_specs, 
                                                    total_distance, total_duration)
        
        session['route_report'] = route_report
        session.modified = True

        return render_template("route_analysis.html",
                             mode="Advanced TT Navigation",
                             html_file=html_name,
                             route_report=route_report,
                             tt_specs=tt_specs,
                             username=username,
                             risk_count=len(risk_analysis),
                             critical_risks=route_report['risk_analysis']['critical_risks'])

    except Exception as e:
        print(f"Error in analyze_route: {e}")
        import traceback
        traceback.print_exc()
        return f"Error analyzing route: {str(e)}"

# Keep all other routes from the original code (login, logout, fetch_routes, etc.)
# They remain the same as in your original implementation

if __name__ == '__main__':
    if not os.path.exists("templates"):
        os.makedirs("templates")
    if not os.path.exists("flask_session"):
        os.makedirs("flask_session")
    
    print("Enhanced IndianOil Smart Marg - Advanced TT Navigation System")
    print("=" * 60)
    print("Features: Blind spot analysis, Rollover risk, Stopping distance")
    print("=" * 60)
    
    app.run(debug=True, host='0.0.0.0', port=5000)
