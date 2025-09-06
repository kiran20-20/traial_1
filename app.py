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

# REPLACE your calculate_bearing function with:
def calculate_precise_bearing(lat1, lng1, lat2, lng2):
    """Calculate precise bearing between two points using proper geodesic calculations"""
    lat1, lng1, lat2, lng2 = map(math.radians, [lat1, lng1, lat2, lng2])
    
    dlng = lng2 - lng1
    y = math.sin(dlng) * math.cos(lat2)
    x = math.cos(lat1) * math.sin(lat2) - math.sin(lat1) * math.cos(lat2) * math.cos(dlng)
    
    bearing = math.atan2(y, x)
    bearing = math.degrees(bearing)
    bearing = (bearing + 360) % 360
    
    return bearing

# REPLACE your calculate_turn_angle function with:
def calculate_turn_angle_precise(bearing1, bearing2):
    """Calculate the actual turn angle with proper handling of 360-degree wrap-around"""
    diff = bearing2 - bearing1
    
    # Handle wrap-around cases
    if diff > 180:
        diff -= 360
    elif diff < -180:
        diff += 360
    
    return abs(diff)


def detect_sharp_turns_and_curves(coords, min_turn_angle=45, sample_distance=5):
    """Detect actual sharp turns (90+ degrees) and curves with proper sampling"""
    sharp_turns = []
    curves = []
    
    if len(coords) < sample_distance * 2:
        return sharp_turns, curves
    
    for i in range(sample_distance, len(coords) - sample_distance):
        try:
            point_before = coords[i - sample_distance]
            current_point = coords[i]
            point_after = coords[i + sample_distance]
            
            bearing_in = calculate_precise_bearing(
                point_before[0], point_before[1], 
                current_point[0], current_point[1]
            )
            bearing_out = calculate_precise_bearing(
                current_point[0], current_point[1],
                point_after[0], point_after[1]
            )
            
            turn_angle = calculate_turn_angle_precise(bearing_in, bearing_out)
            turn_direction = "right" if (bearing_out - bearing_in + 360) % 360 < 180 else "left"
            
            if turn_angle >= 90:  # Sharp turn (90+ degrees)
                sharp_turns.append({
                    'location': current_point,
                    'index': i,
                    'turn_angle': turn_angle,
                    'direction': turn_direction,
                    'bearing_in': bearing_in,
                    'bearing_out': bearing_out,
                    'severity': 'critical' if turn_angle > 120 else 'high'
                })
            elif turn_angle >= min_turn_angle:  # Moderate curve
                curves.append({
                    'location': current_point,
                    'index': i,
                    'turn_angle': turn_angle,
                    'direction': turn_direction,
                    'bearing_in': bearing_in,
                    'bearing_out': bearing_out,
                    'severity': 'moderate' if turn_angle > 60 else 'low'
                })
                
        except Exception as e:
            print(f"Error calculating turn at index {i}: {e}")
            continue
    
    return sharp_turns, curves

def calculate_blind_spots(lat, lng, bearing, tt_specs):
    """Calculate precise blind spot polygons for truck tankers"""
    bearing_rad = math.radians(bearing)
    
    left_angle_start = bearing_rad - math.radians(150)
    left_angle_end = bearing_rad - math.radians(90)
    right_angle_start = bearing_rad + math.radians(90)
    right_angle_end = bearing_rad + math.radians(150)
    rear_angle_start = bearing_rad + math.radians(135)
    rear_angle_end = bearing_rad + math.radians(225)
    
    blind_spots = {}
    
    # Left blind spot
    left_blind_spot = [(lat, lng)]
    for angle in np.linspace(left_angle_start, left_angle_end, 8):
        for radius in [2, 8]:
            dlat = radius * math.cos(angle) / 111111
            dlng = radius * math.sin(angle) / (111111 * math.cos(math.radians(lat)))
            left_blind_spot.append((lat + dlat, lng + dlng))
    
    # Right blind spot
    right_blind_spot = [(lat, lng)]
    for angle in np.linspace(right_angle_start, right_angle_end, 8):
        for radius in [2, 10]:
            dlat = radius * math.cos(angle) / 111111
            dlng = radius * math.sin(angle) / (111111 * math.cos(math.radians(lat)))
            right_blind_spot.append((lat + dlat, lng + dlng))
    
    # Rear blind spot
    rear_blind_spot = [(lat, lng)]
    for angle in np.linspace(rear_angle_start, rear_angle_end, 10):
        for radius in [3, 15]:
            dlat = radius * math.cos(angle) / 111111
            dlng = radius * math.sin(angle) / (111111 * math.cos(math.radians(lat)))
            rear_blind_spot.append((lat + dlat, lng + dlng))
    
    return {
        'left': left_blind_spot,
        'right': right_blind_spot,
        'rear': rear_blind_spot
    }



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

@app.route('/analyze_route', methods=['POST'])
@login_required
def analyze_route():
    """Enhanced route analysis with proper turn detection and animation"""
    try:
        directions = session.get('directions')
        tt_specs = session.get('tt_specs')
        username = session.get('username', 'User')
        index = int(request.form['route_index'])

        if not directions or index >= len(directions) or not tt_specs:
            return "Invalid route selected or session data expired. Please start over."

        selected = directions[index]
        coords = polyline.decode(selected['overview_polyline']['points'])
        source = session['source']
        destination = session['destination']
        
        total_distance = selected['legs'][0]['distance']['text']
        total_duration = selected['legs'][0]['duration']['text']

        # Detect sharp turns and curves with proper algorithm
        sharp_turns, curves = detect_sharp_turns_and_curves(coords, min_turn_angle=45, sample_distance=8)
        
        print(f"Detected {len(sharp_turns)} sharp turns (90°+) and {len(curves)} curves")
        
        # Get POIs (simplified version)
        def get_pois(keyword):
            pois = []
            try:
                sample_coords = coords[::30] if len(coords) > 30 else coords
                for lat, lng in sample_coords:
                    try:
                        places = gmaps.places_nearby(location=(lat, lng), radius=500, keyword=keyword)
                        for place in places.get('results', [])[:2]:
                            pois.append({
                                'name': place['name'],
                                'location': (
                                    place['geometry']['location']['lat'],
                                    place['geometry']['location']['lng']
                                ),
                                'type': keyword
                            })
                    except Exception as e:
                        continue
            except Exception as e:
                print(f"Error in get_pois for {keyword}: {e}")
            return pois

        all_pois = []
        for keyword in ['hospital', 'police', 'fuel']:
            all_pois.extend(get_pois(keyword))

        # Create enhanced map with animation
        center_lat = sum(coord[0] for coord in coords) / len(coords)
        center_lng = sum(coord[1] for coord in coords) / len(coords)
        
        m = folium.Map(location=(center_lat, center_lng), zoom_start=12)
        
        # Add route with color coding
        for i in range(len(coords) - 1):
            segment = [coords[i], coords[i + 1]]
            segment_color = 'green'  # Default safe
            
            # Check for nearby sharp turns
            for turn in sharp_turns:
                if abs(turn['index'] - i) <= 3:
                    segment_color = 'red' if turn['severity'] == 'critical' else 'orange'
                    break
            
            # Check for curves if no sharp turns
            if segment_color == 'green':
                for curve in curves:
                    if abs(curve['index'] - i) <= 2:
                        segment_color = 'yellow'
                        break
            
            folium.PolyLine(segment, color=segment_color, weight=6, opacity=0.8).add_to(m)
        
        # Add start/end markers
        folium.Marker(source, popup='START', icon=folium.Icon(color='green', icon='play', prefix='fa')).add_to(m)
        folium.Marker(destination, popup='DESTINATION', icon=folium.Icon(color='red', icon='stop', prefix='fa')).add_to(m)
        
        # Add sharp turn markers with blind spots
        for turn in sharp_turns:
            lat, lng = turn['location']
            
            turn_popup = f"""
            <div style='font-family: Arial; width: 300px;'>
                <h4 style='color: red;'>⚠️ SHARP TURN</h4>
                <p><strong>Angle:</strong> {turn['turn_angle']:.1f}°</p>
                <p><strong>Direction:</strong> {turn['direction'].upper()}</p>
                <p><strong>Speed:</strong> 10-15 km/h recommended</p>
                <p style='color: red; font-weight: bold;'>HIGH ROLLOVER RISK!</p>
            </div>
            """
            
            icon_color = 'darkred' if turn['severity'] == 'critical' else 'red'
            folium.Marker(
                location=(lat, lng),
                popup=turn_popup,
                icon=folium.Icon(color=icon_color, icon='exclamation-triangle', prefix='fa')
            ).add_to(m)
            
            # Add blind spots
            bearing = turn['bearing_out']
            blind_spots = calculate_blind_spots(lat, lng, bearing, tt_specs)
            
            for spot_name, spot_coords in blind_spots.items():
                if len(spot_coords) > 3:
                    folium.Polygon(
                        locations=spot_coords,
                        color='purple',
                        fill=True,
                        fillColor='purple',
                        fillOpacity=0.3,
                        weight=2,
                        popup=f"{spot_name.title()} blind spot"
                    ).add_to(m)
        
        # Add truck animation
        truck_animation = f"""
        <script>
            var routeCoords = {json.dumps(coords)};
            var sharpTurns = {json.dumps(sharp_turns)};
            var currentIndex = 0;
            var truckMarker = null;
            var animationSpeed = 200;
            
            function createTruckIcon(bearing) {{
                return L.divIcon({{
                    html: '<div style="transform: rotate(' + bearing + 'deg); font-size: 24px;">🚛</div>',
                    iconSize: [30, 30],
                    iconAnchor: [15, 15]
                }});
            }}
            
            function calculateBearing(lat1, lng1, lat2, lng2) {{
                var dLng = (lng2 - lng1) * Math.PI / 180;
                var lat1Rad = lat1 * Math.PI / 180;
                var lat2Rad = lat2 * Math.PI / 180;
                var y = Math.sin(dLng) * Math.cos(lat2Rad);
                var x = Math.cos(lat1Rad) * Math.sin(lat2Rad) - Math.sin(lat1Rad) * Math.cos(lat2Rad) * Math.cos(dLng);
                var bearing = Math.atan2(y, x) * 180 / Math.PI;
                return (bearing + 360) % 360;
            }}
            
            function checkNearbyHazards(currentPos) {{
                for (var i = 0; i < sharpTurns.length; i++) {{
                    var turn = sharpTurns[i];
                    var distance = Math.sqrt(
                        Math.pow(currentPos[0] - turn.location[0], 2) + 
                        Math.pow(currentPos[1] - turn.location[1], 2)
                    ) * 111111; // Convert to meters
                    
                    if (distance < 100) {{
                        return {{
                            type: 'sharp_turn',
                            angle: turn.turn_angle,
                            direction: turn.direction,
                            severity: turn.severity
                        }};
                    }}
                }}
                return null;
            }}
            
            function moveTruck() {{
                if (currentIndex >= routeCoords.length - 1) {{
                    currentIndex = 0;
                }}
                
                var currentPos = routeCoords[currentIndex];
                var nextPos = routeCoords[Math.min(currentIndex + 1, routeCoords.length - 1)];
                
                if (truckMarker) {{
                    map.removeLayer(truckMarker);
                }}
                
                var bearing = calculateBearing(currentPos[0], currentPos[1], nextPos[0], nextPos[1]);
                var hazard = checkNearbyHazards(currentPos);
                
                truckMarker = L.marker([currentPos[0], currentPos[1]], {{
                    icon: createTruckIcon(bearing)
                }}).addTo(map);
                
                var popupContent = `
                    <div style='text-align: center; font-family: Arial;'>
                        <h4>🚛 Live Position</h4>
                        <p><strong>Progress:</strong> ${{Math.round((currentIndex/routeCoords.length)*100)}}%</p>
                        <p><strong>TT:</strong> {tt_specs['capacity_range']}</p>
                `;
                
                if (hazard) {{
                    popupContent += `
                        <div style='background: red; color: white; padding: 5px; border-radius: 3px; margin: 5px 0;'>
                            <strong>⚠️ HAZARD ALERT!</strong><br>
                            Sharp ${{hazard.direction}} turn: ${{hazard.angle.toFixed(1)}}°<br>
                            REDUCE SPEED TO 10-15 KM/H!
                        </div>
                    `;
                }}
                
                popupContent += '</div>';
                truckMarker.bindPopup(popupContent);
                
                if (hazard) {{
                    truckMarker.openPopup();
                }}
                
                currentIndex++;
            }}
            
            setInterval(moveTruck, animationSpeed);
        </script>
        """
        
        m.get_root().html.add_child(folium.Element(truck_animation))
        
        # Save map
        unique_map_id = uuid4().hex
        html_name = f"route_map_{unique_map_id}.html"
        m.save(f"templates/{html_name}")

        # Generate report
        route_report = {
            'total_distance': total_distance,
            'total_duration': total_duration,
            'sharp_turns_detected': len(sharp_turns),
            'curves_detected': len(curves),
            'critical_turns': len([t for t in sharp_turns if t['severity'] == 'critical']),
            'safety_recommendations': [
                f"CRITICAL: {len(sharp_turns)} sharp turns detected (90°+)",
                f"Reduce speed to 10-15 km/h at sharp turns",
                f"Watch for blind spots at turns",
                f"Total curves requiring caution: {len(curves)}"
            ]
        }

        session['route_report'] = route_report
        session.modified = True

        return render_template("route_analysis.html",
                               mode="Enhanced TT Navigation",
                               html_file=html_name,
                               route_report=route_report,
                               sharp_turns=len(sharp_turns),
                               curves=len(curves),
                               tt_specs=tt_specs,
                               username=username)

    except Exception as e:
        print(f"Error in analyze_route: {e}")
        import traceback
        traceback.print_exc()
        return f"Error analyzing route: {str(e)}"

@app.route('/detailed_report')
@login_required
def detailed_report():
    """Show detailed route analysis report with TT specifications"""
    try:
        report = session.get('route_report')
        tt_specs = session.get('tt_specs')
        username = session.get('username', 'User')
        if not report or not tt_specs:
            return "No route analysis data found. Please analyze a route first."
        
        return render_template("detailed_report.html", report=report, tt_specs=tt_specs, username=username)
        
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

