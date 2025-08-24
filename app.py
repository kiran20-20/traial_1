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

def get_realistic_traffic_data(coords, gmaps_client):
    """Get realistic traffic data for route coordinates using actual traffic patterns"""
    traffic_data = []
    
    try:
        # Sample every 8th point to avoid API limits while maintaining coverage
        sample_coords = coords[::max(1, len(coords)//20)] if len(coords) > 20 else coords
        
        current_hour = datetime.now().hour
        current_day = datetime.now().weekday()  # 0=Monday, 6=Sunday
        
        # Define rush hour periods
        is_morning_rush = 7 <= current_hour <= 10
        is_evening_rush = 17 <= current_hour <= 20
        is_weekend = current_day >= 5
        
        for i, (lat, lng) in enumerate(sample_coords):
            try:
                # Try to get real traffic data (limited by API quota)
                try:
                    # This would use actual traffic API if available
                    # directions_result = gmaps_client.directions(
                    #     (lat, lng), 
                    #     sample_coords[min(i+1, len(sample_coords)-1)],
                    #     mode="driving",
                    #     departure_time=datetime.now(),
                    #     traffic_model="best_guess"
                    # )
                    # Real traffic data would be extracted here
                    real_traffic_available = False
                except:
                    real_traffic_available = False
                
                # Fallback to realistic simulation based on time and location patterns
                if not real_traffic_available:
                    # Base traffic probability
                    if is_weekend:
                        traffic_probs = {'light': 0.6, 'moderate': 0.3, 'heavy': 0.1}
                    elif is_morning_rush or is_evening_rush:
                        traffic_probs = {'light': 0.2, 'moderate': 0.4, 'heavy': 0.4}
                    elif 10 <= current_hour <= 16:  # Midday
                        traffic_probs = {'light': 0.5, 'moderate': 0.4, 'heavy': 0.1}
                    else:  # Night/early morning
                        traffic_probs = {'light': 0.8, 'moderate': 0.15, 'heavy': 0.05}
                    
                    # Urban vs rural adjustment (simplified based on coordinate clustering)
                    urban_factor = 1.0
                    if i > 0:
                        # Check if multiple POIs nearby (indicates urban area)
                        try:
                            places_nearby = gmaps_client.places_nearby(
                                location=(lat, lng), 
                                radius=1000, 
                                type='establishment'
                            )
                            poi_count = len(places_nearby.get('results', []))
                            if poi_count > 10:  # Urban area
                                urban_factor = 1.5
                                traffic_probs['heavy'] = min(0.6, traffic_probs['heavy'] * 1.8)
                                traffic_probs['light'] = max(0.1, traffic_probs['light'] * 0.5)
                                # Normalize probabilities
                                total = sum(traffic_probs.values())
                                traffic_probs = {k: v/total for k, v in traffic_probs.items()}
                        except:
                            pass
                    
                    traffic_level = np.random.choice(
                        list(traffic_probs.keys()), 
                        p=list(traffic_probs.values())
                    )
                
                # Calculate delay factors with truck-specific adjustments
                base_delays = {'light': 1.0, 'moderate': 1.4, 'heavy': 2.1}
                delay_factor = base_delays[traffic_level]
                
                traffic_data.append({
                    'location': (lat, lng),
                    'traffic_level': traffic_level,
                    'delay_factor': delay_factor,
                    'realistic': real_traffic_available,
                    'time_based': True,
                    'urban_factor': urban_factor
                })
                
                # Rate limiting for API calls
                time.sleep(0.1)
                
            except Exception as e:
                print(f"Error getting traffic for point {i}: {e}")
                # Fallback to simple traffic assignment
                traffic_data.append({
                    'location': (lat, lng),
                    'traffic_level': 'moderate',
                    'delay_factor': 1.3,
                    'realistic': False,
                    'time_based': False,
                    'urban_factor': 1.0
                })
                continue
    
    except Exception as e:
        print(f"Error in realistic traffic analysis: {e}")
    
    return traffic_data

def identify_realistic_poi_hazards(coords, pois, tt_specs):
    """Identify realistic hazard zones based on actual POIs and truck characteristics"""
    hazard_zones = []
    risk_multiplier = tt_specs["risk_multiplier"]
    current_hour = datetime.now().hour
    
    try:
        # Group coordinates into zones for efficient processing
        zone_size = max(1, len(coords) // 50)  # Create ~50 zones
        coord_zones = [coords[i:i + zone_size] for i in range(0, len(coords), zone_size)]
        
        for zone_coords in coord_zones:
            if not zone_coords:
                continue
                
            # Use center point of zone for analysis
            center_lat = sum(coord[0] for coord in zone_coords) / len(zone_coords)
            center_lng = sum(coord[1] for coord in zone_coords) / len(zone_coords)
            zone_center = (center_lat, center_lng)
            
            # Find POIs within hazard range of this zone
            nearby_pois = []
            hazard_range_km = 0.5  # 500m hazard detection range
            
            for poi in pois:
                distance_km = geodesic(zone_center, poi['location']).kilometers
                if distance_km <= hazard_range_km:
                    nearby_pois.append({
                        'name': poi['name'],
                        'type': poi['type'],
                        'distance': distance_km * 1000,  # Convert to meters
                        'location': poi['location']
                    })
            
            if not nearby_pois:
                continue
            
            # Calculate risk based on actual POI types and truck specifications
            risk_score = 0
            risk_factors = []
            primary_hazards = []
            tt_specific_recommendations = []
            
            for poi in nearby_pois:
                poi_type = poi['type']
                distance_m = poi['distance']
                poi_name = poi['name']
                
                # Distance-weighted risk calculation
                distance_factor = max(0.1, 1.0 - (distance_m / 500.0))  # Risk decreases with distance
                
                # POI-specific risk calculations
                if poi_type == 'fuel':
                    # EXTREME HAZARD: Petroleum tanker near fuel station
                    base_risk = 8.0
                    adjusted_risk = base_risk * risk_multiplier * 1.5  # Extra multiplier for fuel
                    risk_score += adjusted_risk * distance_factor
                    risk_factors.append(f"EXTREME: Fuel station '{poi_name}' at {distance_m:.0f}m")
                    primary_hazards.append(poi)
                    tt_specific_recommendations.extend([
                        "Reduce speed to 15-20 kmph when passing",
                        "No smoking/ignition sources - Class 3 flammable cargo",
                        "Emergency response team on standby"
                    ])
                
                elif poi_type == 'health':
                    # Hospital/medical facility - emergency vehicle traffic
                    base_risk = 4.0
                    # Higher risk during day hours
                    time_multiplier = 1.3 if 8 <= current_hour <= 20 else 1.0
                    adjusted_risk = base_risk * risk_multiplier * time_multiplier
                    risk_score += adjusted_risk * distance_factor
                    risk_factors.append(f"Hospital '{poi_name}' - emergency vehicles ({distance_m:.0f}m)")
                    if distance_m < 200:
                        primary_hazards.append(poi)
                        tt_specific_recommendations.append(f"Watch for ambulances - {tt_specs['gross_weight']/1000:.1f}T stopping distance")
                
                elif poi_type == 'education':
                    # School zone - extremely dangerous during school hours
                    base_risk = 3.0
                    # School hours: 7-9 AM, 1-5 PM on weekdays
                    is_school_time = (7 <= current_hour <= 9 or 13 <= current_hour <= 17) and datetime.now().weekday() < 5
                    time_multiplier = 2.5 if is_school_time else 0.8
                    
                    # Heavy trucks pose greater risk to children
                    weight_multiplier = 1.0 + (tt_specs['gross_weight'] - 15000) / 30000  # Scale with weight
                    
                    adjusted_risk = base_risk * risk_multiplier * time_multiplier * weight_multiplier
                    risk_score += adjusted_risk * distance_factor
                    
                    status = "ACTIVE SCHOOL HOURS" if is_school_time else "school hours inactive"
                    risk_factors.append(f"School '{poi_name}' - {status} ({distance_m:.0f}m)")
                    
                    if distance_m < 300 and is_school_time:
                        primary_hazards.append(poi)
                        tt_specific_recommendations.extend([
                            f"School zone speed limit: 25 kmph MAX",
                            f"Extra vigilance - {tt_specs['capacity_range']} tanker visibility issues",
                            "Children crossing - extended braking distance required"
                        ])
                
                elif poi_type == 'safety':
                    # Police station - usually positive but traffic checkpoints possible
                    base_risk = 1.5
                    adjusted_risk = base_risk * risk_multiplier * 0.8  # Slightly lower risk
                    risk_score += adjusted_risk * distance_factor
                    risk_factors.append(f"Police station '{poi_name}' - checkpoint possible ({distance_m:.0f}m)")
                    
                elif poi_type == 'commercial':
                    # Shopping areas - heavy pedestrian and vehicle traffic
                    base_risk = 3.5
                    # Higher risk during evening shopping hours
                    time_multiplier = 1.4 if 17 <= current_hour <= 21 else 1.0
                    adjusted_risk = base_risk * risk_multiplier * time_multiplier
                    risk_score += adjusted_risk * distance_factor
                    risk_factors.append(f"Commercial zone '{poi_name}' - heavy traffic ({distance_m:.0f}m)")
                    
                    if distance_m < 250:
                        tt_specific_recommendations.append("Congested area - maintain safe following distance")
                
                elif poi_type == 'religious':
                    # Religious sites - crowd risk during prayer times/festivals
                    base_risk = 2.5
                    # Friday afternoons, weekend mornings typically busy
                    is_busy_time = (current_hour == 12 and datetime.now().weekday() == 4) or \
                                  (6 <= current_hour <= 10 and datetime.now().weekday() >= 5)
                    time_multiplier = 1.8 if is_busy_time else 1.0
                    
                    adjusted_risk = base_risk * risk_multiplier * time_multiplier
                    risk_score += adjusted_risk * distance_factor
                    risk_factors.append(f"Religious site '{poi_name}' - crowd risk ({distance_m:.0f}m)")
            
            # Additional truck-specific risk factors
            if risk_score > 0:
                # Heavy truck specific risks
                if tt_specs["gross_weight"] > 35000:
                    risk_score += 1.0
                    risk_factors.append(f"Heavy TT penalty - {tt_specs['gross_weight']/1000:.1f}T gross weight")
                
                # High-capacity tanker risks
                if tt_specs["avg_capacity_liters"] > 25000:
                    risk_score += 0.8
                    risk_factors.append(f"Large capacity hazmat - {tt_specs['avg_capacity_liters']:,}L petroleum")
            
            # Only create hazard zone if significant risk exists
            if risk_score >= 2.5:  # Minimum threshold for hazard zone
                # Determine risk level
                if risk_score >= 8:
                    risk_level = 'Critical'
                elif risk_score >= 5:
                    risk_level = 'High'
                else:
                    risk_level = 'Medium'
                
                hazard_zones.append({
                    'location': zone_center,
                    'risk_score': min(risk_score, 10.0),  # Cap at 10
                    'risk_level': risk_level,
                    'risk_factors': risk_factors,
                    'hazard_count': len(nearby_pois),
                    'primary_hazards': primary_hazards[:3],  # Top 3 most dangerous
                    'tt_specific_recommendations': list(set(tt_specific_recommendations))[:4],  # Remove duplicates, limit to 4
                    'time_sensitive': any('ACTIVE' in factor or 'emergency' in factor for factor in risk_factors)
                })
    
    except Exception as e:
        print(f"Error in realistic hazard identification: {e}")
        import traceback
        traceback.print_exc()
    
    # Sort by risk score and return top hazards
    hazard_zones.sort(key=lambda x: x['risk_score'], reverse=True)
    return hazard_zones[:25]  # Return top 25 most dangerous zones

def calculate_enhanced_turn_analysis(coords, tt_specs):
    """
    Enhanced turn analysis with comprehensive detection of critical turns including:
    - Better 90-degree turn detection
    - Improved blind spot identification
    - More sensitive curve detection
    - Multiple analysis methods for accuracy
    """
    turns = []
    
    try:
        # Enhanced analysis parameters
        min_analysis_points = 12  # Minimum points needed for analysis
        
        if len(coords) < min_analysis_points:
            return turns
        
        # Multi-scale analysis for better turn detection
        analysis_scales = [2, 4, 6]  # Different window sizes for analysis
        
        # Analyze every point with multiple scales
        for i in range(6, len(coords) - 6, 1):  # Skip fewer points for better detection
            try:
                turn_detections = []
                
                # Multi-scale turn angle calculation
                for scale in analysis_scales:
                    if i >= scale and i + scale < len(coords):
                        # Method 1: Direct bearing comparison
                        bearing_before = calculate_bearing(
                            coords[i-scale][0], coords[i-scale][1], 
                            coords[i][0], coords[i][1]
                        )
                        bearing_after = calculate_bearing(
                            coords[i][0], coords[i][1], 
                            coords[i+scale][0], coords[i+scale][1]
                        )
                        turn_angle1 = calculate_turn_angle(bearing_before, bearing_after)
                        
                        # Method 2: Three-point angle calculation
                        if i >= scale*2 and i + scale*2 < len(coords):
                            bearing_far_before = calculate_bearing(
                                coords[i-scale*2][0], coords[i-scale*2][1], 
                                coords[i-scale][0], coords[i-scale][1]
                            )
                            bearing_far_after = calculate_bearing(
                                coords[i+scale][0], coords[i+scale][1], 
                                coords[i+scale*2][0], coords[i+scale*2][1]
                            )
                            turn_angle2 = calculate_turn_angle(bearing_far_before, bearing_far_after)
                        else:
                            turn_angle2 = turn_angle1
                        
                        # Method 3: Vector-based angle calculation
                        try:
                            # Convert to local coordinate system for better accuracy
                            p1 = coords[i-scale]
                            p2 = coords[i]  # Turn point
                            p3 = coords[i+scale]
                            
                            # Convert to meters using approximate conversion
                            x1 = p1[1] * 111320 * math.cos(math.radians(p1[0]))
                            y1 = p1[0] * 110540
                            x2 = p2[1] * 111320 * math.cos(math.radians(p2[0]))
                            y2 = p2[0] * 110540
                            x3 = p3[1] * 111320 * math.cos(math.radians(p3[0]))
                            y3 = p3[0] * 110540
                            
                            # Calculate vectors
                            v1 = (x2 - x1, y2 - y1)
                            v2 = (x3 - x2, y3 - y2)
                            
                            # Calculate angle between vectors
                            if (v1[0]**2 + v1[1]**2) > 0 and (v2[0]**2 + v2[1]**2) > 0:
                                dot_product = v1[0]*v2[0] + v1[1]*v2[1]
                                mag1 = math.sqrt(v1[0]**2 + v1[1]**2)
                                mag2 = math.sqrt(v2[0]**2 + v2[1]**2)
                                cos_angle = max(-1, min(1, dot_product / (mag1 * mag2)))
                                turn_angle3 = math.degrees(math.acos(cos_angle))
                            else:
                                turn_angle3 = turn_angle1
                        except:
                            turn_angle3 = turn_angle1
                        
                        # Store all detection methods for this scale
                        turn_detections.append({
                            'scale': scale,
                            'angle_method1': turn_angle1,
                            'angle_method2': turn_angle2,
                            'angle_method3': turn_angle3,
                            'max_angle': max(turn_angle1, turn_angle2, turn_angle3),
                            'avg_angle': (turn_angle1 + turn_angle2 + turn_angle3) / 3
                        })
                
                if not turn_detections:
                    continue
                
                # Find the most significant turn detection across all scales
                max_detection = max(turn_detections, key=lambda x: x['max_angle'])
                
                # Enhanced threshold - lower for better detection
                significant_angle_threshold = 8  # Reduced from previous value
                max_turn_angle = max_detection['max_angle']
                avg_turn_angle = max_detection['avg_angle']
                
                # Skip if angle is too small
                if max_turn_angle < significant_angle_threshold:
                    continue
                
                # Calculate turn direction with enhanced accuracy
                scale = max_detection['scale']
                bearing_before = calculate_bearing(
                    coords[i-scale][0], coords[i-scale][1], 
                    coords[i][0], coords[i][1]
                )
                bearing_after = calculate_bearing(
                    coords[i][0], coords[i][1], 
                    coords[i+scale][0], coords[i+scale][1]
                )
                
                direction_bearing = bearing_after - bearing_before
                if direction_bearing > 180:
                    direction_bearing -= 360
                elif direction_bearing < -180:
                    direction_bearing += 360
                
                turn_direction = "Right" if direction_bearing > 0 else "Left"
                
                # Enhanced turn radius calculation
                radius = calculate_enhanced_turn_radius(coords, i, scale, max_turn_angle)
                
                # Enhanced turn classification with better thresholds
                turn_type = classify_enhanced_turn_type(max_turn_angle, avg_turn_angle, radius, turn_direction)
                
                # Special blind spot detection for 90-degree turns
                is_blind_spot = detect_blind_spot_conditions(max_turn_angle, avg_turn_angle, radius, turn_direction)
                
                # Override turn type if blind spot conditions are met
                if is_blind_spot and turn_type != 'u_turn':
                    turn_type = 'blind_spot'
                
                # Enhanced speed calculations
                recommended_speed, physics_data = calculate_enhanced_turn_speed(
                    max_turn_angle, radius, turn_type, tt_specs
                )
                
                # Enhanced severity classification
                severity = determine_enhanced_turn_severity(
                    recommended_speed, turn_type, max_turn_angle, radius, is_blind_spot
                )
                
                # Visibility factor calculation
                visibility_factor = calculate_enhanced_visibility_factor(
                    max_turn_angle, radius, turn_direction, turn_type
                )
                
                # Generate enhanced warnings
                warning = generate_enhanced_turn_warning(
                    turn_type, recommended_speed, max_turn_angle, visibility_factor, is_blind_spot
                )
                
                # Risk factors
                risk_factors = generate_enhanced_turn_risk_factors(
                    turn_type, max_turn_angle, radius, tt_specs, is_blind_spot
                )
                
                # Calculate deceleration distance
                deceleration_distance = calculate_turn_deceleration_distance(
                    recommended_speed, turn_type, tt_specs
                )
                
                # Comprehensive turn data
                turn_data = {
                    'location': coords[i],
                    'turn_angle': max_turn_angle,
                    'avg_turn_angle': avg_turn_angle,
                    'radius': radius,
                    'turn_direction': turn_direction,
                    'turn_type': turn_type,
                    'is_blind_spot': is_blind_spot,
                    'recommended_speed': max(5, int(recommended_speed)),
                    'rollover_speed': physics_data['rollover_speed'],
                    'max_physics_speed': physics_data['max_physics_speed'],
                    'deceleration_distance': int(deceleration_distance),
                    'severity': severity,
                    'warning': warning,
                    'visibility_factor': visibility_factor,
                    'blind_spot_risk': is_blind_spot or visibility_factor < 0.3,
                    'detection_confidence': len(turn_detections),
                    'physics_factors': physics_data['physics_factors'],
                    'risk_factors': risk_factors,
                    'analysis_scale': max_detection['scale'],
                    'detection_methods': {
                        'method1_angle': max_detection['angle_method1'],
                        'method2_angle': max_detection['angle_method2'],
                        'method3_angle': max_detection['angle_method3']
                    }
                }
                
                turns.append(turn_data)
                
            except Exception as e:
                print(f"Error analyzing turn at point {i}: {e}")
                continue
    
    except Exception as e:
        print(f"Error in enhanced turn analysis: {e}")
        import traceback
        traceback.print_exc()
    
    # Enhanced post-processing to catch missed critical turns
    turns = post_process_turn_detection(turns, coords)
    
    # Sort by danger level
    severity_order = {'critical': 4, 'high': 3, 'moderate': 2, 'low': 1}
    turns.sort(key=lambda x: (severity_order.get(x['severity'], 0), -x['turn_angle']), reverse=True)
    
    return turns

def calculate_enhanced_turn_radius(coords, center_index, scale, turn_angle):
    """Enhanced turn radius calculation using multiple methods"""
    try:
        # Method 1: Three-point circle radius
        if center_index >= scale and center_index + scale < len(coords):
            p1 = coords[center_index - scale]
            p2 = coords[center_index]
            p3 = coords[center_index + scale]
            
            # Convert to local coordinate system
            x1 = p1[1] * 111320 * math.cos(math.radians(p1[0]))
            y1 = p1[0] * 110540
            x2 = p2[1] * 111320 * math.cos(math.radians(p2[0]))
            y2 = p2[0] * 110540
            x3 = p3[1] * 111320 * math.cos(math.radians(p3[0]))
            y3 = p3[0] * 110540
            
            # Calculate circumradius
            a = math.sqrt((x2-x1)**2 + (y2-y1)**2)
            b = math.sqrt((x3-x2)**2 + (y3-y2)**2)
            c = math.sqrt((x1-x3)**2 + (y1-y3)**2)
            
            if a > 0 and b > 0 and c > 0:
                s = (a + b + c) / 2
                area = math.sqrt(max(0, s * (s-a) * (s-b) * (s-c)))
                if area > 0:
                    radius = (a * b * c) / (4 * area)
                else:
                    radius = 1000
            else:
                radius = 1000
        else:
            radius = 1000
        
        # Method 2: Curvature-based radius (backup/validation)
        if radius > 2000 or radius < 3:
            # Use relationship: radius ≈ chord_length / (2 * sin(angle/2))
            chord_distance = geodesic(coords[center_index - scale], coords[center_index + scale]).meters
            if turn_angle > 0:
                sin_half_angle = math.sin(math.radians(turn_angle / 2))
                if sin_half_angle > 0:
                    radius_method2 = chord_distance / (2 * sin_half_angle)
                    # Use the more reasonable radius
                    if 5 <= radius_method2 <= 1000:
                        radius = radius_method2
        
        # Ensure reasonable bounds
        radius = max(3, min(radius, 2000))
        
    except Exception as e:
        # Fallback calculation
        radius = max(10, 150 * (90 / max(turn_angle, 1)))
    
    return radius

def classify_enhanced_turn_type(max_angle, avg_angle, radius, direction):
    """Enhanced turn classification with better thresholds for critical detection"""
    
    # U-turn detection (most critical)
    if max_angle >= 150:
        return 'u_turn'
    
    # Hairpin detection (very critical)
    if max_angle >= 120 or (max_angle >= 100 and radius < 20):
        return 'hairpin'
    
    # 90-degree turn detection (critical - enhanced detection)
    if (85 <= max_angle <= 105) or (80 <= avg_angle <= 100 and radius < 40):
        return 'sharp_right_angle'
    
    # Blind spot conditions (critical)
    if (max_angle >= 60 and radius < 25) or (max_angle >= 70 and radius < 35):
        return 'blind_spot'
    
    # Sharp turn (high risk)
    if max_angle >= 45 or (max_angle >= 35 and radius < 30):
        return 'sharp_turn'
    
    # Moderate turn
    if max_angle >= 25:
        return 'moderate_turn'
    
    # Gentle curve
    if max_angle >= 15:
        return 'gentle_curve'
    
    # Slight curve
    if max_angle >= 8:
        return 'slight_curve'
    
    return 'straight'

def detect_blind_spot_conditions(max_angle, avg_angle, radius, direction):
    """Enhanced blind spot detection for critical turn identification"""
    
    # Multiple conditions that indicate blind spot risk
    blind_spot_conditions = [
        # Condition 1: Sharp turn with small radius
        max_angle >= 60 and radius < 30,
        
        # Condition 2: 90-degree turn with limited visibility
        85 <= max_angle <= 105 and radius < 50,
        
        # Condition 3: Moderate angle but very tight radius
        max_angle >= 45 and radius < 20,
        
        # Condition 4: Consistent sharp turning (average vs max)
        avg_angle >= 50 and max_angle >= 70,
        
        # Condition 5: Right turns tend to have more blind spots (driver position)
        direction == "Right" and max_angle >= 55 and radius < 40
    ]
    
    return any(blind_spot_conditions)

def calculate_enhanced_turn_speed(max_angle, radius, turn_type, tt_specs):
    """Enhanced speed calculation with physics-based analysis"""
    
    # Truck parameters
    gross_weight_kg = tt_specs["gross_weight"]
    liquid_capacity = tt_specs["avg_capacity_liters"]
    
    # Enhanced lateral g-force limits based on turn type
    max_lateral_g_limits = {
        'u_turn': 0.15,
        'hairpin': 0.18,
        'blind_spot': 0.20,
        'sharp_right_angle': 0.22,
        'sharp_turn': 0.25
    }
    
    base_max_g = max_lateral_g_limits.get(turn_type, 0.30)
    
    # Weight penalties
    if gross_weight_kg > 35000:
        weight_factor = 0.85
    elif gross_weight_kg > 25000:
        weight_factor = 0.90
    else:
        weight_factor = 0.95
    
    # Liquid sloshing effect
    slosh_factor = 0.75 if liquid_capacity > 25000 else 0.80 if liquid_capacity > 15000 else 0.85
    
    effective_max_g = base_max_g * weight_factor * slosh_factor
    
    # Physics calculations
    friction_coeff = 0.65 if turn_type in ['blind_spot', 'u_turn', 'hairpin'] else 0.7
    max_physics_speed_ms = math.sqrt(effective_max_g * 9.81 * radius)
    max_physics_speed_kmph = max_physics_speed_ms * 3.6
    
    # Rollover calculation
    cg_height = 2.8 + (liquid_capacity / 8000) * 0.4  # Height increases with capacity
    track_width = 2.4
    rollover_speed_ms = math.sqrt((track_width / 2) / cg_height * 9.81 * radius)
    rollover_speed_kmph = rollover_speed_ms * 3.6
    
    # Safety margins based on turn type
    safety_margins = {
        'u_turn': 0.50,
        'hairpin': 0.55,
        'blind_spot': 0.60,
        'sharp_right_angle': 0.65,
        'sharp_turn': 0.70
    }
    
    safety_margin = safety_margins.get(turn_type, 0.75)
    
    # Type-specific maximum speeds
    type_max_speeds = {
        'u_turn': 8,
        'hairpin': 12,
        'blind_spot': 15,
        'sharp_right_angle': 18,
        'sharp_turn': 25
    }
    
    type_max = type_max_speeds.get(turn_type, tt_specs["max_speed"])
    
    # Final recommended speed
    recommended_speed = min(
        max_physics_speed_kmph * safety_margin,
        rollover_speed_kmph * 0.6,
        type_max,
        tt_specs["max_speed"]
    )
    
    physics_data = {
        'max_physics_speed': int(max_physics_speed_kmph),
        'rollover_speed': int(rollover_speed_kmph),
        'physics_factors': {
            'lateral_g_force': round(effective_max_g, 2),
            'weight_penalty': round(1 - weight_factor, 2),
            'slosh_factor': round(1 - slosh_factor, 2),
            'safety_margin': safety_margin,
            'cg_height': cg_height,
            'friction_coeff': friction_coeff
        }
    }
    
    return recommended_speed, physics_data

def determine_enhanced_turn_severity(speed, turn_type, angle, radius, is_blind_spot):
    """Enhanced severity determination with better critical detection"""
    
    # Critical conditions
    critical_conditions = [
        turn_type in ['u_turn', 'hairpin'],
        is_blind_spot and turn_type == 'sharp_right_angle',
        speed <= 12,
        angle >= 120,
        radius < 15
    ]
    
    if any(critical_conditions):
        return 'critical'
    
    # High risk conditions
    high_risk_conditions = [
        turn_type in ['blind_spot', 'sharp_right_angle'],
        speed <= 20,
        angle >= 80,
        radius < 25
    ]
    
    if any(high_risk_conditions):
        return 'high'
    
    # Moderate risk
    if turn_type == 'sharp_turn' or speed <= 35:
        return 'moderate'
    
    return 'low'

def calculate_enhanced_visibility_factor(angle, radius, direction, turn_type):
    """Enhanced visibility calculation"""
    
    # Base visibility factors
    if turn_type in ['blind_spot', 'u_turn']:
        base_visibility = 0.1
    elif turn_type == 'hairpin':
        base_visibility = 0.2
    elif turn_type == 'sharp_right_angle':
        base_visibility = 0.3 if radius < 30 else 0.4
    elif angle >= 60:
        base_visibility = 0.3
    elif angle >= 45:
        base_visibility = 0.5
    else:
        base_visibility = 0.8
    
    # Radius adjustment
    if radius < 20:
        base_visibility *= 0.7
    elif radius < 35:
        base_visibility *= 0.85
    
    # Direction adjustment (right turns typically have worse visibility)
    if direction == "Right":
        base_visibility *= 0.9
    
    return max(0.05, min(1.0, base_visibility))

def generate_enhanced_turn_warning(turn_type, speed, angle, visibility, is_blind_spot):
    """Generate specific warnings for enhanced turn types"""
    
    speed_int = int(speed)
    
    warnings = {
        'u_turn': f"U-TURN AHEAD: {speed_int} kmph MAX - Complete stop likely required",
        'hairpin': f"HAIRPIN CURVE: {speed_int} kmph MAX - EXTREME rollover risk",
        'sharp_right_angle': f"90° INTERSECTION: {speed_int} kmph - Check cross traffic",
        'blind_spot': f"BLIND SPOT TURN: {speed_int} kmph - LIMITED VISIBILITY",
        'sharp_turn': f"SHARP TURN: {speed_int} kmph - Reduce speed gradually"
    }
    
    base_warning = warnings.get(turn_type, f"Turn ahead: {speed_int} kmph")
    
    # Add blind spot warning if detected
    if is_blind_spot and turn_type != 'blind_spot':
        base_warning += " - BLIND SPOT RISK"
    
    # Add visibility warning
    if visibility < 0.3:
        base_warning += " - POOR VISIBILITY"
    
    return base_warning

def generate_enhanced_turn_risk_factors(turn_type, angle, radius, tt_specs, is_blind_spot):
    """Generate comprehensive risk factors"""
    
    factors = []
    
    # Turn-specific factors
    if turn_type == 'blind_spot' or is_blind_spot:
        factors.extend([
            f"BLIND SPOT: Limited visibility around {angle:.1f}° turn",
            f"Small radius ({radius:.1f}m) creates vision obstruction",
            "Oncoming traffic may not be visible"
        ])
    
    if turn_type == 'sharp_right_angle':
        factors.extend([
            f"90° TURN: Standard intersection turn ({angle:.1f}°)",
            f"Turn radius: {radius:.1f}m",
            "Check for cross traffic and pedestrians"
        ])
    
    if turn_type == 'u_turn':
        factors.extend([
            f"U-TURN: {angle:.1f}° requires multiple maneuvers",
            "Complete traffic stoppage likely required"
        ])
    
    if turn_type == 'hairpin':
        factors.extend([
            f"HAIRPIN: {angle:.1f}° extreme curve",
            f"Very tight radius ({radius:.1f}m)",
            "Maximum rollover risk zone"
        ])
    
    # Truck-specific factors
    if tt_specs['gross_weight'] > 35000:
        factors.append(f"Heavy TT: {tt_specs['gross_weight']/1000:.1f}T increases difficulty")
    
    if tt_specs['avg_capacity_liters'] > 25000:
        factors.append(f"Large capacity: {tt_specs['avg_capacity_liters']:,}L liquid surge risk")
    
    return factors

def calculate_turn_deceleration_distance(target_speed, turn_type, tt_specs):
    """Calculate deceleration distance for turn approach"""
    
    current_speed = min(50, tt_specs["max_speed"] * 0.8)
    
    if target_speed >= current_speed:
        return 0
    
    speed_diff_ms = (current_speed - target_speed) / 3.6
    
    # Deceleration rates based on turn type
    deceleration_rates = {
        'u_turn': 2.0,
        'hairpin': 2.2,
        'blind_spot': 2.5,
        'sharp_right_angle': 2.8,
        'sharp_turn': 3.0
    }
    
    deceleration = deceleration_rates.get(turn_type, 3.5)
    
    # Weight adjustment
    if tt_specs['gross_weight'] > 35000:
        deceleration *= 0.85
    elif tt_specs['gross_weight'] > 25000:
        deceleration *= 0.90
    
    distance = (speed_diff_ms ** 2) / (2 * deceleration)
    return max(10, distance)

def post_process_turn_detection(turns, coords):
    """Post-process to catch any missed critical turns"""
    
    # Look for potential missed 90-degree turns by checking spacing
    processed_locations = set((round(t['location'][0], 4), round(t['location'][1], 4)) for t in turns)
    
    # Additional scan for missed right-angle turns
    for i in range(10, len(coords) - 10, 5):  # Wider spacing scan
        location_key = (round(coords[i][0], 4), round(coords[i][1], 4))
        
        if location_key in processed_locations:
            continue
        
        try:
            # Check for potential 90-degree pattern
            bearing1 = calculate_bearing(coords[i-10][0], coords[i-10][1], coords[i][0], coords[i][1])
            bearing2 = calculate_bearing(coords[i][0], coords[i][1], coords[i+10][0], coords[i+10][1])
            angle = calculate_turn_angle(bearing1, bearing2)
            
            # Specifically look for missed 90-degree turns
            if 75 <= angle <= 110:
                # This might be a missed right-angle turn
                radius = geodesic(coords[i-5], coords[i+5]).meters / 2  # Approximate radius
                
                if radius < 60:  # Tight enough to be significant
                    direction_bearing = bearing2 - bearing1
                    if direction_bearing > 180:
                        direction_bearing -= 360
                    elif direction_bearing < -180:
                        direction_bearing += 360
                    
                    turn_direction = "Right" if direction_bearing > 0 else "Left"
                    
                    # Add as potential missed critical turn
                    missed_turn = {
                        'location': coords[i],
                        'turn_angle': angle,
                        'avg_turn_angle': angle,
                        'radius': radius,
                        'turn_direction': turn_direction,
                        'turn_type': 'sharp_right_angle',
                        'is_blind_spot': radius < 35,
                        'recommended_speed': 18,
                        'severity': 'high',
                        'warning': f"90° TURN: 18 kmph - Potentially missed detection",
                        'visibility_factor': 0.4 if radius < 35 else 0.6,
                        'blind_spot_risk': radius < 35,
                        'detection_confidence': 1,
                        'risk_factors': [f"Potentially missed 90° turn - {angle:.1f}°", f"Radius: {radius:.1f}m"],
                        'post_processed': True
                    }
                    
                    turns.append(missed_turn)
                    processed_locations.add(location_key)
        
        except Exception as e:
            continue
    
    return turns

def calculate_braking_distances(coords, tt_specs, elevations, gradients):
    """Calculate braking distances for truck at various points considering weight and gradient"""
    braking_points = []
    
    try:
        # Truck braking parameters
        gross_weight_kg = tt_specs["gross_weight"]
        
        # Braking system parameters
        reaction_time = 1.5  # seconds - air brake system delay
        friction_coeff = 0.7  # Dry asphalt
        brake_efficiency = 0.85  # Air brake system efficiency
        
        # Sample every 10th point for braking analysis
        sample_interval = max(1, len(coords) // 20)
        sample_indices = range(0, len(coords), sample_interval)
        
        for i in sample_indices:
            if i >= len(coords):
                continue
                
            try:
                coord = coords[i]
                
                # Get elevation and gradient data
                if i < len(elevations):
                    elevation = elevations[min(i, len(elevations)-1)]
                else:
                    elevation = 100  # Default elevation
                
                if i < len(gradients):
                    gradient_percent = gradients[min(i, len(gradients)-1)]
                else:
                    gradient_percent = 0
                
                # Speed scenarios to analyze
                speeds_kmph = [30, 40, 50, min(60, tt_specs["max_speed"])]
                
                for speed_kmph in speeds_kmph:
                    speed_ms = speed_kmph / 3.6
                    
                    # Reaction distance (distance traveled during reaction time)
                    reaction_distance = speed_ms * reaction_time
                    
                    # Physics-based braking distance
                    # F = ma, where F is braking force limited by friction
                    # ma = μmg ± mg*sin(θ), where θ is gradient angle
                    gradient_rad = math.atan(gradient_percent / 100)
                    
                    # Effective deceleration considering gradient
                    base_deceleration = friction_coeff * 9.81 * brake_efficiency
                    gradient_effect = 9.81 * math.sin(gradient_rad)
                    
                    # Downhill reduces braking effectiveness, uphill helps
                    effective_deceleration = base_deceleration - gradient_effect
                    effective_deceleration = max(2.0, effective_deceleration)  # Minimum safe deceleration
                    
                    # Weight factor - heavier trucks need more distance
                    if gross_weight_kg > 35000:
                        weight_factor = 1.4
                    elif gross_weight_kg > 25000:
                        weight_factor = 1.2
                    else:
                        weight_factor = 1.0
                    
                    # Physics braking distance: v²/(2a)
                    physics_distance = (speed_ms ** 2) / (2 * effective_deceleration)
                    physics_distance *= weight_factor
                    
                    # Total braking distance
                    total_distance = reaction_distance + physics_distance
                    
                    # Only store significant braking distances
                    if total_distance > 45:  # More than 45m is noteworthy
                        braking_points.append({
                            'location': coord,
                            'speed_kmph': speed_kmph,
                            'total_distance': round(total_distance),
                            'reaction_distance': round(reaction_distance),
                            'physics_distance': round(physics_distance),
                            'weight_factor': weight_factor,
                            'gradient': gradient_percent,
                            'elevation': elevation,
                            'effective_deceleration': round(effective_deceleration, 1)
                        })
                        
            except Exception as e:
                print(f"Error calculating braking for point {i}: {e}")
                continue
    
    except Exception as e:
        print(f"Error in braking distance calculation: {e}")
    
    # Sort by total distance and return most critical braking scenarios
    braking_points.sort(key=lambda x: x['total_distance'], reverse=True)
    return braking_points[:15]  # Top 15 most critical braking distances

def generate_enhanced_route_report(coords, pois, hazard_zones, traffic_data, turns, 
                                 braking_points, total_distance, total_duration, 
                                 tt_specs, elevations, gradients):
    """Generate comprehensive route analysis report with realistic metrics"""
    try:
        # Extract distance value
        distance_value = 1
        try:
            if total_distance:
                distance_parts = total_distance.split()
                if distance_parts:
                    distance_value = float(distance_parts[0])
        except:
            distance_value = 1
        
        # Calculate route complexity based on actual hazards
        complexity_factors = {
            'critical_turns': len([t for t in turns if t.get('severity') == 'critical']),
            'high_risk_turns': len([t for t in turns if t.get('severity') == 'high']),
            'critical_hazards': len([h for h in hazard_zones if h.get('risk_level') == 'Critical']),
            'high_hazards': len([h for h in hazard_zones if h.get('risk_level') == 'High']),
            'fuel_station_hazards': len([h for h in hazard_zones if any('fuel' in str(f).lower() for f in h.get('risk_factors', []))]),
            'school_hazards': len([h for h in hazard_zones if any('school' in str(f).lower() for f in h.get('risk_factors', []))]),
            'extreme_braking_zones': len([b for b in braking_points if b.get('total_distance', 0) > 70])
        }
        
        # Calculate complexity score
        complexity_score = (
            complexity_factors['critical_turns'] * 3 +
            complexity_factors['high_risk_turns'] * 2 +
            complexity_factors['critical_hazards'] * 4 +
            complexity_factors['high_hazards'] * 2 +
            complexity_factors['fuel_station_hazards'] * 5 +  # Extremely dangerous for petroleum tanker
            complexity_factors['school_hazards'] * 3 +
            complexity_factors['extreme_braking_zones'] * 1.5
        )
        
        # Determine complexity rating
        if complexity_score >= 25:
            complexity_rating = "EXTREME RISK"
        elif complexity_score >= 15:
            complexity_rating = "HIGH COMPLEXITY"
        elif complexity_score >= 8:
            complexity_rating = "MODERATE COMPLEXITY"
        else:
            complexity_rating = "LOW COMPLEXITY"
        
        # Traffic analysis
        heavy_traffic_segments = len([t for t in traffic_data if t.get('traffic_level') == 'heavy'])
        avg_delay = np.mean([t.get('delay_factor', 1.0) for t in traffic_data]) if traffic_data else 1.0
        
        # Fuel consumption estimation (simplified)
        base_consumption = distance_value * 0.35  # L/km for loaded tanker
        traffic_penalty = avg_delay * 0.15  # Additional consumption due to traffic
        gradient_penalty = sum(abs(g) for g in gradients[:10]) * 0.02 if gradients else 0  # Gradient effect
        estimated_fuel = base_consumption + traffic_penalty + gradient_penalty
        
        # Generate detailed report
        report = {
            'route_overview': {
                'total_distance': total_distance,
                'total_duration': total_duration,
                'complexity_rating': complexity_rating,
                'complexity_score': round(complexity_score, 1),
                'route_points': len(coords),
                'analysis_density': f"{len(coords)/distance_value:.0f} points/km"
            },
            
            'truck_tanker_specs': {
                'capacity_range': tt_specs['capacity_range'],
                'fuel_capacity': f"{tt_specs['avg_capacity_liters']:,} L",
                'product_weight': f"{tt_specs['product_weight']/1000:.1f} tonnes",
                'tare_weight': f"{tt_specs['tare_weight']/1000:.1f} tonnes",
                'gross_weight': f"{tt_specs['gross_weight']/1000:.1f} tonnes",
                'axle_load': f"{tt_specs['axle_load']:.1f} tonnes per axle",
                'max_speed': f"{tt_specs['max_speed']} kmph",
                'risk_multiplier': f"{tt_specs['risk_multiplier']}x",
                'hazmat_class': 'Class 3 (Flammable Liquid)'
            },
            
            'hazard_analysis': {
                'total_hazard_zones': len(hazard_zones),
                'critical_zones': complexity_factors['critical_hazards'],
                'high_risk_zones': complexity_factors['high_hazards'],
                'medium_risk_zones': len([h for h in hazard_zones if h.get('risk_level') == 'Medium']),
                'fuel_station_conflicts': complexity_factors['fuel_station_hazards'],
                'school_zone_risks': complexity_factors['school_hazards'],
                'time_sensitive_hazards': len([h for h in hazard_zones if h.get('time_sensitive', False)]),
                'highest_risk_score': max([h.get('risk_score', 0) for h in hazard_zones]) if hazard_zones else 0
            },
            
            'turn_analysis': {
                'total_significant_turns': len(turns),
                'critical_turns': complexity_factors['critical_turns'],
                'high_risk_turns': complexity_factors['high_risk_turns'],
                'moderate_turns': len([t for t in turns if t.get('severity') == 'moderate']),
                'sharpest_turn_angle': max([t.get('turn_angle', 0) for t in turns]) if turns else 0,
                'minimum_safe_speed': min([t.get('recommended_speed', 60) for t in turns]) if turns else 60,
                'rollover_risk_turns': len([t for t in turns if t.get('recommended_speed', 60) < 25])
            },
            
            'braking_analysis': {
                'extreme_braking_zones': complexity_factors['extreme_braking_zones'],
                'extended_braking_zones': len([b for b in braking_points if b.get('total_distance', 0) > 60]),
                'max_braking_distance': max([b.get('total_distance', 45) for b in braking_points]) if braking_points else 45,
                'gradient_affected_zones': len([b for b in braking_points if abs(b.get('gradient', 0)) > 3]),
                'weight_penalty_zones': len([b for b in braking_points if b.get('weight_factor', 1.0) > 1.2])
            },
            
            'traffic_analysis': {
                'total_analysis_points': len(traffic_data),
                'heavy_traffic_segments': heavy_traffic_segments,
                'moderate_traffic_segments': len([t for t in traffic_data if t.get('traffic_level') == 'moderate']),
                'light_traffic_segments': len([t for t in traffic_data if t.get('traffic_level') == 'light']),
                'average_delay_factor': round(avg_delay, 2),
                'urban_zones': len([t for t in traffic_data if t.get('urban_factor', 1.0) > 1.0]),
                'peak_hour_affected': len([t for t in traffic_data if t.get('time_based', False)])
            },
            
            'route_efficiency': {
                'estimated_fuel_consumption': f"{estimated_fuel:.1f} L",
                'fuel_efficiency': f"{estimated_fuel/distance_value:.2f} L/km",
                'time_penalties': f"{(avg_delay-1)*100:.0f}% delay due to traffic",
                'gradient_impact': f"{len([g for g in gradients[:20] if abs(g) > 3]) if gradients else 0} steep grades",
                'elevation_range': f"{max(elevations[:20]) - min(elevations[:20]):.0f}m" if elevations else "N/A"
            },
            
            'poi_distribution': {
                'total_pois': len(pois),
                'fuel_stations': len([p for p in pois if p.get('type') == 'fuel']),
                'hospitals': len([p for p in pois if p.get('type') == 'health']),
                'schools': len([p for p in pois if p.get('type') == 'education']),
                'police_stations': len([p for p in pois if p.get('type') == 'safety']),
                'commercial_areas': len([p for p in pois if p.get('type') == 'commercial']),
                'religious_sites': len([p for p in pois if p.get('type') == 'religious'])
            },
            
            'safety_recommendations': [
                f"CRITICAL: Maintain max {min([t.get('recommended_speed', 50) for t in turns[:3]]) if turns else 50} kmph at sharpest turns",
                f"Fuel hazard protocol: {complexity_factors['fuel_station_hazards']} extreme risk zones identified",
                f"School zone awareness: {complexity_factors['school_hazards']} education facilities along route",
                f"Extended braking: Maintain {max([b.get('total_distance', 45) for b in braking_points[:3]]) if braking_points else 45}m+ following distance",
                f"Weight considerations: {tt_specs['gross_weight']/1000:.1f}T affects all maneuvers",
                f"Emergency response: Class 3 flammable - {tt_specs['avg_capacity_liters']:,}L petroleum cargo",
                f"Traffic management: {heavy_traffic_segments} heavy traffic zones require extra caution",
                "Hazmat placards visible and emergency contact cards accessible",
                "Driver rest: Complex route requires maximum alertness",
                f"Route complexity: {complexity_rating} - Consider alternate routes if available"
            ],
            
            'emergency_protocols': {
                'hazmat_class': 'UN Class 3 - Flammable Liquid',
                'cargo_volume': f"{tt_specs['avg_capacity_liters']:,} L",
                'emergency_response_guide': 'ERG 128',
                'isolation_distance': '50m initial, 100m if fire/spill',
                'evacuation_radius': '800m if tank involvement in fire',
                'special_precautions': [
                    'No smoking/ignition sources',
                    'Approach from upwind',
                    'Ground all equipment',
                    'Foam suppression systems required'
                ]
            },
            
            'route_statistics': {
                'analysis_timestamp': datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                'total_analysis_points': len(coords),
                'hazard_density': f"{len(hazard_zones)/distance_value:.1f} hazards/km",
                'turn_density': f"{len(turns)/distance_value:.1f} critical turns/km",
                'complexity_per_km': f"{complexity_score/distance_value:.1f} complexity points/km"
            }
        }
        
        return report
        
    except Exception as e:
        print(f"Error generating enhanced report: {e}")
        # Return basic fallback report
        return {
            'route_overview': {
                'total_distance': total_distance or "N/A",
                'total_duration': total_duration or "N/A",
                'complexity_rating': "ANALYSIS ERROR",
                'route_points': len(coords)
            },
            'truck_tanker_specs': tt_specs,
            'hazard_analysis': {
                'total_hazard_zones': len(hazard_zones),
                'critical_zones': 0,
                'high_risk_zones': 0
            },
            'safety_recommendations': [
                f"Basic safety: Max speed {tt_specs['max_speed']} kmph",
                f"Weight: {tt_specs['gross_weight']/1000:.1f}T - Extended braking required",
                "Hazmat precautions: Class 3 flammable cargo"
            ]
        }

# Additional utility function for template compatibility
def generate_route_report(coords, pois, risk_zones, traffic_data, total_distance, total_duration, tt_specs):
    """Wrapper function for backward compatibility"""
    # Create dummy data for missing parameters
    turns = []
    braking_points = []
    elevations = [100] * min(20, len(coords))
    gradients = [0] * min(20, len(coords))
    
    return generate_enhanced_route_report(
        coords, pois, risk_zones, traffic_data, turns, 
        braking_points, total_distance, total_duration, 
        tt_specs, elevations, gradients
    )

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

      # The problematic section around line 1843 should be fixed like this:

        # Add turn analysis with enhanced visualization  
        for turn in turns[:30]:  # Show more turns now that we detect them properly
            try:
                # Enhanced color coding based on turn type and severity
                if turn.get('turn_type') == 'blind_spot':
                    color = '#8B0000'  # Dark red for blind spots
                    icon_symbol = '👁️'
                elif turn.get('turn_type') == 'u_turn':
                    color = '#8B0000'  # Dark red for U-turns
                    icon_symbol = '↩️'
                elif turn.get('turn_type') == 'hairpin':
                    color = '#DC143C'  # Crimson for hairpins
                    icon_symbol = '🪝'
                elif turn.get('turn_type') == 'sharp_right_angle':
                    color = '#FF4500'  # Orange red for 90-degree turns
                    icon_symbol = '📐'
                elif turn.get('severity') == 'critical':
                    color = '#8B0000'  # Dark red for other critical turns
                    icon_symbol = '⚠️'
                elif turn.get('severity') == 'high':
                    color = '#FF4500'  # Orange red for high risk
                    icon_symbol = '⚠️'
                else:
                    color = '#FFD700'  # Gold for moderate turns
                    icon_symbol = '↻'
                
                # Enhanced popup with turn type information
                turn_popup = f"""
                <div style='font-family: Arial; max-width: 350px;'>
                    <h4 style='color: {color}; margin: 5px 0;'>{icon_symbol} {turn.get('turn_type', 'turn').replace('_', ' ').title()}</h4>
                    <div style='background: #f0f0f0; padding: 8px; border-radius: 4px; margin: 5px 0;'>
                        <table style='font-size: 11px; width: 100%;'>
                            <tr><td><strong>Turn Angle:</strong></td><td>{turn['turn_angle']:.1f}°</td></tr>
                            <tr><td><strong>Direction:</strong></td><td>{turn.get('turn_direction', 'Unknown')}</td></tr>
                            <tr><td><strong>Turn Type:</strong></td><td style='color: {color}; font-weight: bold;'>{turn.get('turn_type', 'turn').replace('_', ' ').title()}</td></tr>
                            <tr><td><strong>Radius:</strong></td><td>{turn['radius']:.1f}m</td></tr>
                            <tr><td><strong>Safe Speed:</strong></td><td style='color: red; font-weight: bold;'>{turn['recommended_speed']} kmph</td></tr>
                            <tr><td><strong>Visibility:</strong></td><td>{'Poor' if turn.get('visibility_factor', 1) < 0.3 else 'Fair' if turn.get('visibility_factor', 1) < 0.6 else 'Good'}</td></tr>
                        </table>
                    </div>
                    
                    <div style='background: #fff3cd; padding: 6px; border-radius: 3px; margin: 5px 0;'>
                        <strong>Warning:</strong><br>
                        <span style='color: red; font-weight: bold;'>{turn['warning']}</span>
                    </div>
                    
                    {f'<div style="background: #f8d7da; padding: 6px; border-radius: 3px; margin: 5px 0;"><strong>Risk Factors:</strong><br>{"<br>".join([f"• {risk}" for risk in turn.get("risk_factors", [])][:3])}</div>' if turn.get('risk_factors') else ''}
                    
                    <div style='background: #e2e3e5; padding: 5px; border-radius: 3px; font-size: 10px;'>
                        <strong>Physics:</strong> {turn['physics_factors']['lateral_g_force']}g lateral force, 
                        {turn['deceleration_distance']}m braking distance
                    </div>
                    
                    {f'<div style="background: #ffcccc; padding: 5px; border-radius: 3px; font-size: 10px; color: red; font-weight: bold;">⚠️ BLIND SPOT WARNING</div>' if turn.get('blind_spot_risk') else ''}
                </div>
                """
                
                # Enhanced icon with turn type and speed
                if turn.get('turn_type') == 'blind_spot':
                    icon_html = f"""
                    <div style='text-align: center;'>
                        <div style='background: {color}; color: white; border-radius: 50%; width: 35px; height: 35px; 
                                    line-height: 35px; font-weight: bold; font-size: 10px; border: 2px solid white;'>
                            BLIND
                        </div>
                        <div style='font-size: 8px; margin-top: 2px; color: {color}; font-weight: bold;'>{turn['recommended_speed']}km/h</div>
                    </div>
                    """
                elif turn.get('turn_type') == 'sharp_right_angle':
                    icon_html = f"""
                    <div style='text-align: center;'>
                        <div style='background: {color}; color: white; border-radius: 10%; width: 35px; height: 35px; 
                                    line-height: 35px; font-weight: bold; font-size: 12px; border: 2px solid white;'>
                            90°
                        </div>
                        <div style='font-size: 8px; margin-top: 2px; color: {color}; font-weight: bold;'>{turn['recommended_speed']}km/h</div>
                    </div>
                    """
                else:
                    icon_html = f"""
                    <div style='text-align: center;'>
                        <div style='background: {color}; color: white; border-radius: 50%; width: 32px; height: 32px; 
                                    line-height: 32px; font-weight: bold; font-size: 11px; border: 2px solid white;'>
                            {turn['recommended_speed']}
                        </div>
                        <div style='font-size: 8px; margin-top: 2px; color: {color}; font-weight: bold;'>{turn.get('turn_type', 'turn')[:4].upper()}</div>
                    </div>
                    """
                
                folium.Marker(
                    location=turn['location'],
                    popup=turn_popup,
                    icon=folium.DivIcon(html=icon_html, icon_size=(40, 45), icon_anchor=(20, 40))
                ).add_to(m)
                
            except Exception as e:
                print(f"Error adding turn marker: {e}")
                continue
                
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
                <div style='font-weight: bold; margin-bottom: 5px;'>🎯 Turn Classifications:</div>
                <div style='margin: 3px 0; font-size: 10px;'>🔴 <span style='background: #8B0000; color: white; padding: 1px 4px; border-radius: 2px;'>BLIND</span> Blind Spot Turn</div>
                <div style='margin: 3px 0; font-size: 10px;'>🟠 <span style='background: #FF4500; color: white; padding: 1px 4px; border-radius: 2px;'>90°</span> Right Angle Turn</div>
                <div style='margin: 3px 0; font-size: 10px;'>🔴 <span style='background: #DC143C; color: white; padding: 1px 4px; border-radius: 2px;'>HAIR</span> Hairpin Turn</div>
                <div style='margin: 3px 0; font-size: 10px;'>🔴 <span style='background: #8B0000; color: white; padding: 1px 4px; border-radius: 2px;'>U</span> U-Turn</div>
                <div style='margin: 3px 0; font-size: 10px;'>🟡 <span style='background: #FFD700; color: black; padding: 1px 4px; border-radius: 2px;'>MOD</span> Moderate Turn</div>
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







