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
import google.generativeai as genai


app = Flask(__name__)
app.secret_key = 'your_secret_key_here'
app.config['SESSION_TYPE'] = 'filesystem'
Session(app)

# Replace OpenAI imports with:
try:
    import google.generativeai as genai
    GEMINI_API_KEY = os.environ.get("OPENAI_API_KEY")
    if GEMINI_API_KEY:
        genai.configure(api_key=GEMINI_API_KEY)
        ai_client = True
    else:
        ai_client = False
        print("GEMINI_API_KEY not found")
except Exception as e:
    print(f"Gemini initialization error: {e}")
    ai_client = False
    

API_KEY = os.environ.get("API_KEY")  # Secure access
gmaps = googlemaps.Client(key=API_KEY)

# Login credentials - modify these as needed
LOGIN_CREDENTIALS = {
    "Vadinar": "Vadinar@123"
}

# Truck Tanker (TT) Specifications with Indian standards
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
        "cg_height": 2.3,
        "track_width": 2.0,
        "stability_factor": 1.0
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
        "cg_height": 2.4,
        "track_width": 2.0,
        "stability_factor": 0.95
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
        "cg_height": 2.5,
        "track_width": 2.0,
        "stability_factor": 0.88
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
        "cg_height": 2.6,
        "track_width": 2.0,
        "stability_factor": 0.80
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
        "cg_height": 2.8,
        "track_width": 2.0,
        "stability_factor": 0.70
    }
}

# ADD AFTER TT_SPECIFICATIONS:
PRACTICAL_SPEED_MATRIX = { ... }
PRACTICAL_RISK_CATEGORIES = { ... }

# Default values (will be updated based on TT selection)
TRUCK_WEIGHT = 25.0  # Will be dynamically set
MAX_SPEED_LIMIT = 50  # Will be dynamically set
SAFE_TURN_ANGLE = 130  # degrees
DANGEROUS_TURN_ANGLE = 30  # degrees


def get_working_gemini_model():
    """Try different model names until one works"""
    model_attempts = [
        'gemini-1.5-flash-latest',
        'gemini-1.5-flash',
        'gemini-1.5-flash-001',
        'gemini-1.5-pro-latest',
        'gemini-1.5-pro',
        'gemini-pro',
        'models/gemini-1.5-flash-latest',
        'models/gemini-1.5-flash',
        'models/gemini-1.5-pro',
        'models/gemini-pro'
    ]
    
    for model_name in model_attempts:
        try:
            model = genai.GenerativeModel(model_name)
            # Quick test to see if it works
            test = model.generate_content("Hi")
            if test.text:
                print(f"✅ Successfully using model: {model_name}")
                return model
        except Exception as e:
            print(f"❌ {model_name} failed: {str(e)[:50]}")
            continue
    
    print("⚠️ All models failed, using fallback")
    return None



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


def analyze_route_with_ai(coords, sharp_turns, curves, tt_specs, pois):
    """Give AI complete access to all route analysis data"""
    if not ai_client:
        return generate_fallback_analysis(sharp_turns, curves, tt_specs, pois)
    
    try:
        model = get_working_gemini_model()  # ✅ NEW LINE
        if not model:
            return generate_comprehensive_fallback(sharp_turns, curves, tt_specs, pois, session.get('route_report', {}))
        
        # Prepare comprehensive data summary
        route_report = session.get('route_report', {})
        total_distance = route_report.get('total_distance', 'Unknown')
        total_duration = route_report.get('total_duration', 'Unknown')
        
        # Detailed turn analysis
        critical_turns = [t for t in sharp_turns if t.get('severity') == 'critical']
        high_turns = [t for t in sharp_turns if t.get('severity') == 'high']
        
        # POI breakdown
        hospitals = [p for p in pois if p['type'] == 'hospital']
        police = [p for p in pois if p['type'] == 'police']
        fuel_stations = [p for p in pois if p['type'] == 'fuel']
        
        # Turn details with specific angles
        turn_analysis = []
        for i, turn in enumerate(sharp_turns):
            turn_analysis.append(f"Turn {i+1}: {turn['turn_angle']:.1f}° {turn['direction']} ({turn['severity']} severity)")
        
        curve_analysis = []
        for i, curve in enumerate(curves):
            curve_analysis.append(f"Curve {i+1}: {curve['turn_angle']:.1f}° {curve['direction']}")
        
        prompt = f"""COMPREHENSIVE TRUCK TANKER ROUTE ANALYSIS
Analyze ALL provided data and give detailed safety recommendations.

=== VEHICLE SPECIFICATIONS ===
- Type: {tt_specs['capacity_range']} Petroleum Tanker
- Fuel Capacity: {tt_specs['avg_capacity_liters']:,} liters
- Tare Weight: {tt_specs['tare_weight']/1000:.1f}T (empty vehicle)
- Product Weight: {tt_specs['product_weight']/1000:.1f}T (petroleum cargo)
- Gross Weight: {tt_specs['gross_weight']/1000:.1f}T (fully loaded)
- Axle Load: {tt_specs['axle_load']:.1f}T per axle
- Maximum Legal Speed: {tt_specs['max_speed']} km/h
- Turn Sensitivity: {tt_specs['turn_sensitivity']}x (rollover factor)
- Risk Multiplier: {tt_specs['risk_multiplier']}x (hazard amplification)

=== COMPLETE ROUTE DATA ===
- Total Distance: {total_distance}
- Estimated Duration: {total_duration}
- Route Points Analyzed: {len(coords)} GPS coordinates
- Points per Kilometer: {len(coords)/(float(total_distance.split()[0]) if total_distance != 'Unknown' else 1):.1f}

=== DETAILED HAZARD ANALYSIS ===
Sharp Turns (90+ degrees): {len(sharp_turns)} total
{chr(10).join(turn_analysis[:10])}  

Critical Severity Turns: {len(critical_turns)}
High Severity Turns: {len(high_turns)}

Moderate Curves (45-90 degrees): {len(curves)} total
{chr(10).join(curve_analysis[:5])}

=== INFRASTRUCTURE ALONG ROUTE ===
Emergency Facilities:
- Hospitals: {len(hospitals)} ({', '.join([h['name'] for h in hospitals[:3]])})
- Police Stations: {len(police)} ({', '.join([p['name'] for p in police[:3]])})
- Fuel Stations: {len(fuel_stations)} ({', '.join([f['name'] for f in fuel_stations[:3]])})

=== ANALYSIS REQUIRED ===
Based on ALL the above data, provide:

1. OVERALL SAFETY ASSESSMENT (1-10 scale, 10=extremely dangerous)
2. SPECIFIC SPEED RECOMMENDATIONS:
   - Highway speed for {tt_specs['gross_weight']/1000:.1f}T tanker
   - Speed for each severity level of turns
   - Minimum speeds for safety
3. ROUTE-SPECIFIC WARNINGS for the {len(critical_turns)} critical turns
4. EMERGENCY PREPAREDNESS based on available facilities
5. LOAD-SPECIFIC ADVICE for {tt_specs['avg_capacity_liters']:,}L petroleum cargo
6. TIME MANAGEMENT for {total_duration} journey
7. CRITICAL CHECKPOINTS where extra caution is needed

Consider the liquid cargo dynamics, high center of gravity, and rollover risks specific to this vehicle configuration."""

        response = model.generate_content(prompt)
        return response.text
        
    except Exception as e:
        print(f"Gemini API error: {e}")
        return generate_comprehensive_fallback(sharp_turns, curves, tt_specs, pois, route_report)

def generate_comprehensive_fallback(sharp_turns, curves, tt_specs, pois, route_report):
    """Comprehensive fallback using all available data"""
    
    critical_turns = len([t for t in sharp_turns if t.get('severity') == 'critical'])
    high_turns = len([t for t in sharp_turns if t.get('severity') == 'high'])
    hospitals = len([p for p in pois if p['type'] == 'hospital'])
    
    # Risk calculation based on all factors
    base_risk = 3
    if critical_turns > 3: base_risk += 3
    if len(sharp_turns) > 8: base_risk += 2
    if tt_specs['gross_weight'] > 30000: base_risk += 1
    if hospitals < 2: base_risk += 1
    
    risk_score = min(10, base_risk)
    
    return f"""COMPREHENSIVE ROUTE SAFETY ANALYSIS
{tt_specs['capacity_range']} PETROLEUM TANKER

=== OVERALL ASSESSMENT ===
Safety Rating: {risk_score}/10 {'(EXTREME CAUTION)' if risk_score > 7 else '(HIGH ALERT)' if risk_score > 5 else '(MODERATE RISK)'}
Route Distance: {route_report.get('total_distance', 'Analyzing...')}
Estimated Duration: {route_report.get('total_duration', 'Calculating...')}

=== VEHICLE LOAD ANALYSIS ===
Current Configuration: {tt_specs['gross_weight']/1000:.1f}T Total Weight
- Empty Vehicle: {tt_specs['tare_weight']/1000:.1f}T
- Petroleum Cargo: {tt_specs['product_weight']/1000:.1f}T ({tt_specs['avg_capacity_liters']:,}L)
- Axle Loading: {tt_specs['axle_load']:.1f}T per axle
- Center of Gravity: ELEVATED due to liquid cargo

=== DETAILED SPEED MATRIX ===
Highway Driving: {min(tt_specs['max_speed'], 50)} km/h maximum
Moderate Curves: {max(15, int(30/tt_specs['turn_sensitivity']))} km/h
Sharp Turns: {max(8, int(12/tt_specs['turn_sensitivity']))} km/h  
Critical Turns: {max(5, int(8/tt_specs['turn_sensitivity']))} km/h
Emergency Zones: 10 km/h maximum

=== HAZARD BREAKDOWN ===
Critical Risk Points: {critical_turns} locations requiring extreme caution
High Risk Points: {high_turns} sharp turns needing significant speed reduction
Moderate Risk Points: {len(curves)} curves requiring careful navigation
Total Hazard Points: {len(sharp_turns) + len(curves)}

=== EMERGENCY INFRASTRUCTURE ===
Medical Facilities: {hospitals} hospitals along route
Law Enforcement: {len([p for p in pois if p['type'] == 'police'])} police stations
Fuel/Service: {len([p for p in pois if p['type'] == 'fuel'])} fuel stations
Emergency Response: {'ADEQUATE' if hospitals >= 2 else 'LIMITED'} coverage

=== LIQUID CARGO DYNAMICS ===
Petroleum Product Behavior:
- Surge Effect: High risk during acceleration/braking
- Rollover Risk: Amplified by {tt_specs['turn_sensitivity']}x on turns
- Stability: Compromised at speeds >35 km/h on curves
- Braking: Requires {int(tt_specs['gross_weight']/500)}m additional distance

=== CRITICAL ACTION POINTS ===
1. Pre-departure: Verify {tt_specs['avg_capacity_liters']:,}L load securement
2. Navigation: Reduce speed {(tt_specs['turn_sensitivity']-1)*100:.0f}% below normal on turns
3. Emergency: {hospitals} medical facilities available for response
4. Compliance: ADR requirements for {tt_specs['product_weight']/1000:.1f}T petroleum transport
5. Communication: Maintain contact every 30 minutes during transit"""
        

def generate_safety_briefing(tt_specs, weather_condition="clear"):
    """Generate AI-powered safety briefing using Gemini"""
    if not ai_client:
        return generate_fallback_briefing(tt_specs, weather_condition)
    
    try:
        model = get_working_gemini_model()  # ✅ NEW LINE
        if not model:
            return generate_fallback_briefing(tt_specs, weather_condition)
        
        prompt = f"""Generate a pre-trip safety checklist for this specific vehicle. Do not ask for more information.

VEHICLE SPECIFICATIONS PROVIDED:
- Tanker type: {tt_specs['capacity_range']}
- Cargo: {tt_specs['avg_capacity_liters']:,} liters petroleum products
- Gross weight: {tt_specs['gross_weight']/1000:.1f} tonnes
- Axle load: {tt_specs['axle_load']:.1f}T per axle
- Max speed: {tt_specs['max_speed']} km/h

CREATE CHECKLIST WITH:
1. 5 critical pre-departure checks
2. 3 speed/driving rules
3. 2 emergency procedures
4. Regulatory requirements

Format as numbered list. Keep concise and actionable."""

        response = model.generate_content(prompt)
        return response.text
        
    except Exception as e:
        print(f"Gemini briefing error: {e}")
        return generate_fallback_briefing(tt_specs, weather_condition)


# Add fallback functions for when AI is unavailable
def generate_fallback_analysis(sharp_turns, curves, tt_specs, pois):
    """Fallback analysis when AI is unavailable"""
    total_hazards = len(sharp_turns) + len(curves)
    critical_turns = len([t for t in sharp_turns if t.get('severity') == 'critical'])
    
    if critical_turns > 5:
        risk_rating = "9/10 - EXTREMELY HIGH RISK"
    elif total_hazards > 10:
        risk_rating = "7/10 - HIGH RISK" 
    elif total_hazards > 5:
        risk_rating = "5/10 - MODERATE RISK"
    else:
        risk_rating = "3/10 - LOW RISK"
    
    return f"""ROUTE SAFETY ASSESSMENT - {tt_specs['capacity_range']} TANKER

OVERALL SAFETY RATING: {risk_rating}

HAZARD SUMMARY:
- Sharp turns (90°+): {len(sharp_turns)}
- Critical severity: {critical_turns}
- Moderate curves: {len(curves)}
- Emergency facilities: {len(pois)}

TOP 3 SAFETY RECOMMENDATIONS:
1. SPEED CONTROL: Max {tt_specs['max_speed']} km/h, reduce to 10-15 km/h at sharp turns
2. BRAKE INSPECTION: Essential for {tt_specs['gross_weight']/1000:.1f}T vehicle - check before departure
3. LOAD MONITORING: Liquid surge increases rollover risk - avoid sudden maneuvers

SPEED STRATEGY:
- Normal sections: {tt_specs['max_speed']} km/h maximum
- Curves (45-90°): 25-35 km/h
- Sharp turns (90°+): 10-15 km/h
- Emergency stops: Plan 6-second following distance

EMERGENCY PREPAREDNESS:
- ADR certification and documentation current
- Emergency contact numbers accessible
- Spill response equipment checked
- Route permits verified for hazardous materials"""

def generate_fallback_briefing(tt_specs, weather_condition):
    """Fallback briefing when AI is unavailable"""
    return f"""PRE-TRIP SAFETY BRIEFING - {tt_specs['capacity_range']} TANKER

CRITICAL VEHICLE CHECKS:
1. Brake system inspection - priority for {tt_specs['gross_weight']/1000:.1f}T vehicle
2. Tire pressure verification (load-appropriate pressure)
3. Tank integrity and valve operation check
4. Emergency equipment inventory (fire extinguisher, spill kit)
5. ADR placards and documentation verification

OPERATIONAL PARAMETERS:
- Speed limit: {tt_specs['max_speed']} km/h maximum
- Turn speed: 15 km/h maximum on curves
- Following distance: 6-second minimum rule
- Axle load: {tt_specs['axle_load']:.1f}T - verify bridge restrictions

EMERGENCY PROTOCOLS:
1. Spill response: Isolate area, contact emergency services immediately
2. Fire safety: 300m evacuation radius, foam-based suppression only
3. Rollover prevention: Reduce speed significantly on curves
4. Communication: Emergency hotline accessible throughout journey

REGULATORY COMPLIANCE:
- Driver ADR certification current and accessible
- Vehicle inspection documentation valid
- Hazardous material transport permits verified
- Insurance coverage confirmed for petroleum products

Weather: {weather_condition} - Adjust driving accordingly"""


def ai_chat_gemini(user_question, tt_specs):
    """Enhanced chat function with full access to route analysis data"""
    if not ai_client:
        return "AI assistant unavailable. Please contact your safety supervisor for guidance."
    
    try:
        print("📡 Initializing Gemini model...")
        model = get_working_gemini_model()  # ✅ NEW LINE
        if not model:
            return "AI assistant temporarily unavailable. Please try again."
        
        # Get comprehensive route data from session
        coords = session.get('coords', [])
        sharp_turns = session.get('sharp_turns', [])
        curves = session.get('curves', [])
        all_pois = session.get('all_pois', [])
        route_report = session.get('route_report', {})
        
        # Build comprehensive context with all available data
        context_parts = [
            f"You are an expert truck tanker safety assistant with COMPLETE access to the current route analysis.",
            f"",
            f"=== CURRENT VEHICLE SPECIFICATIONS ===",
            f"- Vehicle Type: {tt_specs.get('capacity_range', 'Unknown')} Petroleum Tanker",
            f"- Fuel Capacity: {tt_specs.get('avg_capacity_liters', 0):,} liters",
            f"- Tare Weight: {tt_specs.get('tare_weight', 0)/1000:.1f}T (empty vehicle)",
            f"- Product Weight: {tt_specs.get('product_weight', 0)/1000:.1f}T (petroleum cargo)",
            f"- Gross Weight: {tt_specs.get('gross_weight', 0)/1000:.1f}T (fully loaded)",
            f"- Axle Load: {tt_specs.get('axle_load', 0):.1f}T per axle",
            f"- Maximum Speed: {tt_specs.get('max_speed', 50)} km/h",
            f"- Turn Sensitivity: {tt_specs.get('turn_sensitivity', 1.0)}x (rollover risk multiplier)",
            f"- Risk Multiplier: {tt_specs.get('risk_multiplier', 1.0)}x",
            f""
        ]
        
        # Add route analysis data if available
        if route_report:
            context_parts.extend([
                f"=== CURRENT ROUTE ANALYSIS ===",
                f"- Total Distance: {route_report.get('total_distance', 'Unknown')}",
                f"- Estimated Duration: {route_report.get('total_duration', 'Unknown')}",
                f"- Route Points Analyzed: {len(coords)} GPS coordinates",
                f""
            ])
            
            route_analysis = route_report.get('route_analysis', {})
            if route_analysis:
                context_parts.extend([
                    f"=== HAZARD BREAKDOWN ===",
                    f"- Critical Risk Zones: {route_analysis.get('critical_risk_zones', 0)}",
                    f"- High Risk Zones: {route_analysis.get('high_risk_zones', 0)}",
                    f"- Medium Risk Zones: {route_analysis.get('medium_risk_zones', 0)}",
                    f"- Total Hazard Points: {route_analysis.get('critical_risk_zones', 0) + route_analysis.get('high_risk_zones', 0) + route_analysis.get('medium_risk_zones', 0)}",
                    f""
                ])
        
        # Add detailed turn analysis
        if sharp_turns:
            critical_turns = [t for t in sharp_turns if t.get('severity') == 'critical']
            high_turns = [t for t in sharp_turns if t.get('severity') == 'high']
            
            context_parts.extend([
                f"=== SHARP TURN ANALYSIS ===",
                f"- Total Sharp Turns (90°+): {len(sharp_turns)}",
                f"- Critical Severity: {len(critical_turns)} turns",
                f"- High Severity: {len(high_turns)} turns",
                f""
            ])
            
            # Add specific turn details (first 5 most critical)
            critical_turns_sorted = sorted(critical_turns, key=lambda x: x.get('turn_angle', 0), reverse=True)
            if critical_turns_sorted:
                context_parts.append("=== MOST CRITICAL TURNS ===")
                for i, turn in enumerate(critical_turns_sorted[:5]):
                    context_parts.append(f"Turn {i+1}: {turn.get('turn_angle', 0):.1f}° {turn.get('direction', 'unknown')} turn (CRITICAL)")
                context_parts.append("")
        
        # Add curve analysis
        if curves:
            context_parts.extend([
                f"=== CURVE ANALYSIS ===",
                f"- Moderate Curves (45-90°): {len(curves)}",
                f"- Average curve angle: {sum(c.get('turn_angle', 0) for c in curves) / len(curves):.1f}°",
                f""
            ])
        
        # Add emergency infrastructure
        if all_pois:
            hospitals = [p for p in all_pois if p['type'] == 'hospital']
            police = [p for p in all_pois if p['type'] == 'police']
            fuel_stations = [p for p in all_pois if p['type'] == 'fuel']
            
            context_parts.extend([
                f"=== EMERGENCY INFRASTRUCTURE ===",
                f"- Hospitals: {len(hospitals)} ({', '.join([h['name'] for h in hospitals[:3]])}{'...' if len(hospitals) > 3 else ''})",
                f"- Police Stations: {len(police)} ({', '.join([p['name'] for p in police[:3]])}{'...' if len(police) > 3 else ''})",
                f"- Fuel Stations: {len(fuel_stations)} ({', '.join([f['name'] for f in fuel_stations[:3]])}{'...' if len(fuel_stations) > 3 else ''})",
                f""
            ])
        
        # Add safety recommendations from analysis
        if route_report and 'safety_recommendations' in route_report:
            context_parts.extend([
                f"=== CURRENT SAFETY RECOMMENDATIONS ===",
                f"- " + f"\n- ".join(route_report['safety_recommendations'][:5]),
                f""
            ])
        
        # Final context assembly
        context_parts.extend([
            f"=== DRIVER QUESTION ===",
            f"The driver operating this {tt_specs.get('capacity_range', 'Unknown')} tanker asks:",
            f'"{user_question}"',
            f"",
            f"=== INSTRUCTIONS ===",
            f"Based on ALL the route analysis data above, provide a detailed, practical answer.",
            f"Reference specific hazards, turn angles, distances, and safety measures when relevant.",
            f"Consider the vehicle's {tt_specs.get('gross_weight', 0)/1000:.1f}T weight and {tt_specs.get('turn_sensitivity', 1.0)}x turn sensitivity.",
            f"If the question relates to specific route hazards, reference the actual turn data and POI locations.",
            f"Provide actionable safety advice based on the current route conditions."
        ])
        
        # Combine all context
        full_context = "\n".join(context_parts)
        
        response = model.generate_content(full_context)
        return response.text
        
    except Exception as e:
        print(f"Gemini chat error: {e}")
        return f"AI assistant temporarily unavailable. For immediate safety concerns, contact your dispatcher. (Error: {str(e)})"

def interpolate_route_for_accuracy(coords, target_points_per_km=300):
    """Interpolate route to achieve target point density"""
    if len(coords) < 2:
        return coords
    
    try:
        interpolated = [coords[0]]
        
        for i in range(1, len(coords)):
            start = coords[i-1]
            end = coords[i]
            
            # Calculate distance between consecutive points
            distance_km = geodesic(start, end).kilometers
            
            # If points are too far apart, add intermediate points
            if distance_km > (1.0 / target_points_per_km):
                # Calculate how many points we need to insert
                num_intermediate = int(distance_km * target_points_per_km)
                
                # Add intermediate points using linear interpolation
                for j in range(1, num_intermediate + 1):
                    ratio = j / (num_intermediate + 1)
                    lat = start[0] + (end[0] - start[0]) * ratio
                    lng = start[1] + (end[1] - start[1]) * ratio
                    interpolated.append((lat, lng))
            
            interpolated.append(end)
        
        print(f"Route interpolation: {len(coords)} → {len(interpolated)} points")
        print(f"Density improvement: {len(interpolated)/len(coords):.1f}x more points")
        
        return interpolated
        
    except Exception as e:
        print(f"Interpolation error: {e}")
        return coords

# REPLACE your calculate_bearing function with:
def calculate_precise_bearing(lat1, lng1, lat2, lng2):
    """Enhanced bearing calculation using spherical trigonometry"""
    try:
        lat1_rad, lng1_rad = math.radians(lat1), math.radians(lng1)
        lat2_rad, lng2_rad = math.radians(lat2), math.radians(lng2)
        
        dlng = lng2_rad - lng1_rad
        y = math.sin(dlng) * math.cos(lat2_rad)
        x = (math.cos(lat1_rad) * math.sin(lat2_rad) - 
             math.sin(lat1_rad) * math.cos(lat2_rad) * math.cos(dlng))
        
        bearing = math.atan2(y, x)
        bearing_degrees = math.degrees(bearing)
        return (bearing_degrees + 360) % 360
    except Exception as e:
        print(f"Bearing calculation error: {e}")
        return 0

def calculate_curvature_metrics(coords, index, sample_distance=3):
    """Calculate curvature metrics using pure Python"""
    if index < sample_distance or index >= len(coords) - sample_distance:
        return {'radius': float('inf'), 'curvature': 0, 'turn_rate': 0}
    
    try:
        p1 = coords[index - sample_distance]
        p2 = coords[index]
        p3 = coords[index + sample_distance]
        
        # Convert to approximate planar coordinates
        lat_center = p2[0]
        cos_lat = math.cos(math.radians(lat_center))
        
        x1 = (p1[1] - p2[1]) * cos_lat * 111320
        y1 = (p1[0] - p2[0]) * 111320
        x3 = (p3[1] - p2[1]) * cos_lat * 111320
        y3 = (p3[0] - p2[0]) * 111320
        
        # Calculate distances
        a = math.sqrt(x1**2 + y1**2)
        b = math.sqrt(x3**2 + y3**2)
        c = math.sqrt((x3-x1)**2 + (y3-y1)**2)
        
        if a < 1e-6 or b < 1e-6 or c < 1e-6:
            return {'radius': float('inf'), 'curvature': 0, 'turn_rate': 0}
        
        # Calculate area using cross product
        area = abs(x1 * y3 - x3 * y1) / 2
        
        if area < 1e-10:
            radius = float('inf')
            curvature = 0
        else:
            # Circumradius formula - pure math, no scipy needed
            radius = (a * b * c) / (4 * area)
            curvature = 1 / radius if radius > 0 else 0
        
        total_distance = a + b
        turn_rate = curvature * total_distance if total_distance > 0 else 0
        
        return {'radius': radius, 'curvature': curvature, 'turn_rate': turn_rate}
        
    except Exception as e:
        print(f"Curvature calculation error: {e}")
        return {'radius': float('inf'), 'curvature': 0, 'turn_rate': 0}

def calculate_practical_physics_risk_score(turn_angle, curvature_radius, tt_specs):
    """PRACTICAL risk scoring based on real truck tanker operations"""
    try:
        gross_weight = tt_specs.get('gross_weight', 25000)
        cg_height = tt_specs.get('cg_height', 2.5)
        track_width = tt_specs.get('track_width', 2.0)
        stability_factor = tt_specs.get('stability_factor', 1.0)
        
        # PRACTICAL SPEED RECOMMENDATIONS based on real-world scenarios:
        if turn_angle >= 90:    # CRITICAL: U-turns, roundabouts, tight turns
            approach_speed = 10   # Walking pace - liquid surge risk very high
        elif turn_angle >= 65:  # HIGH RISK: Highway ramps, sharp corners
            approach_speed = 18   # Slow residential speed
        elif turn_angle >= 45:  # MODERATE: Normal intersections, city turns
            approach_speed = 25   # City driving speed
        elif turn_angle >= 25:  # CAUTION: Highway curves, wide turns
            approach_speed = 35   # Reduced highway speed
        else:                   # NORMAL: Straight roads, gentle bends
            approach_speed = 50   # Normal driving (up to vehicle max)
        
        approach_speed_ms = approach_speed / 3.6
        
        # Enhanced radius calculations for practical scenarios
        if curvature_radius > 0 and curvature_radius != float('inf'):
            lateral_acceleration = approach_speed_ms**2 / curvature_radius
        else:
            # Practical radius estimates based on turn types
            if turn_angle >= 90:
                estimated_radius = 15    # Tight intersections/roundabouts
            elif turn_angle >= 65:
                estimated_radius = 25    # Highway ramps
            elif turn_angle >= 45:
                estimated_radius = 50    # Normal turns
            else:
                estimated_radius = 100   # Wide curves
            lateral_acceleration = approach_speed_ms**2 / estimated_radius
        
        rollover_threshold = 9.81 * (track_width / 2) / cg_height * stability_factor
        risk_ratio = lateral_acceleration / rollover_threshold
        
        # PRACTICAL risk multipliers based on cargo and weight
        if gross_weight > 35000:    # Heavy tanker (30+ KL)
            risk_ratio *= 1.6       # Significant increase for heavy loads
        elif gross_weight > 25000:  # Medium tanker (16-24 KL)
            risk_ratio *= 1.3       # Moderate increase
        else:                       # Light tanker (12-16 KL)
            risk_ratio *= 1.1       # Slight increase
        
        # Additional practical factors for liquid surge
        if turn_angle >= 90:        # U-turns and sharp corners
            risk_ratio *= 1.8       # High surge risk
        elif turn_angle >= 65:      # Highway ramps and exits
            risk_ratio *= 1.4       # Moderate surge risk
        
        physics_score = min(10.0, risk_ratio * 5.5)
        
        return physics_score
    except Exception as e:
        print(f"Practical physics calculation error: {e}")
        return 5.0

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

def detect_practical_hazards(coords, min_turn_angle=25, sample_distance=5, tt_specs=None):
    """PRACTICAL hazard detection with real-world criteria and scenarios"""
    
    # Interpolate for higher accuracy
    print(f"Original route: {len(coords)} points")
    coords = interpolate_route_for_accuracy(coords, target_points_per_km=50)
    print(f"Enhanced route: {len(coords)} points")
    
    sharp_turns = []
    curves = []
    
    if len(coords) < sample_distance * 2:
        return sharp_turns, curves
    
    if not tt_specs:
        tt_specs = TT_SPECIFICATIONS["16-20KL"]
    
    for i in range(sample_distance, len(coords) - sample_distance):
        try:
            bearing_in = calculate_precise_bearing(
                coords[i - sample_distance][0], coords[i - sample_distance][1],
                coords[i][0], coords[i][1]
            )
            bearing_out = calculate_precise_bearing(
                coords[i][0], coords[i][1],
                coords[i + sample_distance][0], coords[i + sample_distance][1]
            )
            
            turn_angle = calculate_turn_angle_precise(bearing_in, bearing_out)
            
            if turn_angle >= min_turn_angle:
                # Get curvature metrics
                curvature_metrics = calculate_curvature_metrics(coords, i, sample_distance)
                
                # Calculate practical risk score
                physics_score = calculate_practical_physics_risk_score(turn_angle, curvature_metrics['radius'], tt_specs)
                
                # Determine direction
                bearing_diff = bearing_out - bearing_in
                if bearing_diff > 180:
                    bearing_diff -= 360
                elif bearing_diff < -180:
                    bearing_diff += 360
                turn_direction = "right" if bearing_diff > 0 else "left"
                
                # PRACTICAL severity classification with real-world context
                if turn_angle >= 90:        # U-turns, tight roundabouts
                    severity = 'critical'
                    risk_category = 'U-Turn/Roundabout/Tight Turn'
                    warning = 'LIQUID SURGE DANGER - Use extreme caution'
                    scenario_type = 'critical_maneuver'
                elif turn_angle >= 65:     # Highway ramps, sharp corners  
                    severity = 'high'
                    risk_category = 'Highway Ramp/Sharp Corner'
                    warning = 'HIGH ROLLOVER RISK - Reduce speed significantly'
                    scenario_type = 'highway_hazard'
                elif turn_angle >= 45:     # Normal intersections
                    severity = 'moderate'
                    risk_category = 'Intersection/City Turn'
                    warning = 'CAUTION REQUIRED - Standard intersection speed'
                    scenario_type = 'normal_turn'
                else:                       # Gentle curves
                    severity = 'low'
                    risk_category = 'Highway Curve/Wide Turn'
                    warning = 'REDUCE SPEED - Monitor liquid movement'
                    scenario_type = 'gentle_curve'
                
                # Get practical speed recommendation
                practical_speed = get_practical_speed(turn_angle, tt_specs)
                
                hazard = {
                    'location': coords[i],
                    'index': i,
                    'turn_angle': turn_angle,
                    'curvature_radius': curvature_metrics['radius'],
                    'direction': turn_direction,
                    'bearing_in': bearing_in,
                    'bearing_out': bearing_out,
                    'severity': severity,
                    'physics_score': physics_score,
                    'risk_category': risk_category,
                    'warning': warning,
                    'scenario_type': scenario_type,
                    'practical_speed': practical_speed
                }
                
                # Classify based on practical criteria
                if turn_angle >= 45:  # Significant turns requiring attention
                    sharp_turns.append(hazard)
                else:                # Gentle curves
                    curves.append(hazard)
                    
        except Exception as e:
            print(f"Error analyzing turn at index {i}: {e}")
            continue
    
    print(f"Practical detection: {len(sharp_turns)} significant turns, {len(curves)} gentle curves")
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

def get_practical_speed(turn_angle, tt_specs):
    """Get practical speed recommendations based on real driving scenarios"""
    tanker_type = tt_specs.get('capacity_range', '16-20KL')
    
    # Practical speed matrix based on tanker capacity
    speed_matrix = {
        '12-16KL': {    # Light tanker
            'critical': 12,     # U-turns, roundabouts
            'high': 20,         # Highway ramps
            'moderate': 28,     # Intersections
            'low': 40           # Highway curves
        },
        '16-20KL': {    # Medium tanker  
            'critical': 10,
            'high': 18,
            'moderate': 25,
            'low': 35
        },
        '20-24KL': {    # Heavy tanker
            'critical': 8,
            'high': 15,
            'moderate': 22,
            'low': 32
        },
        '24-30KL': {    # Very heavy tanker
            'critical': 8,
            'high': 12,
            'moderate': 20,
            'low': 30
        },
        '30KL+': {      # Extra heavy tanker
            'critical': 5,
            'high': 10,
            'moderate': 18,
            'low': 28
        }
    }
    
    # Get speeds for this tanker type
    speeds = speed_matrix.get(tanker_type, speed_matrix['16-20KL'])
    
    # Return appropriate speed based on turn angle
    if turn_angle >= 90:
        return speeds['critical']
    elif turn_angle >= 65:
        return speeds['high']
    elif turn_angle >= 45:
        return speeds['moderate']
    else:
        return speeds['low']


def get_practical_colors(turn_angle, physics_score):
    """Get practical color coding for map visualization based on real scenarios"""
    
    if turn_angle >= 90:        # Critical: U-turns, roundabouts
        return {
            'color': 'darkred',
            'icon_color': 'darkred',
            'alert_level': 'CRITICAL',
            'scenario': 'U-Turn/Roundabout'
        }
    elif turn_angle >= 65:      # High: Highway ramps, sharp corners
        return {
            'color': 'red',
            'icon_color': 'red', 
            'alert_level': 'HIGH RISK',
            'scenario': 'Highway Ramp'
        }
    elif turn_angle >= 45:      # Moderate: Normal intersections
        return {
            'color': 'orange',
            'icon_color': 'orange',
            'alert_level': 'MODERATE',
            'scenario': 'Intersection'
        }
    else:                       # Low: Gentle curves
        return {
            'color': 'yellow',
            'icon_color': 'yellow',
            'alert_level': 'CAUTION',
            'scenario': 'Highway Curve'
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

def interpolate_route_advanced(coords, target_points_per_km=100):
    """Advanced interpolation using spline-like smoothing"""
    if len(coords) < 4:
        return coords
    
    try:
        interpolated = []
        
        for i in range(len(coords) - 1):
            start = coords[i]
            end = coords[i + 1]
            
            # Add the start point
            interpolated.append(start)
            
            # Calculate segment distance
            distance_km = geodesic(start, end).kilometers
            
            # Determine number of intermediate points needed
            if distance_km > (1.0 / target_points_per_km):
                num_points = max(1, int(distance_km * target_points_per_km))
                
                # Use Catmull-Rom spline for smoother interpolation
                for j in range(1, num_points + 1):
                    t = j / (num_points + 1)
                    
                    # Get control points for smooth interpolation
                    p0 = coords[max(0, i-1)]
                    p1 = start
                    p2 = end
                    p3 = coords[min(len(coords)-1, i+2)]
                    
                    # Catmull-Rom interpolation
                    lat = catmull_rom_interpolate(p0[0], p1[0], p2[0], p3[0], t)
                    lng = catmull_rom_interpolate(p0[1], p1[1], p2[1], p3[1], t)
                    
                    interpolated.append((lat, lng))
        
        # Add the final point
        interpolated.append(coords[-1])
        
        print(f"Advanced interpolation: {len(coords)} → {len(interpolated)} points")
        return interpolated
        
    except Exception as e:
        print(f"Advanced interpolation error: {e}")
        return coords

def catmull_rom_interpolate(p0, p1, p2, p3, t):
    """Catmull-Rom spline interpolation for smooth curves"""
    return 0.5 * (
        (2 * p1) +
        (-p0 + p2) * t +
        (2*p0 - 5*p1 + 4*p2 - p3) * t*t +
        (-p0 + 3*p1 - 3*p2 + p3) * t*t*t
    )


def get_optimal_density(distance_km):
    """Get optimal point density based on route length"""
    if distance_km < 10:      # Short city routes
        return 100  # 100 points/km
    elif distance_km < 50:    # Medium routes  
        return 75   # 75 points/km
    elif distance_km < 200:   # Long routes
        return 50   # 50 points/km
    else:                     # Very long routes
        return 25   # 25 points/km (to avoid memory issues)

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


def load_ro_data():
    """Load consignee data from Excel file with actual column names"""
    try:
        df_ro = pd.read_excel("IOCL_Plant_data.xlsx")
        ro_data = {}
        
        for _, row in df_ro.iterrows():
            try:
                # Extract data using your actual column names
                state_code = str(row['State code']).strip().upper() if pd.notna(row['State code']) else None
                sap_code = str(row['SAP Code']).strip() if pd.notna(row['SAP Code']) else None
                consignee = str(row['Consignee']).strip() if pd.notna(row['Consignee']) else None
                lat = float(row['Latitude']) if pd.notna(row['Latitude']) else None
                lng = float(row['Longitude']) if pd.notna(row['Longitude']) else None
                sales_group_desc = str(row['Sales Group Desc']).strip() if pd.notna(row['Sales Group Desc']) else None
                customer_type = str(row['Customer Type']).strip() if pd.notna(row['Customer Type']) else None
                
                # Only add if required fields are present
                if all([state_code, sap_code, consignee, lat, lng]):
                    if state_code not in ro_data:
                        ro_data[state_code] = {}
                        
                    ro_data[state_code][sap_code] = {
                        'name': consignee,
                        'district': sales_group_desc or 'Unknown',
                        'region': customer_type or 'Unknown',
                        'lat': lat,
                        'lng': lng
                    }
                else:
                    print(f"Skipping incomplete row: SAP Code {sap_code}")
                    
            except (ValueError, TypeError) as e:
                print(f"Error processing consignee row: {e}")
                continue
                
        print(f"Loaded {sum(len(state_ros) for state_ros in ro_data.values())} consignee locations across {len(ro_data)} states")
        return ro_data
        
    except FileNotFoundError:
        print("IOCL_Plant_data.xlsx not found, consignee selection will be disabled")
        return {}
    except Exception as e:
        print(f"Error loading consignee data: {e}")
        return {}

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
        username = session.get('username', 'User')
        
        # Load IOCL Landmarks with data validation (existing code)
        landmarks = []
        
        try:
            df_iocl = pd.read_excel("IOCL_Landmark_Details.xlsx")
            
            for _, row in df_iocl.iterrows():
                try:
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
            landmarks = [
                {'name': 'Delhi Terminal', 'lat': 28.6139, 'lng': 77.2090},
                {'name': 'Mumbai Terminal', 'lat': 19.0760, 'lng': 72.8777},
                {'name': 'Bangalore Terminal', 'lat': 12.9716, 'lng': 77.5946},
                {'name': 'Chennai Terminal', 'lat': 13.0827, 'lng': 80.2707},
                {'name': 'Kolkata Terminal', 'lat': 22.5726, 'lng': 88.3639}
            ]
        except Exception as e:
            print(f"Error loading landmarks Excel file: {e}")
            landmarks = []

        # Load consignee data (NEW)
        ro_data = load_ro_data()

        # Pass all data to template (UPDATED)
        return render_template(
            "route_form.html",
            landmarks=landmarks,
            ro_data=ro_data,  # ADD THIS LINE
            tt_specifications=TT_SPECIFICATIONS,
            username=username
        )
        
    except Exception as e:
        print(f"Error loading data: {e}")
        import traceback
        traceback.print_exc()
        
        # Fallback page (existing code - no changes needed)
        username = session.get('username', 'User')
        tt_options = ""
        for tt_key, tt_data in TT_SPECIFICATIONS.items():
            tt_options += f'<option value="{tt_key}">{tt_data["capacity_range"]} ({tt_data["gross_weight"]/1000:.1f}T)</option>'
        
        return f"""
        <html><body>
        <h2>IndianOil Smart Marg - Truck Tanker Navigation</h2>
        <p>Welcome, {username}! <a href="/logout">Logout</a></p>
        <p>Basic form (data loading failed)</p>
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


# ==============================================================================
# ADD THESE NEW ROUTES TO YOUR app.py FILE (after your existing routes)
# ==============================================================================

@app.route('/get_suggested_questions')
@login_required
def get_suggested_questions():
    """Generate contextual question suggestions based on current route analysis"""
    try:
        # Get current analysis data
        tt_specs = session.get('tt_specs', {})
        sharp_turns = session.get('sharp_turns', [])
        curves = session.get('curves', [])
        all_pois = session.get('all_pois', [])
        route_report = session.get('route_report', {})
        coords = session.get('coords', [])
        
        suggestions = {
            'general': [],
            'hazard_specific': [],
            'emergency': [],
            'operational': []
        }
        
        # Generate suggestions based on available data
        if tt_specs:
            # General vehicle questions
            suggestions['general'].extend([
                f"What's the maximum safe speed for my {tt_specs.get('capacity_range', 'tanker')}?",
                f"How should I handle curves with a {tt_specs.get('gross_weight', 0)/1000:.1f}T loaded tanker?",
                f"What are the braking requirements for {tt_specs.get('avg_capacity_liters', 0):,}L of petroleum?",
                "What pre-trip safety checks should I perform?",
                "How do I calculate safe following distance for my tanker?",
                "What are the stability risks with liquid cargo?"
            ])
            
            # Weight-specific questions
            if tt_specs.get('gross_weight', 0) > 30000:
                suggestions['operational'].extend([
                    "Are there bridge weight restrictions on this route?",
                    "How does my heavy load affect stopping distance?",
                    "What are the axle weight regulations I need to follow?",
                    f"Is my {tt_specs.get('gross_weight', 0)/1000:.1f}T tanker too heavy for city roads?"
                ])
            
            # Capacity-specific questions
            if tt_specs.get('avg_capacity_liters', 0) > 25000:
                suggestions['operational'].extend([
                    "How do I manage liquid surge in a large tanker?",
                    "What are the parking restrictions for large petroleum tankers?",
                    "Do I need special permits for this capacity?"
                ])
        
        # Hazard-specific suggestions based on actual route analysis
        if sharp_turns:
            critical_turns = [t for t in sharp_turns if t.get('severity') == 'critical']
            high_turns = [t for t in sharp_turns if t.get('severity') == 'high']
            
            if critical_turns:
                suggestions['hazard_specific'].extend([
                    f"How should I navigate the {len(critical_turns)} critical turns detected?",
                    f"What speed should I use for turns over 120 degrees?",
                    "How do I prevent rollover on sharp turns?",
                    "What's the safest approach angle for critical turns?",
                    "Should I use engine braking before sharp turns?"
                ])
            
            if len(sharp_turns) > 5:
                suggestions['hazard_specific'].extend([
                    f"This route has {len(sharp_turns)} sharp turns - is it safe for my tanker?",
                    "Should I take an alternate route with fewer sharp turns?",
                    "How do I manage liquid surge during multiple turns?",
                    "What's the cumulative risk of multiple sharp turns?"
                ])
            
            # Specific turn angle questions
            max_angle = max((t.get('turn_angle', 0) for t in sharp_turns), default=0)
            if max_angle > 130:
                suggestions['hazard_specific'].extend([
                    f"How do I safely navigate a {max_angle:.0f}° turn with liquid cargo?",
                    f"Is a {max_angle:.0f}° turn safe for petroleum tankers?",
                    "What are the blind spot risks at extreme turns?"
                ])
        
        if curves:
            suggestions['hazard_specific'].extend([
                f"What's the recommended speed for the {len(curves)} curves on this route?",
                "How do moderate curves affect liquid cargo stability?",
                "Should I use engine braking on curved sections?",
                "How do I maintain control through continuous curves?"
            ])
        
        # Emergency and infrastructure questions
        if all_pois:
            hospitals = [p for p in all_pois if p['type'] == 'hospital']
            police = [p for p in all_pois if p['type'] == 'police']
            fuel_stations = [p for p in all_pois if p['type'] == 'fuel']
            
            if hospitals:
                suggestions['emergency'].extend([
                    f"Where are the {len(hospitals)} hospitals along my route?",
                    "What should I do if there's a medical emergency?",
                    "How do I contact emergency services while carrying petroleum?",
                    f"Which hospital is closest to the dangerous turns?",
                    "What's the evacuation procedure near medical facilities?"
                ])
            
            if police:
                suggestions['emergency'].extend([
                    "What documents do police need for hazmat transport?",
                    "How do I handle a police stop with petroleum cargo?",
                    "What are my rights during a hazmat inspection?",
                    "Should I notify police of my route in advance?"
                ])
            
            if fuel_stations:
                suggestions['operational'].extend([
                    f"Can I use any of the {len(fuel_stations)} fuel stations on this route?",
                    "What are the fueling safety procedures for tankers?",
                    "Where should I plan my fuel stops?",
                    "Are there restrictions on tanker fueling?",
                    "How do I ground my vehicle while fueling?"
                ])
            
            if not hospitals:
                suggestions['emergency'].append("Are there medical facilities along this route?")
            if not police:
                suggestions['emergency'].append("Where are the nearest police stations?")
        
        # Route-specific operational questions
        if route_report:
            distance = route_report.get('total_distance', '')
            duration = route_report.get('total_duration', '')
            
            if distance and duration:
                suggestions['operational'].extend([
                    f"How should I manage fatigue on this {distance} journey?",
                    f"What rest stops should I plan for a {duration} trip?",
                    "How do I maintain optimal fuel economy on this route?",
                    f"Is {duration} too long for one driver?",
                    "What are the mandatory rest requirements?"
                ])
            
            # Traffic and timing questions
            suggestions['operational'].extend([
                "What's the best time to start this journey?",
                "How do I handle heavy traffic with a loaded tanker?",
                "Should I avoid rush hour on this route?",
                "Are there time restrictions for petroleum transport?",
                "What are the night driving regulations?"
            ])
        
        # Weather and environmental questions
        suggestions['operational'].extend([
            "How does weather affect tanker safety?",
            "What should I do if visibility becomes poor?",
            "How do I handle crosswinds with liquid cargo?",
            "Should I delay travel in bad weather?",
            "What are the temperature considerations for petroleum?"
        ])
        
        # Regulatory and compliance questions
        suggestions['operational'].extend([
            "What ADR documentation do I need?",
            "Are there time restrictions for hazmat transport?",
            "What are the parking regulations for petroleum tankers?",
            "Do I need route permits for this journey?",
            "What are the insurance requirements?",
            "How do I comply with hazmat placarding rules?"
        ])
        
        # Emergency response questions
        suggestions['emergency'].extend([
            "What's the emergency response procedure for spills?",
            "How do I evacuate if there's a fire risk?",
            "What's the emergency contact number for petroleum incidents?",
            "How do I isolate the vehicle in an emergency?",
            "What's the evacuation radius for petroleum tankers?",
            "How do I use emergency shut-off valves?",
            "What fire suppression equipment do I need?"
        ])
        
        # Remove duplicates and limit suggestions
        for category in suggestions:
            suggestions[category] = list(dict.fromkeys(suggestions[category]))[:8]  # Limit to 8 per category
        
        return {
            'suggestions': suggestions,
            'context': {
                'has_route_data': bool(coords),
                'sharp_turns': len(sharp_turns),
                'curves': len(curves),
                'pois': len(all_pois),
                'tt_type': tt_specs.get('capacity_range', 'Unknown'),
                'total_suggestions': sum(len(cat) for cat in suggestions.values())
            },
            'status': 'success'
        }
        
    except Exception as e:
        print(f"Error generating suggestions: {e}")
        return {
            'suggestions': {
                'general': [
                    "What's the maximum safe speed for my tanker?",
                    "How should I handle sharp turns?",
                    "What are the braking requirements?",
                    "What pre-trip checks should I perform?",
                    "How do I calculate safe following distance?"
                ]
            },
            'context': {'has_route_data': False},
            'status': 'fallback'
        }



@app.route('/safety_briefing')
@login_required
def safety_briefing():
    """Get AI-powered safety briefing"""
    try:
        tt_specs = session.get('tt_specs', {})
        if not tt_specs:
            return {"error": "No truck specifications found", "status": "failed"}
        
        briefing = generate_safety_briefing(tt_specs)
        
        return {
            "briefing": briefing,
            "status": "success"
        }
        
    except Exception as e:
        return {"error": str(e), "status": "failed"}

@app.route('/ai_chat', methods=['POST'])
@login_required
def ai_chat():
    """Enhanced chat with AI about route safety using complete analysis data"""
    try:
        user_question = request.json.get('question', '')
        tt_specs = session.get('tt_specs', {})
        
        if not user_question.strip():
            return {"error": "Please provide a question", "status": "failed"}
        
        # Ensure we have TT specs
        if not tt_specs:
            return {"error": "No truck specifications found. Please analyze a route first.", "status": "failed"}
        
        answer = ai_chat_gemini(user_question, tt_specs)
        
        return {
            "answer": answer,
            "status": "success",
            "context_info": {
                "route_analyzed": bool(session.get('coords')),
                "sharp_turns": len(session.get('sharp_turns', [])),
                "curves": len(session.get('curves', [])),
                "pois": len(session.get('all_pois', [])),
                "tt_type": tt_specs.get('capacity_range', 'Unknown')
            }
        }
        
    except Exception as e:
        return {"error": f"Chat error: {str(e)}", "status": "failed"}


# ==============================================================================
# ADD THIS NEW ROUTE FOR AI ANALYSIS ACCESS
# ==============================================================================

@app.route('/ai_analysis/current')
@login_required
def ai_current_analysis():
    """Get AI-powered route analysis with full data access"""
    try:
        # Get route data from session
        coords = session.get('coords', [])
        sharp_turns = session.get('sharp_turns', [])
        curves = session.get('curves', [])
        tt_specs = session.get('tt_specs', {})
        all_pois = session.get('all_pois', [])
        
        if not coords or not tt_specs:
            return {"error": "No route data found. Please analyze a route first.", "status": "failed"}
        
        ai_analysis = analyze_route_with_ai(coords, sharp_turns, curves, tt_specs, all_pois)
        
        return {
            "ai_analysis": ai_analysis,
            "status": "success"
        }
        
    except Exception as e:
        return {"error": str(e), "status": "failed"}


# ============================================================================
# COMPLETE analyze_route FUNCTION - REPLACE ENTIRE FUNCTION IN YOUR app.py
# ============================================================================

@app.route('/analyze_route', methods=['POST'])
@login_required
def analyze_route():
    """Enhanced route analysis based on IOCL format with comprehensive reporting"""
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

        # Ensure templates directory exists
        templates_dir = Path("templates")
        templates_dir.mkdir(exist_ok=True)
        
        # Enhanced hazard detection with IOCL standards
        print(f"🔍 Starting IOCL-standard analysis for {total_distance} route...")
        sharp_turns, curves = detect_practical_hazards(coords, min_turn_angle=25, sample_distance=2, tt_specs=tt_specs)
        
        print(f"📊 IOCL analysis: {len(sharp_turns)} significant turns, {len(curves)} gentle curves")
        
        # Enhanced POI collection for emergency infrastructure
        all_pois = []
        try:
            for keyword in ['hospital', 'police', 'fuel', 'pharmacy', 'fire station']:
                sample_coords = coords[::15] if len(coords) > 15 else coords
                for lat, lng in sample_coords[:8]:  # Optimized sampling
                    try:
                        places = gmaps.places_nearby(location=(lat, lng), radius=1500, keyword=keyword)
                        for place in places.get('results', [])[:3]:
                            poi_data = {
                                'name': place['name'],
                                'location': (
                                    place['geometry']['location']['lat'],
                                    place['geometry']['location']['lng']
                                ),
                                'type': keyword,
                                'place_id': place.get('place_id', ''),
                                'rating': place.get('rating', 'N/A'),
                                'vicinity': place.get('vicinity', ''),
                                'types': place.get('types', [])
                            }
                            all_pois.append(poi_data)
                    except Exception as e:
                        print(f"POI search error for {keyword}: {e}")
                        continue
        except Exception as e:
            print(f"Error in POI collection: {e}")

        # Remove duplicate POIs
        unique_pois = []
        for poi in all_pois:
            is_duplicate = False
            for existing in unique_pois:
                lat_diff = abs(poi['location'][0] - existing['location'][0])
                lng_diff = abs(poi['location'][1] - existing['location'][1])
                if lat_diff < 0.002 and lng_diff < 0.002:  # ~200m tolerance
                    is_duplicate = True
                    break
            if not is_duplicate:
                unique_pois.append(poi)
        
        all_pois = unique_pois[:25]  # Limit to 25 most relevant

        # Create enhanced location mapping with IOCL standards
        location_mapping = create_iocl_location_mapping(sharp_turns, curves, all_pois, source, destination, tt_specs)

        # Store enhanced data in session
        session['coords'] = coords
        session['sharp_turns'] = sharp_turns
        session['curves'] = curves
        session['all_pois'] = all_pois
        session['location_mapping'] = location_mapping
        session['source'] = source
        session['destination'] = destination
        session.modified = True

        # ===== ENHANCED MAP GENERATION - IOCL STYLE =====
        try:
            center_lat = sum(coord[0] for coord in coords) / len(coords)
            center_lng = sum(coord[1] for coord in coords) / len(coords)
            
            # Create professional IOCL-style map
            m = folium.Map(
                location=(center_lat, center_lng), 
                zoom_start=11,
                tiles='OpenStreetMap',
                control_scale=True,
                prefer_canvas=True,
                zoom_control=True,
                scrollWheelZoom=True
            )

            # Add IOCL branding and route
            folium.PolyLine(
                coords,
                color='#1e3c72',
                weight=8,
                opacity=0.9,
                popup=f"IOCL Route Analysis - {total_distance} - {total_duration}",
                tooltip=f"🚛 {tt_specs['capacity_range']} Tank Truck Route"
            ).add_to(m)

            # Add enhanced danger zone markers with IOCL standards
            for i, turn in enumerate(sharp_turns):
                lat, lng = turn['location']
                turn_angle = turn['turn_angle']
                
                # IOCL risk classification
                if turn_angle >= 90:
                    marker_color = 'darkred'
                    severity = 'CRITICAL'
                    speed_limit = 10
                    icon_name = 'exclamation-triangle'
                elif turn_angle >= 65:
                    marker_color = 'red'
                    severity = 'HIGH RISK'
                    speed_limit = 18
                    icon_name = 'warning'
                elif turn_angle >= 45:
                    marker_color = 'orange'
                    severity = 'MODERATE'
                    speed_limit = 25
                    icon_name = 'info-circle'
                else:
                    marker_color = 'yellow'
                    severity = 'LOW RISK'
                    speed_limit = 35
                    icon_name = 'info'

                # Enhanced IOCL-style popup
                popup_html = f"""
                <div style='font-family: Arial, sans-serif; width: 380px; max-width: 380px;'>
                    <div style='background: linear-gradient(135deg, #1e3c72 0%, #2a5298 100%); color: white; padding: 12px; margin: -8px -8px 12px -8px; text-align: center; font-weight: bold; border-radius: 6px 6px 0 0;'>
                        🚨 IOCL DANGER ZONE DZ-{i+1:02d}
                    </div>
                    
                    <table style='width: 100%; font-size: 11px; margin: 8px 0;'>
                        <tr style='background: #f8f9fa;'>
                            <td style='padding: 6px; font-weight: bold;'>Hazard Classification:</td>
                            <td style='padding: 6px; color: {marker_color}; font-weight: bold;'>{turn.get('risk_category', 'Sharp Turn')}</td>
                        </tr>
                        <tr>
                            <td style='padding: 6px; font-weight: bold;'>Turn Geometry:</td>
                            <td style='padding: 6px;'>{turn_angle:.1f}° {turn['direction']} turn</td>
                        </tr>
                        <tr style='background: #f8f9fa;'>
                            <td style='padding: 6px; font-weight: bold;'>Risk Level:</td>
                            <td style='padding: 6px; color: {marker_color}; font-weight: bold;'>{severity}</td>
                        </tr>
                        <tr>
                            <td style='padding: 6px; font-weight: bold;'>Max Safe Speed:</td>
                            <td style='padding: 6px; color: red; font-weight: bold;'>{speed_limit} km/h</td>
                        </tr>
                        <tr style='background: #f8f9fa;'>
                            <td style='padding: 6px; font-weight: bold;'>GPS Coordinates:</td>
                            <td style='padding: 6px; font-family: monospace; font-size: 10px;'>{lat:.6f}, {lng:.6f}</td>
                        </tr>
                        <tr>
                            <td style='padding: 6px; font-weight: bold;'>Vehicle Type:</td>
                            <td style='padding: 6px;'>{tt_specs['capacity_range']} Petroleum Tanker</td>
                        </tr>
                        <tr style='background: #f8f9fa;'>
                            <td style='padding: 6px; font-weight: bold;'>Gross Weight:</td>
                            <td style='padding: 6px;'>{tt_specs['gross_weight']/1000:.1f}T</td>
                        </tr>
                    </table>
                    
                    <div style='background: #fff3cd; border: 1px solid #fdd663; padding: 10px; margin: 8px 0; border-radius: 4px; border-left: 4px solid #f0ad4e;'>
                        <div style='font-weight: bold; color: #8a6d3b; margin-bottom: 6px;'>⚠️ IOCL SAFETY PROTOCOLS:</div>
                        <div style='font-size: 10px; color: #8a6d3b; line-height: 1.4;'>
                            • Engine braking mandatory before turn<br>
                            • Monitor liquid surge indicators<br>
                            • Activate emergency flashers<br>
                            • Radio position report to control<br>
                            • Reduce to {speed_limit} km/h maximum<br>
                            • Maintain 6-second following distance
                        </div>
                    </div>
                    
                    <div style='text-align: center; margin-top: 12px;'>
                        <button onclick='navigator.clipboard.writeText("{lat:.6f}, {lng:.6f}")' 
                                style='background: #1e3c72; color: white; border: none; padding: 6px 12px; border-radius: 4px; cursor: pointer; font-size: 10px;'>
                            📋 Copy GPS Coordinates
                        </button>
                    </div>
                </div>
                """

                folium.Marker(
                    location=(lat, lng),
                    popup=folium.Popup(popup_html, max_width=420),
                    icon=folium.Icon(color=marker_color, icon=icon_name, prefix='fa'),
                    tooltip=f"DZ-{i+1:02d}: {severity} - {turn_angle:.1f}° turn - Speed: {speed_limit} km/h"
                ).add_to(m)

            # Add IOCL-style emergency facility markers
            facility_counts = {'medical': 0, 'police': 0, 'fuel': 0, 'pharmacy': 0, 'fire': 0}
            
            for poi in all_pois:
                lat, lng = poi['location']
                
                # Enhanced facility classification
                facility_type = classify_facility_type(poi['type'], poi.get('types', []))
                facility_counts[facility_type] += 1
                
                facility_popup = create_iocl_facility_popup(poi, facility_type, facility_counts[facility_type])
                
                # Facility-specific icons
                icon_config = get_facility_icon_config(facility_type)
                
                folium.Marker(
                    location=(lat, lng),
                    popup=folium.Popup(facility_popup, max_width=350),
                    icon=folium.Icon(**icon_config),
                    tooltip=f"{facility_type.title()} Facility: {poi['name']}"
                ).add_to(m)

            # Add enhanced IOCL start/end markers
            folium.Marker(
                source, 
                popup=folium.Popup(create_iocl_route_marker_popup('START', source, tt_specs, total_distance, total_duration), max_width=320),
                icon=folium.Icon(color='green', icon='play', prefix='fa', icon_size=(20, 20)),
                tooltip="🚛 IOCL Route Origin - Start Safety Protocols"
            ).add_to(m)
            
            folium.Marker(
                destination, 
                popup=folium.Popup(create_iocl_route_marker_popup('END', destination, tt_specs, total_distance, total_duration), max_width=320),
                icon=folium.Icon(color='blue', icon='stop', prefix='fa', icon_size=(20, 20)),
                tooltip="🏁 IOCL Route Destination - Complete Safety Checklist"
            ).add_to(m)

            # Add comprehensive IOCL route intelligence overlay
            intelligence_html = create_iocl_intelligence_overlay(tt_specs, sharp_turns, all_pois, total_distance, total_duration)
            m.get_root().html.add_child(folium.Element(intelligence_html))

            # Enhanced file saving with IOCL naming convention
            timestamp = int(time.time())
            unique_id = f"{username}_{timestamp}_{index}"
            html_filename = f"iocl_route_analysis_{unique_id}.html"
            
            templates_path = os.path.join(os.getcwd(), "templates")
            os.makedirs(templates_path, exist_ok=True)
            full_file_path = os.path.join(templates_path, html_filename)
            
            try:
                m.save(full_file_path)
                print(f"✅ IOCL map saved successfully: {full_file_path}")
                
                if os.path.exists(full_file_path) and os.path.getsize(full_file_path) > 1500:
                    print(f"✅ IOCL map verified: {os.path.getsize(full_file_path)} bytes")
                    html_file = html_filename
                else:
                    raise Exception(f"IOCL map verification failed: {full_file_path}")
                    
            except Exception as e:
                print(f"❌ IOCL map save error: {e}")
                html_file = create_iocl_fallback_map(coords, sharp_turns, all_pois, tt_specs, f"iocl_fallback_{timestamp}.html")
                
        except Exception as e:
            print(f"❌ IOCL map generation error: {e}")
            html_file = create_iocl_fallback_map(coords, sharp_turns, all_pois, tt_specs, f"iocl_error_{timestamp}.html")

        # Create comprehensive IOCL route report
        route_report = generate_iocl_route_report(
            coords, all_pois, sharp_turns, curves, total_distance, total_duration, tt_specs, location_mapping, html_file
        )

        # Store complete route report in session
        session['route_report'] = route_report
        session.modified = True

        # Calculate IOCL statistics for template
        critical_turns = len([t for t in sharp_turns if t['turn_angle'] >= 90])
        high_turns = len([t for t in sharp_turns if 65 <= t['turn_angle'] < 90])
        moderate_turns = len([t for t in sharp_turns if 45 <= t['turn_angle'] < 65])
        low_turns = len([t for t in sharp_turns if 25 <= t['turn_angle'] < 45])

        print(f"✅ IOCL analysis completed: {len(location_mapping['danger_zones'])} danger zones, {len(location_mapping['safety_facilities'])} facilities")

        # Use IOCL-style template
        return render_template("iocl_route_analysis.html",
                               mode="IOCL Professional GPS Analysis",
                               turns=len(sharp_turns) + len(curves),
                               poi_count=len(all_pois),
                               html_file=html_file,
                               route_report=route_report,
                               risk_zones=len(sharp_turns) + len(curves),
                               high_risk_zones=critical_turns + high_turns,
                               sharp_turns=sharp_turns,
                               curves=curves,
                               all_pois=all_pois,
                               critical_turns=critical_turns,
                               high_turns=high_turns,
                               moderate_turns=moderate_turns,
                               low_turns=low_turns,
                               tt_specs=tt_specs,
                               username=username,
                               location_mapping=location_mapping,
                               source=source,
                               destination=destination)

    except Exception as e:
        print(f"❌ Error in IOCL analyze_route: {e}")
        traceback.print_exc()
        return f"Error in IOCL route analysis: {str(e)}. Please try again."


# ===================================================================
# 2. ENHANCED DETAILED REPORT FUNCTION - IOCL FORMAT
# ===================================================================

@app.route('/detailed_report')
@login_required
def detailed_report():
    """Enhanced detailed report following IOCL PDF format"""
    try:
        # Get all session data
        route_report = session.get('route_report', {})
        tt_specs = session.get('tt_specs', {})
        sharp_turns = session.get('sharp_turns', [])
        curves = session.get('curves', [])
        all_pois = session.get('all_pois', [])
        username = session.get('username', 'User')
        location_mapping = session.get('location_mapping', {})
        
        if not route_report or not tt_specs:
            return redirect(url_for('home'))
        
        # Calculate comprehensive statistics
        critical_turns = len([t for t in sharp_turns if t['turn_angle'] >= 90])
        high_turns = len([t for t in sharp_turns if 65 <= t['turn_angle'] < 90])
        moderate_turns = len([t for t in sharp_turns if 45 <= t['turn_angle'] < 65])
        
        # Generate current timestamp for report
        current_timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        
        # Use IOCL official report template
        return render_template('iocl_official_report.html',
                               route_report=route_report,
                               tt_specs=tt_specs,
                               sharp_turns=sharp_turns,
                               curves=curves,
                               all_pois=all_pois,
                               critical_turns=critical_turns,
                               high_turns=high_turns,
                               moderate_turns=moderate_turns,
                               username=username,
                               current_timestamp=current_timestamp,
                               location_mapping=location_mapping)
                               
    except Exception as e:
        print(f"Error generating IOCL detailed report: {e}")
        return f"Error generating detailed report: {str(e)}"


# ===================================================================
# 3. ENHANCED VIEW MAP FUNCTION
# ===================================================================

@app.route('/view_map/<filename>')
def view_map(filename):
    """Enhanced map viewing with security and IOCL branding"""
    try:
        # Security check - only allow specific file patterns
        if not filename.endswith('.html') or '..' in filename or '/' in filename:
            return "Invalid file request", 400
        
        file_path = os.path.join("templates", filename)
        
        if not os.path.exists(file_path):
            return f"IOCL map file not found: {filename}", 404
        
        # Verify file size for security
        file_size = os.path.getsize(file_path)
        if file_size < 100 or file_size > 50 * 1024 * 1024:  # 100B to 50MB
            return "Invalid IOCL map file size", 400
        
        return send_from_directory("templates", filename)
        
    except Exception as e:
        print(f"Error serving IOCL map: {e}")
        return f"Error loading IOCL map: {str(e)}", 500


# ===================================================================
# 4. ENHANCED AI CHAT FUNCTION - IOCL CONTEXT
# ===================================================================

@app.route('/ai_chat', methods=['POST'])
@login_required  
def ai_chat():
    """Enhanced AI chat with IOCL route analysis context"""
    try:
        data = request.get_json()
        question = data.get('question', '').strip()
        
        if not question:
            return jsonify({'status': 'error', 'error': 'Please enter a question'})
        
        # Get IOCL route context from session
        route_report = session.get('route_report', {})
        tt_specs = session.get('tt_specs', {})
        sharp_turns = session.get('sharp_turns', [])
        all_pois = session.get('all_pois', [])
        username = session.get('username', 'User')
        
        # Build comprehensive IOCL context
        context_parts = [
            f"🛡️ IOCL ROUTE ANALYSIS CONTEXT for {username}:",
            f"Vehicle: {tt_specs.get('capacity_range', 'Unknown')} petroleum tanker truck",
            f"Route Distance: {route_report.get('total_distance', 'N/A')}",
            f"Route Duration: {route_report.get('total_duration', 'N/A')}",
            f"Total Hazard Zones: {len(sharp_turns)}",
            f"Emergency Facilities: {len(all_pois)}",
            ""
        ]
        
        # Add critical hazards to context
        critical_hazards = [t for t in sharp_turns if t['turn_angle'] >= 90]
        if critical_hazards:
            context_parts.append(f"⚠️ CRITICAL HAZARDS ({len(critical_hazards)}):")
            for i, hazard in enumerate(critical_hazards[:3]):  # Top 3 critical
                context_parts.append(f"• DZ-{i+1}: {hazard['turn_angle']:.1f}° {hazard['direction']} turn - Speed limit: 10-15 km/h")
        
        # Add vehicle specifications
        context_parts.extend([
            "",
            f"🚛 VEHICLE SPECIFICATIONS:",
            f"• Tank Capacity: {tt_specs.get('avg_capacity_liters', 0):,} liters",
            f"• Gross Weight: {tt_specs.get('gross_weight', 0)/1000:.1f} tonnes",
            f"• Max Legal Speed: {tt_specs.get('max_speed', 50)} km/h",
            f"• Risk Multiplier: {tt_specs.get('risk_multiplier', 1)}x",
            ""
        ])
        
        # Add safety protocols
        context_parts.extend([
            "🛡️ IOCL SAFETY PROTOCOLS:",
            "• Speed reduction mandatory at hazard zones", 
            "• Engine braking on all turns and descents",
            "• Continuous liquid surge monitoring",
            "• Emergency communication every 30 minutes",
            "• 6-second following distance maintenance",
            "",
            f"❓ USER QUESTION: {question}"
        ])
        
        full_context = "\n".join(context_parts)
        
        # Generate AI response (replace with your AI service)
        try:
            ai_answer = generate_iocl_ai_response(question, context_parts, critical_hazards, tt_specs, all_pois)
            
            # Enhance response with IOCL branding
            enhanced_answer = f"🛡️ **IOCL Safety Assistant Response:**\n\n{ai_answer}\n\n---\n*Based on IOCL petroleum transport safety standards and current route analysis data.*"
            
            return jsonify({
                'status': 'success', 
                'answer': enhanced_answer,
                'context_used': 'IOCL Route Analysis Data',
                'timestamp': datetime.now().isoformat()
            })
            
        except Exception as ai_error:
            print(f"AI service error: {ai_error}")
            
            # IOCL fallback responses
            fallback_responses = {
                'hazard': f"⚠️ **Route Hazard Summary:**\n\n• **Critical Zones:** {len(critical_hazards)} requiring 10-15 km/h speed\n• **Total Hazards:** {len(sharp_turns)} identified zones\n• **Safety Protocol:** Engine braking mandatory, monitor liquid surge\n• **Emergency Contacts:** Fire-101, Police-100, Medical-108",
                'speed': f"🚛 **IOCL Speed Recommendations:**\n\n• **Maximum Legal Speed:** {tt_specs.get('max_speed', 50)} km/h\n• **Critical Zones:** 10-15 km/h maximum\n• **High Risk Zones:** 18-25 km/h maximum\n• **Vehicle Weight:** {tt_specs.get('gross_weight', 0)/1000:.1f}T affects braking\n• **Following Distance:** Maintain 6 seconds minimum",
                'emergency': f"🏥 **Emergency Infrastructure:**\n\n• **Medical Facilities:** {len([p for p in all_pois if 'hospital' in p['type'].lower()])} hospitals available\n• **Police Stations:** {len([p for p in all_pois if 'police' in p['type'].lower()])} law enforcement\n• **Fuel Stations:** {len([p for p in all_pois if 'fuel' in p['type'].lower()])} refueling points\n• **Emergency Numbers:** 101-Fire, 100-Police, 108-Medical",
                'safety': f"📋 **IOCL Safety Checklist:**\n\n• Pre-departure inspection complete\n• Fire suppression system operational\n• Emergency equipment verified\n• Route authorization confirmed\n• Weather conditions acceptable\n• Communication protocols established\n• Load securement verified\n• ADR documentation current"
            }
            
            # Determine appropriate fallback based on question keywords
            question_lower = question.lower()
            if any(word in question_lower for word in ['hazard', 'danger', 'risk', 'turn']):
                fallback_answer = fallback_responses['hazard']
            elif any(word in question_lower for word in ['speed', 'limit', 'fast', 'slow']):
                fallback_answer = fallback_responses['speed'] 
            elif any(word in question_lower for word in ['emergency', 'hospital', 'police', 'help']):
                fallback_answer = fallback_responses['emergency']
            elif any(word in question_lower for word in ['safety', 'checklist', 'protocol', 'procedure']):
                fallback_answer = fallback_responses['safety']
            else:
                fallback_answer = "🛡️ **IOCL Safety Assistant:**\n\nI can help you with route hazards, speed recommendations, emergency facilities, and safety protocols. Please specify your question about the current route analysis."
            
            return jsonify({
                'status': 'success',
                'answer': fallback_answer,
                'context_used': 'IOCL Fallback Response',
                'note': 'AI service temporarily unavailable - using IOCL knowledge base'
            })
            
    except Exception as e:
        print(f"Error in IOCL AI chat: {e}")
        return jsonify({
            'status': 'error',
            'error': 'IOCL Safety Assistant temporarily unavailable. Please refer to the route analysis data above.',
            'fallback_contact': 'Emergency: 101-Fire, 100-Police, 108-Medical'
        })


# ===================================================================
# 5. ADDITIONAL ENHANCED ROUTES
# ===================================================================

@app.route('/safety_briefing')
@login_required
def safety_briefing():
    """Generate IOCL safety briefing based on route analysis"""
    try:
        route_report = session.get('route_report', {})
        tt_specs = session.get('tt_specs', {})
        
        if route_report and tt_specs:
            return jsonify({'status': 'success', 'briefing_available': True})
        else:
            return jsonify({'status': 'error', 'message': 'No route analysis available'})
            
    except Exception as e:
        return jsonify({'status': 'error', 'message': str(e)})

@app.route('/export_route_data')
@login_required
def export_route_data():
    """Export IOCL route analysis data in JSON format"""
    try:
        export_data = {
            'route_report': session.get('route_report', {}),
            'tt_specs': session.get('tt_specs', {}),
            'location_mapping': session.get('location_mapping', {}),
            'export_timestamp': datetime.now().isoformat(),
            'analysis_standard': 'IOCL Professional GPS Analysis v2.0',
            'format_version': '2.0'
        }
        
        return jsonify(export_data)
        
    except Exception as e:
        return jsonify({'error': str(e)}), 500

@app.route('/route_summary_api')
@login_required 
def route_summary_api():
    """API endpoint for IOCL route summary data"""
    try:
        route_report = session.get('route_report', {})
        sharp_turns = session.get('sharp_turns', [])
        tt_specs = session.get('tt_specs', {})
        
        summary = {
            'route_distance': route_report.get('total_distance', 'N/A'),
            'route_duration': route_report.get('total_duration', 'N/A'), 
            'critical_hazards': len([t for t in sharp_turns if t['turn_angle'] >= 90]),
            'total_hazards': len(sharp_turns),
            'vehicle_type': tt_specs.get('capacity_range', 'Unknown'),
            'max_speed': tt_specs.get('max_speed', 50),
            'gross_weight': f"{tt_specs.get('gross_weight', 0)/1000:.1f}T",
            'analysis_timestamp': datetime.now().isoformat(),
            'status': 'success'
        }
        
        return jsonify(summary)
        
    except Exception as e:
        return jsonify({'status': 'error', 'message': str(e)}), 500
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





















