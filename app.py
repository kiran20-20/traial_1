from flask import Flask, render_template, request, session, redirect, url_for, send_from_directory, make_response
import googlemaps
import polyline
import folium
from datetime import datetime
from flask_session import Session
from branca.element import Template, MacroElement
import os
import pandas as pd
import json
import glob
from uuid import uuid4

app = Flask(__name__)
app.secret_key = 'your_secret_key_here'
app.config['SESSION_TYPE'] = 'filesystem'
Session(app)

API_KEY = os.environ.get("API_KEY")  # Secure access
gmaps = googlemaps.Client(key=API_KEY)

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
    # 🔁 Clear session and old route files
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
    session.modified = True  # Ensure session is saved

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

    def get_pois(keyword):
        pois = []
        for lat, lng in coords[::15]:
            try:
                places = gmaps.places_nearby(location=(lat, lng), radius=200, keyword=keyword)
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

    m = folium.Map(location=source, zoom_start=13)
    folium.Marker(source, popup='Start', icon=folium.Icon(color='green', icon='flag', prefix='fa')).add_to(m)
    folium.Marker(destination, popup='End', icon=folium.Icon(color='black', icon='flag-checkered', prefix='fa')).add_to(m)
    folium.PolyLine(coords, color='blue', weight=5).add_to(m)

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

    for step in steps:
        instruction = step['html_instructions']
        lat = step['end_location']['lat']
        lng = step['end_location']['lng']
        angle_est = round(step['distance']['value'] / 100, 1)

        if "blind" in instruction.lower():
            icon_type = 'exclamation-triangle'
            color = 'red'
            title = "⚠️ Blind Spot Warning"
        elif "left" in instruction.lower():
            icon_type = 'arrow-left'
            color = 'blue'
            title = "Turn Left"
        elif "right" in instruction.lower():
            icon_type = 'arrow-right'
            color = 'green'
            title = "Turn Right"
        elif "u-turn" in instruction.lower():
            icon_type = 'undo'
            color = 'purple'
            title = "U-turn"
        else:
            icon_type = 'arrow-up'
            color = 'gray'
            title = "Go Straight"

        popup_html = f"""
        <div style='font-family:Arial; font-size:13px'>
            <b>{title}</b><br>
            {instruction}<br>
            <i>Estimated angle: {angle_est}°</i>
        </div>
        """
        icon = folium.Icon(color=color, icon=icon_type, prefix='fa')
        folium.Marker(
            location=(lat, lng),
            popup=popup_html,
            icon=icon
        ).add_to(m)

    legend_html = """
    {% macro html(this, kwargs) %}
    <div style="
        position: fixed;
        bottom: 50px;
        left: 50px;
        width: 220px;
        background-color: white;
        border: 2px solid grey;
        border-radius: 5px;
        z-index: 9999;
        padding: 10px;
        font-size: 14px;
    ">
        <h4>Legend</h4>
        <div><i class="fa fa-plus fa-lg" style="color:red"></i> Hospital</div>
        <div><i class="fa fa-shield fa-lg" style="color:blue"></i> Police</div>
        <div><i class="fa fa-gas-pump fa-lg" style="color:orange"></i> Fuel</div>
        <div><i class="fa fa-arrow-left fa-lg" style="color:blue"></i> Left Turn</div>
        <div><i class="fa fa-arrow-right fa-lg" style="color:green"></i> Right Turn</div>
        <div><i class="fa fa-undo fa-lg" style="color:purple"></i> U-turn</div>
        <div><i class="fa fa-exclamation-triangle fa-lg" style="color:red"></i> Blind Spot</div>
        <div><i class="fa fa-flag fa-lg" style="color:green"></i> Start</div>
        <div><i class="fa fa-flag-checkered fa-lg" style="color:black"></i> End</div>
    </div>
    {% endmacro %}
    """
    legend = MacroElement()
    legend._template = Template(legend_html)
    m.get_root().add_child(legend)

    unique_map_id = uuid4().hex
    html_name = f"route_map_{unique_map_id}.html"
    m.save(f"templates/{html_name}")

    return render_template("route_analysis.html",
                           mode=session['vehicle'],
                           turns=sum("turn" in s['html_instructions'].lower() for s in steps),
                           poi_count=len(all_pois),
                           html_file=html_name)

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
