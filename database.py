import sqlite3
from datetime import datetime

def init_database():
    db_path = 'route_maps.db'
    conn = sqlite3.connect(db_path)
    cursor = conn.cursor()
    
    cursor.execute('''
        CREATE TABLE IF NOT EXISTS route_maps (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            sap_code TEXT UNIQUE NOT NULL,
            terminal_name TEXT NOT NULL,
            terminal_coords TEXT NOT NULL,
            consignee_name TEXT NOT NULL,
            consignee_coords TEXT NOT NULL,
            tt_type TEXT NOT NULL,
            tt_capacity INTEGER NOT NULL,
            route_distance TEXT,
            route_duration TEXT,
            map_file TEXT NOT NULL,
            created_date TEXT NOT NULL,
            created_by TEXT NOT NULL,
            status TEXT DEFAULT 'active'
        )
    ''')
    
    cursor.execute('''
        CREATE INDEX IF NOT EXISTS idx_sap_code 
        ON route_maps(sap_code)
    ''')
    
    conn.commit()
    conn.close()
    print("✅ Database initialized")

def save_route_map(data):
    conn = sqlite3.connect('route_maps.db')
    cursor = conn.cursor()
    
    try:
        cursor.execute('''
            INSERT INTO route_maps (
                sap_code, terminal_name, terminal_coords,
                consignee_name, consignee_coords, tt_type, tt_capacity,
                route_distance, route_duration, map_file,
                created_date, created_by
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        ''', (
            data['sap_code'], data['terminal_name'], data['terminal_coords'],
            data['consignee_name'], data['consignee_coords'], data['tt_type'],
            data['tt_capacity'], data.get('route_distance', ''),
            data.get('route_duration', ''), data['map_file'],
            datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
            data.get('created_by', 'Terminal Operator')
        ))
        conn.commit()
        return True, "Map saved"
    except sqlite3.IntegrityError:
        return False, "SAP code exists"
    except Exception as e:
        return False, str(e)
    finally:
        conn.close()

def get_route_map_by_sap(sap_code):
    conn = sqlite3.connect('route_maps.db')
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM route_maps WHERE sap_code = ? AND status = "active"', (sap_code,))
    row = cursor.fetchone()
    conn.close()
    
    if row:
        columns = [d[0] for d in cursor.description]
        return dict(zip(columns, row))
    return None

def get_all_route_maps(limit=50):
    conn = sqlite3.connect('route_maps.db')
    cursor = conn.cursor()
    cursor.execute('SELECT * FROM route_maps WHERE status = "active" ORDER BY created_date DESC LIMIT ?', (limit,))
    rows = cursor.fetchall()
    conn.close()
    
    if rows:
        columns = [d[0] for d in cursor.description]
        return [dict(zip(columns, row)) for row in rows]
    return []

if __name__ == '__main__':
    init_database()
