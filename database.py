import sqlite3
import os
from datetime import datetime

DB_PATH = os.environ.get('DATABASE_PATH', 'route_maps.db')

def init_database():
    """Initialize the route maps database"""
    # Ensure directory exists (important for /data path on Render)
    db_dir = os.path.dirname(DB_PATH)
    if db_dir and not os.path.exists(db_dir):
        os.makedirs(db_dir, exist_ok=True)
    
    conn = sqlite3.connect(DB_PATH)
    cursor = conn.cursor()
    
    # Create table for storing SAP code to map relationships
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
    
    # Create index on sap_code for fast lookups
    cursor.execute('''
        CREATE INDEX IF NOT EXISTS idx_sap_code 
        ON route_maps(sap_code)
    ''')
    
    conn.commit()
    conn.close()
    
    print(f"✅ Database initialized successfully at: {DB_PATH}")

def save_route_map(data):
    """
    Save route map information
    FIXED: Handles both new routes and updates to existing/deleted routes
    """
    conn = sqlite3.connect(DB_PATH)
    cursor = conn.cursor()
    
    try:
        # Check if route exists (including deleted ones)
        cursor.execute('''
            SELECT id, status FROM route_maps WHERE sap_code = ?
        ''', (data['sap_code'],))
        
        existing = cursor.fetchone()
        
        if existing:
            # Route exists (either active or deleted) - UPDATE it
            cursor.execute('''
                UPDATE route_maps SET
                    terminal_name = ?,
                    terminal_coords = ?,
                    consignee_name = ?,
                    consignee_coords = ?,
                    tt_type = ?,
                    tt_capacity = ?,
                    route_distance = ?,
                    route_duration = ?,
                    map_file = ?,
                    created_date = ?,
                    created_by = ?,
                    status = 'active'
                WHERE sap_code = ?
            ''', (
                data['terminal_name'],
                data['terminal_coords'],
                data['consignee_name'],
                data['consignee_coords'],
                data['tt_type'],
                data['tt_capacity'],
                data.get('route_distance', ''),
                data.get('route_duration', ''),
                data['map_file'],
                datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                data.get('created_by', 'Terminal Operator'),
                data['sap_code']
            ))
            conn.commit()
            return True, "Route map updated successfully"
        else:
            # New route - INSERT
            cursor.execute('''
                INSERT INTO route_maps (
                    sap_code, terminal_name, terminal_coords,
                    consignee_name, consignee_coords, tt_type, tt_capacity,
                    route_distance, route_duration, map_file,
                    created_date, created_by
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ''', (
                data['sap_code'],
                data['terminal_name'],
                data['terminal_coords'],
                data['consignee_name'],
                data['consignee_coords'],
                data['tt_type'],
                data['tt_capacity'],
                data.get('route_distance', ''),
                data.get('route_duration', ''),
                data['map_file'],
                datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                data.get('created_by', 'Terminal Operator')
            ))
            conn.commit()
            return True, "Route map saved successfully"
            
    except Exception as e:
        print(f"❌ Database error: {e}")
        return False, f"Error saving map: {str(e)}"
    finally:
        conn.close()

def get_route_map_by_sap(sap_code):
    """Retrieve route map by SAP code - handles both integer and float formats"""
    conn = sqlite3.connect(DB_PATH)
    cursor = conn.cursor()
    
    # Clean the SAP code input
    sap_clean = str(sap_code).strip()
    if '.' in sap_clean:
        try:
            sap_clean = str(int(float(sap_clean)))
        except:
            pass
    
    # Try exact match first
    cursor.execute('''
        SELECT * FROM route_maps 
        WHERE sap_code = ? AND status = 'active'
    ''', (sap_clean,))
    
    row = cursor.fetchone()
    
    # If not found and input doesn't have decimal, try with .0
    if not row and '.' not in sap_code:
        cursor.execute('''
            SELECT * FROM route_maps 
            WHERE sap_code = ? AND status = 'active'
        ''', (sap_clean + '.0',))
        row = cursor.fetchone()
    
    # If not found and input has decimal, try without decimal
    if not row and '.' in str(sap_code):
        try:
            sap_without_decimal = str(int(float(sap_code)))
            cursor.execute('''
                SELECT * FROM route_maps 
                WHERE sap_code = ? AND status = 'active'
            ''', (sap_without_decimal,))
            row = cursor.fetchone()
        except:
            pass
    
    conn.close()
    
    if row:
        columns = [desc[0] for desc in cursor.description]
        return dict(zip(columns, row))
    return None

def get_all_route_maps(limit=50):
    """Get all active route maps ordered by creation date"""
    conn = sqlite3.connect(DB_PATH)
    cursor = conn.cursor()
    
    cursor.execute('''
        SELECT * FROM route_maps 
        WHERE status = 'active'
        ORDER BY created_date DESC 
        LIMIT ?
    ''', (limit,))
    
    rows = cursor.fetchall()
    conn.close()
    
    if rows:
        columns = [desc[0] for desc in cursor.description]
        return [dict(zip(columns, row)) for row in rows]
    return []

def delete_route_map(sap_code):
    """
    Soft delete a route map
    FIXED: Now properly handles re-saving after delete
    """
    conn = sqlite3.connect(DB_PATH)
    cursor = conn.cursor()
    
    try:
        # Clean SAP code
        sap_clean = str(sap_code).strip()
        if '.' in sap_clean:
            try:
                sap_clean = str(int(float(sap_clean)))
            except:
                pass
        
        cursor.execute('''
            UPDATE route_maps 
            SET status = 'deleted' 
            WHERE sap_code = ?
        ''', (sap_clean,))
        
        conn.commit()
        
        if cursor.rowcount > 0:
            return True, "Route map deleted successfully"
        else:
            return False, "Route map not found"
    except Exception as e:
        return False, f"Error deleting map: {str(e)}"
    finally:
        conn.close()

def get_database_stats():
    """Get database statistics - useful for debugging"""
    conn = sqlite3.connect(DB_PATH)
    cursor = conn.cursor()
    
    try:
        # Total routes
        cursor.execute('SELECT COUNT(*) FROM route_maps WHERE status = "active"')
        active_count = cursor.fetchone()[0]
        
        cursor.execute('SELECT COUNT(*) FROM route_maps WHERE status = "deleted"')
        deleted_count = cursor.fetchone()[0]
        
        cursor.execute('SELECT COUNT(*) FROM route_maps')
        total_count = cursor.fetchone()[0]
        
        return {
            'active': active_count,
            'deleted': deleted_count,
            'total': total_count,
            'db_path': DB_PATH,
            'db_exists': os.path.exists(DB_PATH),
            'db_size': os.path.getsize(DB_PATH) if os.path.exists(DB_PATH) else 0
        }
    except Exception as e:
        return {'error': str(e)}
    finally:
        conn.close()

if __name__ == '__main__':
    # Initialize database when run directly
    init_database()
    
    # Print stats
    stats = get_database_stats()
    print("\n📊 Database Statistics:")
    print(f"  Location: {stats.get('db_path')}")
    print(f"  Exists: {stats.get('db_exists')}")
    print(f"  Size: {stats.get('db_size', 0) / 1024:.2f} KB")
    print(f"  Active Routes: {stats.get('active', 0)}")
    print(f"  Deleted Routes: {stats.get('deleted', 0)}")
    print(f"  Total Routes: {stats.get('total', 0)}")
