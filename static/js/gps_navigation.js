<!-- Add this JavaScript file as static/js/gps_navigation.js -->
<!DOCTYPE html>
<html>
<head>
    <title>GPS Navigation Integration</title>
    <script>
// GPS Navigation System for Truck Tanker Navigation
class GPSTruckNavigation {
    constructor(routeCoords, sharpTurns, curves, ttSpecs, allPois) {
        this.routeCoords = routeCoords;
        this.sharpTurns = sharpTurns;
        this.curves = curves;
        this.ttSpecs = ttSpecs;
        this.allPois = allPois;
        
        // GPS tracking variables
        this.watchId = null;
        this.currentGPSPosition = null;
        this.isTracking = false;
        this.lastAnnouncedHazard = null;
        this.routeProgress = 0;
        
        // Voice synthesis
        this.speechSynthesis = window.speechSynthesis;
        this.voiceEnabled = true;
        
        // Distance thresholds (in meters)
        this.CRITICAL_ALERT_DISTANCE = 200;  // 200m before critical hazard
        this.WARNING_DISTANCE = 500;         // 500m before hazard
        this.INFO_DISTANCE = 1000;           // 1km for general info
        this.ROUTE_DEVIATION_THRESHOLD = 50; // 50m off route
        
        // Tracking variables
        this.lastHazardIndex = -1;
        this.currentSpeed = 0;
        this.isOffRoute = false;
        
        this.initGPSTracking();
    }
    
    initGPSTracking() {
        if (!navigator.geolocation) {
            this.showError("GPS not supported on this device");
            return;
        }
        
        // Request high accuracy GPS
        this.gpsOptions = {
            enableHighAccuracy: true,
            timeout: 10000,
            maximumAge: 1000
        };
        
        // Add GPS status display
        this.addGPSStatusDisplay();
    }
    
    startGPSTracking() {
        if (this.isTracking) return;
        
        this.showStatus("Starting GPS tracking...", "info");
        
        this.watchId = navigator.geolocation.watchPosition(
            (position) => this.handleGPSUpdate(position),
            (error) => this.handleGPSError(error),
            this.gpsOptions
        );
        
        this.isTracking = true;
        
        // Initial announcement
        this.speak(`GPS navigation started for ${this.ttSpecs.capacity_range} tanker. 
                   Route analysis active with ${this.sharpTurns.length} sharp turns detected. Drive safely.`, 'normal');
    }
    
    stopGPSTracking() {
        if (!this.isTracking) return;
        
        if (this.watchId) {
            navigator.geolocation.clearWatch(this.watchId);
            this.watchId = null;
        }
        
        this.isTracking = false;
        this.showStatus("GPS tracking stopped", "info");
        this.speak("GPS navigation stopped", 'normal');
    }
    
    handleGPSUpdate(position) {
        this.currentGPSPosition = {
            lat: position.coords.latitude,
            lng: position.coords.longitude,
            accuracy: position.coords.accuracy,
            speed: position.coords.speed || 0, // m/s
            heading: position.coords.heading || 0,
            timestamp: position.timestamp
        };
        
        // Convert speed to km/h
        this.currentSpeed = (this.currentGPSPosition.speed * 3.6) || 0;
        
        // Update display
        this.updateGPSDisplay();
        
        // Check route position and hazards
        this.analyzeCurrentPosition();
        
        // Send position to server for logging
        this.reportPositionToServer();
    }
    
    handleGPSError(error) {
        let errorMsg = "GPS error: ";
        switch(error.code) {
            case error.PERMISSION_DENIED:
                errorMsg += "Location access denied. Please enable GPS permissions.";
                break;
            case error.POSITION_UNAVAILABLE:
                errorMsg += "Location unavailable. Check GPS signal.";
                break;
            case error.TIMEOUT:
                errorMsg += "GPS timeout. Retrying...";
                break;
            default:
                errorMsg += "Unknown GPS error.";
        }
        
        this.showError(errorMsg);
        console.error("GPS Error:", error);
    }
    
    analyzeCurrentPosition() {
        if (!this.currentGPSPosition) return;
        
        const currentPos = [this.currentGPSPosition.lat, this.currentGPSPosition.lng];
        
        // Find closest point on route
        const routeInfo = this.findClosestRoutePoint(currentPos);
        
        if (!routeInfo) return;
        
        // Check if off route
        if (routeInfo.distance > this.ROUTE_DEVIATION_THRESHOLD) {
            this.handleOffRoute(routeInfo.distance);
        } else {
            this.isOffRoute = false;
            this.analyzeUpcomingHazards(routeInfo.index, currentPos);
            this.checkNearbyPOIs(currentPos);
            this.monitorSpeed(routeInfo.index);
        }
        
        // Update progress
        this.routeProgress = (routeInfo.index / this.routeCoords.length) * 100;
    }
    
    findClosestRoutePoint(currentPos) {
        let closestIndex = 0;
        let minDistance = Infinity;
        
        for (let i = 0; i < this.routeCoords.length; i++) {
            const distance = this.calculateDistance(currentPos, this.routeCoords[i]);
            if (distance < minDistance) {
                minDistance = distance;
                closestIndex = i;
            }
        }
        
        return {
            index: closestIndex,
            distance: minDistance,
            routePoint: this.routeCoords[closestIndex]
        };
    }
    
    analyzeUpcomingHazards(currentRouteIndex, currentPos) {
        // Check for sharp turns ahead
        for (const turn of this.sharpTurns) {
            if (turn.index <= currentRouteIndex) continue; // Already passed
            
            const distanceToTurn = this.calculateDistance(currentPos, turn.location);
            const hazardKey = `turn_${turn.index}`;
            
            if (distanceToTurn <= this.CRITICAL_ALERT_DISTANCE && 
                this.lastAnnouncedHazard !== hazardKey) {
                
                this.announceCriticalTurn(turn, distanceToTurn);
                this.lastAnnouncedHazard = hazardKey;
                
            } else if (distanceToTurn <= this.WARNING_DISTANCE && 
                      this.lastAnnouncedHazard !== `warning_${hazardKey}`) {
                
                this.announceUpcomingTurn(turn, distanceToTurn);
                this.lastAnnouncedHazard = `warning_${hazardKey}`;
            }
        }
        
        // Check for curves ahead
        for (const curve of this.curves) {
            if (curve.index <= currentRouteIndex) continue;
            
            const distanceToCurve = this.calculateDistance(currentPos, curve.location);
            const hazardKey = `curve_${curve.index}`;
            
            if (distanceToCurve <= this.WARNING_DISTANCE && 
                this.lastAnnouncedHazard !== hazardKey) {
                
                this.announceCurve(curve, distanceToCurve);
                this.lastAnnouncedHazard = hazardKey;
            }
        }
    }
    
    announceCriticalTurn(turn, distance) {
        const recommendedSpeed = this.getRecommendedSpeed(turn.turn_angle, 'sharp_turn');
        const distanceText = distance < 100 ? 
            `${Math.round(distance)} meters` : 
            `${(distance/1000).toFixed(1)} kilometers`;
        
        const message = `CRITICAL ALERT! Sharp ${turn.direction} turn ahead in ${distanceText}. 
                        ${turn.turn_angle.toFixed(0)} degree turn. 
                        Reduce speed to ${recommendedSpeed} kilometers per hour immediately. 
                        High rollover risk for loaded tanker.`;
        
        this.speak(message, 'critical');
        this.showHazardAlert(turn, distance, 'critical');
        
        // Visual alert
        this.flashScreen('red');
    }
    
    announceUpcomingTurn(turn, distance) {
        const distanceText = `${(distance/1000).toFixed(1)} kilometers`;
        const message = `Sharp ${turn.direction} turn approaching in ${distanceText}. 
                        Prepare to reduce speed for ${turn.severity} severity turn.`;
        
        this.speak(message, 'warning');
        this.showHazardAlert(turn, distance, 'warning');
    }
    
    announceCurve(curve, distance) {
        const recommendedSpeed = this.getRecommendedSpeed(curve.turn_angle, 'curve');
        const message = `Curve ahead. Reduce speed to ${recommendedSpeed} kilometers per hour 
                        for ${curve.turn_angle.toFixed(0)} degree ${curve.direction} curve.`;
        
        this.speak(message, 'normal');
    }
    
    checkNearbyPOIs(currentPos) {
        for (const poi of this.allPois) {
            const distance = this.calculateDistance(currentPos, poi.location);
            
            if (distance <= 1000 && !poi.announced) { // Within 1km
                let message = "";
                
                switch(poi.type) {
                    case 'hospital':
                        message = `Hospital nearby: ${poi.name}. Emergency medical facility available.`;
                        break;
                    case 'police':
                        message = `Police station nearby: ${poi.name}. Law enforcement available.`;
                        break;
                    case 'fuel':
                        message = `Fuel station nearby: ${poi.name}. Check tanker fueling restrictions.`;
                        break;
                }
                
                if (message) {
                    this.speak(message, 'info');
                    poi.announced = true; // Prevent repeated announcements
                }
            }
        }
    }
    
    monitorSpeed(routeIndex) {
        // Get current hazard level at this position
        const hazardLevel = this.getHazardLevelAtPosition(routeIndex);
        const recommendedSpeed = this.getContextualSpeedLimit(hazardLevel);
        
        if (this.currentSpeed > recommendedSpeed + 10) { // 10 km/h tolerance
            const message = `Speed alert! Current speed ${Math.round(this.currentSpeed)} kilometers per hour. 
                           Recommended maximum ${recommendedSpeed} for loaded ${this.ttSpecs.capacity_range} tanker.`;
            this.speak(message, 'urgent');
        }
    }
    
    handleOffRoute(distance) {
        if (!this.isOffRoute && distance > this.ROUTE_DEVIATION_THRESHOLD) {
            this.isOffRoute = true;
            const message = `Route deviation detected. You are ${Math.round(distance)} meters off the analyzed route. 
                           Return to planned route for safety analysis coverage.`;
            this.speak(message, 'warning');
            this.showStatus("OFF ROUTE - Return to planned path", "error");
        }
    }
    
    getRecommendedSpeed(angle, hazardType) {
        const baseSensitivity = this.ttSpecs.turn_sensitivity || 1.0;
        
        if (hazardType === 'sharp_turn') {
            if (angle > 120) return Math.max(8, Math.round(12 / baseSensitivity));
            if (angle > 90) return Math.max(12, Math.round(18 / baseSensitivity));
        } else if (hazardType === 'curve') {
            return Math.max(25, Math.round(35 / baseSensitivity));
        }
        
        return Math.min(this.ttSpecs.max_speed || 50, 45);
    }
    
    getHazardLevelAtPosition(routeIndex) {
        // Check if current position has hazards
        for (const turn of this.sharpTurns) {
            if (Math.abs(turn.index - routeIndex) <= 5) {
                return turn.severity === 'critical' ? 'critical' : 'high';
            }
        }
        
        for (const curve of this.curves) {
            if (Math.abs(curve.index - routeIndex) <= 3) {
                return 'moderate';
            }
        }
        
        return 'normal';
    }
    
    getContextualSpeedLimit(hazardLevel) {
        const maxSpeed = this.ttSpecs.max_speed || 50;
        
        switch(hazardLevel) {
            case 'critical': return 15;
            case 'high': return 25;
            case 'moderate': return 35;
            default: return maxSpeed;
        }
    }
    
    calculateDistance(pos1, pos2) {
        const R = 6371000; // Earth radius in meters
        const lat1 = pos1[0] * Math.PI / 180;
        const lat2 = pos2[0] * Math.PI / 180;
        const deltaLat = (pos2[0] - pos1[0]) * Math.PI / 180;
        const deltaLng = (pos2[1] - pos1[1]) * Math.PI / 180;
        
        const a = Math.sin(deltaLat/2) * Math.sin(deltaLat/2) +
                 Math.cos(lat1) * Math.cos(lat2) *
                 Math.sin(deltaLng/2) * Math.sin(deltaLng/2);
        const c = 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1-a));
        
        return R * c;
    }
    
    speak(message, priority = 'normal') {
        if (!this.voiceEnabled || !this.speechSynthesis) return;
        
        // Cancel previous speech for urgent messages
        if (priority === 'critical' || priority === 'urgent') {
            this.speechSynthesis.cancel();
        }
        
        const utterance = new SpeechSynthesisUtterance(message);
        utterance.rate = priority === 'critical' ? 0.8 : 1.0;
        utterance.volume = priority === 'critical' ? 1.0 : 0.8;
        
        this.speechSynthesis.speak(utterance);
        
        // Log to console
        console.log(`GPS Voice [${priority}]: ${message}`);
    }
    
    reportPositionToServer() {
        if (!this.currentGPSPosition) return;
        
        // Send position data to Flask server
        fetch('/report_gps_position', {
            method: 'POST',
            headers: {
                'Content-Type': 'application/json',
            },
            body: JSON.stringify({
                latitude: this.currentGPSPosition.lat,
                longitude: this.currentGPSPosition.lng,
                accuracy: this.currentGPSPosition.accuracy,
                speed: this.currentSpeed,
                timestamp: this.currentGPSPosition.timestamp
            })
        })
        .catch(error => console.error('Error reporting position:', error));
    }
    
    // UI Helper Methods
    addGPSStatusDisplay() {
        // This will be displayed in the existing control panel
        // GPS status updates will be shown in the main control panel
    }
    
    updateGPSDisplay() {
        if (!this.currentGPSPosition) return;
        
        const statusElement = document.getElementById('gps-status');
        if (statusElement) {
            const pos = this.currentGPSPosition;
            statusElement.innerHTML = `GPS: Active (±${Math.round(pos.accuracy)}m) | Speed: ${Math.round(this.currentSpeed)} km/h | Progress: ${this.routeProgress.toFixed(1)}%`;
            statusElement.style.background = pos.accuracy < 20 ? '#d4edda' : '#fff3cd';
            statusElement.style.color = pos.accuracy < 20 ? '#155724' : '#856404';
        }
    }
    
    showHazardAlert(hazard, distance, severity) {
        const progressElement = document.getElementById('progress-display');
        if (progressElement) {
            const alertColor = severity === 'critical' ? '#ff4444' : 
                              severity === 'warning' ? '#ff8800' : '#ffaa00';
            
            progressElement.innerHTML = `
                <div style="background: ${alertColor}; color: white; padding: 8px; border-radius: 4px; font-weight: bold;">
                    ${severity.toUpperCase()}: ${hazard.turn_angle.toFixed(0)}° ${hazard.direction} turn in ${Math.round(distance)}m
                </div>
            `;
        }
    }
    
    showStatus(message, type) {
        const statusElement = document.getElementById('gps-status');
        if (statusElement) {
            statusElement.innerHTML = message;
            
            const colors = {
                'info': '#d1ecf1',
                'error': '#f8d7da',
                'success': '#d4edda'
            };
            
            statusElement.style.background = colors[type] || '#f0f0f0';
        }
    }
    
    showError(message) {
        this.showStatus(message, 'error');
        console.error("GPS Navigation Error:", message);
    }
    
    flashScreen(color) {
        // Create flash overlay
        const flash = document.createElement('div');
        flash.style.cssText = `
            position: fixed; top: 0; left: 0; width: 100%; height: 100%;
            background: ${color}; opacity: 0.3; z-index: 9999;
            pointer-events: none;
        `;
        
        document.body.appendChild(flash);
        
        setTimeout(() => {
            flash.style.opacity = '0';
            setTimeout(() => document.body.removeChild(flash), 300);
        }, 200);
    }
    
    toggleVoice(enabled) {
        this.voiceEnabled = enabled;
        this.speak(enabled ? "Voice guidance enabled" : "Voice guidance disabled", 'info');
    }
}

// Make class globally available
window.GPSTruckNavigation = GPSTruckNavigation;
    </script>
</head>
<body>
    <!-- This template shows the GPS integration structure -->
    <h2>GPS Navigation Integration Ready</h2>
    <p>Save the JavaScript above as static/js/gps_navigation.js in your Flask app directory.</p>
</body>
</html>
