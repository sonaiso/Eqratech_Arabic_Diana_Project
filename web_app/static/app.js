// JavaScript for Arabic Grammar Activities Web App

async function loadActivities() {
    const activitiesList = document.getElementById('activities-list');
    const totalActivitiesElement = document.getElementById('total-activities');
    
    // Show loading state
    activitiesList.innerHTML = '<div class="loading">جاري التحميل... Loading...</div>';
    
    try {
        const response = await fetch('/api/activities');
        
        if (!response.ok) {
            throw new Error(`HTTP error! status: ${response.status}`);
        }
        
        const data = await response.json();
        
        // Update total activities count
        totalActivitiesElement.textContent = data.total_activities;
        
        // Clear loading state
        activitiesList.innerHTML = '';
        
        if (data.activities.length === 0) {
            activitiesList.innerHTML = '<div class="info-card">لا توجد أنشطة متاحة حالياً / No activities available</div>';
            return;
        }
        
        // Display activities
        data.activities.forEach(activity => {
            const card = document.createElement('div');
            card.className = 'activity-card';
            card.innerHTML = `
                <h4>${activity.sheet_name}</h4>
                <p>Engine: ${activity.engine_class}</p>
            `;
            activitiesList.appendChild(card);
        });
        
    } catch (error) {
        console.error('Error loading activities:', error);
        activitiesList.innerHTML = `
            <div class="error">
                <strong>خطأ في تحميل الأنشطة / Error loading activities</strong><br>
                ${error.message}
            </div>
        `;
    }
}

// Auto-load activities on page load
document.addEventListener('DOMContentLoaded', () => {
    loadActivities();
});
