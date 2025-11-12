"""FastAPI application for Arabic grammar activities web interface.

This module provides a web API for accessing Arabic grammar engine activities.
Engine classes are loaded once at startup for better performance.
"""
import logging
from typing import List, Dict, Any
from contextlib import asynccontextmanager

from fastapi import FastAPI, Request
from fastapi.responses import HTMLResponse, JSONResponse
from fastapi.staticfiles import StaticFiles
from fastapi.templating import Jinja2Templates
from pydantic import BaseModel, Field

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

# Global variable to cache engines
ENGINES: List[Any] = []


class Activity(BaseModel):
    """Model for a single activity."""
    sheet_name: str = Field(..., description="The sheet name of the activity")
    engine_class: str = Field(..., description="The engine class name")


class ActivitiesResponse(BaseModel):
    """Response model for /api/activities endpoint."""
    date: str = Field(..., description="Response date in ISO format")
    total_activities: int = Field(..., description="Total number of activities available")
    activities: List[Activity] = Field(..., description="List of available activities")


@asynccontextmanager
async def lifespan(app: FastAPI):
    """Application lifespan manager - loads engines at startup."""
    global ENGINES
    
    logger.info("Starting application - loading engines...")
    
    try:
        # Import and load engines at startup
        from Main_engine import collect_engines
        ENGINES = collect_engines()
        logger.info(f"Successfully loaded {len(ENGINES)} engine(s)")
        
        # Log loaded engines for debugging
        for engine in ENGINES:
            sheet_name = getattr(engine, 'SHEET_NAME', 'Unknown')
            logger.info(f"  - {engine.__name__}: {sheet_name}")
            
    except ImportError as e:
        logger.error(f"Failed to import Main_engine: {e}")
        logger.error("Application will start with zero engines. Ensure Main_engine.py exists in PYTHONPATH.")
        ENGINES = []
    except Exception as e:
        logger.error(f"Error loading engines: {e}")
        ENGINES = []
    
    # Validate engines
    if not ENGINES:
        logger.warning("No engines loaded - the application will have no activities available")
    
    yield
    
    # Cleanup (if needed)
    logger.info("Shutting down application")


# Create FastAPI app with lifespan
app = FastAPI(
    title="Arabic Grammar Activities API",
    description="API for accessing Arabic grammar engine activities",
    version="1.0.0",
    lifespan=lifespan
)

# Mount static files and templates
app.mount("/static", StaticFiles(directory="web_app/static"), name="static")
templates = Jinja2Templates(directory="web_app/templates")


@app.get("/", response_class=HTMLResponse)
async def root(request: Request):
    """Serve the main web interface."""
    return templates.TemplateResponse(
        "index.html",
        {
            "request": request,
            "total_activities": len(ENGINES)
        }
    )


@app.get("/health")
async def health():
    """Health check endpoint."""
    return {
        "status": "ok",
        "engines_loaded": len(ENGINES)
    }


@app.get("/api/activities", response_model=ActivitiesResponse)
async def get_activities():
    """Get list of available activities.
    
    Returns:
        ActivitiesResponse: List of activities with metadata.
    """
    from datetime import datetime
    
    activities = []
    for engine in ENGINES:
        activities.append(
            Activity(
                sheet_name=getattr(engine, 'SHEET_NAME', engine.__name__),
                engine_class=engine.__name__
            )
        )
    
    return ActivitiesResponse(
        date=datetime.utcnow().isoformat(),
        total_activities=len(activities),
        activities=activities
    )
