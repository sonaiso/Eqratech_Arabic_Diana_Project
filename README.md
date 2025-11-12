# Eqratech_Arabic_Diana_Project

Python NLP Project with all Arabic tools verbs and names

## Setup Instructions

### 1. Create a Virtual Environment

```bash
# Create virtual environment
python -m venv venv

# Activate on Linux/Mac
source venv/bin/activate

# Activate on Windows
venv\Scripts\activate
```

### 2. Install Dependencies

```bash
pip install -r requirements.txt
```

### 3. Run the Web Application

#### Option A: Using the helper script (Recommended)

```bash
python run_server.py
```

This will start the server on `http://127.0.0.1:8000`

For development with auto-reload:
```bash
python run_server.py --reload
```

#### Option B: Using uvicorn directly

```bash
# Make sure PYTHONPATH includes the current directory
PYTHONPATH=. uvicorn web_app.main:app --reload --host 127.0.0.1 --port 8000
```

On Windows (PowerShell):
```powershell
$env:PYTHONPATH="."; uvicorn web_app.main:app --reload --host 127.0.0.1 --port 8000
```

### 4. Access the Application

- **Web UI**: Open your browser and navigate to `http://127.0.0.1:8000/`
- **API Documentation**: Visit `http://127.0.0.1:8000/docs` for interactive API docs
- **API Endpoint**: `http://127.0.0.1:8000/api/activities` returns JSON data

## Requirements

- Python 3.7+
- `Main_engine.py` must exist in the repository root and provide a `collect_engines()` function that returns a list of engine classes
- Each engine class should have:
  - `SHEET_NAME` attribute (string)
  - `make_df()` class method that returns a pandas DataFrame

## Notes

- If `Main_engine.py` is missing or not importable, the application will start but show no activities
- Check the server logs for startup errors and warnings
- Pinned dependency versions in `requirements.txt` ensure reproducible installations

