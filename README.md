# Eqratech_Arabic_Diana_Project

Python NLP Project with all Arabic tools, verbs and names.

This project provides a comprehensive Arabic grammar engine system with a web interface for accessing various linguistic activities and classifications.

## Features

- Multiple Arabic grammar engines for different linguistic categories
- Web API for accessing grammar activities
- FastAPI-based web application with interactive UI
- Automatic engine discovery and loading at startup
- Support for exporting grammar data to Excel

## Setup

### Prerequisites

- Python 3.8 or higher
- pip (Python package installer)

### Installation

1. Clone the repository:
```bash
git clone https://github.com/sonaiso/Eqratech_Arabic_Diana_Project.git
cd Eqratech_Arabic_Diana_Project
```

2. Create a virtual environment (recommended):
```bash
python -m venv venv

# On Windows:
venv\Scripts\activate

# On macOS/Linux:
source venv/bin/activate
```

3. Install dependencies:
```bash
pip install -r requirements.txt
```

## Running the Application

### Method 1: Using run_server.py (Recommended)

```bash
python run_server.py
```

With auto-reload for development:
```bash
python run_server.py --reload
```

### Method 2: Using uvicorn directly

```bash
PYTHONPATH=. uvicorn web_app.main:app --reload --host 127.0.0.1 --port 8000
```

On Windows (PowerShell):
```powershell
$env:PYTHONPATH="."; uvicorn web_app.main:app --reload --host 127.0.0.1 --port 8000
```

On Windows (Command Prompt):
```cmd
set PYTHONPATH=.
uvicorn web_app.main:app --reload --host 127.0.0.1 --port 8000
```

### Method 3: Using VS Code

If you're using Visual Studio Code:
1. Open the project folder in VS Code
2. Press F5 or use the Run menu to start debugging
3. Select "Python: FastAPI" or "Python: Run Server (run_server.py)" configuration

## Accessing the Application

Once the server is running, open your browser and navigate to:
- **Web UI**: http://127.0.0.1:8000/
- **API Documentation**: http://127.0.0.1:8000/docs
- **API Activities Endpoint**: http://127.0.0.1:8000/api/activities
- **Health Check**: http://127.0.0.1:8000/health

## About Main_engine.py

The `Main_engine.py` module is responsible for discovering and collecting all available grammar engine classes in the project. It:

- Automatically scans for modules ending with `_engine.py`
- Identifies classes that inherit from `BaseReconstructionEngine`
- Validates that each engine has required attributes (`SHEET_NAME`, `make_df`)
- Returns a deduplicated list of engine classes

The web application loads these engines once at startup using `Main_engine.collect_engines()` and caches them for better performance.

## PYTHONPATH Usage

The application requires the project root directory to be in the Python path to import modules correctly. This is handled automatically by:

- `run_server.py` - sets up the path internally
- VS Code configurations - sets `PYTHONPATH` in launch configurations
- Manual uvicorn commands - requires setting `PYTHONPATH=.` before running

## Development

### VS Code Configuration

The project includes VS Code configuration files in `.vscode/`:
- `launch.json` - Debug configurations for FastAPI and Python scripts
- `settings.json` - Python environment and formatting settings
- `tasks.json` - Common tasks like running the server and installing dependencies

### Project Structure

```
Eqratech_Arabic_Diana_Project/
├── web_app/                 # Web application
│   ├── main.py             # FastAPI application
│   ├── templates/          # HTML templates
│   └── static/             # CSS, JavaScript, images
├── .vscode/                # VS Code configuration
├── *_engine.py             # Grammar engine modules
├── Main_engine.py          # Engine discovery and collection
├── base_reconstruction_engine.py  # Base engine class
├── requirements.txt        # Python dependencies (pinned versions)
├── run_server.py          # Server launcher script
└── README.md              # This file
```

## Exporting Grammar Data

To export all grammar data to an Excel file:

```python
from Main_engine import export_all
export_all('output_file.xlsx')
```

Or use the VS Code task "Export Grammar Data".

## Troubleshooting

### No engines loaded
If the application starts with zero engines:
- Ensure `Main_engine.py` exists in the repository root
- Verify that `PYTHONPATH` includes the project root directory
- Check the application logs for import errors

### Import errors
- Make sure all dependencies are installed: `pip install -r requirements.txt`
- Verify you're using Python 3.8 or higher
- Check that the virtual environment is activated

## Contributing

Contributions are welcome! Please ensure your code follows the project structure and includes appropriate documentation.

## License

This project is part of the Eqratech Arabic Diana Project.
