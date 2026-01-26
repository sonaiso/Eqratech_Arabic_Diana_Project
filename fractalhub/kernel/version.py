"""
FractalHub Kernel Version Management

Provides version metadata for all records and traces.
Ensures backward compatibility tracking.
"""

from datetime import datetime, timezone
from typing import Dict, Any

KERNEL_VERSION = "1.2"
API_VERSION = "1.2.0"
SCHEMA_VERSION = "1.2"
MIN_KERNEL_VERSION = "1.0"


def get_version_metadata(include_timestamp: bool = True) -> Dict[str, Any]:
    """
    Get version metadata for inclusion in all records and traces.
    
    Args:
        include_timestamp: Whether to include creation timestamp
        
    Returns:
        Dictionary containing version metadata
        
    Example:
        >>> metadata = get_version_metadata()
        >>> metadata['kernel_version']
        '1.2'
        >>> 'created_at' in metadata
        True
    """
    metadata = {
        "kernel_version": KERNEL_VERSION,
        "api_version": API_VERSION,
        "schema_version": SCHEMA_VERSION,
        "compatibility": {
            "min_kernel_version": MIN_KERNEL_VERSION,
            "breaking_changes": False
        }
    }
    
    if include_timestamp:
        metadata["created_at"] = datetime.now(timezone.utc).isoformat()
    
    return metadata


def check_compatibility(version: str) -> bool:
    """
    Check if a given version is compatible with current kernel.
    
    Args:
        version: Version string to check (e.g., "1.0", "1.1", "1.2")
        
    Returns:
        True if compatible, False otherwise
        
    Example:
        >>> check_compatibility("1.0")
        True
        >>> check_compatibility("0.9")
        False
    """
    try:
        # Simple string comparison for version compatibility
        # Since we use format X.Y, lexicographic comparison works for our use case
        # For more complex versioning, consider using packaging.version module
        return version >= MIN_KERNEL_VERSION
    except (ValueError, TypeError):
        return False


def get_version_info() -> Dict[str, str]:
    """
    Get simple version information dictionary.
    
    Returns:
        Dictionary with kernel, API, and schema versions
    """
    return {
        "kernel_version": KERNEL_VERSION,
        "api_version": API_VERSION,
        "schema_version": SCHEMA_VERSION,
    }
