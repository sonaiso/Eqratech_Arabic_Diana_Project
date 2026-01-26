#!/usr/bin/env python
"""
FractalHub Dictionary Validator Script

Validates dictionary YAML file for v02 compliance.

Usage:
    python scripts/validate_dictionary.py [path/to/dictionary.yaml]
"""

import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from fractalhub.dictionary.validator import DictionaryValidator


def main():
    """Main validation function."""
    # Get dictionary path from command line or use default
    if len(sys.argv) > 1:
        dict_path = sys.argv[1]
    else:
        # Default to v02 dictionary
        dict_path = Path(__file__).parent.parent / "fractalhub" / "data" / "fractalhub_dictionary_v02.yaml"
    
    print(f"Validating dictionary: {dict_path}")
    print()
    
    try:
        # Create validator and run validation
        validator = DictionaryValidator(str(dict_path))
        is_valid, errors, warnings = validator.validate()
        
        # Print report
        print(validator.get_report())
        
        # Exit with appropriate code
        if is_valid:
            sys.exit(0)
        else:
            sys.exit(1)
    
    except FileNotFoundError as e:
        print(f"❌ Error: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"❌ Unexpected error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
