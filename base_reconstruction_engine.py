"""Base class for reconstruction engines."""

import pandas as pd


class BaseReconstructionEngine:
    """Base class that all engine classes should inherit from.
    
    Each engine should define:
    - SHEET_NAME: str - The name for the sheet in the Excel output
    - make_df(): classmethod that returns a pandas DataFrame
    """
    
    SHEET_NAME = "Base"
    
    @classmethod
    def make_df(cls) -> pd.DataFrame:
        """Generate and return a DataFrame for this engine.
        
        Should be overridden by subclasses.
        """
        raise NotImplementedError("Subclasses must implement make_df()")
