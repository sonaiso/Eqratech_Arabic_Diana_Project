"""Base class for all reconstruction engines."""
import pandas as pd


class BaseReconstructionEngine:
    """Base class that all engine classes should inherit from."""
    
    SHEET_NAME = "Base"  # Override in subclasses
    
    @classmethod
    def make_df(cls) -> pd.DataFrame:
        """Generate a DataFrame with the engine's data.
        
        Returns:
            pd.DataFrame: The generated data.
        """
        raise NotImplementedError("Subclasses must implement make_df()")
