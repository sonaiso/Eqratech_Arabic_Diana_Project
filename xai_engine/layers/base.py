"""
Base class for all XAI layers

All layers must:
1. Declare their position in the pipeline
2. Validate inputs from previous layer
3. Enforce constraints
4. Produce structured output
5. Enable tracing
"""

from abc import ABC, abstractmethod
from typing import Any, Dict, Optional
from ..core.constraints import GlobalConstraints


class LayerBase(ABC):
    """
    Abstract base class for all XAI layers
    
    Attributes:
        layer_name: Name of this layer
        layer_sequence: Ordered list of all layers
        domain: Domain configuration
        constraints: Global constraints enforcer
    """
    
    def __init__(self, layer_name: str, domain: Any):
        self.layer_name = layer_name
        self.layer_sequence = [
            "form",
            "semantic",
            "relational",
            "measurement",
            "judgment",
            "explanation"
        ]
        self.domain = domain
        self.constraints = GlobalConstraints()
        self.trace = []
    
    def get_layer_index(self) -> int:
        """Get the index of this layer in the sequence"""
        return self.layer_sequence.index(self.layer_name)
    
    def can_receive_from(self, source_layer: str) -> bool:
        """Check if this layer can receive input from source_layer"""
        try:
            source_idx = self.layer_sequence.index(source_layer)
            current_idx = self.get_layer_index()
            
            # Can only receive from immediate predecessor
            return source_idx == current_idx - 1
        except ValueError:
            return False
    
    def validate_input(self, input_data: Any, source_layer: Optional[str] = None) -> None:
        """
        Validate input from previous layer
        
        Args:
            input_data: Data from previous layer
            source_layer: Name of source layer
            
        Raises:
            ConstraintViolation: If validation fails
        """
        if source_layer and not self.can_receive_from(source_layer):
            self.constraints.no_layer_jump(
                source_layer,
                self.layer_name,
                self.layer_sequence
            )
        
        if input_data is None:
            from ..core.constraints import ConstraintViolation
            raise ConstraintViolation(
                "INVALID_INPUT",
                f"{self.layer_name} received None input from {source_layer}",
                {"layer": self.layer_name, "source": source_layer}
            )
    
    def log_operation(self, operation: str, details: Dict[str, Any]) -> None:
        """Log an operation for tracing"""
        self.trace.append({
            "layer": self.layer_name,
            "operation": operation,
            "details": details,
        })
    
    @abstractmethod
    def process(self, input_data: Any) -> Any:
        """
        Process input and produce output
        
        Args:
            input_data: Input from previous layer (or raw input for first layer)
            
        Returns:
            Output object specific to this layer
        """
        pass
    
    def get_trace(self) -> list:
        """Get the trace of operations performed by this layer"""
        return self.trace.copy()
    
    def clear_trace(self) -> None:
        """Clear the trace"""
        self.trace = []
