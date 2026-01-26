"""
FractalHub Gate System

Core gates implementing Al-Nabhani's Four Conditions of Mind:
1. Reality (form_stream)
2. Brain (executor)
3. Sensing (channel)
4. Prior Knowledge (lexicon_ids/ruleset_ids)

5 Core Gates:
- G_ATTEND: Attention mechanism
- G_CODEC_VERIFY: Form verification
- G_SPEECH_ACT: Speech act recognition
- G_MEMORY_READ: Memory retrieval
- G_MEMORY_WRITE: Memory storage
"""

from dataclasses import dataclass
from enum import Enum
from typing import Dict, Any, Optional, Callable, List
from uuid import uuid4
import time

from fractalhub.kernel.version import get_version_metadata


class GateType(Enum):
    """Core gate types in the consciousness system."""
    G_ATTEND = "G_ATTEND"
    G_CODEC_VERIFY = "G_CODEC_VERIFY"
    G_SPEECH_ACT = "G_SPEECH_ACT"
    G_MEMORY_READ = "G_MEMORY_READ"
    G_MEMORY_WRITE = "G_MEMORY_WRITE"


@dataclass
class FourConditions:
    """
    Al-Nabhani's Four Conditions of Mind.
    
    Every gate passage must satisfy all four conditions:
    - Reality: The form stream being processed
    - Brain: The executor/processor
    - Sensing: The channel/modality
    - Prior Knowledge: Dictionary evidence (lexicon_ids/ruleset_ids)
    """
    reality: Any  # form_stream
    brain: str  # executor identifier
    sensing: str  # channel (text/audio/visual)
    prior_knowledge: Dict[str, List[str]]  # lexicon_ids, ruleset_ids
    
    def validate(self) -> tuple[bool, List[str]]:
        """
        Validate that all four conditions are present.
        
        Returns:
            (is_valid, error_messages)
        """
        errors = []
        
        if self.reality is None:
            errors.append("Reality (form_stream) is required")
        
        if not self.brain:
            errors.append("Brain (executor) is required")
        
        if not self.sensing:
            errors.append("Sensing (channel) is required")
        
        if not self.prior_knowledge or not any(self.prior_knowledge.values()):
            errors.append("Prior Knowledge (lexicon_ids/ruleset_ids) is required")
        
        return (len(errors) == 0, errors)


@dataclass
class Gate:
    """
    A gate passage in the C2 layer.
    
    Gates document the transition from C1 (signifier) to C3 (signified).
    NO C3 without C2 gate passage.
    NO C2 without C1 four conditions.
    
    Attributes:
        gate_id: Unique gate identifier
        gate_type: Type from GateType enum
        conditions: The four conditions of mind
        input_data: Input to the gate
        output_data: Gate processing result
        execution_time: Latency in seconds
        metadata: Version information
    """
    gate_id: str
    gate_type: GateType
    conditions: FourConditions
    input_data: Any = None
    output_data: Any = None
    execution_time: float = 0.0
    metadata: Dict[str, Any] = None
    
    def __post_init__(self):
        if self.metadata is None:
            self.metadata = get_version_metadata()
    
    def validate(self) -> tuple[bool, List[str]]:
        """
        Validate gate completeness.
        
        Returns:
            (is_valid, error_messages)
        """
        errors = []
        
        # Validate four conditions
        conditions_valid, conditions_errors = self.conditions.validate()
        if not conditions_valid:
            errors.extend(conditions_errors)
        
        if self.input_data is None:
            errors.append("Gate must have input_data")
        
        return (len(errors) == 0, errors)
    
    def execute(self, processor: Optional[Callable] = None) -> Any:
        """
        Execute the gate with optional processor function.
        
        Args:
            processor: Optional function to process input_data
            
        Returns:
            Processing result
        """
        start_time = time.time()
        
        # Validate before execution
        is_valid, errors = self.validate()
        if not is_valid:
            raise ValueError(f"Gate validation failed: {errors}")
        
        # Execute processor if provided
        if processor:
            self.output_data = processor(self.input_data)
        else:
            # Default: pass through
            self.output_data = self.input_data
        
        self.execution_time = time.time() - start_time
        return self.output_data
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert gate to dictionary representation."""
        return {
            "gate_id": self.gate_id,
            "gate_type": self.gate_type.value,
            "conditions": {
                "reality": str(self.conditions.reality)[:100],  # Truncate for brevity
                "brain": self.conditions.brain,
                "sensing": self.conditions.sensing,
                "prior_knowledge": self.conditions.prior_knowledge,
            },
            "execution_time": self.execution_time,
            "metadata": self.metadata,
        }


class GateRegistry:
    """
    Registry for managing gate instances and enforcing architecture.
    
    Enforces:
    - NO C2 without C1 four conditions
    - Proper gate sequencing
    """
    
    def __init__(self):
        self.gates: Dict[str, Gate] = {}
    
    def create_gate(
        self,
        gate_type: GateType,
        reality: Any,
        brain: str,
        sensing: str,
        prior_knowledge: Dict[str, List[str]],
        input_data: Any = None
    ) -> Gate:
        """
        Create a new gate with four conditions validation.
        
        Args:
            gate_type: Type of gate to create
            reality: Form stream (C1 requirement)
            brain: Executor identifier
            sensing: Channel/modality
            prior_knowledge: Dictionary evidence (lexicon_ids, ruleset_ids)
            input_data: Optional input data
            
        Returns:
            New Gate instance
            
        Raises:
            ValueError: If four conditions not satisfied
        """
        conditions = FourConditions(
            reality=reality,
            brain=brain,
            sensing=sensing,
            prior_knowledge=prior_knowledge
        )
        
        # Enforce: NO C2 without C1 four conditions
        is_valid, errors = conditions.validate()
        if not is_valid:
            raise ValueError(f"Cannot create gate - four conditions not satisfied: {errors}")
        
        gate_id = f"{gate_type.value}:{uuid4().hex[:8]}"
        gate = Gate(
            gate_id=gate_id,
            gate_type=gate_type,
            conditions=conditions,
            input_data=input_data
        )
        
        self.gates[gate_id] = gate
        return gate
    
    def get_gate(self, gate_id: str) -> Optional[Gate]:
        """Retrieve gate by ID."""
        return self.gates.get(gate_id)
    
    def validate_gate_chain(self, gate_ids: List[str]) -> tuple[bool, List[str]]:
        """
        Validate a chain of gates.
        
        Args:
            gate_ids: List of gate IDs in order
            
        Returns:
            (is_valid, error_messages)
        """
        errors = []
        
        for gate_id in gate_ids:
            gate = self.get_gate(gate_id)
            if not gate:
                errors.append(f"Gate {gate_id} not found")
                continue
            
            is_valid, gate_errors = gate.validate()
            if not is_valid:
                errors.extend([f"{gate_id}: {e}" for e in gate_errors])
        
        return (len(errors) == 0, errors)
    
    def get_statistics(self) -> Dict[str, Any]:
        """Get gate system statistics."""
        total_gates = len(self.gates)
        gates_by_type = {}
        total_execution_time = 0.0
        
        for gate in self.gates.values():
            gate_type = gate.gate_type.value
            gates_by_type[gate_type] = gates_by_type.get(gate_type, 0) + 1
            total_execution_time += gate.execution_time
        
        return {
            "total_gates": total_gates,
            "gates_by_type": gates_by_type,
            "total_execution_time": total_execution_time,
            "avg_execution_time": total_execution_time / total_gates if total_gates > 0 else 0.0,
        }


# Global gate registry instance
gate_registry = GateRegistry()
