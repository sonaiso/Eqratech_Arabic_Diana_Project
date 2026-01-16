"""
Trace: C2 trace management

Manages the sequential execution trace of gates with full audit trail.
"""

from typing import List, Any, Optional
from dataclasses import dataclass, field


@dataclass
class TraceEntry:
    """
    Single gate execution entry.
    
    Records:
    - gate_id: Which gate executed
    - inputs: Input values
    - outputs: Output values
    - prior_ids: Evidence/knowledge IDs used
    """
    gate_id: str
    inputs: List[Any]
    outputs: List[Any]
    prior_ids: List[str] = field(default_factory=list)
    
    def to_dict(self) -> dict:
        """Convert to dictionary"""
        return {
            'gate': self.gate_id,
            'in': self.inputs,
            'out': self.outputs,
            'prior_ids': self.prior_ids
        }


class C2Trace:
    """
    C2 Trace manager.
    
    Maintains sequential gate execution history.
    Enforces traceability and evidence requirements.
    """
    
    def __init__(self):
        """Initialize empty trace"""
        self.entries: List[TraceEntry] = []
    
    def add(self, gate_id: str, inputs: List[Any], 
            outputs: List[Any], prior_ids: List[str] = None):
        """
        Add gate execution to trace.
        
        Args:
            gate_id: Gate identifier
            inputs: Input values
            outputs: Output values  
            prior_ids: Evidence IDs (required for meaning gates)
        """
        entry = TraceEntry(
            gate_id=gate_id,
            inputs=inputs,
            outputs=outputs,
            prior_ids=prior_ids or []
        )
        
        # Validate meaning gates have priors
        if 'MEANING' in gate_id or 'SEMANTIC' in gate_id:
            if len(entry.prior_ids) == 0:
                raise ValueError(
                    f"Gate {gate_id} produces meaning but has no prior_ids"
                )
        
        self.entries.append(entry)
    
    def get_output(self, gate_id: str) -> Optional[List[Any]]:
        """
        Get output of specific gate.
        
        Args:
            gate_id: Gate to look up
            
        Returns:
            Output list or None if not found
        """
        for entry in self.entries:
            if entry.gate_id == gate_id:
                return entry.outputs
        return None
    
    def get_last_output(self) -> Optional[List[Any]]:
        """Get output of last executed gate"""
        if self.entries:
            return self.entries[-1].outputs
        return None
    
    def find_by_gate(self, gate_id: str) -> List[TraceEntry]:
        """
        Find all executions of specific gate.
        
        Args:
            gate_id: Gate to search for
            
        Returns:
            List of matching entries
        """
        return [e for e in self.entries if e.gate_id == gate_id]
    
    def to_list(self) -> List[dict]:
        """
        Convert trace to list of dicts.
        
        Returns:
            List of trace entry dicts
        """
        return [e.to_dict() for e in self.entries]
    
    def __len__(self) -> int:
        """Get trace length"""
        return len(self.entries)
    
    def __iter__(self):
        """Iterate over entries"""
        return iter(self.entries)
