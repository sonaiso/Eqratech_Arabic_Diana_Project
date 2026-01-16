"""
Record: The locked record structure (C1-C2-C3)

A record is the fundamental processing unit with three locked layers:
- C1: Signifier (form + sensing conditions)
- C2: Trace (gate processing chain)  
- C3: Signified (meaning graph)

Locking rules:
- No C3 without C2 trace
- No C2 without C1 conditions (reality/brain/sensing/priors)
- No meaning generation without prior_ids
"""

from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional
from enum import Enum


class SensingChannel(Enum):
    """Sensing channels (الحس)"""
    READ = "read"      # قراءة
    HEAR = "hear"      # سماع
    SEE = "see"        # رؤية


class ExecutorType(Enum):
    """Brain executor types (الدماغ الصالح)"""
    KERNEL_SAFE = "KernelSafe"
    HUMAN = "Human"
    VERIFIED = "Verified"


@dataclass
class C1Layer:
    """
    C1: Signifier Layer (الدال + شروط العقل)
    
    Represents form and the four conditions of mind:
    1. Reality (الواقع): form_stream
    2. Brain (الدماغ): executor
    3. Sensing (الحس): channel
    4. Prior knowledge (المعلومات السابقة): priors
    """
    
    # The form/text/phonemes
    form_stream: str
    
    # Codec payload (reversible encoding)
    codec_version: int
    payload_unit_ids: List[int]
    checksum: str
    
    # Prior knowledge (معلومات سابقة) - IDs only
    lexicon_ids: List[str] = field(default_factory=list)
    ruleset_ids: List[str] = field(default_factory=list)
    
    # Sensing channel (الحس)
    sensing_channel: SensingChannel = SensingChannel.READ
    
    # Brain executor (الدماغ الصالح)
    executor: ExecutorType = ExecutorType.KERNEL_SAFE
    
    def verify_conditions(self) -> bool:
        """
        Verify all four conditions of mind are met.
        
        Returns:
            True if all conditions satisfied
        """
        return (
            len(self.form_stream) > 0 and          # Reality exists
            self.executor is not None and          # Brain is present
            self.sensing_channel is not None and   # Sensing is specified
            len(self.lexicon_ids) > 0              # Prior knowledge exists
        )


@dataclass
class TraceEntry:
    """Single gate execution in C2 trace"""
    gate_id: str
    inputs: List[Any]
    outputs: List[Any]
    prior_ids: List[str] = field(default_factory=list)  # Evidence IDs


@dataclass
class C2Layer:
    """
    C2: Trace Layer (سلسلة البوابات)
    
    Sequential gate processing with full audit trail.
    No generative explanations - only IDs and results.
    """
    
    trace: List[TraceEntry] = field(default_factory=list)
    
    def add_entry(self, gate_id: str, inputs: List[Any], 
                  outputs: List[Any], prior_ids: List[str] = None):
        """
        Add a gate execution to trace.
        
        Args:
            gate_id: Gate identifier
            inputs: Input values
            outputs: Output values
            prior_ids: Evidence/prior knowledge IDs
        """
        self.trace.append(TraceEntry(
            gate_id=gate_id,
            inputs=inputs,
            outputs=outputs,
            prior_ids=prior_ids or []
        ))
    
    def get_output(self, gate_id: str) -> Optional[List[Any]]:
        """
        Get output of specific gate.
        
        Args:
            gate_id: Gate to look up
            
        Returns:
            Output list or None if not found
        """
        for entry in self.trace:
            if entry.gate_id == gate_id:
                return entry.outputs
        return None


@dataclass
class C3Layer:
    """
    C3: Signified Layer (المدلول)
    
    The meaning graph with:
    - Signified graph (nodes: entities/events/roles, edges: relations)
    - Vectors (attention, self_model, value)
    - Invariants (conservation, symmetry constraints)
    """
    
    signified_graph: Dict[str, Any] = field(default_factory=dict)
    
    # Consciousness vectors
    attention_vector: List[float] = field(default_factory=list)
    self_model_state: Dict[str, Any] = field(default_factory=dict)
    value_state: Dict[str, Any] = field(default_factory=dict)
    
    # Invariants tracking
    conservation_checks: List[str] = field(default_factory=list)
    symmetry_checks: List[str] = field(default_factory=list)
    violations: List[str] = field(default_factory=list)
    
    def add_violation(self, violation_id: str):
        """Record an invariant violation"""
        self.violations.append(violation_id)
    
    def is_valid(self) -> bool:
        """Check if C3 satisfies all invariants"""
        return len(self.violations) == 0


@dataclass
class Record:
    """
    Locked Record (C1-C2-C3)
    
    The fundamental unit of conscious processing.
    Enforces locking rules - no layer can exist without its prerequisites.
    
    Attributes:
        record_id: Unique record identifier
        c1: Signifier layer with sensing conditions
        c2: Trace layer with gate executions
        c3: Signified layer with meaning graph
    """
    
    record_id: str
    c1: C1Layer
    c2: C2Layer = field(default_factory=C2Layer)
    c3: Optional[C3Layer] = None
    
    def __post_init__(self):
        """Validate locking rules on creation"""
        self.validate_locks()
    
    def validate_locks(self) -> bool:
        """
        Enforce locking rules:
        1. C1 must satisfy four conditions
        2. C3 requires C2 trace
        3. C2 requires C1 conditions
        
        Raises:
            ValueError: If locking rules violated
            
        Returns:
            True if valid
        """
        # Rule 1: C1 conditions
        if not self.c1.verify_conditions():
            raise ValueError(
                "C1 locking violation: All four conditions "
                "(reality/brain/sensing/priors) must be satisfied"
            )
        
        # Rule 2: No C3 without C2
        if self.c3 is not None and len(self.c2.trace) == 0:
            raise ValueError(
                "C2-C3 locking violation: C3 cannot exist without C2 trace"
            )
        
        # Rule 3: Any C2 gate producing meaning must have prior_ids
        for entry in self.c2.trace:
            if 'MEANING' in entry.gate_id or 'SEMANTIC' in entry.gate_id:
                if len(entry.prior_ids) == 0:
                    raise ValueError(
                        f"C2 locking violation: Gate {entry.gate_id} "
                        "produces meaning without prior_ids"
                    )
        
        return True
    
    def to_dict(self) -> dict:
        """
        Serialize record to dictionary.
        
        Returns:
            Dictionary representation
        """
        return {
            'record_id': self.record_id,
            'c1': {
                'form_stream': self.c1.form_stream,
                'codec': {
                    'ver': self.c1.codec_version,
                    'payload_u128': self.c1.payload_unit_ids,
                    'checksum32': self.c1.checksum
                },
                'priors': {
                    'lexicon_ids': self.c1.lexicon_ids,
                    'ruleset_ids': self.c1.ruleset_ids
                },
                'sensing': {
                    'channel': self.c1.sensing_channel.value
                },
                'brain': {
                    'executor': self.c1.executor.value
                }
            },
            'c2_trace': [
                {
                    'gate': e.gate_id,
                    'in': e.inputs,
                    'out': e.outputs,
                    'prior_ids': e.prior_ids
                }
                for e in self.c2.trace
            ],
            'c3': {
                'signified_graph': self.c3.signified_graph if self.c3 else {},
                'vectors': {
                    'attention': self.c3.attention_vector if self.c3 else [],
                    'self_model': self.c3.self_model_state if self.c3 else {},
                    'value': self.c3.value_state if self.c3 else {}
                },
                'invariants': {
                    'conservation': self.c3.conservation_checks if self.c3 else [],
                    'symmetry': self.c3.symmetry_checks if self.c3 else [],
                    'violations': self.c3.violations if self.c3 else []
                }
            } if self.c3 else None
        }
