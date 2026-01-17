"""
FractalHub Trace System

Enhanced trace schema with gate passage documentation,
evidence tracking, and resource usage monitoring.

Core principle: NO meaning without documented trace.
"""

from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Dict, List, Any, Optional
from uuid import uuid4
import time

from fractalhub.kernel.version import get_version_metadata


@dataclass
class Trace:
    """
    Enhanced trace record for v1.2
    
    Documents every gate passage with:
    - Execution latency
    - Evidence strength (epistemic confidence)
    - Invariant check results
    - Resource usage
    
    Attributes:
        trace_id: Unique trace identifier
        gate_chain: List of gate IDs in execution order
        prior_ids: Required evidence (lexicon_ids, ruleset_ids)
        evidence_strength: Epistemic confidence (0.0-1.0)
        gate_latency: Execution time per gate in seconds
        invariant_checks_report: Results of constraint validation
        resource_usage: Memory and CPU tracking
        metadata: Version and creation info
    """
    
    trace_id: str = field(default_factory=lambda: f"C2:TRACE:{uuid4().hex[:12]}")
    gate_chain: List[str] = field(default_factory=list)
    prior_ids: Dict[str, List[str]] = field(default_factory=dict)
    evidence_strength: float = 1.0
    gate_latency: Dict[str, float] = field(default_factory=dict)
    invariant_checks_report: Dict[str, List[str]] = field(default_factory=lambda: {
        "passed": [],
        "failed": [],
        "warnings": []
    })
    resource_usage: Dict[str, int] = field(default_factory=lambda: {
        "memory_bytes": 0,
        "cpu_microseconds": 0
    })
    metadata: Dict[str, Any] = field(default_factory=get_version_metadata)
    created_at: str = field(default_factory=lambda: datetime.now(timezone.utc).isoformat())
    
    def add_gate(self, gate_id: str, latency: Optional[float] = None) -> None:
        """
        Add a gate to the chain with optional latency.
        
        Args:
            gate_id: Gate identifier (e.g., "G_ATTEND:001")
            latency: Execution time in seconds
        """
        self.gate_chain.append(gate_id)
        if latency is not None:
            self.gate_latency[gate_id] = latency
    
    def add_prior_id(self, category: str, id_value: str) -> None:
        """
        Add evidence from dictionary.
        
        Args:
            category: "lexicon_ids" or "ruleset_ids"
            id_value: Entry ID from dictionary
        """
        if category not in self.prior_ids:
            self.prior_ids[category] = []
        if id_value not in self.prior_ids[category]:
            self.prior_ids[category].append(id_value)
    
    def add_invariant_check(self, status: str, check_name: str) -> None:
        """
        Record invariant validation result.
        
        Args:
            status: "passed", "failed", or "warning"
            check_name: Name of the invariant checked
        """
        if status in self.invariant_checks_report:
            self.invariant_checks_report[status].append(check_name)
    
    def has_prior_ids(self) -> bool:
        """Check if trace has any prior_ids evidence."""
        return bool(self.prior_ids and any(self.prior_ids.values()))
    
    def validate(self) -> tuple[bool, List[str]]:
        """
        Validate trace completeness.
        
        Returns:
            (is_valid, error_messages)
        """
        errors = []
        
        if not self.gate_chain:
            errors.append("Trace must have at least one gate")
        
        if not self.has_prior_ids():
            errors.append("Trace must have prior_ids evidence (NO meaning without evidence)")
        
        if not (0.0 <= self.evidence_strength <= 1.0):
            errors.append(f"Evidence strength must be 0.0-1.0, got {self.evidence_strength}")
        
        return (len(errors) == 0, errors)
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert trace to dictionary representation."""
        return {
            "trace_id": self.trace_id,
            "gate_chain": self.gate_chain,
            "prior_ids": self.prior_ids,
            "evidence_strength": self.evidence_strength,
            "gate_latency": self.gate_latency,
            "invariant_checks_report": self.invariant_checks_report,
            "resource_usage": self.resource_usage,
            "metadata": self.metadata,
            "created_at": self.created_at,
        }


class TraceManager:
    """
    Manages trace lifecycle and validation.
    
    Enforces locked architecture constraints:
    - NO C3 without C2 trace
    - NO C2 without C1 conditions
    """
    
    def __init__(self):
        self.traces: Dict[str, Trace] = {}
    
    def create_trace(self, evidence_strength: float = 1.0) -> Trace:
        """
        Create a new trace with version metadata.
        
        Args:
            evidence_strength: Initial epistemic confidence (0.0-1.0)
            
        Returns:
            New Trace instance
        """
        trace = Trace(evidence_strength=evidence_strength)
        self.traces[trace.trace_id] = trace
        return trace
    
    def get_trace(self, trace_id: str) -> Optional[Trace]:
        """Retrieve trace by ID."""
        return self.traces.get(trace_id)
    
    def validate_trace(self, trace_id: str) -> tuple[bool, List[str]]:
        """
        Validate a trace by ID.
        
        Returns:
            (is_valid, error_messages)
        """
        trace = self.get_trace(trace_id)
        if not trace:
            return (False, [f"Trace {trace_id} not found"])
        return trace.validate()
    
    def enforce_c2_requirement(self, c3_object_id: str, trace_id: str) -> bool:
        """
        Enforce locked architecture: NO C3 without C2 trace.
        
        Args:
            c3_object_id: ID of C3 object being created
            trace_id: Required trace ID
            
        Returns:
            True if requirement satisfied, False otherwise
        """
        trace = self.get_trace(trace_id)
        if not trace:
            return False
        
        is_valid, errors = trace.validate()
        return is_valid
    
    def get_statistics(self) -> Dict[str, Any]:
        """Get trace system statistics."""
        total_traces = len(self.traces)
        total_gates = sum(len(t.gate_chain) for t in self.traces.values())
        traces_with_evidence = sum(1 for t in self.traces.values() if t.has_prior_ids())
        
        return {
            "total_traces": total_traces,
            "total_gates": total_gates,
            "traces_with_evidence": traces_with_evidence,
            "evidence_rate": traces_with_evidence / total_traces if total_traces > 0 else 0.0,
        }
