"""
Enhanced Explainable Output Schema

This module provides a structured format for comprehensive explanatory reports
that include:
- Executive summary with failure points
- Layer-by-layer trace
- Before/After chains
- C1/C2/C3 governance framework
- Formatted human-readable and JSON output
"""

from dataclasses import dataclass, field
from typing import Dict, List, Any, Optional
from datetime import datetime
from enum import Enum


class ReportFormat(Enum):
    """Output format for explanatory reports"""
    HUMAN_READABLE = "human_readable"
    JSON = "json"
    MARKDOWN = "markdown"


@dataclass
class FailurePoint:
    """
    A point where the judgment could fail
    
    Attributes:
        condition: The condition that would cause failure
        reason: Why this would cause failure
        impact: What would happen if this fails
        mitigation: How to prevent or handle this failure
    """
    condition: str
    reason: str
    impact: str
    mitigation: Optional[str] = None
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "condition": self.condition,
            "reason": self.reason,
            "impact": self.impact,
            "mitigation": self.mitigation,
        }


@dataclass
class ScopeDefinition:
    """
    Detailed scope definition with validity constraints
    
    Attributes:
        validity_domain: Domain where judgment is valid
        temporal_scope: Time constraints
        spatial_scope: Location/space constraints
        quantification: Universal/particular/conditional
        preconditions: What must be true for judgment to apply
        exclusions: What is explicitly excluded
    """
    validity_domain: str
    temporal_scope: str = "unspecified"
    spatial_scope: str = "unspecified"
    quantification: str = "particular"
    preconditions: List[str] = field(default_factory=list)
    exclusions: List[str] = field(default_factory=list)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "validity_domain": self.validity_domain,
            "temporal_scope": self.temporal_scope,
            "spatial_scope": self.spatial_scope,
            "quantification": self.quantification,
            "preconditions": self.preconditions,
            "exclusions": self.exclusions,
        }


@dataclass
class GovernanceAnnotation:
    """
    C1/C2/C3 governance framework annotation
    
    C1: Conceptual framework (التصور)
    C2: Representational system (التمثيل)  
    C3: Verification rules (التحقق)
    
    Attributes:
        c1_framework: Conceptual ontology used
        c2_representation: How concepts are represented
        c3_verification: Verification and validation rules
        epistemic_order: Order of evidence (if applicable)
        constraints: Governance constraints applied
    """
    c1_framework: str
    c2_representation: str
    c3_verification: str
    epistemic_order: Optional[List[str]] = None
    constraints: List[str] = field(default_factory=list)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "c1_framework": self.c1_framework,
            "c2_representation": self.c2_representation,
            "c3_verification": self.c3_verification,
            "epistemic_order": self.epistemic_order,
            "constraints": self.constraints,
        }


@dataclass
class LayerTrace:
    """
    Detailed trace for a single layer
    
    Attributes:
        layer_name: Name of the layer
        input_summary: What entered this layer
        processing_steps: Steps performed
        output_summary: What was produced
        decisions_made: Key decisions and why
        alternatives_rejected: What was considered but rejected
    """
    layer_name: str
    input_summary: str
    processing_steps: List[str]
    output_summary: str
    decisions_made: List[Dict[str, str]]
    alternatives_rejected: List[Dict[str, str]] = field(default_factory=list)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "layer_name": self.layer_name,
            "input_summary": self.input_summary,
            "processing_steps": self.processing_steps,
            "output_summary": self.output_summary,
            "decisions_made": self.decisions_made,
            "alternatives_rejected": self.alternatives_rejected,
        }


@dataclass
class ExecutiveSummary:
    """
    Executive summary of the judgment
    
    Attributes:
        judgment_text: The final judgment in natural language
        judgment_type: Type of judgment (proposition/directive/etc)
        epistemic_weight: Confidence level with justification
        scope: Scope definition with constraints
        failure_points: Points where judgment could fail
        key_evidence: Main evidence supporting judgment
        timestamp: When this judgment was made
    """
    judgment_text: str
    judgment_type: str
    epistemic_weight: Dict[str, Any]
    scope: ScopeDefinition
    failure_points: List[FailurePoint]
    key_evidence: List[str] = field(default_factory=list)
    timestamp: str = field(default_factory=lambda: datetime.utcnow().isoformat())
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "judgment_text": self.judgment_text,
            "judgment_type": self.judgment_type,
            "epistemic_weight": self.epistemic_weight,
            "scope": self.scope.to_dict(),
            "failure_points": [fp.to_dict() for fp in self.failure_points],
            "key_evidence": self.key_evidence,
            "timestamp": self.timestamp,
        }


@dataclass
class ExplanatoryReport:
    """
    Complete explanatory report with all components
    
    This is the enhanced output schema that provides:
    - Executive summary
    - Layer-by-layer trace
    - Before/After chains
    - C1/C2/C3 governance
    - Formatted output
    """
    
    # Core components
    executive_summary: ExecutiveSummary
    layer_traces: List[LayerTrace]
    before_after_chain: Dict[str, Any]
    governance: GovernanceAnnotation
    
    # Metadata
    input_text: str
    domain: str
    processing_time_ms: float
    xai_version: str = "1.0.0"
    architecture: str = "locked_v1"
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for JSON export"""
        return {
            "xai_version": self.xai_version,
            "architecture": self.architecture,
            "domain": self.domain,
            "input_text": self.input_text,
            "processing_time_ms": self.processing_time_ms,
            "executive_summary": self.executive_summary.to_dict(),
            "layer_traces": [lt.to_dict() for lt in self.layer_traces],
            "before_after_chain": self.before_after_chain,
            "governance": self.governance.to_dict(),
        }
    
    def to_human_readable(self) -> str:
        """
        Format as human-readable text report
        
        Returns structured text with Arabic/English headers
        """
        lines = []
        
        # Header
        lines.append("=" * 80)
        lines.append("تقرير تفسيري كامل | Complete Explanatory Report")
        lines.append("=" * 80)
        lines.append(f"Input: {self.input_text}")
        lines.append(f"Domain: {self.domain}")
        lines.append(f"Processing Time: {self.processing_time_ms:.2f}ms")
        lines.append(f"Timestamp: {self.executive_summary.timestamp}")
        lines.append("")
        
        # Executive Summary
        lines.append("─" * 80)
        lines.append("A) الملخص التنفيذي | Executive Summary")
        lines.append("─" * 80)
        lines.append(f"الحكم | Judgment: {self.executive_summary.judgment_text}")
        lines.append(f"النوع | Type: {self.executive_summary.judgment_type}")
        
        ew = self.executive_summary.epistemic_weight
        lines.append(f"الوزن المعرفي | Epistemic Weight: {ew['level']} ({ew['confidence']:.2f})")
        lines.append(f"  التبرير | Justification: {ew['justification']}")
        
        # Scope
        lines.append(f"\nالنطاق | Scope:")
        scope = self.executive_summary.scope
        lines.append(f"  - Validity Domain: {scope.validity_domain}")
        lines.append(f"  - Quantification: {scope.quantification}")
        lines.append(f"  - Temporal: {scope.temporal_scope}")
        if scope.preconditions:
            lines.append(f"  - Preconditions: {', '.join(scope.preconditions)}")
        
        # Failure Points
        if self.executive_summary.failure_points:
            lines.append(f"\nنقاط الفشل | Failure Points:")
            for i, fp in enumerate(self.executive_summary.failure_points, 1):
                lines.append(f"  {i}. {fp.condition}")
                lines.append(f"     Why: {fp.reason}")
                lines.append(f"     Impact: {fp.impact}")
                if fp.mitigation:
                    lines.append(f"     Mitigation: {fp.mitigation}")
        
        # Layer Traces
        lines.append("")
        lines.append("─" * 80)
        lines.append("B) التتبع الطبقي | Layer-by-Layer Trace")
        lines.append("─" * 80)
        
        for i, trace in enumerate(self.layer_traces, 1):
            lines.append(f"\n{i}. {trace.layer_name.upper()}")
            lines.append(f"   Input: {trace.input_summary}")
            lines.append(f"   Steps:")
            for step in trace.processing_steps:
                lines.append(f"     - {step}")
            lines.append(f"   Output: {trace.output_summary}")
            
            if trace.decisions_made:
                lines.append(f"   Decisions:")
                for decision in trace.decisions_made:
                    lines.append(f"     • {decision.get('decision', '')}: {decision.get('reason', '')}")
        
        # Before/After Chain
        lines.append("")
        lines.append("─" * 80)
        lines.append("C) ما قبل/ما بعد | Before/After Chain")
        lines.append("─" * 80)
        
        ba = self.before_after_chain
        if ba.get('preconditions'):
            lines.append("قبل | Before (Preconditions):")
            for pre in ba['preconditions']:
                lines.append(f"  ← {pre}")
        
        if ba.get('consequences'):
            lines.append("\nبعد | After (Consequences):")
            for cons in ba['consequences']:
                lines.append(f"  → {cons}")
        
        if ba.get('invalidating_conditions'):
            lines.append("\nالموانع | Invalidating Conditions:")
            for inv in ba['invalidating_conditions']:
                lines.append(f"  ⚠ {inv}")
        
        # Governance
        lines.append("")
        lines.append("─" * 80)
        lines.append("D) الحوكمة | Governance (C1/C2/C3)")
        lines.append("─" * 80)
        
        gov = self.governance
        lines.append(f"C1 (التصور | Conceptual): {gov.c1_framework}")
        lines.append(f"C2 (التمثيل | Representation): {gov.c2_representation}")
        lines.append(f"C3 (التحقق | Verification): {gov.c3_verification}")
        
        if gov.epistemic_order:
            lines.append(f"\nترتيب الأدلة | Epistemic Order:")
            for i, order in enumerate(gov.epistemic_order, 1):
                lines.append(f"  {i}. {order}")
        
        if gov.constraints:
            lines.append(f"\nالقيود | Constraints Applied:")
            for constraint in gov.constraints:
                lines.append(f"  ✓ {constraint}")
        
        # Footer
        lines.append("")
        lines.append("=" * 80)
        lines.append(f"XAI Engine v{self.xai_version} | Architecture: {self.architecture}")
        lines.append("=" * 80)
        
        return "\n".join(lines)
    
    def to_markdown(self) -> str:
        """
        Format as Markdown for documentation
        
        Returns markdown-formatted report
        """
        lines = []
        
        lines.append(f"# Explanatory Report")
        lines.append(f"")
        lines.append(f"**Input:** {self.input_text}  ")
        lines.append(f"**Domain:** {self.domain}  ")
        lines.append(f"**Processing Time:** {self.processing_time_ms:.2f}ms  ")
        lines.append(f"")
        
        lines.append(f"## Executive Summary")
        lines.append(f"")
        lines.append(f"**Judgment:** {self.executive_summary.judgment_text}")
        lines.append(f"")
        
        ew = self.executive_summary.epistemic_weight
        lines.append(f"**Epistemic Weight:** {ew['level']} (confidence: {ew['confidence']:.2f})")
        lines.append(f"- *Justification:* {ew['justification']}")
        lines.append(f"")
        
        # Scope table
        lines.append(f"### Scope")
        lines.append(f"")
        scope = self.executive_summary.scope
        lines.append(f"| Aspect | Value |")
        lines.append(f"|--------|-------|")
        lines.append(f"| Validity Domain | {scope.validity_domain} |")
        lines.append(f"| Quantification | {scope.quantification} |")
        lines.append(f"| Temporal | {scope.temporal_scope} |")
        lines.append(f"| Spatial | {scope.spatial_scope} |")
        lines.append(f"")
        
        # Failure points
        if self.executive_summary.failure_points:
            lines.append(f"### Failure Points")
            lines.append(f"")
            for i, fp in enumerate(self.executive_summary.failure_points, 1):
                lines.append(f"{i}. **{fp.condition}**")
                lines.append(f"   - **Reason:** {fp.reason}")
                lines.append(f"   - **Impact:** {fp.impact}")
                if fp.mitigation:
                    lines.append(f"   - **Mitigation:** {fp.mitigation}")
                lines.append(f"")
        
        # Layer traces
        lines.append(f"## Layer-by-Layer Trace")
        lines.append(f"")
        for i, trace in enumerate(self.layer_traces, 1):
            lines.append(f"### {i}. {trace.layer_name}")
            lines.append(f"")
            lines.append(f"**Input:** {trace.input_summary}")
            lines.append(f"")
            lines.append(f"**Processing:**")
            for step in trace.processing_steps:
                lines.append(f"- {step}")
            lines.append(f"")
            lines.append(f"**Output:** {trace.output_summary}")
            lines.append(f"")
        
        # Governance
        lines.append(f"## Governance Framework")
        lines.append(f"")
        gov = self.governance
        lines.append(f"- **C1 (Conceptual):** {gov.c1_framework}")
        lines.append(f"- **C2 (Representation):** {gov.c2_representation}")
        lines.append(f"- **C3 (Verification):** {gov.c3_verification}")
        lines.append(f"")
        
        return "\n".join(lines)
