"""
Judgment Layer (الحكم) - Layer 5

Purpose: Form final judgment based on measurement
Output: JudgmentObject

This layer:
- Constructs propositions or directives
- Assigns epistemic weight
- Defines scope and validity limits
- Prevents overgeneralization

NO MEASUREMENT → NO JUDGMENT
"""

from typing import Any, Dict, List
from .base import LayerBase
from ..core.output_objects import (
    MeasurementTrace,
    RelationGraph,
    JudgmentObject,
    JudgmentType,
    EpistemicWeight,
    EpistemicLevel,
    DiscourseType,
)
from ..core.domain import Domain
import uuid


class JudgmentLayer(LayerBase):
    """
    Layer 5: Judgment formation
    
    Constructs the final judgment based on measurement results.
    """
    
    def __init__(self, domain: Domain):
        super().__init__("judgment", domain)
    
    def process(self, input_data: Dict[str, Any]) -> JudgmentObject:
        """
        Form judgment from measurement and relations
        
        Args:
            input_data: Dict with "measurement_trace", "relation_graph", etc.
            
        Returns:
            JudgmentObject with epistemic weight and scope
        """
        self.validate_input(input_data, "measurement")
        
        measurement_trace = input_data["measurement_trace"]
        relation_graph = input_data["relation_graph"]
        
        self.log_operation("start_judgment_formation", {
            "measurement_id": measurement_trace.measurement_id
        })
        
        # Enforce: no result without measurement
        self.constraints.no_result_without_measurement(
            result="judgment",
            measurement_trace=measurement_trace
        )
        
        # Enforce: no judgment without relation
        self.constraints.no_judgment_without_relation(
            judgment="forming",
            relations=relation_graph.relations
        )
        
        # Determine judgment type
        judgment_type = self._determine_judgment_type(relation_graph)
        
        # Construct judgment content
        content = self._construct_content(measurement_trace, relation_graph)
        
        # Build judgment structure
        structure = self._build_structure(measurement_trace, relation_graph)
        
        # Assign epistemic weight
        epistemic_weight = self._assign_epistemic_weight(
            measurement_trace,
            relation_graph,
            judgment_type
        )
        
        # Define scope
        scope = self._define_scope(measurement_trace, relation_graph, content)
        
        # Enforce: no generalization without scope
        self.constraints.no_generalization_without_scope(
            statement=content,
            scope=scope
        )
        
        # Extract conditions
        conditions = self._extract_conditions(measurement_trace, relation_graph)
        
        judgment_id = f"JUDG_{uuid.uuid4().hex[:8].upper()}"
        
        return JudgmentObject(
            judgment_id=judgment_id,
            judgment_type=judgment_type,
            content=content,
            structure=structure,
            epistemic_weight=epistemic_weight,
            scope=scope,
            conditions=conditions,
            measurement_trace_id=measurement_trace.measurement_id,
        )
    
    def _determine_judgment_type(self, relation_graph: RelationGraph) -> JudgmentType:
        """
        Determine type of judgment from discourse type
        """
        discourse = relation_graph.discourse_type
        
        if discourse == DiscourseType.KHABAR:
            return JudgmentType.PROPOSITION
        elif discourse in [DiscourseType.AMKR, DiscourseType.NAHY]:
            return JudgmentType.DIRECTIVE
        elif discourse == DiscourseType.ISTIFHAM:
            return JudgmentType.QUESTION
        else:
            # NAFY, TAWKID can be propositions or conditionals
            return JudgmentType.PROPOSITION
    
    def _construct_content(
        self,
        measurement_trace: MeasurementTrace,
        relation_graph: RelationGraph
    ) -> str:
        """
        Construct the content of the judgment
        
        This is the natural language expression of the judgment.
        """
        # Extract measured elements
        assignments = measurement_trace.final_assignments
        
        # Get primary relation
        primary = relation_graph.primary_predication
        
        if primary:
            subject = primary.get("subject", "")
            predicate = primary.get("predicate", "")
            
            # Construct based on measurements
            subject_measurement = assignments.get(subject, {}).get("measurement", "")
            predicate_measurement = assignments.get(predicate, {}).get("measurement", "")
            
            return f"[{subject}({subject_measurement})] + [{predicate}({predicate_measurement})]"
        
        return "Complex judgment structure"
    
    def _build_structure(
        self,
        measurement_trace: MeasurementTrace,
        relation_graph: RelationGraph
    ) -> Dict[str, Any]:
        """
        Build structured representation of judgment
        """
        return {
            "relations": [r for r in relation_graph.relations],
            "measurements": measurement_trace.final_assignments,
            "operators": [op.to_dict() for op in measurement_trace.operators],
            "discourse_type": relation_graph.discourse_type.value,
        }
    
    def _assign_epistemic_weight(
        self,
        measurement_trace: MeasurementTrace,
        relation_graph: RelationGraph,
        judgment_type: JudgmentType
    ) -> EpistemicWeight:
        """
        Assign epistemic weight (certainty level)
        
        Factors:
        - Quality of measurement
        - Conflicts resolved
        - Evidence strength
        - Judgment type
        """
        # Base confidence
        confidence = 1.0
        level = EpistemicLevel.YAQIN  # Default: certain
        justification_parts = []
        conditions = []
        
        # Reduce confidence if conflicts exist
        if measurement_trace.conflicts:
            unresolved = [c for c in measurement_trace.conflicts if c.get("resolution") == "pending"]
            if unresolved:
                confidence *= 0.4
                level = EpistemicLevel.SHAKK
                justification_parts.append(f"Unresolved conflicts: {len(unresolved)}")
                conditions.append("pending_conflict_resolution")
            else:
                confidence *= 0.7
                level = EpistemicLevel.ZANN
                justification_parts.append(f"Resolved conflicts: {len(measurement_trace.conflicts)}")
        
        # Adjust based on judgment type
        if judgment_type == JudgmentType.QUESTION:
            level = EpistemicLevel.CONDITIONAL
            confidence = 0.5
            justification_parts.append("Interrogative sentence")
        elif judgment_type == JudgmentType.DIRECTIVE:
            level = EpistemicLevel.CONDITIONAL
            justification_parts.append("Directive requires action")
            conditions.append("conditional_on_action")
        
        # Check operator coverage
        operator_count = len(measurement_trace.operators)
        if operator_count == 0:
            confidence = 0.0
            level = EpistemicLevel.SHAKK
            justification_parts.append("No operators found")
        else:
            justification_parts.append(f"Operators applied: {operator_count}")
        
        justification = "; ".join(justification_parts) if justification_parts else "Clear measurement"
        
        return EpistemicWeight(
            level=level,
            confidence=confidence,
            justification=justification,
            conditions=conditions,
        )
    
    def _define_scope(
        self,
        measurement_trace: MeasurementTrace,
        relation_graph: RelationGraph,
        content: str
    ) -> Dict[str, Any]:
        """
        Define the scope (validity domain) of the judgment
        
        This prevents overgeneralization.
        """
        scope = {
            "validity_domain": "current_statement",
            "temporal": "unspecified",
            "spatial": "unspecified",
            "quantification": "unspecified",
        }
        
        # Check for universal quantifiers
        universal_markers = ["كل", "جميع", "all", "every", "always", "never", "لا", "ليس"]
        if any(marker in content for marker in universal_markers):
            scope["quantification"] = "universal"
            scope["validity_domain"] = "all_instances_in_context"
        else:
            scope["quantification"] = "particular"
            scope["validity_domain"] = "specific_instance"
        
        return scope
    
    def _extract_conditions(
        self,
        measurement_trace: MeasurementTrace,
        relation_graph: RelationGraph
    ) -> List[str]:
        """
        Extract conditions that affect the judgment
        """
        conditions = []
        
        # Conditions from measurement
        for operator in measurement_trace.operators:
            conditions.extend(operator.conditions)
        
        # Conditions from conflicts
        if measurement_trace.conflicts:
            conditions.append("conflict_resolution_applied")
        
        # Conditions from discourse
        discourse = relation_graph.discourse_type
        if discourse != DiscourseType.KHABAR:
            conditions.append(f"discourse_type_{discourse.value}")
        
        return list(set(conditions))  # Remove duplicates
