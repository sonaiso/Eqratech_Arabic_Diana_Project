"""
Explanation Layer (التفسير) - Layer 6

Purpose: Generate complete explanation for the judgment
Output: ExplanationReport

This is the CORE of XAI - making everything explainable.

This layer answers:
- Why this meaning?
- Why this relation?
- Why this measurement?
- Why this judgment?
- What came before?
- What follows from this?
- What alternatives were rejected and why?

NO EXPLANATION → NO OUTPUT
"""

from typing import Any, Dict, List, Optional
from .base import LayerBase
from ..core.output_objects import (
    JudgmentObject,
    ExplanationReport,
    WhyChain,
    BeforeAfterChain,
    MeasurementTrace,
    RelationGraph,
    SemanticCandidates,
)
from ..core.domain import Domain


class ExplanationLayer(LayerBase):
    """
    Layer 6: Explanation generation
    
    Generates complete why-chains for every decision in the pipeline.
    """
    
    def __init__(self, domain: Domain):
        super().__init__("explanation", domain)
    
    def process(self, input_data: Dict[str, Any]) -> ExplanationReport:
        """
        Generate complete explanation for the judgment
        
        Args:
            input_data: Dict with all previous layers' outputs
            
        Returns:
            ExplanationReport with complete why-chains
        """
        self.validate_input(input_data, "judgment")
        
        judgment = input_data["judgment"]
        measurement_trace = input_data["measurement_trace"]
        relation_graph = input_data["relation_graph"]
        semantic_candidates = input_data["semantic_candidates"]
        parse_tree = input_data["parse_tree"]
        
        self.log_operation("start_explanation_generation", {
            "judgment_id": judgment.judgment_id
        })
        
        # Enforce: no explanation without trace
        self.constraints.no_explanation_without_trace(
            explanation="generating",
            trace_id=judgment.measurement_trace_id
        )
        
        # Build why-chains
        why_meaning = self._explain_meaning_selection(
            semantic_candidates,
            measurement_trace
        )
        
        why_relation = self._explain_relation_detection(
            relation_graph,
            parse_tree
        )
        
        why_measurement = self._explain_measurement_process(
            measurement_trace,
            relation_graph
        )
        
        why_judgment = self._explain_judgment_formation(
            judgment,
            measurement_trace,
            relation_graph
        )
        
        # Build before-after chain
        before_after = self._build_before_after_chain(
            judgment,
            measurement_trace,
            relation_graph
        )
        
        # Build full trace
        full_trace = self._build_full_trace(input_data)
        
        # Identify alternative paths
        alternative_paths = self._identify_alternatives(
            semantic_candidates,
            measurement_trace,
            judgment
        )
        
        self.log_operation("explanation_complete", {
            "why_chains": 4,
            "trace_steps": len(full_trace),
            "alternatives": len(alternative_paths),
        })
        
        return ExplanationReport(
            judgment_id=judgment.judgment_id,
            why_this_meaning=why_meaning,
            why_this_relation=why_relation,
            why_this_measurement=why_measurement,
            why_this_judgment=why_judgment,
            before_after=before_after,
            full_trace=full_trace,
            alternative_paths=alternative_paths,
        )
    
    def _explain_meaning_selection(
        self,
        semantic_candidates: List[SemanticCandidates],
        measurement_trace: MeasurementTrace
    ) -> WhyChain:
        """
        Explain why these meanings were selected
        
        Answer: Because measurement selected them from candidates.
        """
        # Count total candidates
        total_candidates = sum(len(sc.candidates) for sc in semantic_candidates)
        selected_count = len(measurement_trace.final_assignments)
        
        question = "Why were these specific meanings selected?"
        answer = (
            f"Out of {total_candidates} candidate meanings, "
            f"{selected_count} were selected through measurement. "
            "Selection was NOT arbitrary - it was determined by operator application."
        )
        evidence = [
            f"Total candidates: {total_candidates}",
            f"Measurement trace: {measurement_trace.measurement_id}",
            f"Operators applied: {len(measurement_trace.operators)}",
        ]
        
        # Next level: Why these operators?
        next_why = WhyChain(
            question="Why were these operators used?",
            answer="Operators were detected from relational structure. "
                   "They are not chosen - they are derived from form and relations.",
            evidence=[
                f"Operators detected: {[op.operator_id for op in measurement_trace.operators]}",
                "Detection based on POS tags and relational patterns",
            ],
            next_why=None,
        )
        
        return WhyChain(
            question=question,
            answer=answer,
            evidence=evidence,
            next_why=next_why,
        )
    
    def _explain_relation_detection(
        self,
        relation_graph: RelationGraph,
        parse_tree: Any
    ) -> WhyChain:
        """
        Explain why these relations were detected
        
        Answer: Because of structural patterns in the form.
        """
        question = "Why were these relations detected?"
        answer = (
            f"Detected {len(relation_graph.relations)} relations "
            f"based on structural patterns in the parsed form. "
            "Relations are required for judgment formation."
        )
        evidence = [
            f"Parse tree depth: {parse_tree.tree.get('depth', 0)}",
            f"POS tags: {len(parse_tree.pos_tags)}",
            f"Primary predication: {relation_graph.primary_predication is not None}",
            f"Discourse type: {relation_graph.discourse_type.value}",
        ]
        
        return WhyChain(
            question=question,
            answer=answer,
            evidence=evidence,
            next_why=None,
        )
    
    def _explain_measurement_process(
        self,
        measurement_trace: MeasurementTrace,
        relation_graph: RelationGraph
    ) -> WhyChain:
        """
        Explain why measurement was performed this way
        
        Answer: Because operators were applied according to their rules.
        """
        question = "Why was measurement performed this way?"
        answer = (
            f"Applied {len(measurement_trace.operators)} operators "
            f"in {len(measurement_trace.applications)} applications. "
        )
        
        if measurement_trace.conflicts:
            answer += (
                f"Resolved {len(measurement_trace.conflicts)} conflicts "
                "using constraint rules."
            )
        
        evidence = [
            f"Operators: {[op.operator_id for op in measurement_trace.operators]}",
            f"Applications: {len(measurement_trace.applications)}",
            f"Conflicts: {len(measurement_trace.conflicts)}",
            f"Final assignments: {len(measurement_trace.final_assignments)}",
        ]
        
        # Next level: Why these conflict resolutions?
        if measurement_trace.conflicts:
            next_why = WhyChain(
                question="Why were conflicts resolved this way?",
                answer="Conflicts resolved using precedence and domain-specific rules.",
                evidence=[f"Conflict {c['conflict_id']}: {c.get('resolution', 'pending')}" 
                         for c in measurement_trace.conflicts],
                next_why=None,
            )
        else:
            next_why = None
        
        return WhyChain(
            question=question,
            answer=answer,
            evidence=evidence,
            next_why=next_why,
        )
    
    def _explain_judgment_formation(
        self,
        judgment: JudgmentObject,
        measurement_trace: MeasurementTrace,
        relation_graph: RelationGraph
    ) -> WhyChain:
        """
        Explain why this judgment was formed
        
        Answer: Because measurement and relations combined to form it.
        """
        question = "Why was this judgment formed?"
        answer = (
            f"Judgment type: {judgment.judgment_type.value}. "
            f"Epistemic weight: {judgment.epistemic_weight.level.value} "
            f"({judgment.epistemic_weight.confidence:.2f}). "
            f"Based on measurement trace {judgment.measurement_trace_id}."
        )
        
        evidence = [
            f"Judgment ID: {judgment.judgment_id}",
            f"Content: {judgment.content}",
            f"Epistemic justification: {judgment.epistemic_weight.justification}",
            f"Scope: {judgment.scope.get('validity_domain', 'unspecified')}",
            f"Conditions: {len(judgment.conditions)}",
        ]
        
        return WhyChain(
            question=question,
            answer=answer,
            evidence=evidence,
            next_why=None,
        )
    
    def _build_before_after_chain(
        self,
        judgment: JudgmentObject,
        measurement_trace: MeasurementTrace,
        relation_graph: RelationGraph
    ) -> BeforeAfterChain:
        """
        Build before-after chain showing dependencies
        """
        preconditions = [
            "Input text must be provided",
            "Form analysis must complete",
            "Relations must be detected",
            "Operators must be available",
            "Measurement must be performed",
        ]
        
        # Add specific preconditions
        if measurement_trace.operators:
            preconditions.append(f"Operators detected: {len(measurement_trace.operators)}")
        
        # Consequences
        consequences = []
        if judgment.judgment_type.value == "proposition":
            consequences.append("Proposition can be evaluated for truth")
            consequences.append("Can be used in further reasoning")
        elif judgment.judgment_type.value == "directive":
            consequences.append("Action is specified")
            consequences.append("Compliance can be evaluated")
        
        # Add scope-based consequences
        if judgment.scope.get("quantification") == "universal":
            consequences.append("Applies to all instances in scope")
        else:
            consequences.append("Applies only to specific instance")
        
        # Invalidating conditions
        invalidating_conditions = []
        for condition in judgment.conditions:
            invalidating_conditions.append(f"If {condition} changes")
        
        if measurement_trace.conflicts:
            invalidating_conditions.append("If conflict resolution is revised")
        
        return BeforeAfterChain(
            judgment_id=judgment.judgment_id,
            preconditions=preconditions,
            consequences=consequences,
            invalidating_conditions=invalidating_conditions,
        )
    
    def _build_full_trace(self, input_data: Dict[str, Any]) -> List[str]:
        """
        Build complete trace from input to output
        """
        trace = [
            "Step 1: Input text received",
            "Step 2: Form layer - tokenization, phonology, morphology, POS tagging",
            "Step 3: Semantic layer - generate meaning candidates",
            "Step 4: Relational layer - detect relations and discourse type",
            "Step 5: Measurement layer - detect operators and apply measurements",
            "Step 6: Judgment layer - form judgment with epistemic weight",
            "Step 7: Explanation layer - generate why-chains (current step)",
        ]
        
        # Add specific details
        parse_tree = input_data.get("parse_tree")
        if parse_tree:
            trace.append(f"  - Tokens: {len(parse_tree.tokens)}")
        
        semantic_candidates = input_data.get("semantic_candidates", [])
        trace.append(f"  - Semantic candidates: {len(semantic_candidates)}")
        
        relation_graph = input_data.get("relation_graph")
        if relation_graph:
            trace.append(f"  - Relations: {len(relation_graph.relations)}")
        
        measurement_trace = input_data.get("measurement_trace")
        if measurement_trace:
            trace.append(f"  - Operators: {len(measurement_trace.operators)}")
            trace.append(f"  - Applications: {len(measurement_trace.applications)}")
        
        judgment = input_data.get("judgment")
        if judgment:
            trace.append(f"  - Judgment: {judgment.judgment_id}")
            trace.append(f"  - Confidence: {judgment.epistemic_weight.confidence:.2f}")
        
        return trace
    
    def _identify_alternatives(
        self,
        semantic_candidates: List[SemanticCandidates],
        measurement_trace: MeasurementTrace,
        judgment: JudgmentObject
    ) -> List[Dict[str, Any]]:
        """
        Identify alternative paths not taken and explain why
        """
        alternatives = []
        
        # Alternative meanings not selected
        for sc in semantic_candidates:
            if len(sc.candidates) > 1:
                selected = measurement_trace.final_assignments.get(sc.token_id, {})
                for candidate in sc.candidates:
                    alternatives.append({
                        "type": "alternative_meaning",
                        "token_id": sc.token_id,
                        "alternative": candidate.get("meaning", ""),
                        "reason_rejected": "Not selected by measurement process",
                        "would_lead_to": "Different judgment",
                    })
        
        # Alternative conflict resolutions
        for conflict in measurement_trace.conflicts:
            if conflict.get("resolution") != "pending":
                alternatives.append({
                    "type": "alternative_resolution",
                    "conflict_id": conflict["conflict_id"],
                    "alternative": "Different conflict resolution strategy",
                    "reason_rejected": f"Used {conflict['resolution']} instead",
                    "would_lead_to": "Different measurement assignments",
                })
        
        return alternatives[:10]  # Limit to 10 alternatives
