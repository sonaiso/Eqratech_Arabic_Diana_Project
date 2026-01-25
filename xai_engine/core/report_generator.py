"""
Report Generator - Converts XAI results to enhanced explanatory reports

This module transforms standard XAI results into comprehensive explanatory
reports with executive summaries, failure analysis, and governance annotations.
"""

from typing import Dict, List, Any
import time
from .explanatory_schema import (
    ExplanatoryReport,
    ExecutiveSummary,
    LayerTrace,
    FailurePoint,
    ScopeDefinition,
    GovernanceAnnotation,
)
from .output_objects import XAIResult, EpistemicLevel


class ReportGenerator:
    """
    Generates enhanced explanatory reports from XAI results
    
    This class transforms the standard XAI pipeline output into
    comprehensive reports with:
    - Executive summaries with failure analysis
    - Detailed layer traces
    - Before/After chains
    - C1/C2/C3 governance annotations
    """
    
    def __init__(self, xai_version: str = "1.0.0", architecture: str = "locked_v1"):
        self.xai_version = xai_version
        self.architecture = architecture
    
    def generate_report(
        self,
        xai_result: XAIResult,
        processing_time_ms: float = 0.0
    ) -> ExplanatoryReport:
        """
        Generate complete explanatory report from XAI result
        
        Args:
            xai_result: Standard XAI pipeline result
            processing_time_ms: Time taken to process (milliseconds)
            
        Returns:
            ExplanatoryReport with all components
        """
        # Generate executive summary
        executive_summary = self._generate_executive_summary(xai_result)
        
        # Generate layer traces
        layer_traces = self._generate_layer_traces(xai_result)
        
        # Extract before/after chain
        before_after_chain = self._extract_before_after_chain(xai_result)
        
        # Generate governance annotation
        governance = self._generate_governance(xai_result)
        
        return ExplanatoryReport(
            executive_summary=executive_summary,
            layer_traces=layer_traces,
            before_after_chain=before_after_chain,
            governance=governance,
            input_text=xai_result.input_text,
            domain=xai_result.domain,
            processing_time_ms=processing_time_ms,
            xai_version=self.xai_version,
            architecture=self.architecture,
        )
    
    def _generate_executive_summary(self, xai_result: XAIResult) -> ExecutiveSummary:
        """Generate executive summary with failure analysis"""
        
        judgment = xai_result.judgment
        
        # Generate scope definition
        scope = ScopeDefinition(
            validity_domain=judgment.scope.get('validity_domain', 'unspecified'),
            temporal_scope=judgment.scope.get('temporal', 'unspecified'),
            spatial_scope=judgment.scope.get('spatial', 'unspecified'),
            quantification=judgment.scope.get('quantification', 'particular'),
            preconditions=[
                "Form analysis completed",
                "Relations detected",
                "Measurement performed",
            ],
            exclusions=[]
        )
        
        # Identify failure points
        failure_points = self._identify_failure_points(xai_result)
        
        # Extract key evidence
        key_evidence = []
        if xai_result.measurement_trace.operators:
            key_evidence.append(
                f"{len(xai_result.measurement_trace.operators)} operators applied"
            )
        if xai_result.relation_graph.relations:
            key_evidence.append(
                f"{len(xai_result.relation_graph.relations)} relations detected"
            )
        key_evidence.append(
            f"Measurement trace: {xai_result.measurement_trace.measurement_id}"
        )
        
        return ExecutiveSummary(
            judgment_text=judgment.content,
            judgment_type=judgment.judgment_type.value,
            epistemic_weight=judgment.epistemic_weight.to_dict(),
            scope=scope,
            failure_points=failure_points,
            key_evidence=key_evidence,
        )
    
    def _identify_failure_points(self, xai_result: XAIResult) -> List[FailurePoint]:
        """
        Identify potential failure points in the judgment
        
        Analyzes the judgment to determine when/why it might fail
        """
        failure_points = []
        
        judgment = xai_result.judgment
        measurement = xai_result.measurement_trace
        relations = xai_result.relation_graph
        
        # Check for conflicts in measurement
        if measurement.conflicts:
            for conflict in measurement.conflicts:
                failure_points.append(FailurePoint(
                    condition=f"Measurement conflict remains unresolved: {conflict.get('conflict_id')}",
                    reason="Multiple operators with contradictory effects",
                    impact="Judgment confidence reduced, alternative interpretations possible",
                    mitigation="Review operator precedence rules and context"
                ))
        
        # Check epistemic weight
        if judgment.epistemic_weight.level == EpistemicLevel.SHAKK:
            failure_points.append(FailurePoint(
                condition="Low epistemic confidence (SHAKK level)",
                reason=judgment.epistemic_weight.justification,
                impact="Judgment may not hold under scrutiny",
                mitigation="Gather more evidence or constrain scope"
            ))
        
        # Check for conditional judgments
        if judgment.conditions:
            for condition in judgment.conditions:
                failure_points.append(FailurePoint(
                    condition=f"Conditional on: {condition}",
                    reason="Judgment validity depends on external condition",
                    impact="Judgment invalid if condition changes",
                    mitigation="Monitor condition or reprocess with updated context"
                ))
        
        # Check scope limitations
        if judgment.scope.get('quantification') == 'universal':
            failure_points.append(FailurePoint(
                condition="Universal quantification applied",
                reason="Judgment claims to apply to all instances",
                impact="Single counterexample invalidates judgment",
                mitigation="Verify scope constraints or reduce to particular quantification"
            ))
        
        # Check for missing operators
        if not measurement.operators:
            failure_points.append(FailurePoint(
                condition="No operators detected",
                reason="Measurement layer found no governing operators",
                impact="Judgment lacks measurement foundation",
                mitigation="Review input structure or add explicit operators"
            ))
        
        # Domain-specific failure points
        domain = xai_result.domain
        if domain == "language":
            # Language-specific failures
            if not relations.primary_predication:
                failure_points.append(FailurePoint(
                    condition="No primary predication found",
                    reason="Sentence lacks clear subject-predicate structure",
                    impact="Judgment may misinterpret sentence meaning",
                    mitigation="Clarify sentence structure or add explicit copula"
                ))
        
        return failure_points
    
    def _generate_layer_traces(self, xai_result: XAIResult) -> List[LayerTrace]:
        """Generate detailed traces for each layer"""
        
        traces = []
        
        # Layer 1: Form
        traces.append(LayerTrace(
            layer_name="Form (الدال)",
            input_summary=f"Raw text: '{xai_result.input_text}'",
            processing_steps=[
                f"Tokenized into {len(xai_result.parse_tree.tokens)} tokens",
                f"Analyzed phonology: {xai_result.parse_tree.phonology.get('total_consonants', 0)} consonants",
                f"Analyzed morphology: {len(xai_result.parse_tree.morphology.get('forms', []))} forms",
                f"Assigned POS tags: {len(xai_result.parse_tree.pos_tags)} tags",
            ],
            output_summary=f"Parse tree with {len(xai_result.parse_tree.tokens)} tokens",
            decisions_made=[
                {
                    "decision": "Tokenization strategy",
                    "reason": "Whitespace-based splitting for Arabic text"
                }
            ]
        ))
        
        # Layer 2: Semantic
        total_candidates = sum(len(sc.candidates) for sc in xai_result.semantic_candidates)
        traces.append(LayerTrace(
            layer_name="Semantic (المدلول)",
            input_summary=f"Parse tree from Form layer",
            processing_steps=[
                f"Generated {total_candidates} meaning candidates",
                "Classified denotation types (Mutabaqa/Tadammun/Iltizam)",
                "Identified concept types (Entity/Event/Relation/etc)",
            ],
            output_summary=f"{len(xai_result.semantic_candidates)} tokens with candidates",
            decisions_made=[
                {
                    "decision": "Candidate generation",
                    "reason": "Lexicon lookup with multiple senses"
                }
            ],
            alternatives_rejected=[
                {
                    "alternative": "Single meaning per token",
                    "reason": "Would prevent context-based disambiguation"
                }
            ]
        ))
        
        # Layer 3: Relational
        traces.append(LayerTrace(
            layer_name="Relational (النِّسب)",
            input_summary="Form + Semantic candidates",
            processing_steps=[
                f"Detected {len(xai_result.relation_graph.relations)} relations",
                f"Classified discourse type: {xai_result.relation_graph.discourse_type.value}",
                f"Identified primary predication: {'Yes' if xai_result.relation_graph.primary_predication else 'No'}",
            ],
            output_summary=f"Relation graph with {len(xai_result.relation_graph.relations)} relations",
            decisions_made=[
                {
                    "decision": f"Discourse type: {xai_result.relation_graph.discourse_type.value}",
                    "reason": "Based on discourse markers and structure"
                }
            ]
        ))
        
        # Layer 4: Measurement
        traces.append(LayerTrace(
            layer_name="Measurement (الإعراب)",
            input_summary="Relation graph",
            processing_steps=[
                f"Detected {len(xai_result.measurement_trace.operators)} operators",
                f"Applied {len(xai_result.measurement_trace.applications)} measurements",
                f"Resolved {len(xai_result.measurement_trace.conflicts)} conflicts",
                f"Generated {len(xai_result.measurement_trace.final_assignments)} final assignments",
            ],
            output_summary=f"Measurement trace: {xai_result.measurement_trace.measurement_id}",
            decisions_made=[
                {
                    "decision": "Operator selection",
                    "reason": "Based on relational structure and POS tags"
                },
                {
                    "decision": "Conflict resolution",
                    "reason": "Applied precedence rules" if xai_result.measurement_trace.conflicts else "No conflicts"
                }
            ]
        ))
        
        # Layer 5: Judgment
        traces.append(LayerTrace(
            layer_name="Judgment (الحكم)",
            input_summary="Measurement trace + Relations",
            processing_steps=[
                f"Formed judgment type: {xai_result.judgment.judgment_type.value}",
                f"Assigned epistemic weight: {xai_result.judgment.epistemic_weight.level.value}",
                f"Defined scope: {xai_result.judgment.scope.get('validity_domain')}",
                f"Extracted {len(xai_result.judgment.conditions)} conditions",
            ],
            output_summary=f"Judgment: {xai_result.judgment.content}",
            decisions_made=[
                {
                    "decision": f"Epistemic weight: {xai_result.judgment.epistemic_weight.level.value}",
                    "reason": xai_result.judgment.epistemic_weight.justification
                }
            ]
        ))
        
        # Layer 6: Explanation
        traces.append(LayerTrace(
            layer_name="Explanation (التفسير)",
            input_summary="Complete pipeline output",
            processing_steps=[
                "Generated why-chains for all decisions",
                "Built before-after chains",
                "Identified alternative paths",
                f"Created {len(xai_result.explanation.full_trace)} trace steps",
            ],
            output_summary=f"Complete explanation with {len(xai_result.explanation.alternative_paths)} alternatives",
            decisions_made=[
                {
                    "decision": "Explanation depth",
                    "reason": "Full trace with all decision points"
                }
            ]
        ))
        
        return traces
    
    def _extract_before_after_chain(self, xai_result: XAIResult) -> Dict[str, Any]:
        """Extract before/after chain from explanation"""
        
        ba = xai_result.explanation.before_after
        
        return {
            "judgment_id": ba.judgment_id,
            "preconditions": ba.preconditions,
            "consequences": ba.consequences,
            "invalidating_conditions": ba.invalidating_conditions,
        }
    
    def _generate_governance(self, xai_result: XAIResult) -> GovernanceAnnotation:
        """
        Generate C1/C2/C3 governance annotation
        
        C1: Conceptual framework
        C2: Representational system
        C3: Verification rules
        """
        
        domain = xai_result.domain
        
        # Domain-specific governance
        if domain == "language":
            c1 = "Arabic linguistic ontology (phonology → morphology → syntax → semantics)"
            c2 = "Token-based representation with operator-governed transformations"
            c3 = "Grammatical verification through operator application (إعراب)"
            epistemic_order = [
                "Lexicon attestation",
                "Morphological patterns",
                "Syntactic rules",
                "Semantic coherence"
            ]
        elif domain == "physics":
            c1 = "Physical reality model (observation → hypothesis → theory)"
            c2 = "Mathematical representation with units and error bounds"
            c3 = "Experimental verification with reproducibility requirements"
            epistemic_order = [
                "Direct observation",
                "Experimental measurement",
                "Theoretical derivation",
                "Model prediction"
            ]
        elif domain == "mathematics":
            c1 = "Mathematical ontology (axioms → definitions → theorems)"
            c2 = "Formal symbolic representation"
            c3 = "Logical proof verification"
            epistemic_order = [
                "Axioms",
                "Proven theorems",
                "Definitions",
                "Lemmas"
            ]
        elif domain == "chemistry":
            c1 = "Chemical reality model (elements → compounds → reactions)"
            c2 = "Molecular representation with stoichiometry"
            c3 = "Experimental verification with reaction conditions"
            epistemic_order = [
                "Empirical observation",
                "Reaction experiments",
                "Theoretical chemistry",
                "Computational models"
            ]
        else:
            c1 = "General conceptual framework"
            c2 = "Standard representation"
            c3 = "Evidence-based verification"
            epistemic_order = None
        
        # Extract constraints that were applied
        constraints = [
            "no_result_without_measurement",
            "no_generalization_without_scope",
            "no_judgment_without_relation",
            "no_explanation_without_trace",
            "no_layer_jump",
            "no_domain_mixing",
            "no_meaning_without_form",
            "require_operator_for_measurement",
        ]
        
        return GovernanceAnnotation(
            c1_framework=c1,
            c2_representation=c2,
            c3_verification=c3,
            epistemic_order=epistemic_order,
            constraints=constraints,
        )
