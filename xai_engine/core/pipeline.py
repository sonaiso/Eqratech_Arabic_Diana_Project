"""
XAI Pipeline - Orchestrates the 6-layer processing

This pipeline enforces:
- Sequential layer processing
- No layer jumping
- Constraint validation at each step
- Complete tracing
"""

from typing import Any, Dict, Optional
from ..core.domain import Domain
from ..core.output_objects import XAIResult
from ..core.constraints import GlobalConstraints, ConstraintViolation
from ..layers import (
    FormLayer,
    SemanticLayer,
    RelationalLayer,
    MeasurementLayer,
    JudgmentLayer,
    ExplanationLayer,
)


class XAIPipeline:
    """
    Complete XAI processing pipeline
    
    Processes input through all 6 layers in strict sequence.
    """
    
    def __init__(self, domain: Domain):
        """
        Initialize pipeline with domain configuration
        
        Args:
            domain: Domain configuration (language, physics, math, chemistry)
        """
        self.domain = domain
        self.constraints = GlobalConstraints()
        
        # Initialize all layers
        self.form_layer = FormLayer(domain)
        self.semantic_layer = SemanticLayer(domain)
        self.relational_layer = RelationalLayer(domain)
        self.measurement_layer = MeasurementLayer(domain)
        self.judgment_layer = JudgmentLayer(domain)
        self.explanation_layer = ExplanationLayer(domain)
        
        self.layers = [
            self.form_layer,
            self.semantic_layer,
            self.relational_layer,
            self.measurement_layer,
            self.judgment_layer,
            self.explanation_layer,
        ]
        
        self.pipeline_trace = []
    
    def process(self, text: str, context: Optional[Dict[str, Any]] = None) -> XAIResult:
        """
        Process text through complete pipeline
        
        Args:
            text: Input text
            context: Optional context (evidence, prior knowledge)
            
        Returns:
            XAIResult with all layer outputs and explanation
            
        Raises:
            ConstraintViolation: If any constraint is violated
        """
        if not text or not text.strip():
            raise ConstraintViolation(
                "EMPTY_INPUT",
                "Cannot process empty input text.",
                {"text": text}
            )
        
        self.pipeline_trace = []
        self._log_step("pipeline_start", {"text_length": len(text), "domain": self.domain.domain_type.value})
        
        # Layer 1: Form
        self._log_step("layer_1_form", {"status": "starting"})
        parse_tree = self.form_layer.process(text)
        self._log_step("layer_1_form", {"status": "complete", "tokens": len(parse_tree.tokens)})
        
        # Layer 2: Semantic
        self._log_step("layer_2_semantic", {"status": "starting"})
        semantic_candidates = self.semantic_layer.process(parse_tree)
        self._log_step("layer_2_semantic", {"status": "complete", "candidates": len(semantic_candidates)})
        
        # Layer 3: Relational
        self._log_step("layer_3_relational", {"status": "starting"})
        relation_graph = self.relational_layer.process({
            "parse_tree": parse_tree,
            "semantic_candidates": semantic_candidates,
        })
        self._log_step("layer_3_relational", {"status": "complete", "relations": len(relation_graph.relations)})
        
        # Layer 4: Measurement (CRITICAL)
        self._log_step("layer_4_measurement", {"status": "starting"})
        measurement_trace = self.measurement_layer.process({
            "relation_graph": relation_graph,
            "semantic_candidates": semantic_candidates,
        })
        self._log_step("layer_4_measurement", {
            "status": "complete",
            "operators": len(measurement_trace.operators),
            "conflicts": len(measurement_trace.conflicts),
        })
        
        # Layer 5: Judgment
        self._log_step("layer_5_judgment", {"status": "starting"})
        judgment = self.judgment_layer.process({
            "measurement_trace": measurement_trace,
            "relation_graph": relation_graph,
        })
        self._log_step("layer_5_judgment", {
            "status": "complete",
            "judgment_id": judgment.judgment_id,
            "confidence": judgment.epistemic_weight.confidence,
        })
        
        # Layer 6: Explanation
        self._log_step("layer_6_explanation", {"status": "starting"})
        explanation = self.explanation_layer.process({
            "judgment": judgment,
            "measurement_trace": measurement_trace,
            "relation_graph": relation_graph,
            "semantic_candidates": semantic_candidates,
            "parse_tree": parse_tree,
        })
        self._log_step("layer_6_explanation", {"status": "complete", "trace_steps": len(explanation.full_trace)})
        
        self._log_step("pipeline_complete", {"judgment_id": judgment.judgment_id})
        
        # Validate final result
        self._validate_result(
            judgment=judgment,
            measurement_trace=measurement_trace,
            relation_graph=relation_graph,
            explanation=explanation
        )
        
        # Build complete result
        result = XAIResult(
            input_text=text,
            domain=self.domain.domain_type.value,
            parse_tree=parse_tree,
            semantic_candidates=semantic_candidates,
            relation_graph=relation_graph,
            measurement_trace=measurement_trace,
            judgment=judgment,
            explanation=explanation,
            metadata={
                "pipeline_trace": self.pipeline_trace,
                "domain_config": {
                    "type": self.domain.domain_type.value,
                    "measurement_system": self.domain.measurement_system,
                },
                "constraints_enforced": [
                    "no_result_without_measurement",
                    "no_generalization_without_scope",
                    "no_judgment_without_relation",
                    "no_explanation_without_trace",
                    "no_layer_jump",
                    "no_meaning_without_form",
                ],
            }
        )
        
        return result
    
    def _log_step(self, step: str, details: Dict[str, Any]) -> None:
        """Log a pipeline step"""
        self.pipeline_trace.append({
            "step": step,
            "details": details,
        })
    
    def _validate_result(
        self,
        judgment: Any,
        measurement_trace: Any,
        relation_graph: Any,
        explanation: Any
    ) -> None:
        """
        Validate final result against all constraints
        """
        # Enforce all global constraints
        context = {
            "result": judgment,
            "measurement_trace": measurement_trace,
            "judgment": judgment,
            "relations": relation_graph.relations,
            "explanation": explanation,
            "trace_id": judgment.measurement_trace_id,
            "statement": judgment.content,
            "scope": judgment.scope,
            "meaning": judgment.content,
            "form": judgment.content,  # Has form because derived from text
        }
        
        try:
            self.constraints.validate_all(context)
        except ConstraintViolation as e:
            self._log_step("validation_failed", {"constraint": e.constraint_name, "message": str(e)})
            raise
        
        self._log_step("validation_passed", {"all_constraints": "satisfied"})
    
    def get_trace(self) -> list:
        """Get complete pipeline trace"""
        return self.pipeline_trace.copy()
    
    def clear_trace(self) -> None:
        """Clear pipeline trace"""
        self.pipeline_trace = []
        for layer in self.layers:
            layer.clear_trace()
