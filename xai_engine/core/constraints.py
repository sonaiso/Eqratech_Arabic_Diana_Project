"""
Global Constraints Enforcement

These constraints are enforced at runtime to prevent:
- Hallucination
- Unjustified conclusions
- Layer violations
- Domain mixing

NO EXCEPTIONS. NO COMPROMISE.
"""

from typing import Any, Dict, Optional
from dataclasses import dataclass


class ConstraintViolation(Exception):
    """Raised when a global constraint is violated"""
    
    def __init__(self, constraint_name: str, message: str, context: Optional[Dict[str, Any]] = None):
        self.constraint_name = constraint_name
        self.context = context or {}
        super().__init__(f"❌ CONSTRAINT VIOLATED: {constraint_name}\n{message}")


@dataclass
class GlobalConstraints:
    """
    Global constraints enforced across all layers and domains
    
    These are ARCHITECTURAL RULES, not configuration options.
    They cannot be disabled or bypassed.
    """
    
    @staticmethod
    def no_result_without_measurement(
        result: Any,
        measurement_trace: Optional[Any]
    ) -> None:
        """
        ❌ لا نتيجة بلا قياس
        No conclusion without measurement
        
        Every output must have a measurement trace showing how it was derived.
        """
        if result is not None and measurement_trace is None:
            raise ConstraintViolation(
                "NO_RESULT_WITHOUT_MEASUREMENT",
                "Cannot produce result without measurement trace.\n"
                "Every conclusion must show HOW it was measured/derived.",
                {"result_type": type(result).__name__}
            )
    
    @staticmethod
    def no_generalization_without_scope(
        statement: str,
        scope: Optional[Dict[str, Any]]
    ) -> None:
        """
        ❌ لا تعميم بلا نطاق
        No generalization without explicit scope
        
        Universal claims must specify their domain of validity.
        """
        # Check for universal quantifiers in Arabic/English
        universal_indicators = [
            "كل", "جميع", "all", "every", "always", 
            "never", "لا", "ليس", "none"
        ]
        
        if any(ind in statement for ind in universal_indicators):
            if scope is None or not scope.get("validity_domain"):
                raise ConstraintViolation(
                    "NO_GENERALIZATION_WITHOUT_SCOPE",
                    f"Statement contains universal quantifier but lacks scope.\n"
                    f"Statement: {statement[:100]}\n"
                    "Universal claims must specify validity domain.",
                    {"statement": statement, "scope": scope}
                )
    
    @staticmethod
    def no_judgment_without_relation(
        judgment: Any,
        relations: Optional[Any]
    ) -> None:
        """
        ❌ لا حكم بلا علاقة
        No judgment without relational structure
        
        A judgment requires relations between elements.
        Isolated concepts cannot form judgments.
        """
        if judgment is not None and (relations is None or not relations):
            raise ConstraintViolation(
                "NO_JUDGMENT_WITHOUT_RELATION",
                "Cannot form judgment without relational structure.\n"
                "Judgments require relations between concepts (إسناد، تقييد، تضمين).",
                {"judgment_type": type(judgment).__name__}
            )
    
    @staticmethod
    def no_explanation_without_trace(
        explanation: Any,
        trace_id: Optional[str]
    ) -> None:
        """
        ❌ لا تفسير بلا سند
        No explanation without documented trace
        
        Every explanation must point to the trace that generated it.
        """
        if explanation is not None and not trace_id:
            raise ConstraintViolation(
                "NO_EXPLANATION_WITHOUT_TRACE",
                "Cannot provide explanation without trace reference.\n"
                "Explanations must be grounded in documented operations.",
                {"explanation_type": type(explanation).__name__}
            )
    
    @staticmethod
    def no_layer_jump(
        from_layer: str,
        to_layer: str,
        layer_sequence: list
    ) -> None:
        """
        ❌ لا قفز بين الطبقات
        No jumping between layers
        
        Layers must be processed in sequence: Form → Semantic → Relational → Measurement → Judgment
        """
        try:
            from_idx = layer_sequence.index(from_layer)
            to_idx = layer_sequence.index(to_layer)
            
            if to_idx != from_idx + 1:
                raise ConstraintViolation(
                    "NO_LAYER_JUMP",
                    f"Cannot jump from {from_layer} to {to_layer}.\n"
                    f"Layers must be processed sequentially: {' → '.join(layer_sequence)}",
                    {"from_layer": from_layer, "to_layer": to_layer}
                )
        except ValueError as e:
            raise ConstraintViolation(
                "INVALID_LAYER",
                f"Unknown layer encountered: {e}",
                {"from_layer": from_layer, "to_layer": to_layer}
            )
    
    @staticmethod
    def no_domain_mixing(
        current_domain: str,
        operator_domain: str
    ) -> None:
        """
        ❌ لا خلط بين المجالات
        No mixing between domains
        
        Operators from one domain cannot be applied to another.
        Language operators ≠ Physics operators ≠ Math operators
        """
        if current_domain != operator_domain:
            raise ConstraintViolation(
                "NO_DOMAIN_MIXING",
                f"Cannot apply {operator_domain} operators to {current_domain} domain.\n"
                "Each domain has its own measurement system.",
                {"current_domain": current_domain, "operator_domain": operator_domain}
            )
    
    @staticmethod
    def no_meaning_without_form(
        meaning: Any,
        form: Optional[Any]
    ) -> None:
        """
        ❌ لا معنى بلا دال
        No meaning without signifier
        
        All meanings must be grounded in form (text, symbols, signals).
        Floating meanings are hallucinations.
        """
        if meaning is not None and form is None:
            raise ConstraintViolation(
                "NO_MEANING_WITHOUT_FORM",
                "Cannot generate meaning without corresponding form.\n"
                "All semantics must be grounded in signifiers (NO HALLUCINATION).",
                {"meaning_type": type(meaning).__name__}
            )
    
    @staticmethod
    def require_operator_for_measurement(
        measurement: Any,
        operator: Optional[Any]
    ) -> None:
        """
        ❌ لا قياس بلا عامل
        No measurement without operator
        
        Measurements require explicit operators (governors, gates, rules).
        """
        if measurement is not None and operator is None:
            raise ConstraintViolation(
                "REQUIRE_OPERATOR_FOR_MEASUREMENT",
                "Cannot perform measurement without operator.\n"
                "All measurements require explicit operators (عامل، حاكم).",
                {"measurement_type": type(measurement).__name__}
            )
    
    @staticmethod
    def validate_all(context: Dict[str, Any]) -> None:
        """
        Run all applicable constraint checks based on context
        
        Args:
            context: Dictionary with keys like 'result', 'measurement_trace', 
                    'judgment', 'relations', etc.
        """
        # Check each constraint if relevant data is present
        if 'result' in context:
            GlobalConstraints.no_result_without_measurement(
                context.get('result'),
                context.get('measurement_trace')
            )
        
        if 'statement' in context:
            GlobalConstraints.no_generalization_without_scope(
                context.get('statement', ''),
                context.get('scope')
            )
        
        if 'judgment' in context:
            GlobalConstraints.no_judgment_without_relation(
                context.get('judgment'),
                context.get('relations')
            )
        
        if 'explanation' in context:
            GlobalConstraints.no_explanation_without_trace(
                context.get('explanation'),
                context.get('trace_id')
            )
        
        if 'meaning' in context:
            GlobalConstraints.no_meaning_without_form(
                context.get('meaning'),
                context.get('form')
            )
        
        if 'measurement' in context:
            GlobalConstraints.require_operator_for_measurement(
                context.get('measurement'),
                context.get('operator')
            )
        
        if 'from_layer' in context and 'to_layer' in context:
            layer_sequence = context.get('layer_sequence', [
                'form', 'semantic', 'relational', 'measurement', 'judgment', 'explanation'
            ])
            GlobalConstraints.no_layer_jump(
                context['from_layer'],
                context['to_layer'],
                layer_sequence
            )
        
        if 'current_domain' in context and 'operator_domain' in context:
            GlobalConstraints.no_domain_mixing(
                context['current_domain'],
                context['operator_domain']
            )
