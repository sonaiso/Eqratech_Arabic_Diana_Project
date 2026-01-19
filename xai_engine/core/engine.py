"""
XAI Engine - Main entry point

This is the top-level interface for the XAI system.
"""

from typing import Any, Dict, Optional
from .domain import Domain, DomainType
from .pipeline import XAIPipeline
from .output_objects import XAIResult


class XAIEngine:
    """
    XAI Engine - Explainable AI with Strict Epistemological Constraints
    
    This engine:
    - Generates judgments, not predictions
    - Measures every transition
    - Explains every decision
    - Prevents hallucination through architectural locks
    
    Usage:
        >>> engine = XAIEngine.for_language()
        >>> result = engine.process("النص العربي هنا")
        >>> print(result.judgment.content)
        >>> print(result.explanation.why_this_judgment.answer)
    """
    
    def __init__(self, domain: Domain):
        """
        Initialize XAI engine with domain configuration
        
        Args:
            domain: Domain configuration
        """
        self.domain = domain
        self.pipeline = XAIPipeline(domain)
        self.version = "1.0.0"
        self.architecture = "locked_v1"
    
    @classmethod
    def for_language(cls, operators_catalog: Optional[Dict[str, Any]] = None) -> "XAIEngine":
        """
        Create XAI engine for language domain
        
        Args:
            operators_catalog: Optional catalog of grammatical operators
            
        Returns:
            XAIEngine configured for language processing
        """
        domain = Domain.language(operators_catalog)
        return cls(domain)
    
    @classmethod
    def for_physics(cls, operators_catalog: Optional[Dict[str, Any]] = None) -> "XAIEngine":
        """
        Create XAI engine for physics domain
        
        Args:
            operators_catalog: Optional catalog of physical measurement operators
            
        Returns:
            XAIEngine configured for physics
        """
        domain = Domain.physics(operators_catalog)
        return cls(domain)
    
    @classmethod
    def for_mathematics(cls, operators_catalog: Optional[Dict[str, Any]] = None) -> "XAIEngine":
        """
        Create XAI engine for mathematics domain
        
        Args:
            operators_catalog: Optional catalog of logical operators
            
        Returns:
            XAIEngine configured for mathematics
        """
        domain = Domain.mathematics(operators_catalog)
        return cls(domain)
    
    @classmethod
    def for_chemistry(cls, operators_catalog: Optional[Dict[str, Any]] = None) -> "XAIEngine":
        """
        Create XAI engine for chemistry domain
        
        Args:
            operators_catalog: Optional catalog of reaction operators
            
        Returns:
            XAIEngine configured for chemistry
        """
        domain = Domain.chemistry(operators_catalog)
        return cls(domain)
    
    def process(
        self,
        text: str,
        context: Optional[Dict[str, Any]] = None
    ) -> XAIResult:
        """
        Process input text and generate judgment with explanation
        
        Args:
            text: Input text to process
            context: Optional context (evidence, prior knowledge)
            
        Returns:
            XAIResult with complete processing trace and explanation
            
        Example:
            >>> engine = XAIEngine.for_language()
            >>> result = engine.process("محمد طالب مجتهد")
            >>> print(result.judgment.content)
            >>> print(result.explanation.why_this_judgment.answer)
        """
        return self.pipeline.process(text, context)
    
    def get_info(self) -> Dict[str, Any]:
        """
        Get engine information
        
        Returns:
            Dictionary with engine metadata
        """
        return {
            "version": self.version,
            "architecture": self.architecture,
            "domain": {
                "type": self.domain.domain_type.value,
                "name": self.domain.name,
                "measurement_system": self.domain.measurement_system,
            },
            "layers": [
                "form",
                "semantic",
                "relational",
                "measurement",
                "judgment",
                "explanation",
            ],
            "constraints": [
                "no_result_without_measurement",
                "no_generalization_without_scope",
                "no_judgment_without_relation",
                "no_explanation_without_trace",
                "no_layer_jump",
                "no_domain_mixing",
                "no_meaning_without_form",
                "require_operator_for_measurement",
            ],
            "philosophy": "Thinking = Reality + Prior Knowledge + Relations → Judgment",
        }
    
    def get_trace(self) -> list:
        """
        Get the pipeline trace from last processing
        
        Returns:
            List of trace entries
        """
        return self.pipeline.get_trace()
    
    def clear_trace(self) -> None:
        """Clear the pipeline trace"""
        self.pipeline.clear_trace()
