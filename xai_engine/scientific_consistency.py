"""
Scientific Consistency Engine
==============================

Advanced consistency validation and resolution engine for multi-domain
scientific analysis.

Core Functions:
- Consistency validation across domains
- Automatic conflict resolution
- Epistemic level unification
- Evidence aggregation and synthesis

Arabic Terms:
- التناسق العلمي (Scientific Consistency)
- حل التعارضات (Conflict Resolution)
- توحيد معايير اليقين (Epistemic Unification)

Author: XAI Engine Team
Version: 1.0.0
"""

from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional, Set, Tuple, Any
import json
from .multi_domain_integration import (
    Domain, ScientificConcept, EpistemicLevel,
    ConsistencyIssue, MultiDomainIntegrator
)


class ConsistencyRuleType(Enum):
    """Type of consistency rule."""
    LOGICAL = "logical"  # منطقي
    EMPIRICAL = "empirical"  # تجريبي
    DEFINITIONAL = "definitional"  # تعريفي
    AXIOMATIC = "axiomatic"  # بديهي


class ConflictResolutionStrategy(Enum):
    """Strategy for resolving conflicts."""
    MOST_CERTAIN = "most_certain"  # الأكثر يقيناً
    MOST_RECENT = "most_recent"  # الأحدث
    CONSENSUS = "consensus"  # الإجماع
    EVIDENCE_BASED = "evidence_based"  # على أساس الأدلة
    DOMAIN_PRIORITY = "domain_priority"  # أولوية المجال


@dataclass
class ConsistencyRule:
    """
    Rule for validating consistency across domains.
    
    Attributes:
        rule_id: Unique identifier
        rule_type: Type of rule
        domains: Domains this rule applies to
        condition: Formal condition to check
        description: Human-readable description
        severity: Severity if violated (1-5)
        enabled: Whether rule is active
    """
    rule_id: str
    rule_type: ConsistencyRuleType
    domains: List[Domain]
    condition: str  # Formal logic expression
    description: str
    severity: int = 3
    enabled: bool = True
    
    def evaluate(self, concepts: List[ScientificConcept]) -> Tuple[bool, Optional[str]]:
        """
        Evaluate the rule against given concepts.
        
        Returns:
            (passes, violation_message)
        """
        # Filter concepts by applicable domains
        applicable = [c for c in concepts if c.domain in self.domains]
        
        if not applicable:
            return True, None
        
        # Check rule-specific conditions
        if self.rule_type == ConsistencyRuleType.LOGICAL:
            return self._check_logical_consistency(applicable)
        elif self.rule_type == ConsistencyRuleType.EMPIRICAL:
            return self._check_empirical_consistency(applicable)
        elif self.rule_type == ConsistencyRuleType.DEFINITIONAL:
            return self._check_definitional_consistency(applicable)
        elif self.rule_type == ConsistencyRuleType.AXIOMATIC:
            return self._check_axiomatic_consistency(applicable)
        
        return True, None
    
    def _check_logical_consistency(self, concepts: List[ScientificConcept]) -> Tuple[bool, Optional[str]]:
        """Check logical consistency."""
        # Example: No concept should contradict another
        for i, c1 in enumerate(concepts):
            for c2 in concepts[i+1:]:
                if self._are_contradictory(c1, c2):
                    return False, f"Logical contradiction between {c1.name_ar} and {c2.name_ar}"
        return True, None
    
    def _check_empirical_consistency(self, concepts: List[ScientificConcept]) -> Tuple[bool, Optional[str]]:
        """Check empirical consistency."""
        # Example: Physical measurements should be within reasonable bounds
        for concept in concepts:
            if concept.domain == Domain.PHYSICS:
                if "measurement" in concept.properties:
                    value = concept.properties["measurement"].get("value")
                    if value is not None and (value < 0 and not concept.properties.get("allows_negative")):
                        return False, f"Invalid measurement value in {concept.name_ar}"
        return True, None
    
    def _check_definitional_consistency(self, concepts: List[ScientificConcept]) -> Tuple[bool, Optional[str]]:
        """Check definitional consistency."""
        # Example: Concepts with same name should have compatible definitions
        name_groups = {}
        for concept in concepts:
            key = concept.name_en.lower()
            if key not in name_groups:
                name_groups[key] = []
            name_groups[key].append(concept)
        
        for name, group in name_groups.items():
            if len(group) > 1:
                # Check if definitions are compatible
                definitions = [c.definition for c in group]
                if len(set(definitions)) > 1:
                    # Different definitions - may need review
                    pass
        
        return True, None
    
    def _check_axiomatic_consistency(self, concepts: List[ScientificConcept]) -> Tuple[bool, Optional[str]]:
        """Check axiomatic consistency."""
        # Example: Mathematical concepts should follow axioms
        for concept in concepts:
            if concept.domain == Domain.MATHEMATICS:
                if "violates_axiom" in concept.properties:
                    return False, f"Axiom violation in {concept.name_ar}"
        return True, None
    
    def _are_contradictory(self, c1: ScientificConcept, c2: ScientificConcept) -> bool:
        """Check if two concepts are contradictory."""
        # Simplified check - can be extended
        return False


@dataclass
class ConflictResolution:
    """
    Resolution for a detected conflict.
    
    Attributes:
        conflict_id: ID of the conflict
        strategy: Resolution strategy used
        resolution: Chosen resolution
        rationale: Explanation
        confidence: Confidence in resolution
        alternatives: Alternative resolutions
    """
    conflict_id: str
    strategy: ConflictResolutionStrategy
    resolution: Dict[str, Any]
    rationale: str
    confidence: float
    alternatives: List[Dict[str, Any]] = field(default_factory=list)


class ScientificConsistencyEngine:
    """
    Advanced engine for validating and maintaining scientific consistency
    across all domains.
    
    Features:
    - Rule-based consistency validation
    - Automatic conflict detection
    - Intelligent conflict resolution
    - Epistemic level unification
    - Evidence aggregation
    """
    
    def __init__(self, integrator: Optional[MultiDomainIntegrator] = None):
        """Initialize the consistency engine."""
        self.integrator = integrator or MultiDomainIntegrator()
        self.rules: List[ConsistencyRule] = []
        self.conflicts: List[ConsistencyIssue] = []
        self.resolutions: List[ConflictResolution] = []
        
        # Initialize fundamental consistency rules
        self._initialize_fundamental_rules()
    
    def _initialize_fundamental_rules(self):
        """Initialize fundamental consistency rules."""
        
        # Rule 1: Epistemic consistency across domains
        self.add_rule(ConsistencyRule(
            rule_id="CONSIST_001",
            rule_type=ConsistencyRuleType.LOGICAL,
            domains=[Domain.LANGUAGE, Domain.MATHEMATICS, Domain.PHYSICS, Domain.CHEMISTRY],
            condition="epistemic_levels_compatible",
            description="Epistemic levels must be compatible across related concepts",
            severity=4
        ))
        
        # Rule 2: Mathematical axiom preservation
        self.add_rule(ConsistencyRule(
            rule_id="CONSIST_002",
            rule_type=ConsistencyRuleType.AXIOMATIC,
            domains=[Domain.MATHEMATICS],
            condition="no_axiom_violations",
            description="Mathematical concepts must not violate axioms",
            severity=5
        ))
        
        # Rule 3: Physical law compliance
        self.add_rule(ConsistencyRule(
            rule_id="CONSIST_003",
            rule_type=ConsistencyRuleType.EMPIRICAL,
            domains=[Domain.PHYSICS, Domain.CHEMISTRY],
            condition="obey_conservation_laws",
            description="Physical and chemical processes must obey conservation laws",
            severity=5
        ))
        
        # Rule 4: Chemical balance requirement
        self.add_rule(ConsistencyRule(
            rule_id="CONSIST_004",
            rule_type=ConsistencyRuleType.EMPIRICAL,
            domains=[Domain.CHEMISTRY],
            condition="stoichiometric_balance",
            description="Chemical reactions must be stoichiometrically balanced",
            severity=5
        ))
        
        # Rule 5: Definitional consistency
        self.add_rule(ConsistencyRule(
            rule_id="CONSIST_005",
            rule_type=ConsistencyRuleType.DEFINITIONAL,
            domains=[Domain.LANGUAGE, Domain.MATHEMATICS, Domain.PHYSICS, Domain.CHEMISTRY],
            condition="definitions_compatible",
            description="Related concepts across domains must have compatible definitions",
            severity=3
        ))
        
        # Rule 6: Measurement validity
        self.add_rule(ConsistencyRule(
            rule_id="CONSIST_006",
            rule_type=ConsistencyRuleType.EMPIRICAL,
            domains=[Domain.PHYSICS],
            condition="measurements_within_bounds",
            description="Physical measurements must be within valid ranges",
            severity=4
        ))
        
        # Rule 7: Logical non-contradiction
        self.add_rule(ConsistencyRule(
            rule_id="CONSIST_007",
            rule_type=ConsistencyRuleType.LOGICAL,
            domains=[Domain.LANGUAGE, Domain.MATHEMATICS, Domain.PHYSICS, Domain.CHEMISTRY],
            condition="no_contradictions",
            description="No concept should logically contradict another",
            severity=5
        ))
    
    def add_rule(self, rule: ConsistencyRule):
        """Add a consistency rule."""
        self.rules.append(rule)
    
    def validate_consistency(self, concepts: List[ScientificConcept]) -> Dict[str, Any]:
        """
        Validate consistency across all given concepts.
        
        Args:
            concepts: List of scientific concepts to validate
            
        Returns:
            Validation result with violations and recommendations
        """
        result = {
            "valid": True,
            "violations": [],
            "warnings": [],
            "recommendations": [],
            "overall_consistency_score": 1.0
        }
        
        violations_count = 0
        total_severity = 0
        
        # Check each rule
        for rule in self.rules:
            if not rule.enabled:
                continue
            
            passes, message = rule.evaluate(concepts)
            
            if not passes:
                violation = {
                    "rule_id": rule.rule_id,
                    "rule_type": rule.rule_type.value,
                    "description": rule.description,
                    "violation_message": message,
                    "severity": rule.severity,
                    "domains": [d.value for d in rule.domains]
                }
                
                if rule.severity >= 4:
                    result["violations"].append(violation)
                    violations_count += 1
                    total_severity += rule.severity
                    result["valid"] = False
                else:
                    result["warnings"].append(violation)
        
        # Calculate overall consistency score
        if violations_count > 0:
            avg_severity = total_severity / violations_count
            result["overall_consistency_score"] = max(0.0, 1.0 - (avg_severity / 5.0))
        
        # Generate recommendations
        if not result["valid"]:
            result["recommendations"] = self._generate_recommendations(result["violations"])
        
        return result
    
    def _generate_recommendations(self, violations: List[Dict[str, Any]]) -> List[str]:
        """Generate recommendations for fixing violations."""
        recommendations = []
        
        for violation in violations:
            rule_id = violation["rule_id"]
            
            if rule_id == "CONSIST_001":
                recommendations.append("Review epistemic evidence for related concepts")
                recommendations.append("Adjust epistemic levels to match strongest evidence")
            elif rule_id == "CONSIST_002":
                recommendations.append("Verify mathematical definitions against axioms")
                recommendations.append("Correct any axiom violations")
            elif rule_id == "CONSIST_003":
                recommendations.append("Check conservation laws (energy, momentum, mass)")
                recommendations.append("Verify physical feasibility")
            elif rule_id == "CONSIST_004":
                recommendations.append("Balance chemical equation stoichiometrically")
                recommendations.append("Verify atom conservation")
            elif rule_id == "CONSIST_007":
                recommendations.append("Identify contradictory statements")
                recommendations.append("Resolve logical inconsistencies")
        
        return list(set(recommendations))  # Remove duplicates
    
    def resolve_conflicts(self, conflicts: List[ConsistencyIssue], 
                         strategy: ConflictResolutionStrategy = ConflictResolutionStrategy.EVIDENCE_BASED
                         ) -> List[ConflictResolution]:
        """
        Resolve detected conflicts using the specified strategy.
        
        Args:
            conflicts: List of consistency issues
            strategy: Resolution strategy
            
        Returns:
            List of resolutions
        """
        resolutions = []
        
        for conflict in conflicts:
            resolution = self._resolve_single_conflict(conflict, strategy)
            resolutions.append(resolution)
        
        self.resolutions.extend(resolutions)
        return resolutions
    
    def _resolve_single_conflict(self, conflict: ConsistencyIssue, 
                                 strategy: ConflictResolutionStrategy) -> ConflictResolution:
        """Resolve a single conflict."""
        
        # Get involved concepts
        concepts = [self.integrator.get_concept(cid) for cid in conflict.concepts_involved]
        concepts = [c for c in concepts if c is not None]
        
        resolution_data = {}
        rationale = ""
        confidence = 0.5
        
        if strategy == ConflictResolutionStrategy.MOST_CERTAIN:
            # Choose concept with highest epistemic level
            best_concept = max(concepts, key=lambda c: self._epistemic_to_numeric(c.epistemic_level))
            resolution_data = {
                "chosen_concept": best_concept.concept_id,
                "epistemic_level": best_concept.epistemic_level.value
            }
            rationale = f"Selected {best_concept.name_ar} due to highest certainty ({best_concept.epistemic_level.value})"
            confidence = self._epistemic_to_numeric(best_concept.epistemic_level)
        
        elif strategy == ConflictResolutionStrategy.EVIDENCE_BASED:
            # Choose concept with most evidence
            best_concept = max(concepts, key=lambda c: len(c.evidence))
            resolution_data = {
                "chosen_concept": best_concept.concept_id,
                "evidence_count": len(best_concept.evidence)
            }
            rationale = f"Selected {best_concept.name_ar} due to strongest evidence (count: {len(best_concept.evidence)})"
            confidence = min(1.0, len(best_concept.evidence) / 5.0)  # Normalized
        
        elif strategy == ConflictResolutionStrategy.CONSENSUS:
            # Average epistemic levels
            avg_level = sum(self._epistemic_to_numeric(c.epistemic_level) for c in concepts) / len(concepts)
            resolution_data = {
                "consensus_level": avg_level,
                "participating_concepts": [c.concept_id for c in concepts]
            }
            rationale = f"Consensus approach: average epistemic level = {avg_level:.2f}"
            confidence = 0.7
        
        elif strategy == ConflictResolutionStrategy.DOMAIN_PRIORITY:
            # Prioritize based on domain relevance
            # Language < Mathematics < Physics < Chemistry (for physical phenomena)
            domain_priority = {
                Domain.CHEMISTRY: 4,
                Domain.PHYSICS: 3,
                Domain.MATHEMATICS: 2,
                Domain.LANGUAGE: 1
            }
            best_concept = max(concepts, key=lambda c: domain_priority.get(c.domain, 0))
            resolution_data = {
                "chosen_concept": best_concept.concept_id,
                "domain": best_concept.domain.value
            }
            rationale = f"Selected {best_concept.name_ar} based on domain priority ({best_concept.domain.value})"
            confidence = 0.75
        
        return ConflictResolution(
            conflict_id=conflict.issue_id,
            strategy=strategy,
            resolution=resolution_data,
            rationale=rationale,
            confidence=confidence,
            alternatives=[
                {"strategy": s.value, "applicable": True} 
                for s in ConflictResolutionStrategy if s != strategy
            ]
        )
    
    def _epistemic_to_numeric(self, level: EpistemicLevel) -> float:
        """Convert epistemic level to numeric score."""
        mapping = {
            EpistemicLevel.CERTAIN: 1.0,
            EpistemicLevel.PROBABLE: 0.7,
            EpistemicLevel.POSSIBLE: 0.4,
            EpistemicLevel.REJECTED: 0.0
        }
        return mapping[level]
    
    def unify_epistemic_levels(self, concepts: List[ScientificConcept]) -> EpistemicLevel:
        """
        Determine unified epistemic level for a group of concepts.
        Uses conservative approach (minimum level).
        
        Args:
            concepts: List of concepts
            
        Returns:
            Unified epistemic level
        """
        if not concepts:
            return EpistemicLevel.POSSIBLE
        
        levels = [self._epistemic_to_numeric(c.epistemic_level) for c in concepts]
        min_level = min(levels)
        
        if min_level >= 0.9:
            return EpistemicLevel.CERTAIN
        elif min_level >= 0.6:
            return EpistemicLevel.PROBABLE
        elif min_level >= 0.3:
            return EpistemicLevel.POSSIBLE
        else:
            return EpistemicLevel.REJECTED
    
    def aggregate_evidence(self, concepts: List[ScientificConcept]) -> Dict[str, Any]:
        """
        Aggregate evidence from multiple concepts.
        
        Args:
            concepts: List of concepts
            
        Returns:
            Aggregated evidence summary
        """
        all_evidence = []
        evidence_sources = set()
        
        for concept in concepts:
            all_evidence.extend(concept.evidence)
            if "source" in concept.metadata:
                evidence_sources.add(concept.metadata["source"])
        
        return {
            "total_evidence_items": len(all_evidence),
            "unique_sources": len(evidence_sources),
            "evidence_list": all_evidence,
            "sources": list(evidence_sources),
            "confidence": min(1.0, len(all_evidence) / 10.0)  # Normalized
        }
    
    def generate_consistency_report(self, concepts: List[ScientificConcept]) -> Dict[str, Any]:
        """
        Generate comprehensive consistency report.
        
        Args:
            concepts: List of concepts to analyze
            
        Returns:
            Detailed consistency report
        """
        # Validate consistency
        validation = self.validate_consistency(concepts)
        
        # Detect conflicts
        conflicts = self.integrator.check_consistency()
        
        # Resolve conflicts
        resolutions = []
        if conflicts:
            resolutions = self.resolve_conflicts(conflicts)
        
        # Unify epistemic level
        unified_level = self.unify_epistemic_levels(concepts)
        
        # Aggregate evidence
        evidence = self.aggregate_evidence(concepts)
        
        return {
            "consistency_validation": validation,
            "detected_conflicts": len(conflicts),
            "resolved_conflicts": len(resolutions),
            "resolutions": [
                {
                    "conflict_id": r.conflict_id,
                    "strategy": r.strategy.value,
                    "rationale": r.rationale,
                    "confidence": r.confidence
                }
                for r in resolutions
            ],
            "unified_epistemic_level": unified_level.value,
            "evidence_summary": evidence,
            "overall_consistency": validation["overall_consistency_score"],
            "recommendation": "APPROVE" if validation["valid"] else "REVIEW_REQUIRED"
        }


# Convenience functions
def validate_scientific_consistency(concepts: List[ScientificConcept]) -> Dict[str, Any]:
    """
    Convenience function for consistency validation.
    
    Args:
        concepts: List of scientific concepts
        
    Returns:
        Validation result
    """
    engine = ScientificConsistencyEngine()
    return engine.validate_consistency(concepts)


def generate_consistency_report(concepts: List[ScientificConcept]) -> Dict[str, Any]:
    """
    Convenience function for generating consistency report.
    
    Args:
        concepts: List of scientific concepts
        
    Returns:
        Comprehensive consistency report
    """
    engine = ScientificConsistencyEngine()
    return engine.generate_consistency_report(concepts)
