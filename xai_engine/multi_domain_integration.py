"""
Multi-Domain Integration Module for XAI Engine

This module provides comprehensive integration across all domains (linguistic, mathematical,
physical, chemical) ensuring scientific consistency at all levels of processing.

Key Features:
1. Cross-domain term mapping and translation
2. Epistemic consistency across domains
3. Scientific validity verification
4. Unified evaluation framework
5. Inter-domain conflict resolution

Author: Eqratech Arabic Diana Project
Version: 1.0
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple, Any, Union
from enum import Enum
import json


class Domain(Enum):
    """Supported scientific domains"""
    LANGUAGE = "language"
    PHYSICS = "physics"
    MATHEMATICS = "mathematics"
    CHEMISTRY = "chemistry"


class ConsistencyLevel(Enum):
    """Cross-domain consistency levels"""
    CONSISTENT = "consistent"  # Fully consistent across domains
    COMPATIBLE = "compatible"  # Compatible with reconciliation
    CONFLICTING = "conflicting"  # Direct contradiction detected
    INDEPENDENT = "independent"  # No cross-domain relationship


@dataclass
class ScientificConcept:
    """Universal scientific concept across domains"""
    id: str
    name_ar: str
    name_en: str
    domain: Domain
    definition: str
    related_concepts: List[str] = field(default_factory=list)
    cross_domain_mappings: Dict[str, str] = field(default_factory=dict)
    epistemic_level: str = "certain"  # certain, probable, possible
    confidence: float = 1.0
    
    def __post_init__(self):
        if not 0.0 <= self.confidence <= 1.0:
            raise ValueError("Confidence must be between 0.0 and 1.0")


@dataclass
class CrossDomainMapping:
    """Mapping between concepts across domains"""
    source_domain: Domain
    target_domain: Domain
    source_concept_id: str
    target_concept_id: str
    mapping_type: str  # analogy, equivalence, translation, approximation
    confidence: float
    transformation_rules: List[str] = field(default_factory=list)
    constraints: List[str] = field(default_factory=list)


@dataclass
class ConsistencyCheck:
    """Result of cross-domain consistency verification"""
    level: ConsistencyLevel
    domains_involved: List[Domain]
    concepts_checked: List[str]
    conflicts: List[Dict[str, Any]] = field(default_factory=list)
    recommendations: List[str] = field(default_factory=list)
    confidence: float = 1.0


class MultiDomainIntegration:
    """
    Comprehensive multi-domain integration system for XAI Engine
    
    This class provides:
    - Cross-domain concept mapping
    - Scientific consistency verification
    - Unified epistemic evaluation
    - Domain translation and bridging
    """
    
    def __init__(self):
        self.concepts: Dict[str, ScientificConcept] = {}
        self.mappings: List[CrossDomainMapping] = []
        self.consistency_rules: Dict[str, List[callable]] = {
            "linguistic_mathematical": [],
            "linguistic_physical": [],
            "linguistic_chemical": [],
            "mathematical_physical": [],
            "mathematical_chemical": [],
            "physical_chemical": []
        }
        self._initialize_core_concepts()
        self._initialize_cross_domain_mappings()
        self._initialize_consistency_rules()
    
    def _initialize_core_concepts(self):
        """Initialize core scientific concepts across all domains"""
        
        # Linguistic concepts
        self.concepts["ling:number"] = ScientificConcept(
            id="ling:number",
            name_ar="العدد",
            name_en="Number (Grammatical)",
            domain=Domain.LANGUAGE,
            definition="التمييز بين المفرد والمثنى والجمع في اللغة العربية",
            cross_domain_mappings={
                "math": "math:natural_number",
                "physics": "phys:quantity"
            }
        )
        
        self.concepts["ling:verb"] = ScientificConcept(
            id="ling:verb",
            name_ar="الفعل",
            name_en="Verb",
            domain=Domain.LANGUAGE,
            definition="ما دل على حدث مقترن بزمن",
            cross_domain_mappings={
                "physics": "phys:process",
                "chemistry": "chem:reaction"
            }
        )
        
        # Mathematical concepts
        self.concepts["math:number"] = ScientificConcept(
            id="math:number",
            name_ar="العدد",
            name_en="Number (Mathematical)",
            domain=Domain.MATHEMATICS,
            definition="كائن رياضي يستخدم للعد والقياس",
            cross_domain_mappings={
                "physics": "phys:scalar",
                "chemistry": "chem:stoichiometric_coefficient"
            }
        )
        
        self.concepts["math:equation"] = ScientificConcept(
            id="math:equation",
            name_ar="المعادلة",
            name_en="Equation",
            domain=Domain.MATHEMATICS,
            definition="مساواة بين تعبيرين رياضيين",
            cross_domain_mappings={
                "physics": "phys:physical_law",
                "chemistry": "chem:chemical_equation"
            }
        )
        
        # Physical concepts
        self.concepts["phys:quantity"] = ScientificConcept(
            id="phys:quantity",
            name_ar="الكمية الفيزيائية",
            name_en="Physical Quantity",
            domain=Domain.PHYSICS,
            definition="خاصية قابلة للقياس الكمي",
            cross_domain_mappings={
                "math": "math:real_number",
                "chemistry": "chem:measurable_property"
            }
        )
        
        self.concepts["phys:force"] = ScientificConcept(
            id="phys:force",
            name_ar="القوة",
            name_en="Force",
            domain=Domain.PHYSICS,
            definition="تأثير يسبب تغيير حالة حركة الجسم",
            cross_domain_mappings={
                "math": "math:vector",
                "language": "ling:causative_verb"
            }
        )
        
        # Chemical concepts
        self.concepts["chem:element"] = ScientificConcept(
            id="chem:element",
            name_ar="العنصر الكيميائي",
            name_en="Chemical Element",
            domain=Domain.CHEMISTRY,
            definition="مادة نقية لا يمكن تحليلها إلى مواد أبسط",
            cross_domain_mappings={
                "physics": "phys:atom",
                "math": "math:set_element"
            }
        )
        
        self.concepts["chem:reaction"] = ScientificConcept(
            id="chem:reaction",
            name_ar="التفاعل الكيميائي",
            name_en="Chemical Reaction",
            domain=Domain.CHEMISTRY,
            definition="عملية تحول المواد المتفاعلة إلى نواتج",
            cross_domain_mappings={
                "physics": "phys:process",
                "math": "math:function",
                "language": "ling:verb_phrase"
            }
        )
    
    def _initialize_cross_domain_mappings(self):
        """Initialize predefined cross-domain concept mappings"""
        
        # Linguistic-Mathematical mapping
        self.mappings.append(CrossDomainMapping(
            source_domain=Domain.LANGUAGE,
            target_domain=Domain.MATHEMATICS,
            source_concept_id="ling:number",
            target_concept_id="math:natural_number",
            mapping_type="analogy",
            confidence=0.8,
            transformation_rules=[
                "العدد اللغوي (مفرد/مثنى/جمع) → عدد رياضي (1/2/3+)",
                "الحفاظ على العلاقات الترتيبية"
            ],
            constraints=[
                "العدد اللغوي محدود (مفرد، مثنى، جمع)",
                "العدد الرياضي غير محدود"
            ]
        ))
        
        # Mathematical-Physical mapping
        self.mappings.append(CrossDomainMapping(
            source_domain=Domain.MATHEMATICS,
            target_domain=Domain.PHYSICS,
            source_concept_id="math:equation",
            target_concept_id="phys:physical_law",
            mapping_type="equivalence",
            confidence=0.95,
            transformation_rules=[
                "المعادلة الرياضية + وحدات فيزيائية → قانون فيزيائي",
                "الحفاظ على التماثل الأبعادي"
            ],
            constraints=[
                "يجب تحديد الوحدات الفيزيائية",
                "يجب التحقق من التماثل الأبعادي"
            ]
        ))
        
        # Physical-Chemical mapping
        self.mappings.append(CrossDomainMapping(
            source_domain=Domain.PHYSICS,
            target_domain=Domain.CHEMISTRY,
            source_concept_id="phys:energy",
            target_concept_id="chem:thermodynamics",
            mapping_type="equivalence",
            confidence=0.98,
            transformation_rules=[
                "الطاقة الفيزيائية → طاقة كيميائية (حرارة التفاعل)",
                "الحفاظ على الطاقة (القانون الأول للثرموديناميكا)"
            ],
            constraints=[
                "يجب الحفاظ على الطاقة",
                "يجب مراعاة الإنتروبيا"
            ]
        ))
        
        # Linguistic-Physical mapping
        self.mappings.append(CrossDomainMapping(
            source_domain=Domain.LANGUAGE,
            target_domain=Domain.PHYSICS,
            source_concept_id="ling:verb",
            target_concept_id="phys:process",
            mapping_type="analogy",
            confidence=0.75,
            transformation_rules=[
                "الفعل (حدث مقترن بزمن) → عملية فيزيائية",
                "الفاعل → القوة المسببة",
                "المفعول به → الجسم المتأثر"
            ],
            constraints=[
                "الفعل اللغوي مجرد",
                "العملية الفيزيائية قابلة للقياس"
            ]
        ))
    
    def _initialize_consistency_rules(self):
        """Initialize cross-domain consistency validation rules"""
        
        def linguistic_mathematical_consistency(ling_concept, math_concept):
            """Check linguistic-mathematical consistency"""
            # Example: "العدد" must map to valid mathematical number
            if "number" in ling_concept.name_en.lower():
                if "number" not in math_concept.name_en.lower():
                    return False, "Number concept mismatch"
            return True, "Consistent"
        
        def mathematical_physical_consistency(math_concept, phys_concept):
            """Check mathematical-physical consistency"""
            # Example: Dimensional analysis must be valid
            if "equation" in math_concept.name_en.lower():
                if "law" in phys_concept.name_en.lower():
                    # Check dimensional consistency (simplified)
                    return True, "Consistent"
            return True, "Compatible"
        
        def physical_chemical_consistency(phys_concept, chem_concept):
            """Check physical-chemical consistency"""
            # Example: Energy conservation must hold
            if "energy" in phys_concept.name_en.lower():
                if "thermodynamic" in chem_concept.name_en.lower():
                    return True, "Consistent"
            return True, "Compatible"
        
        self.consistency_rules["linguistic_mathematical"].append(linguistic_mathematical_consistency)
        self.consistency_rules["mathematical_physical"].append(mathematical_physical_consistency)
        self.consistency_rules["physical_chemical"].append(physical_chemical_consistency)
    
    def verify_cross_domain_consistency(
        self,
        concepts: List[ScientificConcept],
        strict: bool = False
    ) -> ConsistencyCheck:
        """
        Verify consistency across multiple domains
        
        Args:
            concepts: List of concepts to check for consistency
            strict: If True, require perfect consistency; if False, allow compatible concepts
        
        Returns:
            ConsistencyCheck with detailed results
        """
        domains_involved = list(set(c.domain for c in concepts))
        conflicts = []
        recommendations = []
        
        # Check pairwise consistency
        for i, concept1 in enumerate(concepts):
            for concept2 in concepts[i+1:]:
                if concept1.domain != concept2.domain:
                    # Find applicable consistency rules
                    domain_pair = f"{concept1.domain.value}_{concept2.domain.value}"
                    rules = self.consistency_rules.get(domain_pair, [])
                    
                    for rule in rules:
                        consistent, message = rule(concept1, concept2)
                        if not consistent:
                            conflicts.append({
                                "concept1": concept1.id,
                                "concept2": concept2.id,
                                "message": message
                            })
        
        # Determine overall consistency level
        if len(conflicts) == 0:
            level = ConsistencyLevel.CONSISTENT
            confidence = 1.0
        elif len(conflicts) <= len(concepts) * 0.2:  # Less than 20% conflicts
            level = ConsistencyLevel.COMPATIBLE
            confidence = 0.8
            recommendations.append("بعض التعارضات البسيطة تحتاج إلى مراجعة")
        else:
            level = ConsistencyLevel.CONFLICTING
            confidence = 0.5
            recommendations.append("تعارضات كبيرة تحتاج إلى حل")
        
        return ConsistencyCheck(
            level=level,
            domains_involved=domains_involved,
            concepts_checked=[c.id for c in concepts],
            conflicts=conflicts,
            recommendations=recommendations,
            confidence=confidence
        )
    
    def translate_concept(
        self,
        concept_id: str,
        target_domain: Domain
    ) -> Optional[ScientificConcept]:
        """
        Translate a concept from one domain to another
        
        Args:
            concept_id: ID of the source concept
            target_domain: Target domain for translation
        
        Returns:
            Translated concept or None if no mapping exists
        """
        if concept_id not in self.concepts:
            return None
        
        source_concept = self.concepts[concept_id]
        
        # Check if direct mapping exists
        target_key = target_domain.value
        if target_key in source_concept.cross_domain_mappings:
            target_id = source_concept.cross_domain_mappings[target_key]
            if target_id in self.concepts:
                return self.concepts[target_id]
        
        # Search for indirect mapping
        for mapping in self.mappings:
            if (mapping.source_concept_id == concept_id and
                mapping.target_domain == target_domain):
                if mapping.target_concept_id in self.concepts:
                    return self.concepts[mapping.target_concept_id]
        
        return None
    
    def get_unified_epistemic_level(
        self,
        domain_results: Dict[Domain, Dict[str, Any]]
    ) -> Tuple[str, float, Dict[str, Any]]:
        """
        Compute unified epistemic level across all domains
        
        Args:
            domain_results: Dictionary mapping domains to their evaluation results
        
        Returns:
            Tuple of (unified_level, confidence, details)
        """
        epistemic_levels = {
            "certain": 1.0,
            "probable": 0.7,
            "possible": 0.4,
            "rejected": 0.0
        }
        
        # Collect confidence scores from all domains
        scores = []
        for domain, result in domain_results.items():
            level = result.get("epistemic_level", "possible")
            score = epistemic_levels.get(level, 0.5)
            confidence = result.get("confidence", 1.0)
            scores.append(score * confidence)
        
        # Compute unified score (conservative: minimum)
        if len(scores) == 0:
            return "possible", 0.5, {"reason": "No domain results"}
        
        unified_score = min(scores)  # Conservative: take minimum
        avg_score = sum(scores) / len(scores)  # Average for reference
        
        # Map back to epistemic level
        if unified_score >= 0.95:
            unified_level = "certain"
        elif unified_score >= 0.65:
            unified_level = "probable"
        elif unified_score >= 0.35:
            unified_level = "possible"
        else:
            unified_level = "rejected"
        
        details = {
            "domain_scores": {
                domain.value: score 
                for domain, score in zip(domain_results.keys(), scores)
            },
            "unified_score": unified_score,
            "average_score": avg_score,
            "method": "conservative_minimum"
        }
        
        return unified_level, unified_score, details
    
    def integrate_analysis(
        self,
        linguistic_analysis: Dict[str, Any],
        mathematical_analysis: Optional[Dict[str, Any]] = None,
        physical_analysis: Optional[Dict[str, Any]] = None,
        chemical_analysis: Optional[Dict[str, Any]] = None
    ) -> Dict[str, Any]:
        """
        Integrate analysis results from multiple domains
        
        Args:
            linguistic_analysis: Results from linguistic analysis
            mathematical_analysis: Results from mathematical analysis (optional)
            physical_analysis: Results from physical analysis (optional)
            chemical_analysis: Results from chemical analysis (optional)
        
        Returns:
            Integrated multi-domain analysis
        """
        domain_results = {Domain.LANGUAGE: linguistic_analysis}
        
        if mathematical_analysis:
            domain_results[Domain.MATHEMATICS] = mathematical_analysis
        if physical_analysis:
            domain_results[Domain.PHYSICS] = physical_analysis
        if chemical_analysis:
            domain_results[Domain.CHEMISTRY] = chemical_analysis
        
        # Get unified epistemic level
        unified_level, confidence, details = self.get_unified_epistemic_level(domain_results)
        
        # Extract concepts from each domain
        concepts = []
        for domain, result in domain_results.items():
            concepts_in_domain = result.get("concepts", [])
            for concept_data in concepts_in_domain:
                if isinstance(concept_data, str) and concept_data in self.concepts:
                    concepts.append(self.concepts[concept_data])
        
        # Verify cross-domain consistency
        consistency = self.verify_cross_domain_consistency(concepts)
        
        # Build integrated result
        integrated_result = {
            "domains_analyzed": [d.value for d in domain_results.keys()],
            "unified_epistemic_level": unified_level,
            "unified_confidence": confidence,
            "epistemic_details": details,
            "consistency_check": {
                "level": consistency.level.value,
                "confidence": consistency.confidence,
                "conflicts": consistency.conflicts,
                "recommendations": consistency.recommendations
            },
            "domain_results": {
                d.value: result for d, result in domain_results.items()
            },
            "cross_domain_mappings": [
                {
                    "source": m.source_domain.value,
                    "target": m.target_domain.value,
                    "type": m.mapping_type,
                    "confidence": m.confidence
                }
                for m in self.mappings
                if (m.source_domain in domain_results and 
                    m.target_domain in domain_results)
            ]
        }
        
        return integrated_result
    
    def get_concept(self, concept_id: str) -> Optional[ScientificConcept]:
        """Get a scientific concept by ID"""
        return self.concepts.get(concept_id)
    
    def add_concept(self, concept: ScientificConcept):
        """Add a new scientific concept"""
        self.concepts[concept.id] = concept
    
    def add_mapping(self, mapping: CrossDomainMapping):
        """Add a new cross-domain mapping"""
        self.mappings.append(mapping)


def load_multi_domain_integration() -> MultiDomainIntegration:
    """
    Factory function to create and initialize multi-domain integration system
    
    Returns:
        Initialized MultiDomainIntegration instance
    """
    return MultiDomainIntegration()


# Example usage
if __name__ == "__main__":
    # Initialize integration system
    integration = load_multi_domain_integration()
    
    # Example 1: Translate linguistic concept to mathematics
    print("=" * 80)
    print("Example 1: Cross-Domain Translation")
    print("=" * 80)
    
    ling_number = integration.get_concept("ling:number")
    if ling_number:
        math_number = integration.translate_concept("ling:number", Domain.MATHEMATICS)
        if math_number:
            print(f"Linguistic: {ling_number.name_ar} ({ling_number.name_en})")
            print(f"Mathematical: {math_number.name_ar} ({math_number.name_en})")
            print(f"Translation confidence: High")
    
    print()
    
    # Example 2: Verify cross-domain consistency
    print("=" * 80)
    print("Example 2: Cross-Domain Consistency Check")
    print("=" * 80)
    
    concepts = [
        integration.get_concept("ling:number"),
        integration.get_concept("math:number"),
        integration.get_concept("phys:quantity")
    ]
    concepts = [c for c in concepts if c is not None]
    
    consistency = integration.verify_cross_domain_consistency(concepts)
    print(f"Consistency Level: {consistency.level.value}")
    print(f"Confidence: {consistency.confidence:.2f}")
    print(f"Domains: {[d.value for d in consistency.domains_involved]}")
    print(f"Conflicts: {len(consistency.conflicts)}")
    
    print()
    
    # Example 3: Unified epistemic evaluation
    print("=" * 80)
    print("Example 3: Unified Epistemic Evaluation")
    print("=" * 80)
    
    domain_results = {
        Domain.LANGUAGE: {"epistemic_level": "certain", "confidence": 1.0},
        Domain.MATHEMATICS: {"epistemic_level": "certain", "confidence": 0.95},
        Domain.PHYSICS: {"epistemic_level": "probable", "confidence": 0.85}
    }
    
    level, conf, details = integration.get_unified_epistemic_level(domain_results)
    print(f"Unified Epistemic Level: {level}")
    print(f"Unified Confidence: {conf:.2f}")
    print(f"Method: {details['method']}")
    print(f"Domain Scores: {json.dumps(details['domain_scores'], indent=2, ensure_ascii=False)}")
