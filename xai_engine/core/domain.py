"""
Domain configuration for multi-domain support

The same engine operates on different domains, but constraints differ:
- Language: Measurement = Grammar (إعراب)
- Physics: Measurement = Experiment + Error bounds
- Mathematics: Measurement = Proof
- Chemistry: Measurement = Reaction conditions
"""

from enum import Enum
from dataclasses import dataclass
from typing import Dict, Any, Optional


class DomainType(Enum):
    """Supported domains for XAI engine"""
    LANGUAGE = "language"
    PHYSICS = "physics"
    MATHEMATICS = "mathematics"
    CHEMISTRY = "chemistry"


@dataclass
class Domain:
    """
    Domain configuration
    
    Attributes:
        domain_type: Type of domain
        name: Human-readable name (Arabic and English)
        measurement_system: What counts as measurement in this domain
        operators_catalog: Catalog of valid operators for this domain
        constraints: Domain-specific constraints
    """
    domain_type: DomainType
    name: Dict[str, str]  # {"ar": "اللغة", "en": "Language"}
    measurement_system: str
    operators_catalog: Dict[str, Any]
    constraints: Dict[str, Any]
    
    @classmethod
    def language(cls, operators_catalog: Optional[Dict[str, Any]] = None) -> "Domain":
        """Create language domain configuration"""
        return cls(
            domain_type=DomainType.LANGUAGE,
            name={"ar": "اللغة", "en": "Language"},
            measurement_system="grammatical_operators",
            operators_catalog=operators_catalog or {},
            constraints={
                "require_governor": True,
                "require_case_marking": True,
                "allow_ellipsis": True,
                "require_relation": True,
            }
        )
    
    @classmethod
    def physics(cls, operators_catalog: Optional[Dict[str, Any]] = None) -> "Domain":
        """Create physics domain configuration"""
        return cls(
            domain_type=DomainType.PHYSICS,
            name={"ar": "الفيزياء", "en": "Physics"},
            measurement_system="experimental_verification",
            operators_catalog=operators_catalog or {},
            constraints={
                "require_experiment": True,
                "require_error_bounds": True,
                "require_units": True,
                "require_reproducibility": True,
            }
        )
    
    @classmethod
    def mathematics(cls, operators_catalog: Optional[Dict[str, Any]] = None) -> "Domain":
        """Create mathematics domain configuration"""
        return cls(
            domain_type=DomainType.MATHEMATICS,
            name={"ar": "الرياضيات", "en": "Mathematics"},
            measurement_system="logical_proof",
            operators_catalog=operators_catalog or {},
            constraints={
                "require_axioms": True,
                "require_proof_steps": True,
                "forbid_circular_reasoning": True,
                "require_logical_validity": True,
            }
        )
    
    @classmethod
    def chemistry(cls, operators_catalog: Optional[Dict[str, Any]] = None) -> "Domain":
        """Create chemistry domain configuration"""
        return cls(
            domain_type=DomainType.CHEMISTRY,
            name={"ar": "الكيمياء", "en": "Chemistry"},
            measurement_system="reaction_conditions",
            operators_catalog=operators_catalog or {},
            constraints={
                "require_conditions": True,
                "require_reagents": True,
                "require_stoichiometry": True,
                "track_energy": True,
            }
        )
