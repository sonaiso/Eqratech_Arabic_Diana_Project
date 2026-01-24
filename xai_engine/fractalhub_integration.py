"""
FractalHub Dictionary v02 Integration for XAI Engine

This module integrates the XAI Engine with FractalHub Dictionary v02, providing:
- Dictionary-based lexicon lookup for form and semantic layers
- Provenance tracking from dictionary entries
- Evidence-based validation using dictionary confidence levels
- Epistemic weight mapping (yaqin/zann/shakk → CERTAIN/PROBABLE/POSSIBLE)
- Integration with CTE Gate for evidence requirements

Architecture:
    FractalHub Dict v02 → Lexicon → Form/Semantic Layers → CTE Gate → Judgment

Key Features:
    - Load dictionary units (diacritics, phonemes, morphemes, words)
    - Extract provenance metadata (source_type, confidence, attestation_count)
    - Map epistemic levels between FractalHub and XAI Engine
    - Provide evidence chains for CTE Gate validation
    - Support all 4 domains (language, physics, mathematics, chemistry)

Version: 1.0
Compatible with: FractalHub v1.2, XAI Engine v1.0
"""

from typing import Dict, List, Optional, Any, Tuple
from dataclasses import dataclass
from enum import Enum
import sys
from pathlib import Path

# Add fractalhub to path if not already there
project_root = Path(__file__).parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

try:
    from fractalhub.data import load_dictionary, DictionaryLoader
    FRACTALHUB_AVAILABLE = True
except ImportError:
    FRACTALHUB_AVAILABLE = False
    DictionaryLoader = None


class EpistemicLevel(Enum):
    """
    Epistemic confidence levels (Arabic framework).
    
    Maps to FractalHub provenance confidence levels.
    """
    YAQIN = "yaqin"  # Certainty (يقين) - 1.0
    ZANN = "zann"  # Probability (ظن) - 0.7
    SHAKK = "shakk"  # Doubt (شك) - 0.4


@dataclass
class ProvenanceInfo:
    """
    Provenance metadata from FractalHub dictionary entry.
    
    Attributes:
        source_type: Type of evidence source (corpus, grammar_book, expert, derived)
        confidence: Epistemic level (yaqin/zann/shakk)
        confidence_score: Numeric confidence (0.0-1.0)
        attestation_count: Number of attestations in corpus
        references: List of reference sources
    """
    source_type: str
    confidence: str  # yaqin/zann/shakk
    confidence_score: float  # 0.0-1.0
    attestation_count: int
    references: List[str]
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary."""
        return {
            "source_type": self.source_type,
            "confidence": self.confidence,
            "confidence_score": self.confidence_score,
            "attestation_count": self.attestation_count,
            "references": self.references,
        }


@dataclass
class LexiconEntry:
    """
    Lexicon entry from FractalHub dictionary with provenance.
    
    Attributes:
        lexicon_id: Unique identifier (e.g., "U:DIACRITIC:FATHA")
        entry_type: Type of entry (signifier_only, signified_entity)
        layer: Layer designation (C0, C1, C2, C3)
        form: Form data (Arabic, unicode, IPA, name)
        meaning: Optional meaning data (for signified entities)
        features: List of linguistic features
        provenance: Provenance metadata
        status: Entry status (active, deprecated)
    """
    lexicon_id: str
    entry_type: str  # signifier_only, signified_entity
    layer: str  # C0, C1, C2, C3
    form: Dict[str, Any]
    meaning: Optional[Dict[str, Any]]
    features: List[str]
    provenance: ProvenanceInfo
    status: str  # active, deprecated
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary."""
        return {
            "lexicon_id": self.lexicon_id,
            "entry_type": self.entry_type,
            "layer": self.layer,
            "form": self.form,
            "meaning": self.meaning,
            "features": self.features,
            "provenance": self.provenance.to_dict(),
            "status": self.status,
        }


class FractalHubIntegration:
    """
    Integration layer between XAI Engine and FractalHub Dictionary v02.
    
    Provides:
        - Dictionary loading and caching
        - Lexicon lookup by ID or form
        - Provenance extraction
        - Epistemic level mapping
        - Evidence chain generation for CTE Gate
    
    Example:
        >>> integration = FractalHubIntegration()
        >>> entry = integration.get_lexicon_entry("U:DIACRITIC:FATHA")
        >>> print(f"Confidence: {entry.provenance.confidence}")  # "yaqin"
    """
    
    def __init__(self, dictionary_version: str = "v02", dictionary_path: Optional[str] = None):
        """
        Initialize FractalHub integration.
        
        Args:
            dictionary_version: Dictionary version ("v01" or "v02")
            dictionary_path: Optional custom path to dictionary file
            
        Raises:
            ImportError: If FractalHub is not available
        """
        if not FRACTALHUB_AVAILABLE:
            raise ImportError(
                "FractalHub is required for dictionary integration. "
                "Ensure fractalhub module is available."
            )
        
        self.dictionary_version = dictionary_version
        self.loader: DictionaryLoader = load_dictionary(version=dictionary_version, path=dictionary_path)
        
        # Cache for parsed entries
        self._entry_cache: Dict[str, LexiconEntry] = {}
        
        # Epistemic level mapping
        self._confidence_map = {
            "yaqin": 1.0,
            "zann": 0.7,
            "shakk": 0.4,
        }
    
    def get_lexicon_entry(self, lexicon_id: str) -> Optional[LexiconEntry]:
        """
        Get a lexicon entry by ID.
        
        Args:
            lexicon_id: Lexicon identifier (e.g., "U:DIACRITIC:FATHA")
            
        Returns:
            LexiconEntry or None if not found
            
        Example:
            >>> entry = integration.get_lexicon_entry("U:DIACRITIC:FATHA")
            >>> print(entry.form["name_ar"])  # "فتحة"
        """
        # Check cache first
        if lexicon_id in self._entry_cache:
            return self._entry_cache[lexicon_id]
        
        # Lookup in dictionary
        unit_data = self.loader.get_unit(lexicon_id)
        if not unit_data:
            return None
        
        # Parse entry
        entry = self._parse_unit(unit_data)
        
        # Cache result
        self._entry_cache[lexicon_id] = entry
        
        return entry
    
    def _parse_unit(self, unit_data: Dict[str, Any]) -> LexiconEntry:
        """
        Parse unit data into LexiconEntry.
        
        Args:
            unit_data: Raw unit dictionary from FractalHub
            
        Returns:
            Parsed LexiconEntry
        """
        # Extract provenance
        prov_data = unit_data.get("provenance", {})
        provenance = ProvenanceInfo(
            source_type=prov_data.get("source_type", "derived"),
            confidence=prov_data.get("confidence", "shakk"),
            confidence_score=self._confidence_map.get(prov_data.get("confidence", "shakk"), 0.4),
            attestation_count=prov_data.get("attestation_count", 0),
            references=prov_data.get("references", []),
        )
        
        # Create entry
        entry = LexiconEntry(
            lexicon_id=unit_data.get("lexicon_id", ""),
            entry_type=unit_data.get("type", "signifier_only"),
            layer=unit_data.get("layer", "C1"),
            form=unit_data.get("form", {}),
            meaning=unit_data.get("meaning"),
            features=unit_data.get("features", []),
            provenance=provenance,
            status=unit_data.get("status", "active"),
        )
        
        return entry
    
    def search_by_form(self, form_arabic: str, layer: Optional[str] = None) -> List[LexiconEntry]:
        """
        Search lexicon entries by Arabic form.
        
        Args:
            form_arabic: Arabic form to search for
            layer: Optional layer filter (C0, C1, C2, C3)
            
        Returns:
            List of matching LexiconEntry objects
            
        Example:
            >>> entries = integration.search_by_form("َ")  # Fatha diacritic
            >>> print(entries[0].lexicon_id)  # "U:DIACRITIC:FATHA"
        """
        matches = []
        
        all_units = self.loader.get_all_units()
        for unit_id, unit_data in all_units.items():
            # Check layer filter
            if layer and unit_data.get("layer") != layer:
                continue
            
            # Check form match
            form_data = unit_data.get("form", {})
            if form_data.get("arabic") == form_arabic:
                entry = self.get_lexicon_entry(unit_id)
                if entry:
                    matches.append(entry)
        
        return matches
    
    def get_provenance(self, lexicon_id: str) -> Optional[ProvenanceInfo]:
        """
        Get provenance information for a lexicon entry.
        
        Args:
            lexicon_id: Lexicon identifier
            
        Returns:
            ProvenanceInfo or None if not found
            
        Example:
            >>> prov = integration.get_provenance("U:DIACRITIC:FATHA")
            >>> print(f"Confidence: {prov.confidence}")  # "yaqin"
            >>> print(f"Score: {prov.confidence_score}")  # 1.0
        """
        entry = self.get_lexicon_entry(lexicon_id)
        return entry.provenance if entry else None
    
    def get_confidence_score(self, lexicon_id: str) -> float:
        """
        Get numeric confidence score (0.0-1.0) for a lexicon entry.
        
        Args:
            lexicon_id: Lexicon identifier
            
        Returns:
            Confidence score (1.0 for yaqin, 0.7 for zann, 0.4 for shakk)
            Default 0.0 if not found
            
        Example:
            >>> score = integration.get_confidence_score("U:DIACRITIC:FATHA")
            >>> print(score)  # 1.0 (yaqin)
        """
        provenance = self.get_provenance(lexicon_id)
        return provenance.confidence_score if provenance else 0.0
    
    def get_evidence_chain(self, lexicon_ids: List[str]) -> Dict[str, Any]:
        """
        Generate evidence chain for a list of lexicon IDs.
        
        Used by CTE Gate to validate evidence requirements.
        
        Args:
            lexicon_ids: List of lexicon identifiers
            
        Returns:
            Dictionary with:
                - entries: List of LexiconEntry dictionaries
                - min_confidence: Minimum confidence score
                - max_confidence: Maximum confidence score
                - avg_confidence: Average confidence score
                - total_attestations: Total attestation count
                - sources: Set of unique source types
                
        Example:
            >>> chain = integration.get_evidence_chain(["U:DIACRITIC:FATHA", "U:DIACRITIC:KASRA"])
            >>> print(f"Min confidence: {chain['min_confidence']}")  # 1.0
        """
        entries = []
        confidence_scores = []
        attestations = 0
        sources = set()
        
        for lexicon_id in lexicon_ids:
            entry = self.get_lexicon_entry(lexicon_id)
            if entry:
                entries.append(entry.to_dict())
                confidence_scores.append(entry.provenance.confidence_score)
                attestations += entry.provenance.attestation_count
                sources.add(entry.provenance.source_type)
        
        return {
            "entries": entries,
            "min_confidence": min(confidence_scores) if confidence_scores else 0.0,
            "max_confidence": max(confidence_scores) if confidence_scores else 0.0,
            "avg_confidence": sum(confidence_scores) / len(confidence_scores) if confidence_scores else 0.0,
            "total_attestations": attestations,
            "sources": list(sources),
        }
    
    def validate_evidence(self, lexicon_ids: List[str], min_confidence: float = 0.7) -> Tuple[bool, str]:
        """
        Validate that evidence meets minimum confidence requirement.
        
        Used by CTE Gate NO_HOMONYMY, NO_TRANSFER, etc. conditions.
        
        Args:
            lexicon_ids: List of lexicon identifiers
            min_confidence: Minimum required confidence score (0.0-1.0)
            
        Returns:
            Tuple of (is_valid, reason)
            
        Example:
            >>> valid, reason = integration.validate_evidence(["U:DIACRITIC:FATHA"], min_confidence=0.7)
            >>> print(valid)  # True
            >>> print(reason)  # "All evidence meets minimum confidence (yaqin: 1.0 >= 0.7)"
        """
        chain = self.get_evidence_chain(lexicon_ids)
        
        min_conf = chain["min_confidence"]
        avg_conf = chain["avg_confidence"]
        
        if min_conf >= min_confidence:
            return True, f"All evidence meets minimum confidence (min: {min_conf:.2f} >= {min_confidence:.2f})"
        else:
            return False, f"Evidence below minimum confidence (min: {min_conf:.2f} < {min_confidence:.2f})"
    
    def get_dictionary_stats(self) -> Dict[str, Any]:
        """
        Get statistics about loaded dictionary.
        
        Returns:
            Dictionary with:
                - version: Dictionary version
                - total_units: Total number of units
                - total_gates: Total number of gates
                - units_by_layer: Count of units per layer
                - units_by_type: Count of units per type
                - confidence_distribution: Count by confidence level
                
        Example:
            >>> stats = integration.get_dictionary_stats()
            >>> print(f"Total units: {stats['total_units']}")
            >>> print(f"C1 units: {stats['units_by_layer']['C1']}")
        """
        all_units = self.loader.get_all_units()
        all_gates = self.loader.get_all_gates()
        
        units_by_layer = {}
        units_by_type = {}
        confidence_dist = {"yaqin": 0, "zann": 0, "shakk": 0}
        
        for unit_id, unit_data in all_units.items():
            # Count by layer
            layer = unit_data.get("layer", "unknown")
            units_by_layer[layer] = units_by_layer.get(layer, 0) + 1
            
            # Count by type
            entry_type = unit_data.get("type", "unknown")
            units_by_type[entry_type] = units_by_type.get(entry_type, 0) + 1
            
            # Count by confidence
            prov = unit_data.get("provenance", {})
            conf = prov.get("confidence", "shakk")
            if conf in confidence_dist:
                confidence_dist[conf] += 1
        
        return {
            "version": self.dictionary_version,
            "total_units": len(all_units),
            "total_gates": len(all_gates),
            "units_by_layer": units_by_layer,
            "units_by_type": units_by_type,
            "confidence_distribution": confidence_dist,
        }


# Convenience function for quick integration
def load_fractalhub_integration(version: str = "v02", path: Optional[str] = None) -> FractalHubIntegration:
    """
    Load FractalHub integration for XAI Engine.
    
    Args:
        version: Dictionary version ("v01" or "v02")
        path: Optional custom path to dictionary file
        
    Returns:
        FractalHubIntegration instance
        
    Example:
        >>> integration = load_fractalhub_integration()
        >>> entry = integration.get_lexicon_entry("U:DIACRITIC:FATHA")
        >>> print(f"Provenance: {entry.provenance.confidence}")
    """
    return FractalHubIntegration(dictionary_version=version, dictionary_path=path)


# Check if FractalHub is available
def is_fractalhub_available() -> bool:
    """
    Check if FractalHub module is available.
    
    Returns:
        True if FractalHub can be imported, False otherwise
    """
    return FRACTALHUB_AVAILABLE
