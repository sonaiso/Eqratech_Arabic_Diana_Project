"""
Tests for FractalHub Dictionary v02 Integration with XAI Engine

Tests:
    - Dictionary loading
    - Lexicon entry lookup
    - Provenance extraction
    - Evidence chain generation
    - Confidence validation
    - Form search
    - Statistics generation
"""

import pytest
import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from xai_engine.fractalhub_integration import (
    FractalHubIntegration,
    LexiconEntry,
    ProvenanceInfo,
    EpistemicLevel,
    load_fractalhub_integration,
    is_fractalhub_available,
)


# Skip tests if FractalHub is not available
pytestmark = pytest.mark.skipif(
    not is_fractalhub_available(),
    reason="FractalHub module not available"
)


class TestFractalHubIntegration:
    """Test FractalHub integration with XAI Engine."""
    
    def test_integration_initialization(self):
        """Test basic integration initialization."""
        integration = FractalHubIntegration()
        
        assert integration is not None
        assert integration.dictionary_version == "v02"
        assert integration.loader is not None
    
    def test_load_fractalhub_integration(self):
        """Test convenience function for loading integration."""
        integration = load_fractalhub_integration()
        
        assert integration is not None
        assert isinstance(integration, FractalHubIntegration)
    
    def test_get_lexicon_entry(self):
        """Test getting lexicon entry by ID."""
        integration = FractalHubIntegration()
        
        # Try to get a diacritic entry (should exist in v02)
        entry = integration.get_lexicon_entry("U:DIACRITIC:FATHA")
        
        if entry:  # Entry exists in dictionary
            assert isinstance(entry, LexiconEntry)
            assert entry.lexicon_id == "U:DIACRITIC:FATHA"
            assert entry.layer in ["C0", "C1"]
            assert entry.entry_type == "signifier_only"
            assert entry.status == "active"
            assert isinstance(entry.provenance, ProvenanceInfo)
    
    def test_get_nonexistent_entry(self):
        """Test getting non-existent entry returns None."""
        integration = FractalHubIntegration()
        
        entry = integration.get_lexicon_entry("NONEXISTENT:ID:12345")
        
        assert entry is None
    
    def test_provenance_extraction(self):
        """Test provenance information extraction."""
        integration = FractalHubIntegration()
        
        entry = integration.get_lexicon_entry("U:DIACRITIC:FATHA")
        
        if entry:  # Entry exists
            prov = entry.provenance
            
            assert isinstance(prov, ProvenanceInfo)
            assert prov.source_type in ["corpus", "grammar_book", "expert_validation", "derived"]
            assert prov.confidence in ["yaqin", "zann", "shakk"]
            assert 0.0 <= prov.confidence_score <= 1.0
            assert prov.attestation_count >= 0
            assert isinstance(prov.references, list)
    
    def test_get_provenance(self):
        """Test getting provenance by lexicon ID."""
        integration = FractalHubIntegration()
        
        prov = integration.get_provenance("U:DIACRITIC:FATHA")
        
        if prov:  # Entry exists
            assert isinstance(prov, ProvenanceInfo)
            assert prov.confidence in ["yaqin", "zann", "shakk"]
    
    def test_get_confidence_score(self):
        """Test getting numeric confidence score."""
        integration = FractalHubIntegration()
        
        score = integration.get_confidence_score("U:DIACRITIC:FATHA")
        
        # Score should be 0.0-1.0 or 0.0 if not found
        assert 0.0 <= score <= 1.0
    
    def test_confidence_mapping(self):
        """Test epistemic level confidence mapping."""
        integration = FractalHubIntegration()
        
        # Test mapping
        assert integration._confidence_map["yaqin"] == 1.0
        assert integration._confidence_map["zann"] == 0.7
        assert integration._confidence_map["shakk"] == 0.4
    
    def test_search_by_form(self):
        """Test searching lexicon by Arabic form."""
        integration = FractalHubIntegration()
        
        # Search for fatha diacritic by its form
        entries = integration.search_by_form("َ")
        
        # Should find at least one entry (fatha)
        assert isinstance(entries, list)
        
        if entries:
            assert all(isinstance(e, LexiconEntry) for e in entries)
            assert all(e.form.get("arabic") == "َ" for e in entries)
    
    def test_search_by_form_with_layer_filter(self):
        """Test searching with layer filter."""
        integration = FractalHubIntegration()
        
        # Search in C1 layer only
        entries = integration.search_by_form("َ", layer="C1")
        
        assert isinstance(entries, list)
        
        if entries:
            assert all(e.layer == "C1" for e in entries)
    
    def test_get_evidence_chain(self):
        """Test generating evidence chain for lexicon IDs."""
        integration = FractalHubIntegration()
        
        lexicon_ids = ["U:DIACRITIC:FATHA", "U:DIACRITIC:KASRA"]
        chain = integration.get_evidence_chain(lexicon_ids)
        
        assert isinstance(chain, dict)
        assert "entries" in chain
        assert "min_confidence" in chain
        assert "max_confidence" in chain
        assert "avg_confidence" in chain
        assert "total_attestations" in chain
        assert "sources" in chain
        
        # Confidence scores should be valid
        assert 0.0 <= chain["min_confidence"] <= 1.0
        assert 0.0 <= chain["max_confidence"] <= 1.0
        assert 0.0 <= chain["avg_confidence"] <= 1.0
        assert chain["total_attestations"] >= 0
    
    def test_validate_evidence_pass(self):
        """Test evidence validation that should pass."""
        integration = FractalHubIntegration()
        
        lexicon_ids = ["U:DIACRITIC:FATHA"]
        valid, reason = integration.validate_evidence(lexicon_ids, min_confidence=0.5)
        
        assert isinstance(valid, bool)
        assert isinstance(reason, str)
        
        # If entry exists with yaqin (1.0), should pass 0.5 threshold
        if integration.get_lexicon_entry("U:DIACRITIC:FATHA"):
            prov = integration.get_provenance("U:DIACRITIC:FATHA")
            if prov and prov.confidence == "yaqin":
                assert valid is True
                assert "meets minimum confidence" in reason.lower()
    
    def test_validate_evidence_fail(self):
        """Test evidence validation that should fail."""
        integration = FractalHubIntegration()
        
        lexicon_ids = ["U:DIACRITIC:FATHA"]
        valid, reason = integration.validate_evidence(lexicon_ids, min_confidence=1.5)
        
        # Should fail because max confidence is 1.0
        assert valid is False
        assert "below minimum confidence" in reason.lower()
    
    def test_get_dictionary_stats(self):
        """Test getting dictionary statistics."""
        integration = FractalHubIntegration()
        
        stats = integration.get_dictionary_stats()
        
        assert isinstance(stats, dict)
        assert "version" in stats
        assert "total_units" in stats
        assert "total_gates" in stats
        assert "units_by_layer" in stats
        assert "units_by_type" in stats
        assert "confidence_distribution" in stats
        
        # Version should match
        assert stats["version"] == "v02"
        
        # Counts should be non-negative
        assert stats["total_units"] >= 0
        assert stats["total_gates"] >= 0
        
        # Layer distribution should have valid layers
        for layer in stats["units_by_layer"].keys():
            assert layer in ["C0", "C1", "C2", "C3", "unknown"]
        
        # Confidence distribution should have valid levels
        conf_dist = stats["confidence_distribution"]
        assert "yaqin" in conf_dist
        assert "zann" in conf_dist
        assert "shakk" in conf_dist
    
    def test_entry_caching(self):
        """Test that lexicon entries are cached."""
        integration = FractalHubIntegration()
        
        # Get entry twice
        entry1 = integration.get_lexicon_entry("U:DIACRITIC:FATHA")
        entry2 = integration.get_lexicon_entry("U:DIACRITIC:FATHA")
        
        if entry1:
            # Should return same object (cached)
            assert entry1 is entry2
    
    def test_lexicon_entry_to_dict(self):
        """Test converting LexiconEntry to dictionary."""
        integration = FractalHubIntegration()
        
        entry = integration.get_lexicon_entry("U:DIACRITIC:FATHA")
        
        if entry:
            entry_dict = entry.to_dict()
            
            assert isinstance(entry_dict, dict)
            assert "lexicon_id" in entry_dict
            assert "entry_type" in entry_dict
            assert "layer" in entry_dict
            assert "form" in entry_dict
            assert "provenance" in entry_dict
            assert "status" in entry_dict
    
    def test_provenance_info_to_dict(self):
        """Test converting ProvenanceInfo to dictionary."""
        prov = ProvenanceInfo(
            source_type="corpus",
            confidence="yaqin",
            confidence_score=1.0,
            attestation_count=100,
            references=["Sibawayh"],
        )
        
        prov_dict = prov.to_dict()
        
        assert isinstance(prov_dict, dict)
        assert prov_dict["source_type"] == "corpus"
        assert prov_dict["confidence"] == "yaqin"
        assert prov_dict["confidence_score"] == 1.0
        assert prov_dict["attestation_count"] == 100
        assert prov_dict["references"] == ["Sibawayh"]
    
    def test_epistemic_level_enum(self):
        """Test EpistemicLevel enum."""
        assert EpistemicLevel.YAQIN.value == "yaqin"
        assert EpistemicLevel.ZANN.value == "zann"
        assert EpistemicLevel.SHAKK.value == "shakk"
    
    def test_is_fractalhub_available(self):
        """Test checking if FractalHub is available."""
        available = is_fractalhub_available()
        
        assert isinstance(available, bool)
        # Since tests are running, it should be available
        assert available is True


class TestIntegrationWithCTEGate:
    """Test integration with CTE Gate for evidence validation."""
    
    def test_evidence_for_homonymy_check(self):
        """Test generating evidence for NO_HOMONYMY condition."""
        integration = FractalHubIntegration()
        
        # Get evidence chain for a word
        lexicon_ids = ["U:DIACRITIC:FATHA"]
        chain = integration.get_evidence_chain(lexicon_ids)
        
        # Should have evidence data
        assert "entries" in chain
        assert "avg_confidence" in chain
        
        # Can use this for CTE Gate validation
        if chain["avg_confidence"] >= 0.7:
            # High confidence = less likely to have homonymy
            pass
    
    def test_evidence_for_transfer_check(self):
        """Test generating evidence for NO_TRANSFER condition."""
        integration = FractalHubIntegration()
        
        # Check attestation count (high = established meaning, low = possible transfer)
        entry = integration.get_lexicon_entry("U:DIACRITIC:FATHA")
        
        if entry:
            attestations = entry.provenance.attestation_count
            
            # High attestation count suggests stable meaning (no transfer)
            assert attestations >= 0
    
    def test_confidence_mapping_to_gate_level(self):
        """Test mapping FractalHub confidence to CTE Gate levels."""
        integration = FractalHubIntegration()
        
        # yaqin (1.0) -> CERTAIN
        # zann (0.7) -> PROBABLE  
        # shakk (0.4) -> POSSIBLE
        
        entry = integration.get_lexicon_entry("U:DIACRITIC:FATHA")
        
        if entry:
            conf = entry.provenance.confidence
            score = entry.provenance.confidence_score
            
            if conf == "yaqin":
                assert score == 1.0
                # Maps to GateLevel.CERTAIN
            elif conf == "zann":
                assert score == 0.7
                # Maps to GateLevel.PROBABLE
            elif conf == "shakk":
                assert score == 0.4
                # Maps to GateLevel.POSSIBLE


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
