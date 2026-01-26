"""
Tests for FractalHub Dictionary v02

Validates dictionary loading, structure, and validation.
"""

import pytest
from fractalhub.dictionary import DictionaryLoader, get_dictionary, reload_dictionary
from fractalhub.dictionary.validator import DictionaryValidator
from pathlib import Path


class TestDictionaryLoader:
    """Test dictionary loading functionality."""
    
    def test_loader_initialization(self):
        """Test dictionary loader initializes correctly."""
        loader = DictionaryLoader()
        
        assert loader.data is not None
        assert len(loader.data) > 0
    
    def test_get_meta(self):
        """Test getting dictionary metadata."""
        loader = DictionaryLoader()
        meta = loader.get_meta()
        
        assert 'dict_version' in meta
        assert meta['dict_version'] == 2
        assert 'codec_version' in meta
        assert 'schema_version' in meta
        assert 'generated_at' in meta
        assert 'compatibility' in meta
    
    def test_get_version(self):
        """Test getting dictionary version."""
        loader = DictionaryLoader()
        version = loader.get_version()
        
        assert version == 2
    
    def test_get_provenance_sources(self):
        """Test getting provenance sources."""
        loader = DictionaryLoader()
        sources = loader.get_provenance_sources()
        
        assert 'CLASSICAL_CORPUS' in sources
        assert 'MODERN_USAGE' in sources
        assert 'LINGUISTIC_RULE' in sources
        assert 'PHONOLOGICAL_CONSTRAINT' in sources
    
    def test_get_provenance_source(self):
        """Test getting specific provenance source."""
        loader = DictionaryLoader()
        source = loader.get_provenance_source('CLASSICAL_CORPUS')
        
        assert source is not None
        assert source['source_id'] == 'CLASSICAL_CORPUS'
        assert source['type'] == 'corpus'
        assert source['reliability'] == 1.0
        assert 'description_ar' in source
        assert 'description_en' in source
    
    def test_get_lexicon(self):
        """Test getting entire lexicon."""
        loader = DictionaryLoader()
        lexicon = loader.get_lexicon()
        
        assert len(lexicon) > 0
        assert 'SIGNIFIER:FATHA' in lexicon
        assert 'SIGNIFIED:KITAB:BOOK' in lexicon
    
    def test_get_lexicon_entry(self):
        """Test getting specific lexicon entry."""
        loader = DictionaryLoader()
        
        # Test signifier entry
        fatha = loader.get_lexicon_entry('SIGNIFIER:FATHA')
        assert fatha is not None
        assert fatha['entry_type'] == 'signifier'
        assert fatha['layer'] == 'C1'
        assert fatha['form'] == 'َ'
        assert 'form_ar' in fatha
        assert 'form_en' in fatha
        
        # Test signified entry
        book = loader.get_lexicon_entry('SIGNIFIED:KITAB:BOOK')
        assert book is not None
        assert book['entry_type'] == 'signified'
        assert book['layer'] == 'C3'
        assert 'concept_ar' in book
        assert 'concept_en' in book
    
    def test_get_signifier_entries(self):
        """Test getting all signifier entries."""
        loader = DictionaryLoader()
        signifiers = loader.get_signifier_entries()
        
        assert len(signifiers) > 0
        for entry_id, entry in signifiers.items():
            assert entry['entry_type'] == 'signifier'
            assert entry['layer'] == 'C1'
            assert 'form' in entry
    
    def test_get_signified_entries(self):
        """Test getting all signified entries."""
        loader = DictionaryLoader()
        signifieds = loader.get_signified_entries()
        
        assert len(signifieds) > 0
        for entry_id, entry in signifieds.items():
            assert entry['entry_type'] == 'signified'
            assert entry['layer'] == 'C3'
            assert 'concept_ar' in entry or 'concept_en' in entry
    
    def test_signifier_signified_separation(self):
        """Test that signifiers and signifieds are properly separated."""
        loader = DictionaryLoader()
        
        # Signifiers should NOT have semantic features
        signifiers = loader.get_signifier_entries()
        for entry_id, entry in signifiers.items():
            assert 'semantic_features' not in entry
            assert 'ontology_type' not in entry
        
        # Signifieds should NOT have form
        signifieds = loader.get_signified_entries()
        for entry_id, entry in signifieds.items():
            assert 'form' not in entry
    
    def test_get_rulesets(self):
        """Test getting rulesets."""
        loader = DictionaryLoader()
        rulesets = loader.get_rulesets()
        
        assert len(rulesets) > 0
        assert 'PHONOLOGY:DOUBLE_SUKUN' in rulesets
        assert 'MORPHOLOGY:BROKEN_PLURAL' in rulesets
    
    def test_get_ruleset(self):
        """Test getting specific ruleset."""
        loader = DictionaryLoader()
        ruleset = loader.get_ruleset('PHONOLOGY:DOUBLE_SUKUN')
        
        assert ruleset is not None
        assert ruleset['ruleset_id'] == 'PHONOLOGY:DOUBLE_SUKUN'
        assert ruleset['type'] == 'phonological'
        assert ruleset['layer'] == 'C0'
        assert 'description_ar' in ruleset
        assert 'description_en' in ruleset
    
    def test_get_rulesets_by_layer(self):
        """Test getting rulesets by layer."""
        loader = DictionaryLoader()
        
        c0_rules = loader.get_rulesets_by_layer('C0')
        assert len(c0_rules) > 0
        for ruleset in c0_rules.values():
            assert ruleset['layer'] == 'C0'
        
        c1_rules = loader.get_rulesets_by_layer('C1')
        assert len(c1_rules) > 0
        for ruleset in c1_rules.values():
            assert ruleset['layer'] == 'C1'
    
    def test_get_gates(self):
        """Test getting gates."""
        loader = DictionaryLoader()
        gates = loader.get_gates()
        
        assert len(gates) > 0
        assert 'G_ATTEND' in gates
        assert 'G_CODEC_VERIFY' in gates
        assert 'G_SPEECH_ACT' in gates
        assert 'G_MEMORY_READ' in gates
        assert 'G_MEMORY_WRITE' in gates
    
    def test_get_gate(self):
        """Test getting specific gate."""
        loader = DictionaryLoader()
        gate = loader.get_gate('G_ATTEND')
        
        assert gate is not None
        assert gate['gate_id'] == 'G_ATTEND'
        assert gate['gate_type'] == 'attention'
        assert gate['layer'] == 'C2'
        assert gate['requires_four_conditions'] is True
    
    def test_get_evidence_config(self):
        """Test getting evidence configuration."""
        loader = DictionaryLoader()
        evidence = loader.get_evidence_config()
        
        assert 'epistemic_strength' in evidence
        assert 'reasoning_modes' in evidence
    
    def test_get_epistemic_strengths(self):
        """Test getting epistemic strengths."""
        loader = DictionaryLoader()
        strengths = loader.get_epistemic_strengths()
        
        assert 'YAQIN' in strengths
        assert 'ZANN' in strengths
        assert 'SHAKK' in strengths
        
        assert strengths['YAQIN']['strength'] == 1.0
        assert strengths['ZANN']['strength'] == 0.7
        assert strengths['SHAKK']['strength'] == 0.4
    
    def test_get_reasoning_modes(self):
        """Test getting reasoning modes."""
        loader = DictionaryLoader()
        modes = loader.get_reasoning_modes()
        
        assert 'DEDUCTIVE' in modes
        assert 'INDUCTIVE' in modes
        assert 'ABDUCTIVE' in modes
        assert 'INFERENTIAL' in modes
        
        # All should require prior_ids
        for mode in modes.values():
            assert mode['requires_prior_ids'] is True
    
    def test_get_invariants(self):
        """Test getting invariants."""
        loader = DictionaryLoader()
        invariants = loader.get_invariants()
        
        assert 'conservation_laws' in invariants
        assert 'symmetry_rules' in invariants
    
    def test_get_conservation_laws(self):
        """Test getting conservation laws."""
        loader = DictionaryLoader()
        laws = loader.get_conservation_laws()
        
        assert 'TEMPORAL' in laws
        assert 'REFERENTIAL' in laws
        assert 'CAUSAL' in laws
        assert 'PREDICATIVE' in laws
        assert 'QUANTITATIVE' in laws
        assert 'SCOPE' in laws
    
    def test_get_symmetry_rules(self):
        """Test getting symmetry rules."""
        loader = DictionaryLoader()
        rules = loader.get_symmetry_rules()
        
        assert 'LOGICAL' in rules
        assert 'STRUCTURAL' in rules
        assert 'SEMANTIC' in rules
        assert 'PRAGMATIC' in rules
    
    def test_get_mappings(self):
        """Test getting mappings."""
        loader = DictionaryLoader()
        mappings = loader.get_mappings()
        
        assert 'signifier_to_signified' in mappings
        assert 'ruleset_to_layer' in mappings
    
    def test_get_signifier_to_signified_mapping(self):
        """Test getting signifier to signified mapping."""
        loader = DictionaryLoader()
        mapping = loader.get_signifier_to_signified_mapping('KITAB')
        
        assert mapping is not None
        assert mapping['signifier'] == 'SIGNIFIER:KITAB'
        assert 'SIGNIFIED:KITAB:BOOK' in mapping['signifieds']
    
    def test_search_by_form(self):
        """Test searching entries by form."""
        loader = DictionaryLoader()
        
        results = loader.search_by_form('كتاب')
        assert len(results) > 0
        
        # Should find both signifier and signified
        entry_types = [r['entry_type'] for r in results]
        assert 'signifier' in entry_types or 'signified' in entry_types
    
    def test_validate_prior_ids_success(self):
        """Test validating prior_ids with existing entries."""
        loader = DictionaryLoader()
        
        prior_ids = {
            'lexicon_ids': ['SIGNIFIER:FATHA', 'SIGNIFIED:KITAB:BOOK'],
            'ruleset_ids': ['PHONOLOGY:DOUBLE_SUKUN']
        }
        
        is_valid, errors = loader.validate_prior_ids(prior_ids)
        assert is_valid
        assert len(errors) == 0
    
    def test_validate_prior_ids_invalid_lexicon(self):
        """Test validating prior_ids with non-existent lexicon entry."""
        loader = DictionaryLoader()
        
        prior_ids = {
            'lexicon_ids': ['SIGNIFIER:NONEXISTENT']
        }
        
        is_valid, errors = loader.validate_prior_ids(prior_ids)
        assert not is_valid
        assert len(errors) > 0
        assert 'SIGNIFIER:NONEXISTENT' in errors[0]
    
    def test_validate_prior_ids_invalid_ruleset(self):
        """Test validating prior_ids with non-existent ruleset."""
        loader = DictionaryLoader()
        
        prior_ids = {
            'ruleset_ids': ['RULESET:NONEXISTENT']
        }
        
        is_valid, errors = loader.validate_prior_ids(prior_ids)
        assert not is_valid
        assert len(errors) > 0


class TestGlobalDictionary:
    """Test global dictionary functions."""
    
    def test_get_dictionary(self):
        """Test getting global dictionary instance."""
        dict1 = get_dictionary()
        dict2 = get_dictionary()
        
        # Should return same instance
        assert dict1 is dict2
    
    def test_reload_dictionary(self):
        """Test reloading dictionary."""
        dict1 = get_dictionary()
        dict2 = reload_dictionary()
        
        # Should be different instances
        assert dict1 is not dict2
        
        # But should have same data
        assert dict1.get_version() == dict2.get_version()


class TestDictionaryValidator:
    """Test dictionary validation."""
    
    def test_validator_initialization(self):
        """Test validator initializes correctly."""
        dict_path = Path(__file__).parent.parent / "fractalhub" / "data" / "fractalhub_dictionary_v02.yaml"
        validator = DictionaryValidator(str(dict_path))
        
        assert validator.data is not None
        assert len(validator.data) > 0
    
    def test_validation_success(self):
        """Test validation of valid dictionary."""
        dict_path = Path(__file__).parent.parent / "fractalhub" / "data" / "fractalhub_dictionary_v02.yaml"
        validator = DictionaryValidator(str(dict_path))
        
        is_valid, errors, warnings = validator.validate()
        
        assert is_valid
        assert len(errors) == 0
    
    def test_get_report(self):
        """Test getting validation report."""
        dict_path = Path(__file__).parent.parent / "fractalhub" / "data" / "fractalhub_dictionary_v02.yaml"
        validator = DictionaryValidator(str(dict_path))
        validator.validate()
        
        report = validator.get_report()
        
        assert "FractalHub Dictionary v02 Validation Report" in report
        assert "PASSED" in report


class TestDictionaryProvenance:
    """Test provenance tracking in dictionary."""
    
    def test_all_entries_have_provenance(self):
        """Test that all entries have provenance information."""
        loader = DictionaryLoader()
        lexicon = loader.get_lexicon()
        
        entries_without_provenance = []
        for entry_id, entry in lexicon.items():
            if 'provenance' not in entry:
                entries_without_provenance.append(entry_id)
        
        # All entries should have provenance
        assert len(entries_without_provenance) == 0
    
    def test_provenance_sources_exist(self):
        """Test that all referenced provenance sources exist."""
        loader = DictionaryLoader()
        lexicon = loader.get_lexicon()
        sources = loader.get_provenance_sources()
        
        missing_sources = set()
        for entry_id, entry in lexicon.items():
            if 'provenance' in entry:
                for prov in entry['provenance']:
                    source_id = prov.get('source_id')
                    if source_id and source_id not in sources:
                        missing_sources.add(source_id)
        
        assert len(missing_sources) == 0
    
    def test_provenance_confidence_values(self):
        """Test that provenance confidence values are valid."""
        loader = DictionaryLoader()
        lexicon = loader.get_lexicon()
        
        for entry_id, entry in lexicon.items():
            if 'provenance' in entry:
                for prov in entry['provenance']:
                    if 'confidence' in prov:
                        confidence = prov['confidence']
                        assert 0.0 <= confidence <= 1.0


class TestDictionaryBilingualSupport:
    """Test bilingual (Arabic/English) support."""
    
    def test_all_entries_have_bilingual_descriptions(self):
        """Test that entries have both Arabic and English descriptions."""
        loader = DictionaryLoader()
        
        # Check lexicon
        lexicon = loader.get_lexicon()
        for entry_id, entry in lexicon.items():
            if entry.get('entry_type') == 'signifier':
                assert 'form_ar' in entry
                assert 'form_en' in entry
            elif entry.get('entry_type') == 'signified':
                assert 'concept_ar' in entry
                assert 'concept_en' in entry
        
        # Check rulesets
        rulesets = loader.get_rulesets()
        for ruleset_id, ruleset in rulesets.items():
            assert 'description_ar' in ruleset
            assert 'description_en' in ruleset
        
        # Check gates
        gates = loader.get_gates()
        for gate_id, gate in gates.items():
            assert 'description_ar' in gate
            assert 'description_en' in gate
