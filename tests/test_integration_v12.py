"""
Integration Tests for FractalHub v1.2

Tests the integration between kernel and dictionary,
ensuring locked architecture constraints are enforced.
"""

import pytest
from fractalhub.kernel import (
    Trace,
    TraceManager,
    Gate,
    GateType,
    gate_registry,
    FourConditions,
    FormCodec,
    MeaningCodec,
)
from fractalhub.dictionary import DictionaryLoader, get_dictionary


class TestKernelDictionaryIntegration:
    """Test integration between kernel and dictionary."""
    
    def test_trace_with_dictionary_prior_ids(self):
        """Test creating trace with dictionary-validated prior_ids."""
        dictionary = get_dictionary()
        trace_manager = TraceManager()
        
        # Create trace with valid dictionary entries
        trace = trace_manager.create_trace()
        trace.add_gate("G_ATTEND:001")
        trace.add_prior_id("lexicon_ids", "SIGNIFIER:FATHA")
        trace.add_prior_id("ruleset_ids", "PHONOLOGY:DOUBLE_SUKUN")
        
        # Validate prior_ids against dictionary
        is_valid, errors = dictionary.validate_prior_ids(trace.prior_ids)
        assert is_valid
        
        # Trace should be valid
        trace_valid, trace_errors = trace.validate()
        assert trace_valid
    
    def test_trace_with_invalid_prior_ids(self):
        """Test that invalid prior_ids are caught."""
        dictionary = get_dictionary()
        trace_manager = TraceManager()
        
        # Create trace with invalid dictionary entries
        trace = trace_manager.create_trace()
        trace.add_gate("G_ATTEND:001")
        trace.add_prior_id("lexicon_ids", "SIGNIFIER:NONEXISTENT")
        
        # Validate prior_ids against dictionary
        is_valid, errors = dictionary.validate_prior_ids(trace.prior_ids)
        assert not is_valid
        assert len(errors) > 0
    
    def test_gate_with_dictionary_prior_knowledge(self):
        """Test creating gate with dictionary prior knowledge."""
        dictionary = get_dictionary()
        
        # Get dictionary entries for prior knowledge
        fatha = dictionary.get_lexicon_entry("SIGNIFIER:FATHA")
        double_sukun = dictionary.get_ruleset("PHONOLOGY:DOUBLE_SUKUN")
        
        assert fatha is not None
        assert double_sukun is not None
        
        # Create gate with dictionary prior knowledge
        gate = gate_registry.create_gate(
            gate_type=GateType.G_CODEC_VERIFY,
            reality="text_stream",
            brain="processor_001",
            sensing="text",
            prior_knowledge={
                "lexicon_ids": ["SIGNIFIER:FATHA"],
                "ruleset_ids": ["PHONOLOGY:DOUBLE_SUKUN"]
            },
            input_data="test"
        )
        
        assert gate is not None
        
        # Validate prior_ids
        is_valid, errors = dictionary.validate_prior_ids(
            gate.conditions.prior_knowledge
        )
        assert is_valid
    
    def test_form_codec_with_dictionary_forms(self):
        """Test FormCodec with dictionary signifier forms."""
        dictionary = get_dictionary()
        codec = FormCodec()
        
        # Get signifier entries from dictionary
        signifiers = dictionary.get_signifier_entries()
        
        # Test encoding/decoding with dictionary forms
        for entry_id, entry in list(signifiers.items())[:5]:  # Test first 5
            form = entry.get('form')
            if form and len(form) > 0:
                # Test reversibility
                assert codec.verify_reversibility(form)
    
    def test_meaning_codec_with_dictionary_signifieds(self):
        """Test MeaningCodec with dictionary signified entries."""
        dictionary = get_dictionary()
        codec = MeaningCodec()
        trace_manager = TraceManager()
        
        # Create trace for meaning
        trace = trace_manager.create_trace()
        trace.add_gate("G_MEMORY_WRITE:001")
        trace.add_prior_id("lexicon_ids", "SIGNIFIED:KITAB:BOOK")
        
        # Get signified entry from dictionary
        book = dictionary.get_lexicon_entry("SIGNIFIED:KITAB:BOOK")
        assert book is not None
        
        # Encode meaning with provenance from dictionary
        encoded = codec.encode_meaning(
            concept=book['concept_en'],
            trace_id=trace.trace_id,
            prior_ids={"lexicon_ids": ["SIGNIFIED:KITAB:BOOK"]},
            provenance=book['provenance']
        )
        
        assert encoded['concept'] == 'book'
        assert encoded['layer'] == 'C3'
        
        # Validate prior_ids
        is_valid, errors = dictionary.validate_prior_ids(encoded['prior_ids'])
        assert is_valid
    
    def test_epistemic_strength_from_dictionary(self):
        """Test using epistemic strength definitions from dictionary."""
        dictionary = get_dictionary()
        trace_manager = TraceManager()
        
        # Get epistemic strengths from dictionary
        strengths = dictionary.get_epistemic_strengths()
        
        # Create trace with ZANN (probability) strength
        zann_strength = strengths['ZANN']['strength']
        trace = trace_manager.create_trace(evidence_strength=zann_strength)
        
        assert trace.evidence_strength == 0.7
    
    def test_reasoning_mode_requirements(self):
        """Test reasoning mode requirements from dictionary."""
        dictionary = get_dictionary()
        
        # Get reasoning modes from dictionary
        modes = dictionary.get_reasoning_modes()
        
        # All modes should require prior_ids
        for mode_name, mode in modes.items():
            assert mode['requires_prior_ids'] is True
    
    def test_gate_definitions_from_dictionary(self):
        """Test that dictionary gate definitions match kernel gates."""
        dictionary = get_dictionary()
        
        # Get gate definitions from dictionary
        dict_gates = dictionary.get_gates()
        
        # Check core gates exist
        assert 'G_ATTEND' in dict_gates
        assert 'G_CODEC_VERIFY' in dict_gates
        assert 'G_SPEECH_ACT' in dict_gates
        
        # Check they require four conditions
        for gate_id, gate in dict_gates.items():
            assert gate['requires_four_conditions'] is True
            assert gate['layer'] == 'C2'


class TestLockedArchitecture:
    """Test locked architecture constraints enforcement."""
    
    def test_no_c3_without_c2_trace(self):
        """Test: NO C3 without C2 trace."""
        codec = MeaningCodec()
        
        # Should fail without trace_id
        with pytest.raises(ValueError) as exc_info:
            codec.encode_meaning(
                concept="test",
                trace_id="",  # Empty trace_id
                prior_ids={"lexicon_ids": ["SIGNIFIED:KITAB:BOOK"]},
                provenance=[]
            )
        
        assert "no meaning without c2 trace" in str(exc_info.value).lower()
    
    def test_no_c2_without_c1_conditions(self):
        """Test: NO C2 without C1 four conditions."""
        # Should fail without four conditions
        with pytest.raises(ValueError) as exc_info:
            gate_registry.create_gate(
                gate_type=GateType.G_ATTEND,
                reality=None,  # Missing reality
                brain="processor",
                sensing="text",
                prior_knowledge={}  # Missing prior knowledge
            )
        
        assert "four conditions not satisfied" in str(exc_info.value).lower()
    
    def test_no_meaning_without_prior_ids(self):
        """Test: NO meaning without prior_ids evidence."""
        codec = MeaningCodec()
        
        # Should fail without prior_ids
        with pytest.raises(ValueError) as exc_info:
            codec.encode_meaning(
                concept="test",
                trace_id="C2:TRACE:abc123",
                prior_ids={},  # Empty prior_ids
                provenance=[]
            )
        
        assert "no meaning without prior_ids" in str(exc_info.value).lower()
    
    def test_trace_validation_enforces_prior_ids(self):
        """Test that trace validation enforces prior_ids requirement."""
        trace = Trace()
        trace.add_gate("G_ATTEND:001")
        
        # Should fail without prior_ids
        is_valid, errors = trace.validate()
        assert not is_valid
        assert any("prior_ids" in e.lower() for e in errors)
    
    def test_trace_manager_enforces_c2_requirement(self):
        """Test that TraceManager enforces C2 requirement for C3."""
        trace_manager = TraceManager()
        
        # Invalid trace (no gates, no prior_ids)
        invalid_trace = trace_manager.create_trace()
        
        # Should fail C2 requirement
        result = trace_manager.enforce_c2_requirement(
            "C3:ENTITY:001",
            invalid_trace.trace_id
        )
        assert not result
        
        # Valid trace (with gates and prior_ids)
        valid_trace = trace_manager.create_trace()
        valid_trace.add_gate("G_ATTEND:001")
        valid_trace.add_prior_id("lexicon_ids", "SIGNIFIER:TEST")
        
        # Should pass C2 requirement
        result = trace_manager.enforce_c2_requirement(
            "C3:ENTITY:002",
            valid_trace.trace_id
        )
        assert result
    
    def test_signifier_signified_separation(self):
        """Test strict separation between signifier (C1) and signified (C3)."""
        dictionary = get_dictionary()
        
        # Get signifier and signified entries
        signifiers = dictionary.get_signifier_entries()
        signifieds = dictionary.get_signified_entries()
        
        # Signifiers (C1) must NOT have meaning
        for entry_id, entry in signifiers.items():
            assert 'semantic_features' not in entry
            assert 'ontology_type' not in entry
            assert entry['layer'] == 'C1'
        
        # Signifieds (C3) must NOT have form
        for entry_id, entry in signifieds.items():
            assert 'form' not in entry
            assert entry['layer'] == 'C3'


class TestEndToEndWorkflow:
    """Test complete end-to-end workflows."""
    
    def test_complete_processing_pipeline(self):
        """Test complete processing from form to meaning."""
        dictionary = get_dictionary()
        trace_manager = TraceManager()
        form_codec = FormCodec()
        meaning_codec = MeaningCodec()
        
        # Step 1: Encode form (C1)
        arabic_text = "كتاب"
        encoded_form, checksum = form_codec.encode(arabic_text)
        
        # Step 2: Create trace with dictionary prior_ids (C2)
        trace = trace_manager.create_trace(evidence_strength=1.0)
        trace.add_gate("G_ATTEND:001")
        trace.add_gate("G_CODEC_VERIFY:001")
        trace.add_prior_id("lexicon_ids", "SIGNIFIER:KITAB")
        trace.add_prior_id("lexicon_ids", "SIGNIFIED:KITAB:BOOK")
        trace.add_prior_id("ruleset_ids", "MORPHOLOGY:BROKEN_PLURAL")
        
        # Validate trace
        is_valid, errors = trace.validate()
        assert is_valid
        
        # Step 3: Create meaning with provenance (C3)
        book_entry = dictionary.get_lexicon_entry("SIGNIFIED:KITAB:BOOK")
        meaning = meaning_codec.encode_meaning(
            concept=book_entry['concept_en'],
            trace_id=trace.trace_id,
            prior_ids=trace.prior_ids,
            provenance=book_entry['provenance']
        )
        
        # Validate complete chain
        assert meaning['layer'] == 'C3'
        assert meaning['trace_id'] == trace.trace_id
        assert trace_manager.enforce_c2_requirement("C3:MEANING:001", trace.trace_id)
        
        # Validate prior_ids against dictionary
        is_valid, errors = dictionary.validate_prior_ids(meaning['prior_ids'])
        assert is_valid
        
        # Step 4: Verify reversibility
        decoded_form = form_codec.decode(encoded_form, checksum)
        assert decoded_form == arabic_text
    
    def test_speech_act_with_dictionary(self):
        """Test speech act processing with dictionary."""
        dictionary = get_dictionary()
        trace_manager = TraceManager()
        
        # Get speech act gate from dictionary
        speech_act_gate = dictionary.get_gate('G_SPEECH_ACT')
        assert speech_act_gate is not None
        assert 'supported_types' in speech_act_gate
        
        # Create trace for speech act
        trace = trace_manager.create_trace()
        trace.add_gate("G_SPEECH_ACT:001")
        trace.add_prior_id("lexicon_ids", "SIGNIFIER:KITAB")
        trace.add_prior_id("ruleset_ids", "SYNTAX:VERB_SUBJECT_AGREEMENT")
        
        # Validate
        is_valid, errors = trace.validate()
        assert is_valid
    
    def test_reasoning_with_evidence(self):
        """Test reasoning with epistemic evidence from dictionary."""
        dictionary = get_dictionary()
        trace_manager = TraceManager()
        
        # Get reasoning mode requirements
        deductive = dictionary.get_reasoning_modes()['DEDUCTIVE']
        assert deductive['requires_prior_ids'] is True
        assert deductive['min_strength'] == 0.9
        
        # Create trace with appropriate evidence strength
        trace = trace_manager.create_trace(evidence_strength=0.9)
        trace.add_gate("G_MEMORY_READ:001")
        trace.add_prior_id("lexicon_ids", "SIGNIFIED:KITAB:BOOK")
        trace.add_prior_id("ruleset_ids", "SYNTAX:IDAFA_CONSTRUCT")
        
        # Should be valid for deductive reasoning
        is_valid, errors = trace.validate()
        assert is_valid
        assert trace.evidence_strength >= deductive['min_strength']
    
    def test_phonological_processing(self):
        """Test phonological processing with dictionary rules."""
        dictionary = get_dictionary()
        trace_manager = TraceManager()
        
        # Get phonological rules from dictionary
        double_sukun = dictionary.get_ruleset("PHONOLOGY:DOUBLE_SUKUN")
        assert double_sukun is not None
        assert double_sukun['layer'] == 'C0'
        assert double_sukun['constraint'] == 'NO_CONSECUTIVE_SUKUN'
        
        # Create trace with phonological prior_ids
        trace = trace_manager.create_trace()
        trace.add_gate("G_CODEC_VERIFY:001")
        trace.add_prior_id("lexicon_ids", "SIGNIFIER:SUKUN")
        trace.add_prior_id("ruleset_ids", "PHONOLOGY:DOUBLE_SUKUN")
        
        # Validate
        is_valid, errors = trace.validate()
        assert is_valid


class TestInvariantsIntegration:
    """Test integration with conservation laws and symmetry rules."""
    
    def test_conservation_laws_from_dictionary(self):
        """Test conservation laws defined in dictionary."""
        dictionary = get_dictionary()
        
        # Get conservation laws
        laws = dictionary.get_conservation_laws()
        
        # Check all expected laws exist
        assert 'TEMPORAL' in laws
        assert 'REFERENTIAL' in laws
        assert 'CAUSAL' in laws
        assert 'PREDICATIVE' in laws
        assert 'QUANTITATIVE' in laws
        assert 'SCOPE' in laws
        
        # Each should have required fields
        for law_name, law in laws.items():
            assert 'law_id' in law
            assert 'description_ar' in law
            assert 'description_en' in law
            assert 'constraint' in law
            assert 'penalty' in law
    
    def test_symmetry_rules_from_dictionary(self):
        """Test symmetry rules defined in dictionary."""
        dictionary = get_dictionary()
        
        # Get symmetry rules
        rules = dictionary.get_symmetry_rules()
        
        # Check all expected rules exist
        assert 'LOGICAL' in rules
        assert 'STRUCTURAL' in rules
        assert 'SEMANTIC' in rules
        assert 'PRAGMATIC' in rules
        
        # Each should have required fields
        for rule_name, rule in rules.items():
            assert 'rule_id' in rule
            assert 'description_ar' in rule
            assert 'description_en' in rule
            assert 'constraint' in rule
    
    def test_trace_invariant_checks(self):
        """Test that traces record invariant checks."""
        trace = Trace()
        
        # Add invariant checks
        trace.add_invariant_check("passed", "TEMPORAL_CONSERVATION")
        trace.add_invariant_check("passed", "REFERENTIAL_CONSERVATION")
        trace.add_invariant_check("warnings", "SCOPE_CONSERVATION")
        
        # Check they're recorded
        assert "TEMPORAL_CONSERVATION" in trace.invariant_checks_report['passed']
        assert "REFERENTIAL_CONSERVATION" in trace.invariant_checks_report['passed']
        assert "SCOPE_CONSERVATION" in trace.invariant_checks_report['warnings']


class TestProvenanceTracking:
    """Test provenance tracking through the system."""
    
    def test_provenance_chain_from_dictionary_to_meaning(self):
        """Test that provenance flows from dictionary to meaning."""
        dictionary = get_dictionary()
        trace_manager = TraceManager()
        meaning_codec = MeaningCodec()
        
        # Get entry with provenance from dictionary
        book_entry = dictionary.get_lexicon_entry("SIGNIFIED:KITAB:BOOK")
        assert 'provenance' in book_entry
        assert len(book_entry['provenance']) > 0
        
        # Create trace
        trace = trace_manager.create_trace()
        trace.add_gate("G_MEMORY_WRITE:001")
        trace.add_prior_id("lexicon_ids", "SIGNIFIED:KITAB:BOOK")
        
        # Create meaning with dictionary provenance
        meaning = meaning_codec.encode_meaning(
            concept=book_entry['concept_en'],
            trace_id=trace.trace_id,
            prior_ids=trace.prior_ids,
            provenance=book_entry['provenance']
        )
        
        # Verify provenance chain
        assert meaning['provenance'] == book_entry['provenance']
        
        # Verify sources exist in dictionary
        for prov in meaning['provenance']:
            source = dictionary.get_provenance_source(prov['source_id'])
            assert source is not None
    
    def test_confidence_propagation(self):
        """Test that confidence values propagate correctly."""
        dictionary = get_dictionary()
        
        # Get entry with multiple provenance sources
        book_entry = dictionary.get_lexicon_entry("SIGNIFIED:KITAB:BOOK")
        
        # Check confidence values
        for prov in book_entry['provenance']:
            assert 'confidence' in prov
            assert 0.0 <= prov['confidence'] <= 1.0
            
            # Verify source reliability
            source = dictionary.get_provenance_source(prov['source_id'])
            assert 'reliability' in source
            assert 0.0 <= source['reliability'] <= 1.0
