"""
Tests for FractalHub Kernel v1.2

Validates version metadata, trace system, gates, and codecs.
"""

import pytest
from fractalhub.kernel import (
    get_version_metadata,
    KERNEL_VERSION,
    API_VERSION,
    Trace,
    TraceManager,
    Gate,
    GateType,
    gate_registry,
    FourConditions,
    FormCodec,
    MeaningCodec,
)


class TestVersionMetadata:
    """Test version metadata system."""
    
    def test_version_constants(self):
        """Test that version constants are defined."""
        assert KERNEL_VERSION == "1.2"
        assert API_VERSION == "1.2.0"
    
    def test_get_version_metadata(self):
        """Test version metadata generation."""
        metadata = get_version_metadata()
        
        assert "kernel_version" in metadata
        assert metadata["kernel_version"] == "1.2"
        assert "api_version" in metadata
        assert "schema_version" in metadata
        assert "compatibility" in metadata
        assert "created_at" in metadata
    
    def test_version_metadata_compatibility(self):
        """Test compatibility information."""
        metadata = get_version_metadata()
        
        assert metadata["compatibility"]["min_kernel_version"] == "1.0"
        assert metadata["compatibility"]["breaking_changes"] is False
    
    def test_version_metadata_no_timestamp(self):
        """Test metadata without timestamp."""
        metadata = get_version_metadata(include_timestamp=False)
        
        assert "created_at" not in metadata


class TestTrace:
    """Test enhanced trace system."""
    
    def test_trace_creation(self):
        """Test basic trace creation."""
        trace = Trace()
        
        assert trace.trace_id.startswith("C2:TRACE:")
        assert len(trace.gate_chain) == 0
        assert trace.evidence_strength == 1.0
        assert "kernel_version" in trace.metadata
    
    def test_trace_add_gate(self):
        """Test adding gates to trace."""
        trace = Trace()
        trace.add_gate("G_ATTEND:001", latency=0.5)
        
        assert "G_ATTEND:001" in trace.gate_chain
        assert trace.gate_latency["G_ATTEND:001"] == 0.5
    
    def test_trace_add_prior_id(self):
        """Test adding prior_ids evidence."""
        trace = Trace()
        trace.add_prior_id("lexicon_ids", "SIGNIFIER:FATHA")
        trace.add_prior_id("ruleset_ids", "PHONOLOGY:DOUBLE_SUKUN")
        
        assert "SIGNIFIER:FATHA" in trace.prior_ids["lexicon_ids"]
        assert "PHONOLOGY:DOUBLE_SUKUN" in trace.prior_ids["ruleset_ids"]
    
    def test_trace_add_invariant_check(self):
        """Test recording invariant checks."""
        trace = Trace()
        trace.add_invariant_check("passed", "temporal_conservation")
        trace.add_invariant_check("failed", "scope_coherence")
        
        assert "temporal_conservation" in trace.invariant_checks_report["passed"]
        assert "scope_coherence" in trace.invariant_checks_report["failed"]
    
    def test_trace_validation_no_gates(self):
        """Test trace validation fails without gates."""
        trace = Trace()
        is_valid, errors = trace.validate()
        
        assert not is_valid
        assert any("gate" in e.lower() for e in errors)
    
    def test_trace_validation_no_prior_ids(self):
        """Test trace validation fails without prior_ids."""
        trace = Trace()
        trace.add_gate("G_ATTEND:001")
        is_valid, errors = trace.validate()
        
        assert not is_valid
        assert any("prior_ids" in e.lower() for e in errors)
    
    def test_trace_validation_success(self):
        """Test successful trace validation."""
        trace = Trace()
        trace.add_gate("G_ATTEND:001")
        trace.add_prior_id("lexicon_ids", "SIGNIFIER:TEST")
        
        is_valid, errors = trace.validate()
        assert is_valid
        assert len(errors) == 0
    
    def test_trace_to_dict(self):
        """Test trace serialization."""
        trace = Trace()
        trace.add_gate("G_ATTEND:001")
        trace.add_prior_id("lexicon_ids", "SIGNIFIER:TEST")
        
        trace_dict = trace.to_dict()
        
        assert "trace_id" in trace_dict
        assert "gate_chain" in trace_dict
        assert "prior_ids" in trace_dict
        assert "metadata" in trace_dict


class TestTraceManager:
    """Test trace management system."""
    
    def test_trace_manager_creation(self):
        """Test creating traces via manager."""
        manager = TraceManager()
        trace = manager.create_trace(evidence_strength=0.8)
        
        assert trace.evidence_strength == 0.8
        assert trace.trace_id in manager.traces
    
    def test_trace_manager_get_trace(self):
        """Test retrieving traces."""
        manager = TraceManager()
        trace = manager.create_trace()
        
        retrieved = manager.get_trace(trace.trace_id)
        assert retrieved is trace
    
    def test_trace_manager_validate_trace(self):
        """Test trace validation via manager."""
        manager = TraceManager()
        trace = manager.create_trace()
        trace.add_gate("G_ATTEND:001")
        trace.add_prior_id("lexicon_ids", "SIGNIFIER:TEST")
        
        is_valid, errors = manager.validate_trace(trace.trace_id)
        assert is_valid
    
    def test_trace_manager_enforce_c2_requirement(self):
        """Test C2 requirement enforcement (NO C3 without C2)."""
        manager = TraceManager()
        trace = manager.create_trace()
        trace.add_gate("G_ATTEND:001")
        trace.add_prior_id("lexicon_ids", "SIGNIFIER:TEST")
        
        # Should pass with valid trace
        assert manager.enforce_c2_requirement("C3:ENTITY:001", trace.trace_id)
        
        # Should fail with invalid trace
        invalid_trace = manager.create_trace()
        assert not manager.enforce_c2_requirement("C3:ENTITY:002", invalid_trace.trace_id)
    
    def test_trace_manager_statistics(self):
        """Test trace statistics."""
        manager = TraceManager()
        trace1 = manager.create_trace()
        trace1.add_gate("G_ATTEND:001")
        trace1.add_prior_id("lexicon_ids", "SIGNIFIER:TEST")
        
        trace2 = manager.create_trace()
        trace2.add_gate("G_ATTEND:002")
        trace2.add_gate("G_CODEC_VERIFY:001")
        
        stats = manager.get_statistics()
        
        assert stats["total_traces"] == 2
        assert stats["total_gates"] == 3
        assert stats["traces_with_evidence"] == 1


class TestGates:
    """Test gate system."""
    
    def test_four_conditions_validation_success(self):
        """Test valid four conditions."""
        conditions = FourConditions(
            reality="text_stream",
            brain="processor_001",
            sensing="text",
            prior_knowledge={"lexicon_ids": ["SIGNIFIER:TEST"]}
        )
        
        is_valid, errors = conditions.validate()
        assert is_valid
        assert len(errors) == 0
    
    def test_four_conditions_validation_missing_reality(self):
        """Test four conditions fails without reality."""
        conditions = FourConditions(
            reality=None,
            brain="processor_001",
            sensing="text",
            prior_knowledge={"lexicon_ids": ["SIGNIFIER:TEST"]}
        )
        
        is_valid, errors = conditions.validate()
        assert not is_valid
        assert any("reality" in e.lower() for e in errors)
    
    def test_four_conditions_validation_missing_prior_knowledge(self):
        """Test four conditions fails without prior knowledge."""
        conditions = FourConditions(
            reality="text_stream",
            brain="processor_001",
            sensing="text",
            prior_knowledge={}
        )
        
        is_valid, errors = conditions.validate()
        assert not is_valid
        assert any("prior knowledge" in e.lower() for e in errors)
    
    def test_gate_creation(self):
        """Test gate creation."""
        conditions = FourConditions(
            reality="text_stream",
            brain="processor_001",
            sensing="text",
            prior_knowledge={"lexicon_ids": ["SIGNIFIER:TEST"]}
        )
        
        gate = Gate(
            gate_id="G_ATTEND:001",
            gate_type=GateType.G_ATTEND,
            conditions=conditions,
            input_data="test_input"
        )
        
        assert gate.gate_id == "G_ATTEND:001"
        assert gate.gate_type == GateType.G_ATTEND
        assert gate.input_data == "test_input"
        assert "kernel_version" in gate.metadata
    
    def test_gate_validation(self):
        """Test gate validation."""
        conditions = FourConditions(
            reality="text_stream",
            brain="processor_001",
            sensing="text",
            prior_knowledge={"lexicon_ids": ["SIGNIFIER:TEST"]}
        )
        
        gate = Gate(
            gate_id="G_ATTEND:001",
            gate_type=GateType.G_ATTEND,
            conditions=conditions,
            input_data="test_input"
        )
        
        is_valid, errors = gate.validate()
        assert is_valid
    
    def test_gate_execute(self):
        """Test gate execution."""
        conditions = FourConditions(
            reality="text_stream",
            brain="processor_001",
            sensing="text",
            prior_knowledge={"lexicon_ids": ["SIGNIFIER:TEST"]}
        )
        
        gate = Gate(
            gate_id="G_ATTEND:001",
            gate_type=GateType.G_ATTEND,
            conditions=conditions,
            input_data="input"
        )
        
        result = gate.execute(lambda x: x.upper())
        
        assert result == "INPUT"
        assert gate.output_data == "INPUT"
        assert gate.execution_time > 0
    
    def test_gate_to_dict(self):
        """Test gate serialization."""
        conditions = FourConditions(
            reality="text_stream",
            brain="processor_001",
            sensing="text",
            prior_knowledge={"lexicon_ids": ["SIGNIFIER:TEST"]}
        )
        
        gate = Gate(
            gate_id="G_ATTEND:001",
            gate_type=GateType.G_ATTEND,
            conditions=conditions,
            input_data="test"
        )
        
        gate_dict = gate.to_dict()
        
        assert gate_dict["gate_id"] == "G_ATTEND:001"
        assert gate_dict["gate_type"] == "G_ATTEND"
        assert "conditions" in gate_dict
        assert "metadata" in gate_dict


class TestGateRegistry:
    """Test gate registry system."""
    
    def test_create_gate_success(self):
        """Test creating gate via registry."""
        registry = gate_registry
        
        gate = registry.create_gate(
            gate_type=GateType.G_ATTEND,
            reality="text_stream",
            brain="processor_001",
            sensing="text",
            prior_knowledge={"lexicon_ids": ["SIGNIFIER:TEST"]},
            input_data="test"
        )
        
        assert gate.gate_id in registry.gates
        assert gate.gate_type == GateType.G_ATTEND
    
    def test_create_gate_fails_without_four_conditions(self):
        """Test gate creation fails without four conditions."""
        registry = gate_registry
        
        with pytest.raises(ValueError) as exc_info:
            registry.create_gate(
                gate_type=GateType.G_ATTEND,
                reality=None,
                brain="processor_001",
                sensing="text",
                prior_knowledge={},
                input_data="test"
            )
        
        assert "four conditions not satisfied" in str(exc_info.value).lower()
    
    def test_get_gate(self):
        """Test retrieving gate from registry."""
        registry = gate_registry
        
        gate = registry.create_gate(
            gate_type=GateType.G_ATTEND,
            reality="text_stream",
            brain="processor_001",
            sensing="text",
            prior_knowledge={"lexicon_ids": ["SIGNIFIER:TEST"]}
        )
        
        retrieved = registry.get_gate(gate.gate_id)
        assert retrieved is gate


class TestFormCodec:
    """Test FormCodec for reversible encoding."""
    
    def test_encode_decode_arabic(self):
        """Test encoding and decoding Arabic text."""
        codec = FormCodec()
        original = "السلام عليكم"
        
        encoded, checksum = codec.encode(original)
        decoded = codec.decode(encoded, checksum)
        
        assert decoded == original
        assert isinstance(encoded, list)
        assert isinstance(checksum, str)
    
    def test_encode_decode_with_diacritics(self):
        """Test encoding text with diacritics."""
        codec = FormCodec()
        original = "كِتَابٌ"
        
        encoded, checksum = codec.encode(original)
        decoded = codec.decode(encoded, checksum)
        
        assert decoded == original
    
    def test_checksum_verification(self):
        """Test checksum verification."""
        codec = FormCodec()
        original = "اختبار"
        
        encoded, checksum = codec.encode(original)
        
        # Should succeed with correct checksum
        decoded = codec.decode(encoded, checksum)
        assert decoded == original
        
        # Should fail with wrong checksum
        with pytest.raises(ValueError) as exc_info:
            codec.decode(encoded, "wrong_checksum")
        
        assert "checksum verification failed" in str(exc_info.value).lower()
    
    def test_verify_reversibility(self):
        """Test reversibility verification."""
        codec = FormCodec()
        
        assert codec.verify_reversibility("مرحبا")
        assert codec.verify_reversibility("Hello World")
        assert codec.verify_reversibility("Mixed نص")
    
    def test_batch_encode_decode(self):
        """Test batch encoding and decoding."""
        codec = FormCodec()
        texts = ["مرحبا", "السلام", "أهلا"]
        
        encoded_data = codec.batch_encode(texts)
        decoded_texts = codec.batch_decode(encoded_data)
        
        assert decoded_texts == texts
    
    def test_get_encoding_stats(self):
        """Test encoding statistics."""
        codec = FormCodec()
        text = "اختبار"
        
        stats = codec.get_encoding_stats(text)
        
        assert "original_length" in stats
        assert "encoded_length" in stats
        assert "checksum" in stats
        assert "compression_ratio" in stats
        assert stats["encoding"] == "utf-8"


class TestMeaningCodec:
    """Test MeaningCodec for C3 layer."""
    
    def test_encode_meaning_success(self):
        """Test encoding meaning with provenance."""
        codec = MeaningCodec()
        
        encoded = codec.encode_meaning(
            concept="كتاب",
            trace_id="C2:TRACE:abc123",
            prior_ids={"lexicon_ids": ["SIGNIFIED:KITAB:BOOK"]},
            provenance=[{"source_id": "CLASSICAL_CORPUS", "confidence": 1.0}]
        )
        
        assert encoded["concept"] == "كتاب"
        assert encoded["trace_id"] == "C2:TRACE:abc123"
        assert encoded["layer"] == "C3"
    
    def test_encode_meaning_no_trace(self):
        """Test encoding fails without trace (NO C3 without C2)."""
        codec = MeaningCodec()
        
        with pytest.raises(ValueError) as exc_info:
            codec.encode_meaning(
                concept="كتاب",
                trace_id="",
                prior_ids={"lexicon_ids": ["SIGNIFIED:KITAB:BOOK"]},
                provenance=[]
            )
        
        assert "no meaning without c2 trace" in str(exc_info.value).lower()
    
    def test_encode_meaning_no_prior_ids(self):
        """Test encoding fails without prior_ids (NO meaning without evidence)."""
        codec = MeaningCodec()
        
        with pytest.raises(ValueError) as exc_info:
            codec.encode_meaning(
                concept="كتاب",
                trace_id="C2:TRACE:abc123",
                prior_ids={},
                provenance=[]
            )
        
        assert "no meaning without prior_ids" in str(exc_info.value).lower()
    
    def test_decode_meaning(self):
        """Test decoding meaning."""
        codec = MeaningCodec()
        
        encoded = {
            "concept": "كتاب",
            "trace_id": "C2:TRACE:abc123",
            "prior_ids": {"lexicon_ids": ["SIGNIFIED:KITAB:BOOK"]},
            "provenance": []
        }
        
        concept, trace_id, prior_ids = codec.decode_meaning(encoded)
        
        assert concept == "كتاب"
        assert trace_id == "C2:TRACE:abc123"
        assert "lexicon_ids" in prior_ids
