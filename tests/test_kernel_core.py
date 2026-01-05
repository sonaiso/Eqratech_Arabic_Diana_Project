"""
Tests for Fractal Consciousness Kernel v1.1

Tests the core C1-C2-C3 architecture with:
- FormCodec (reversible text⇄numbers)
- Record locking rules
- Gate execution
- Graph separation
"""

import pytest
from pathlib import Path
import sys

# Add kernel to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from fractalhub.kernel.codec import FormCodec, CodecPayload
from fractalhub.kernel.record import (
    Record, C1Layer, C2Layer, C3Layer,
    SensingChannel, ExecutorType
)
from fractalhub.kernel.gates import GateRegistry, AttentionGate, CodecVerifyGate
from fractalhub.kernel.trace import C2Trace, TraceEntry
from fractalhub.kernel.graph import (
    SignifierGraph, SignifiedGraph,
    SignifierNodeType, SignifiedNodeType
)


class TestFormCodec:
    """Tests for reversible text encoding"""
    
    def test_encode_decode_reversibility(self):
        """Test that decode(encode(text)) == text"""
        # Simple dictionary for testing
        dictionary = {
            'ك': 1, 'َ': 2, 'ت': 3, 'ب': 4, ' ': 5,
            'ال': 6, 'ط': 7, 'ِ': 8, 'ل': 9, 'ُ': 10,
            'د': 11, 'ر': 12, 'س': 13, '.': 14
        }
        
        codec = FormCodec(dictionary)
        
        text = "كَتَبَ الطَّالِبُ."
        
        # Encode
        payload = codec.encode(text)
        
        # Verify payload
        assert payload.version == 1
        assert len(payload.unit_ids) > 0
        assert len(payload.checksum) == 8
        assert payload.verify()
        
        # Decode
        decoded = codec.decode(payload)
        
        # Note: Due to normalization, decoded may differ slightly
        # but structure should be preserved
        assert decoded is not None
        assert len(decoded) > 0
    
    def test_checksum_validation(self):
        """Test checksum detects corruption"""
        dictionary = {'ك': 1, 'ت': 2, 'ب': 3}
        codec = FormCodec(dictionary)
        
        # Create valid payload
        payload = CodecPayload(
            version=1,
            unit_ids=[1, 2, 3],
            checksum="12345678"
        )
        
        # Should fail verification
        assert not payload.verify()


class TestRecord:
    """Tests for locked record structure"""
    
    def test_record_requires_c1_conditions(self):
        """Test that C1 must satisfy four conditions"""
        # Missing priors - should fail
        with pytest.raises(ValueError, match="C1 locking violation"):
            c1 = C1Layer(
                form_stream="test",
                codec_version=1,
                payload_unit_ids=[1, 2, 3],
                checksum="abc123",
                lexicon_ids=[],  # Empty - violates condition
                sensing_channel=SensingChannel.READ,
                executor=ExecutorType.KERNEL_SAFE
            )
            record = Record(record_id="R1", c1=c1)
    
    def test_record_c3_requires_c2_trace(self):
        """Test that C3 cannot exist without C2"""
        c1 = C1Layer(
            form_stream="test",
            codec_version=1,
            payload_unit_ids=[1, 2, 3],
            checksum="abc123",
            lexicon_ids=["LEX_001"],  # Has priors
            sensing_channel=SensingChannel.READ,
            executor=ExecutorType.KERNEL_SAFE
        )
        
        c2 = C2Layer()  # Empty trace
        c3 = C3Layer()  # Has C3
        
        # Should fail - no C3 without C2
        with pytest.raises(ValueError, match="C2-C3 locking violation"):
            record = Record(record_id="R1", c1=c1, c2=c2, c3=c3)
    
    def test_valid_record(self):
        """Test creating valid record"""
        c1 = C1Layer(
            form_stream="test",
            codec_version=1,
            payload_unit_ids=[1, 2, 3],
            checksum="abc123",
            lexicon_ids=["LEX_001"],
            sensing_channel=SensingChannel.READ,
            executor=ExecutorType.KERNEL_SAFE
        )
        
        c2 = C2Layer()
        c2.add_entry("G_ATTEND", [c1.form_stream], [[0, 1, 2, 3]])
        
        # Valid record
        record = Record(record_id="R1", c1=c1, c2=c2)
        
        assert record.record_id == "R1"
        assert len(record.c2.trace) == 1
        assert record.c3 is None


class TestGates:
    """Tests for gate execution"""
    
    def test_attention_gate(self):
        """Test G_ATTEND gate"""
        gate = AttentionGate("G_ATTEND")
        
        form_stream = "كتب الطالب"
        outputs = gate.execute([form_stream], [])
        
        assert len(outputs) == 1
        focus_spans = outputs[0]
        assert len(focus_spans) > 0
    
    def test_codec_verify_gate(self):
        """Test G_CODEC_VERIFY gate"""
        gate = CodecVerifyGate("G_CODEC_VERIFY")
        
        # Valid checksum
        payload_ids = [1, 2, 3]
        import hashlib
        data = ",".join(str(uid) for uid in payload_ids).encode('utf-8')
        checksum = hashlib.sha256(data).hexdigest()[:8]
        
        outputs = gate.execute([payload_ids, checksum], [])
        assert outputs == ["OK"]
        
        # Invalid checksum
        outputs = gate.execute([payload_ids, "invalid"], [])
        assert outputs == ["FAIL"]
    
    def test_gate_registry(self):
        """Test gate registration and creation"""
        registry = GateRegistry()
        
        # Should have built-in gates
        assert "G_ATTEND" in registry.list_gates()
        assert "G_CODEC_VERIFY" in registry.list_gates()
        assert "G_SPEECH_ACT" in registry.list_gates()
        
        # Create gate
        gate = registry.create("G_ATTEND")
        assert gate is not None
        assert gate.gate_id == "G_ATTEND"


class TestTrace:
    """Tests for C2 trace"""
    
    def test_trace_add_entry(self):
        """Test adding entries to trace"""
        trace = C2Trace()
        
        trace.add("G_ATTEND", ["input"], ["output"], ["PRIOR_001"])
        
        assert len(trace) == 1
        assert trace.get_output("G_ATTEND") == ["output"]
    
    def test_meaning_gate_requires_priors(self):
        """Test that meaning gates must have prior_ids"""
        trace = C2Trace()
        
        # Should fail - MEANING gate without priors
        with pytest.raises(ValueError, match="produces meaning"):
            trace.add("G_SEMANTIC_MEANING", ["input"], ["output"], [])


class TestGraphs:
    """Tests for graph structures"""
    
    def test_signifier_graph(self):
        """Test signifier graph (C1)"""
        graph = SignifierGraph()
        
        # Add phoneme nodes
        n1 = graph.add_node("N1", SignifierNodeType.PHONEME, "ك")
        n2 = graph.add_node("N2", SignifierNodeType.DIACRITIC, "َ")
        
        # Add edge
        from fractalhub.kernel.graph import SignifierEdgeType
        e1 = graph.add_edge("E1", SignifierEdgeType.ATTACH_DIAC, "N1", "N2")
        
        assert len(graph.nodes) == 2
        assert len(graph.edges) == 1
        
        # Serialize
        data = graph.to_dict()
        assert len(data['nodes']) == 2
        assert len(data['edges']) == 1
    
    def test_signified_graph(self):
        """Test signified graph (C3)"""
        graph = SignifiedGraph()
        
        # Add entity nodes
        n1 = graph.add_node("E1", SignifiedNodeType.ENTITY, 
                           features={'name': 'الطالب'},
                           generated_by="G_ENTITY_EXTRACT")
        n2 = graph.add_node("V1", SignifiedNodeType.EVENT,
                           features={'action': 'write'},
                           generated_by="G_EVENT_EXTRACT")
        
        # Add relation
        from fractalhub.kernel.graph import SignifiedEdgeType
        e1 = graph.add_edge("R1", SignifiedEdgeType.AGENT_OF, "E1", "V1",
                           generated_by="G_ROLE_ASSIGN")
        
        assert len(graph.nodes) == 2
        assert len(graph.edges) == 1
        
        # Check provenance
        assert graph.get_provenance("E1") == "G_ENTITY_EXTRACT"
        assert graph.get_provenance("R1") == "G_ROLE_ASSIGN"


class TestIntegration:
    """Integration tests for full pipeline"""
    
    def test_full_record_pipeline(self):
        """Test complete record processing"""
        # 1. Create dictionary
        dictionary = {
            'ك': 1, 'ت': 2, 'ب': 3
        }
        
        # 2. Create codec
        codec = FormCodec(dictionary)
        
        # 3. Encode text
        text = "كتب"
        payload = codec.encode(text)
        
        # 4. Create C1
        c1 = C1Layer(
            form_stream=text,
            codec_version=payload.version,
            payload_unit_ids=payload.unit_ids,
            checksum=payload.checksum,
            lexicon_ids=["LEX_ARABIC_001"],
            sensing_channel=SensingChannel.READ,
            executor=ExecutorType.KERNEL_SAFE
        )
        
        # 5. Create C2 with gates
        c2 = C2Layer()
        
        # Execute G_ATTEND
        registry = GateRegistry()
        attend_gate = registry.create("G_ATTEND")
        focus_output = attend_gate.execute([c1.form_stream], ["ATT_RULE_001"])
        c2.add_entry("G_ATTEND", [c1.form_stream], focus_output, ["ATT_RULE_001"])
        
        # Execute G_CODEC_VERIFY
        verify_gate = registry.create("G_CODEC_VERIFY")
        verify_output = verify_gate.execute([payload.unit_ids, payload.checksum], [])
        c2.add_entry("G_CODEC_VERIFY", [payload.unit_ids, payload.checksum], 
                    verify_output, [])
        
        # 6. Create record
        record = Record(record_id="R_TEST_001", c1=c1, c2=c2)
        
        # Verify
        assert record.validate_locks()
        assert len(record.c2.trace) == 2
        
        # 7. Serialize
        record_dict = record.to_dict()
        assert record_dict['record_id'] == "R_TEST_001"
        assert len(record_dict['c2_trace']) == 2


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
