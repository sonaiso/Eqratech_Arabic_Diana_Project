"""
Tests for Reasoning Modes Module (Phase 5)

Tests all four reasoning modes: deductive, inductive, abductive, inferential
"""

import pytest
from fractalhub.kernel.reasoning import (
    ReasoningMode,
    ReasoningStrength,
    Premise,
    Conclusion,
    ReasoningStep,
    DeductiveReasoner,
    InductiveReasoner,
    AbductiveReasoner,
    InferentialReasoner,
    ReasoningEngine,
    create_arabic_reasoning_engine
)


class TestPremise:
    """Tests for Premise class"""
    
    def test_create_premise_with_provenance(self):
        """Test creating premise with provenance"""
        premise = Premise(
            premise_id="P:001",
            content={"statement": "All students write"},
            provenance={"lexicon_ids": ["LEX:001"], "ruleset_ids": []},
            strength=1.0
        )
        assert premise.premise_id == "P:001"
        assert premise.strength == 1.0
    
    def test_premise_requires_provenance(self):
        """Test that premise without provenance raises error"""
        with pytest.raises(ValueError, match="requires provenance"):
            Premise(
                premise_id="P:002",
                content={"statement": "Invalid"},
                provenance={},
                strength=1.0
            )
    
    def test_premise_with_empty_provenance_lists(self):
        """Test premise with empty provenance lists fails"""
        with pytest.raises(ValueError, match="requires provenance"):
            Premise(
                premise_id="P:003",
                content={"statement": "Invalid"},
                provenance={"lexicon_ids": [], "ruleset_ids": []},
                strength=1.0
            )


class TestDeductiveReasoner:
    """Tests for deductive reasoning (استنتاجي)"""
    
    def test_create_deductive_reasoner(self):
        """Test creating deductive reasoner"""
        reasoner = DeductiveReasoner()
        assert len(reasoner.rules) == 0
    
    def test_add_deductive_rule(self):
        """Test adding deductive rule"""
        reasoner = DeductiveReasoner()
        
        def modus_ponens(premises):
            if len(premises) >= 2:
                return {"conclusion": "Q is true"}
            return None
        
        reasoner.add_rule("MODUS_PONENS", modus_ponens)
        assert "MODUS_PONENS" in reasoner.rules
    
    def test_apply_deductive_rule(self):
        """Test applying deductive rule"""
        reasoner = DeductiveReasoner()
        
        def simple_rule(premises):
            return {"result": "derived"}
        
        reasoner.add_rule("SIMPLE", simple_rule)
        
        p1 = Premise("P:1", {"a": 1}, {"lexicon_ids": ["L1"]}, 1.0)
        p2 = Premise("P:2", {"b": 2}, {"lexicon_ids": ["L2"]}, 1.0)
        
        conclusion = reasoner.apply([p1, p2], "SIMPLE", "C:1", "G:DEDUCE")
        
        assert conclusion is not None
        assert conclusion.mode == ReasoningMode.DEDUCTIVE
        assert conclusion.strength == ReasoningStrength.CERTAIN
        assert len(conclusion.premises) == 2
    
    def test_deductive_with_uncertain_premise(self):
        """Test deduction with uncertain premise reduces strength"""
        reasoner = DeductiveReasoner()
        
        def simple_rule(premises):
            return {"result": "derived"}
        
        reasoner.add_rule("SIMPLE", simple_rule)
        
        p1 = Premise("P:1", {"a": 1}, {"lexicon_ids": ["L1"]}, 1.0)
        p2 = Premise("P:2", {"b": 2}, {"lexicon_ids": ["L2"]}, 0.7)  # uncertain
        
        conclusion = reasoner.apply([p1, p2], "SIMPLE", "C:1", "G:DEDUCE")
        
        assert conclusion.strength == ReasoningStrength.PROBABLE  # reduced


class TestInductiveReasoner:
    """Tests for inductive reasoning (استقرائي)"""
    
    def test_create_inductive_reasoner(self):
        """Test creating inductive reasoner"""
        reasoner = InductiveReasoner(min_observations=3)
        assert reasoner.min_observations == 3
    
    def test_generalize_from_observations(self):
        """Test generalizing pattern from observations"""
        reasoner = InductiveReasoner(min_observations=2)
        
        obs1 = Premise("O:1", {"student": "Ahmad", "action": "wrote"}, {"lexicon_ids": ["L1"]})
        obs2 = Premise("O:2", {"student": "Fatima", "action": "wrote"}, {"lexicon_ids": ["L2"]})
        obs3 = Premise("O:3", {"student": "Omar", "action": "wrote"}, {"lexicon_ids": ["L3"]})
        
        def extract_pattern(observations):
            actions = [o.content.get("action") for o in observations]
            if all(a == "wrote" for a in actions):
                return {"generalization": "All students write"}
            return None
        
        conclusion = reasoner.generalize(
            [obs1, obs2, obs3], 
            extract_pattern, 
            "C:GEN", 
            "G:INDUCE"
        )
        
        assert conclusion is not None
        assert conclusion.mode == ReasoningMode.INDUCTIVE
        assert conclusion.strength == ReasoningStrength.DOUBTFUL  # < 10 observations
        assert len(conclusion.premises) == 3
    
    def test_insufficient_observations(self):
        """Test that insufficient observations returns None"""
        reasoner = InductiveReasoner(min_observations=5)
        
        obs1 = Premise("O:1", {"data": 1}, {"lexicon_ids": ["L1"]})
        obs2 = Premise("O:2", {"data": 2}, {"lexicon_ids": ["L2"]})
        
        def extract_pattern(observations):
            return {"pattern": "test"}
        
        conclusion = reasoner.generalize([obs1, obs2], extract_pattern, "C:1", "G:1")
        assert conclusion is None
    
    def test_many_observations_increases_strength(self):
        """Test that many observations increase strength"""
        reasoner = InductiveReasoner(min_observations=2)
        
        observations = [
            Premise(f"O:{i}", {"val": i}, {"lexicon_ids": [f"L{i}"]})
            for i in range(15)
        ]
        
        def extract_pattern(obs):
            return {"pattern": "all positive"}
        
        conclusion = reasoner.generalize(observations, extract_pattern, "C:1", "G:1")
        
        assert conclusion.strength == ReasoningStrength.PROBABLE  # >= 10


class TestAbductiveReasoner:
    """Tests for abductive reasoning (استنباطي)"""
    
    def test_create_abductive_reasoner(self):
        """Test creating abductive reasoner"""
        reasoner = AbductiveReasoner()
        assert len(reasoner.hypotheses) == 0
    
    def test_add_hypothesis(self):
        """Test adding hypothesis with scorer"""
        reasoner = AbductiveReasoner()
        
        def rain_scorer(effect, context):
            if effect.content.get("observation") == "wet ground":
                return 0.8
            return 0.1
        
        reasoner.add_hypothesis("RAIN", rain_scorer)
        assert "RAIN" in reasoner.hypotheses
    
    def test_infer_best_explanation(self):
        """Test inferring best explanation"""
        reasoner = AbductiveReasoner()
        
        def rain_scorer(effect, context):
            if "clouds" in context:
                return 0.9
            return 0.3
        
        def sprinkler_scorer(effect, context):
            if "timer" in context:
                return 0.7
            return 0.2
        
        reasoner.add_hypothesis("RAIN", rain_scorer)
        reasoner.add_hypothesis("SPRINKLER", sprinkler_scorer)
        
        effect = Premise("E:1", {"observation": "wet ground"}, {"lexicon_ids": ["L1"]})
        context = {"clouds": True, "time": "morning"}
        
        conclusion = reasoner.infer_best_explanation(effect, context, "C:1", "G:ABDUCE")
        
        assert conclusion is not None
        assert conclusion.mode == ReasoningMode.ABDUCTIVE
        assert conclusion.content["hypothesis"] == "RAIN"
        assert conclusion.strength == ReasoningStrength.PROBABLE
    
    def test_no_good_explanation(self):
        """Test that low scores return None"""
        reasoner = AbductiveReasoner()
        
        def weak_scorer(effect, context):
            return 0.1  # very weak
        
        reasoner.add_hypothesis("WEAK", weak_scorer)
        
        effect = Premise("E:1", {"data": 1}, {"lexicon_ids": ["L1"]})
        conclusion = reasoner.infer_best_explanation(effect, {}, "C:1", "G:1")
        
        assert conclusion is None


class TestInferentialReasoner:
    """Tests for inferential reasoning (استدلالي)"""
    
    def test_create_inferential_reasoner(self):
        """Test creating inferential reasoner"""
        reasoner = InferentialReasoner()
        assert len(reasoner.inference_rules) == 0
    
    def test_add_inference_rule(self):
        """Test adding inference rule"""
        reasoner = InferentialReasoner()
        
        def simple_inference(evidence, kb):
            return {"inferred": True}
        
        reasoner.add_inference_rule("SIMPLE", simple_inference)
        assert "SIMPLE" in reasoner.inference_rules
    
    def test_make_inference(self):
        """Test making inference from evidence"""
        reasoner = InferentialReasoner()
        
        def combine_evidence(evidence, kb):
            if len(evidence) >= 2:
                return {"combined": [e.content for e in evidence]}
            return None
        
        reasoner.add_inference_rule("COMBINE", combine_evidence)
        
        e1 = Premise("E:1", {"fact": "A"}, {"lexicon_ids": ["L1"]}, 0.9)
        e2 = Premise("E:2", {"fact": "B"}, {"lexicon_ids": ["L2"]}, 0.8)
        
        conclusion = reasoner.infer([e1, e2], {}, "COMBINE", "C:1", "G:INFER")
        
        assert conclusion is not None
        assert conclusion.mode == ReasoningMode.INFERENTIAL
        assert conclusion.strength == ReasoningStrength.PROBABLE  # avg >= 0.6
    
    def test_inference_strength_varies_with_evidence(self):
        """Test that inference strength depends on evidence quality"""
        reasoner = InferentialReasoner()
        
        def simple_inference(evidence, kb):
            return {"result": "inferred"}
        
        reasoner.add_inference_rule("SIMPLE", simple_inference)
        
        # Strong evidence
        strong_evidence = [
            Premise("E:1", {"data": 1}, {"lexicon_ids": ["L1"]}, 1.0),
            Premise("E:2", {"data": 2}, {"lexicon_ids": ["L2"]}, 0.9)
        ]
        conclusion = reasoner.infer(strong_evidence, {}, "SIMPLE", "C:1", "G:1")
        assert conclusion.strength == ReasoningStrength.CERTAIN
        
        # Weak evidence
        weak_evidence = [
            Premise("E:3", {"data": 3}, {"lexicon_ids": ["L3"]}, 0.4),
            Premise("E:4", {"data": 4}, {"lexicon_ids": ["L4"]}, 0.3)
        ]
        conclusion = reasoner.infer(weak_evidence, {}, "SIMPLE", "C:2", "G:2")
        assert conclusion.strength == ReasoningStrength.DOUBTFUL


class TestReasoningEngine:
    """Tests for unified reasoning engine"""
    
    def test_create_reasoning_engine(self):
        """Test creating reasoning engine"""
        engine = ReasoningEngine()
        assert engine.deductive is not None
        assert engine.inductive is not None
        assert engine.abductive is not None
        assert engine.inferential is not None
    
    def test_add_premise(self):
        """Test adding premise to engine"""
        engine = ReasoningEngine()
        premise = Premise("P:1", {"data": 1}, {"lexicon_ids": ["L1"]})
        
        pid = engine.add_premise(premise)
        assert pid == "P:1"
        assert "P:1" in engine.premises
    
    def test_reason_deductive(self):
        """Test deductive reasoning through engine"""
        engine = ReasoningEngine()
        
        # Add rule
        def simple_rule(premises):
            return {"deduced": True}
        engine.deductive.add_rule("RULE:1", simple_rule)
        
        # Add premises
        p1 = Premise("P:1", {"a": 1}, {"lexicon_ids": ["L1"]}, 1.0)
        p2 = Premise("P:2", {"b": 2}, {"lexicon_ids": ["L2"]}, 1.0)
        engine.add_premise(p1)
        engine.add_premise(p2)
        
        # Reason
        conclusion = engine.reason(
            ReasoningMode.DEDUCTIVE,
            ["P:1", "P:2"],
            "C:1",
            "G:DEDUCE",
            rule_id="RULE:1"
        )
        
        assert conclusion is not None
        assert "C:1" in engine.conclusions
        assert len(engine.reasoning_chain) == 1
    
    def test_reason_inductive(self):
        """Test inductive reasoning through engine"""
        engine = ReasoningEngine()
        
        # Add observations
        for i in range(5):
            p = Premise(f"O:{i}", {"value": i}, {"lexicon_ids": [f"L{i}"]})
            engine.add_premise(p)
        
        def pattern_extractor(obs):
            return {"pattern": "increasing"}
        
        conclusion = engine.reason(
            ReasoningMode.INDUCTIVE,
            [f"O:{i}" for i in range(5)],
            "C:GEN",
            "G:INDUCE",
            pattern_extractor=pattern_extractor
        )
        
        assert conclusion is not None
        assert conclusion.mode == ReasoningMode.INDUCTIVE
    
    def test_reason_abductive(self):
        """Test abductive reasoning through engine"""
        engine = ReasoningEngine()
        
        # Add hypothesis
        def hyp_scorer(effect, context):
            return 0.8
        engine.abductive.add_hypothesis("HYP:1", hyp_scorer)
        
        # Add effect
        effect = Premise("E:1", {"effect": "observed"}, {"lexicon_ids": ["L1"]})
        engine.add_premise(effect)
        
        conclusion = engine.reason(
            ReasoningMode.ABDUCTIVE,
            ["E:1"],
            "C:CAUSE",
            "G:ABDUCE",
            context={"info": "relevant"}
        )
        
        assert conclusion is not None
        assert conclusion.mode == ReasoningMode.ABDUCTIVE
    
    def test_reason_inferential(self):
        """Test inferential reasoning through engine"""
        engine = ReasoningEngine()
        
        # Add rule
        def inference_rule(evidence, kb):
            return {"inferred": "value"}
        engine.inferential.add_inference_rule("RULE:INF", inference_rule)
        
        # Add evidence
        e1 = Premise("E:1", {"evidence": 1}, {"lexicon_ids": ["L1"]}, 0.9)
        engine.add_premise(e1)
        
        conclusion = engine.reason(
            ReasoningMode.INFERENTIAL,
            ["E:1"],
            "C:INF",
            "G:INFER",
            rule_id="RULE:INF",
            knowledge_base={}
        )
        
        assert conclusion is not None
        assert conclusion.mode == ReasoningMode.INFERENTIAL
    
    def test_missing_premise_raises_error(self):
        """Test that missing premise raises error"""
        engine = ReasoningEngine()
        
        with pytest.raises(ValueError, match="not found"):
            engine.reason(
                ReasoningMode.DEDUCTIVE,
                ["P:MISSING"],
                "C:1",
                "G:1",
                rule_id="RULE:1"
            )
    
    def test_get_reasoning_trace(self):
        """Test getting reasoning trace"""
        engine = ReasoningEngine()
        
        # Set up and perform reasoning
        def simple_rule(premises):
            return {"result": "ok"}
        engine.deductive.add_rule("R:1", simple_rule)
        
        p = Premise("P:1", {"data": 1}, {"lexicon_ids": ["L1"]}, 1.0)
        engine.add_premise(p)
        
        engine.reason(ReasoningMode.DEDUCTIVE, ["P:1"], "C:1", "G:1", rule_id="R:1")
        
        trace = engine.get_reasoning_trace()
        assert len(trace) == 1
        assert trace[0]['mode'] == 'deductive'
        assert trace[0]['output'] == 'C:1'
    
    def test_export_conclusions(self):
        """Test exporting conclusions"""
        engine = ReasoningEngine()
        
        def simple_rule(premises):
            return {"result": "exported"}
        engine.deductive.add_rule("R:1", simple_rule)
        
        p = Premise("P:1", {"data": 1}, {"lexicon_ids": ["L1"]}, 1.0)
        engine.add_premise(p)
        
        engine.reason(ReasoningMode.DEDUCTIVE, ["P:1"], "C:1", "G:1", rule_id="R:1")
        
        conclusions = engine.export_conclusions()
        assert "C:1" in conclusions
        assert conclusions["C:1"]["mode"] == "deductive"
        assert "justification" in conclusions["C:1"]


class TestArabicReasoningEngine:
    """Tests for Arabic linguistic reasoning engine"""
    
    def test_create_arabic_engine(self):
        """Test creating Arabic reasoning engine"""
        engine = create_arabic_reasoning_engine()
        
        assert engine is not None
        assert "RULE:PREDICATION" in engine.deductive.rules
        assert "RULE:EVENT_EXTRACTION" in engine.inferential.inference_rules
    
    def test_arabic_predicate_rule(self):
        """Test Arabic predication rule"""
        engine = create_arabic_reasoning_engine()
        
        # مسند (predicate)
        musnad = Premise(
            "P:MUSNAD",
            {"type": "musnad", "text": "كاتب", "pos": "noun"},
            {"lexicon_ids": ["LEX:KATIB"]}
        )
        
        # مسند إليه (subject)
        musnad_elayh = Premise(
            "P:MUSNAD_ELAYH",
            {"type": "musnad_elayh", "text": "الطالب", "pos": "noun"},
            {"lexicon_ids": ["LEX:TALIB"]}
        )
        
        engine.add_premise(musnad)
        engine.add_premise(musnad_elayh)
        
        conclusion = engine.reason(
            ReasoningMode.DEDUCTIVE,
            ["P:MUSNAD", "P:MUSNAD_ELAYH"],
            "C:SENTENCE",
            "G:PREDICATE",
            rule_id="RULE:PREDICATION"
        )
        
        assert conclusion is not None
        assert conclusion.content["sentence_type"] == "ismiyya"
    
    def test_arabic_event_extraction(self):
        """Test Arabic event extraction rule"""
        engine = create_arabic_reasoning_engine()
        
        verb = Premise(
            "E:VERB",
            {"pos": "verb", "lemma": "كتب", "tense": "past"},
            {"lexicon_ids": ["LEX:KATABA"]}
        )
        
        subject = Premise(
            "E:SUBJ",
            {"role": "subject", "text": "الطالب"},
            {"lexicon_ids": ["LEX:TALIB"]}
        )
        
        engine.add_premise(verb)
        engine.add_premise(subject)
        
        conclusion = engine.reason(
            ReasoningMode.INFERENTIAL,
            ["E:VERB", "E:SUBJ"],
            "C:EVENT",
            "G:EXTRACT",
            rule_id="RULE:EVENT_EXTRACTION",
            knowledge_base={}
        )
        
        assert conclusion is not None
        assert conclusion.content["event_type"] == "كتب"
        assert conclusion.content["agent"] == "الطالب"
        assert conclusion.content["tense"] == "past"


class TestReasoningIntegration:
    """Integration tests for reasoning system"""
    
    def test_multi_step_reasoning(self):
        """Test multi-step reasoning chain"""
        engine = ReasoningEngine()
        
        # Step 1: Deduction
        def rule1(premises):
            return {"intermediate": "value"}
        engine.deductive.add_rule("R:1", rule1)
        
        p1 = Premise("P:1", {"input": 1}, {"lexicon_ids": ["L1"]}, 1.0)
        engine.add_premise(p1)
        
        c1 = engine.reason(ReasoningMode.DEDUCTIVE, ["P:1"], "C:1", "G:1", rule_id="R:1")
        assert c1 is not None
        
        # Step 2: Use conclusion as premise
        p2 = Premise("P:C1", c1.content, {"lexicon_ids": ["L2"]}, c1.strength.value)
        engine.add_premise(p2)
        
        def rule2(evidence, kb):
            return {"final": "result"}
        engine.inferential.add_inference_rule("R:2", rule2)
        
        c2 = engine.reason(
            ReasoningMode.INFERENTIAL, 
            ["P:C1"], 
            "C:2", 
            "G:2", 
            rule_id="R:2",
            knowledge_base={}
        )
        
        assert c2 is not None
        assert len(engine.reasoning_chain) == 2
    
    def test_combined_modes(self):
        """Test using multiple reasoning modes together"""
        engine = ReasoningEngine()
        
        # Collect observations (inductive)
        observations = []
        for i in range(5):
            p = Premise(f"O:{i}", {"observation": i}, {"lexicon_ids": [f"L{i}"]})
            engine.add_premise(p)
            observations.append(f"O:{i}")
        
        def extract_pattern(obs):
            return {"pattern": "sequence"}
        
        general = engine.reason(
            ReasoningMode.INDUCTIVE,
            observations,
            "C:GENERAL",
            "G:IND",
            pattern_extractor=extract_pattern
        )
        
        assert general is not None
        
        # Use generalization for deduction
        p_gen = Premise(
            "P:GEN", 
            general.content, 
            {"lexicon_ids": ["L_GEN"]},
            general.strength.value
        )
        engine.add_premise(p_gen)
        
        def apply_general(premises):
            return {"specific_case": "derived"}
        engine.deductive.add_rule("R:APPLY", apply_general)
        
        specific = engine.reason(
            ReasoningMode.DEDUCTIVE,
            ["P:GEN"],
            "C:SPECIFIC",
            "G:DED",
            rule_id="R:APPLY"
        )
        
        assert specific is not None
        assert len(engine.reasoning_chain) == 2


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
