"""
Reasoning Modes Module - Phase 5 of Fractal Consciousness Kernel

Implements four reasoning modes based on النبهاني's epistemology:
1. Deductive (استنتاجي): From general principles to specific conclusions
2. Inductive (استقرائي): From specific observations to general principles  
3. Abductive (استنباطي): Inference to best explanation
4. Inferential (استدلالي): General reasoning with evidence

All reasoning requires prior_ids (no reasoning without evidence).
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional, Callable
from enum import Enum


class ReasoningMode(Enum):
    """Four reasoning modes aligned with النبهاني's epistemology"""
    DEDUCTIVE = "deductive"          # استنتاجي: premise → conclusion
    INDUCTIVE = "inductive"          # استقرائي: observations → generalization
    ABDUCTIVE = "abductive"          # استنباطي: effect → best cause
    INFERENTIAL = "inferential"      # استدلالي: evidence → conclusion


class ReasoningStrength(Enum):
    """Epistemic strength of reasoning (aligned with YAQIN/ZANN/SHAKK)"""
    CERTAIN = 1.0      # يقين - deductive with sound premises
    PROBABLE = 0.7     # ظن - inductive/abductive with good evidence
    DOUBTFUL = 0.4     # شك - weak evidence or insufficient data


@dataclass
class Premise:
    """A premise in reasoning (requires provenance)"""
    premise_id: str
    content: Dict[str, Any]
    provenance: Dict[str, List[str]]  # lexicon_ids, ruleset_ids
    strength: float = 1.0
    
    def __post_init__(self):
        """Validate provenance exists"""
        if not self.provenance or not any(self.provenance.values()):
            raise ValueError(f"Premise {self.premise_id} requires provenance (prior_ids)")


@dataclass
class Conclusion:
    """A conclusion from reasoning"""
    conclusion_id: str
    content: Dict[str, Any]
    mode: ReasoningMode
    premises: List[str]  # premise_ids
    strength: ReasoningStrength
    derived_by: str  # gate_id that performed reasoning
    justification: str  # explanation of reasoning step


@dataclass
class ReasoningStep:
    """Single step in reasoning chain"""
    step_id: str
    mode: ReasoningMode
    inputs: List[str]  # premise_ids
    output: str  # conclusion_id
    rule_applied: Optional[str] = None  # rule_id if rule-based
    strength: ReasoningStrength = ReasoningStrength.PROBABLE
    meta: Dict[str, Any] = field(default_factory=dict)


class DeductiveReasoner:
    """
    Deductive reasoning (استنتاجي): From general to specific
    
    Pattern: If P then Q, P is true, therefore Q is true.
    Strength: CERTAIN if premises are sound, else PROBABLE
    
    Example:
        P1: All students write (general)
        P2: Ahmed is a student (specific instance)
        C:  Ahmed writes (conclusion)
    """
    
    def __init__(self):
        self.rules: Dict[str, Callable] = {}
    
    def add_rule(self, rule_id: str, rule_fn: Callable[[List[Premise]], Optional[Conclusion]]):
        """Add a deductive rule"""
        self.rules[rule_id] = rule_fn
    
    def apply(
        self, 
        premises: List[Premise], 
        rule_id: str,
        conclusion_id: str,
        derived_by: str
    ) -> Optional[Conclusion]:
        """Apply deductive rule to premises"""
        if rule_id not in self.rules:
            return None
        
        # Check all premises have CERTAIN strength for deduction
        all_certain = all(p.strength >= 1.0 for p in premises)
        strength = ReasoningStrength.CERTAIN if all_certain else ReasoningStrength.PROBABLE
        
        result = self.rules[rule_id](premises)
        if result is None:
            return None
        
        return Conclusion(
            conclusion_id=conclusion_id,
            content=result,
            mode=ReasoningMode.DEDUCTIVE,
            premises=[p.premise_id for p in premises],
            strength=strength,
            derived_by=derived_by,
            justification=f"Deductive rule {rule_id} applied to premises"
        )


class InductiveReasoner:
    """
    Inductive reasoning (استقرائي): From specific to general
    
    Pattern: Multiple observations → generalization
    Strength: PROBABLE (never CERTAIN in induction)
    
    Example:
        O1: Student1 wrote
        O2: Student2 wrote
        O3: Student3 wrote
        C:  All students write (generalization)
    """
    
    def __init__(self, min_observations: int = 3):
        self.min_observations = min_observations
    
    def generalize(
        self,
        observations: List[Premise],
        pattern_extractor: Callable[[List[Premise]], Dict[str, Any]],
        conclusion_id: str,
        derived_by: str
    ) -> Optional[Conclusion]:
        """Extract general pattern from observations"""
        if len(observations) < self.min_observations:
            return None
        
        # Extract pattern
        pattern = pattern_extractor(observations)
        if not pattern:
            return None
        
        # Induction never yields certainty
        # Strength depends on number of observations
        if len(observations) >= 10:
            strength = ReasoningStrength.PROBABLE
        else:
            strength = ReasoningStrength.DOUBTFUL
        
        return Conclusion(
            conclusion_id=conclusion_id,
            content=pattern,
            mode=ReasoningMode.INDUCTIVE,
            premises=[o.premise_id for o in observations],
            strength=strength,
            derived_by=derived_by,
            justification=f"Generalized from {len(observations)} observations"
        )


class AbductiveReasoner:
    """
    Abductive reasoning (استنباطي): Inference to best explanation
    
    Pattern: Effect observed → infer most likely cause
    Strength: PROBABLE (hypothesis selection)
    
    Example:
        Effect: Ground is wet
        Hypotheses: [rain, sprinkler, spill]
        Best: Rain (most likely explanation given context)
    """
    
    def __init__(self):
        self.hypotheses: Dict[str, Callable] = {}
    
    def add_hypothesis(self, hyp_id: str, scorer: Callable[[Premise, Dict], float]):
        """Add a hypothesis with scoring function"""
        self.hypotheses[hyp_id] = scorer
    
    def infer_best_explanation(
        self,
        effect: Premise,
        context: Dict[str, Any],
        conclusion_id: str,
        derived_by: str
    ) -> Optional[Conclusion]:
        """Find best explanation for observed effect"""
        if not self.hypotheses:
            return None
        
        # Score all hypotheses
        scores = {
            hyp_id: scorer(effect, context)
            for hyp_id, scorer in self.hypotheses.items()
        }
        
        # Select best
        best_hyp = max(scores, key=scores.get)
        best_score = scores[best_hyp]
        
        if best_score < 0.3:
            return None  # No good explanation
        
        strength = (
            ReasoningStrength.PROBABLE if best_score >= 0.7
            else ReasoningStrength.DOUBTFUL
        )
        
        return Conclusion(
            conclusion_id=conclusion_id,
            content={"hypothesis": best_hyp, "score": best_score, "context": context},
            mode=ReasoningMode.ABDUCTIVE,
            premises=[effect.premise_id],
            strength=strength,
            derived_by=derived_by,
            justification=f"Best explanation: {best_hyp} (score: {best_score:.2f})"
        )


class InferentialReasoner:
    """
    Inferential reasoning (استدلالي): General evidence-based reasoning
    
    Pattern: Evidence + knowledge → conclusion
    Strength: Depends on evidence quality and quantity
    
    This is the most general mode, combining aspects of all others.
    Aligned with النبهاني's emphasis on dalil (evidence).
    """
    
    def __init__(self):
        self.inference_rules: Dict[str, Callable] = {}
    
    def add_inference_rule(
        self, 
        rule_id: str, 
        rule_fn: Callable[[List[Premise], Dict], Optional[Dict[str, Any]]]
    ):
        """Add an inference rule"""
        self.inference_rules[rule_id] = rule_fn
    
    def infer(
        self,
        evidence: List[Premise],
        knowledge_base: Dict[str, Any],
        rule_id: str,
        conclusion_id: str,
        derived_by: str
    ) -> Optional[Conclusion]:
        """Make inference from evidence using knowledge base"""
        if rule_id not in self.inference_rules:
            return None
        
        result = self.inference_rules[rule_id](evidence, knowledge_base)
        if result is None:
            return None
        
        # Strength based on evidence quality
        avg_strength = sum(e.strength for e in evidence) / len(evidence) if evidence else 0.5
        
        if avg_strength >= 0.9:
            strength = ReasoningStrength.CERTAIN
        elif avg_strength >= 0.6:
            strength = ReasoningStrength.PROBABLE
        else:
            strength = ReasoningStrength.DOUBTFUL
        
        return Conclusion(
            conclusion_id=conclusion_id,
            content=result,
            mode=ReasoningMode.INFERENTIAL,
            premises=[e.premise_id for e in evidence],
            strength=strength,
            derived_by=derived_by,
            justification=f"Inferred using rule {rule_id} from {len(evidence)} evidence"
        )


@dataclass
class ReasoningEngine:
    """
    Unified reasoning engine combining all four modes
    
    Enforces النبهاني's principle: No reasoning without evidence (prior_ids)
    """
    
    deductive: DeductiveReasoner = field(default_factory=DeductiveReasoner)
    inductive: InductiveReasoner = field(default_factory=InductiveReasoner)
    abductive: AbductiveReasoner = field(default_factory=AbductiveReasoner)
    inferential: InferentialReasoner = field(default_factory=InferentialReasoner)
    
    # Store reasoning chain
    premises: Dict[str, Premise] = field(default_factory=dict)
    conclusions: Dict[str, Conclusion] = field(default_factory=dict)
    reasoning_chain: List[ReasoningStep] = field(default_factory=list)
    
    def add_premise(self, premise: Premise) -> str:
        """Add premise to knowledge base (must have provenance)"""
        self.premises[premise.premise_id] = premise
        return premise.premise_id
    
    def reason(
        self,
        mode: ReasoningMode,
        premise_ids: List[str],
        conclusion_id: str,
        derived_by: str,
        **kwargs
    ) -> Optional[Conclusion]:
        """
        Perform reasoning in specified mode
        
        All reasoning requires premises with provenance (prior_ids).
        Returns conclusion with epistemic strength.
        """
        # Validate all premises exist and have provenance
        premises = []
        for pid in premise_ids:
            if pid not in self.premises:
                raise ValueError(f"Premise {pid} not found")
            premises.append(self.premises[pid])
        
        # Route to appropriate reasoner
        conclusion = None
        
        if mode == ReasoningMode.DEDUCTIVE:
            rule_id = kwargs.get('rule_id')
            if not rule_id:
                raise ValueError("Deductive reasoning requires rule_id")
            conclusion = self.deductive.apply(premises, rule_id, conclusion_id, derived_by)
        
        elif mode == ReasoningMode.INDUCTIVE:
            pattern_extractor = kwargs.get('pattern_extractor')
            if not pattern_extractor:
                raise ValueError("Inductive reasoning requires pattern_extractor")
            conclusion = self.inductive.generalize(
                premises, pattern_extractor, conclusion_id, derived_by
            )
        
        elif mode == ReasoningMode.ABDUCTIVE:
            context = kwargs.get('context', {})
            if len(premises) != 1:
                raise ValueError("Abductive reasoning requires exactly one effect premise")
            conclusion = self.abductive.infer_best_explanation(
                premises[0], context, conclusion_id, derived_by
            )
        
        elif mode == ReasoningMode.INFERENTIAL:
            rule_id = kwargs.get('rule_id')
            knowledge_base = kwargs.get('knowledge_base', {})
            if not rule_id:
                raise ValueError("Inferential reasoning requires rule_id")
            conclusion = self.inferential.infer(
                premises, knowledge_base, rule_id, conclusion_id, derived_by
            )
        
        if conclusion:
            self.conclusions[conclusion_id] = conclusion
            
            # Record reasoning step
            step = ReasoningStep(
                step_id=f"STEP:{len(self.reasoning_chain)}",
                mode=mode,
                inputs=premise_ids,
                output=conclusion_id,
                rule_applied=kwargs.get('rule_id'),
                strength=conclusion.strength,
                meta=kwargs
            )
            self.reasoning_chain.append(step)
        
        return conclusion
    
    def get_reasoning_trace(self) -> List[Dict[str, Any]]:
        """Get full reasoning chain as list of dicts"""
        return [
            {
                'step_id': step.step_id,
                'mode': step.mode.value,
                'inputs': step.inputs,
                'output': step.output,
                'rule': step.rule_applied,
                'strength': step.strength.value,
                'meta': step.meta
            }
            for step in self.reasoning_chain
        ]
    
    def export_conclusions(self) -> Dict[str, Dict[str, Any]]:
        """Export all conclusions with full details"""
        return {
            cid: {
                'content': c.content,
                'mode': c.mode.value,
                'premises': c.premises,
                'strength': c.strength.value,
                'derived_by': c.derived_by,
                'justification': c.justification
            }
            for cid, c in self.conclusions.items()
        }


# Default reasoners with common Arabic linguistic rules
def create_arabic_reasoning_engine() -> ReasoningEngine:
    """
    Create reasoning engine with Arabic linguistic rules
    """
    engine = ReasoningEngine()
    
    # Example deductive rule: مسند + مسند إليه → جملة
    def predicate_rule(premises: List[Premise]) -> Optional[Dict[str, Any]]:
        if len(premises) < 2:
            return None
        
        musnad = next((p for p in premises if p.content.get('type') == 'musnad'), None)
        musnad_elayh = next((p for p in premises if p.content.get('type') == 'musnad_elayh'), None)
        
        if musnad and musnad_elayh:
            return {
                'sentence_type': 'ismiyya' if musnad_elayh.content.get('pos') == 'noun' else 'fi3liyya',
                'musnad': musnad.content,
                'musnad_elayh': musnad_elayh.content
            }
        return None
    
    engine.deductive.add_rule("RULE:PREDICATION", predicate_rule)
    
    # Example inferential rule: verb + subject → event
    def event_inference(evidence: List[Premise], kb: Dict) -> Optional[Dict[str, Any]]:
        verb = next((e for e in evidence if e.content.get('pos') == 'verb'), None)
        subject = next((e for e in evidence if e.content.get('role') == 'subject'), None)
        
        if verb and subject:
            return {
                'event_type': verb.content.get('lemma'),
                'agent': subject.content.get('text'),
                'tense': verb.content.get('tense', 'past')
            }
        return None
    
    engine.inferential.add_inference_rule("RULE:EVENT_EXTRACTION", event_inference)
    
    return engine


__all__ = [
    'ReasoningMode',
    'ReasoningStrength',
    'Premise',
    'Conclusion',
    'ReasoningStep',
    'DeductiveReasoner',
    'InductiveReasoner',
    'AbductiveReasoner',
    'InferentialReasoner',
    'ReasoningEngine',
    'create_arabic_reasoning_engine'
]
