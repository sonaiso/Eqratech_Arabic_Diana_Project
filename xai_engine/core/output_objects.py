"""
Output Objects - Data structures produced by each layer

These objects form the pipeline output and enable full traceability.
"""

from dataclasses import dataclass, field
from typing import Dict, List, Any, Optional
from datetime import datetime
from enum import Enum


class EpistemicLevel(Enum):
    """Epistemic confidence levels (معرفة، ظن، شك)"""
    YAQIN = "certainty"  # يقين - 1.0
    ZANN = "probability"  # ظن - 0.7
    SHAKK = "doubt"  # شك - 0.4
    CONDITIONAL = "conditional"  # مشروط - variable


@dataclass
class EpistemicWeight:
    """
    Epistemic weight of a judgment
    
    Attributes:
        level: Certainty level
        confidence: Numeric confidence (0.0-1.0)
        justification: Why this confidence level
        conditions: Conditions that affect certainty
    """
    level: EpistemicLevel
    confidence: float  # 0.0 to 1.0
    justification: str
    conditions: List[str] = field(default_factory=list)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "level": self.level.value,
            "confidence": self.confidence,
            "justification": self.justification,
            "conditions": self.conditions,
        }


@dataclass
class ParseTree:
    """
    Form Layer output - syntactic structure without meaning
    
    This is pure FORM - no semantic interpretation yet.
    """
    text: str
    tokens: List[Dict[str, Any]]
    tree: Dict[str, Any]
    phonology: Dict[str, Any]
    morphology: Dict[str, Any]
    pos_tags: List[Dict[str, str]]
    layer: str = "form"
    timestamp: str = field(default_factory=lambda: datetime.utcnow().isoformat())
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "text": self.text,
            "tokens": self.tokens,
            "tree": self.tree,
            "phonology": self.phonology,
            "morphology": self.morphology,
            "pos_tags": self.pos_tags,
            "layer": self.layer,
            "timestamp": self.timestamp,
        }


@dataclass
class SemanticCandidates:
    """
    Semantic Layer output - meaning candidates (NOT selected yet)
    
    This layer generates CANDIDATES, selection happens later with measurement.
    """
    token_id: str
    form: str
    candidates: List[Dict[str, Any]]  # Multiple possible meanings
    denotation_types: Dict[str, List[str]]  # mutabaqa, tadammun, iltizam
    concept_types: List[str]  # entity, event, relation, modality, value
    layer: str = "semantic"
    timestamp: str = field(default_factory=lambda: datetime.utcnow().isoformat())
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "token_id": self.token_id,
            "form": self.form,
            "candidates": self.candidates,
            "denotation_types": self.denotation_types,
            "concept_types": self.concept_types,
            "layer": self.layer,
            "timestamp": self.timestamp,
        }


class RelationType(Enum):
    """Types of relations (أنواع النسب)"""
    ISNAD = "predication"  # إسناد
    TAQYEED = "restriction"  # تقييد
    TADMEEN = "inclusion"  # تضمين
    IDAFA = "annexation"  # إضافة
    SIFA = "attribution"  # صفة
    BADAL = "substitution"  # بدل


class DiscourseType(Enum):
    """Discourse types (أنواع الكلام)"""
    KHABAR = "assertive"  # خبر
    AMKR = "imperative"  # أمر
    NAHY = "prohibition"  # نهي
    ISTIFHAM = "interrogation"  # استفهام
    NAFY = "negation"  # نفي
    TAWKID = "emphasis"  # توكيد


@dataclass
class RelationGraph:
    """
    Relational Layer output - structure of relations
    
    Without relations, NO JUDGMENT is possible.
    """
    relations: List[Dict[str, Any]]
    discourse_type: DiscourseType
    primary_predication: Optional[Dict[str, Any]]
    restrictions: List[Dict[str, Any]]
    layer: str = "relational"
    timestamp: str = field(default_factory=lambda: datetime.utcnow().isoformat())
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "relations": self.relations,
            "discourse_type": self.discourse_type.value,
            "primary_predication": self.primary_predication,
            "restrictions": self.restrictions,
            "layer": self.layer,
            "timestamp": self.timestamp,
        }


@dataclass
class Operator:
    """
    An operator that performs measurement
    
    Operators are GOVERNORS - they cause effects on their scope.
    """
    operator_id: str
    operator_type: str  # verb, particle, implicit, etc.
    trigger: str  # What activates this operator
    scope: List[str]  # What it affects
    effect: str  # What it does (case marking, truth value, etc.)
    relation_type: Optional[RelationType]
    conditions: List[str] = field(default_factory=list)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "operator_id": self.operator_id,
            "operator_type": self.operator_type,
            "trigger": self.trigger,
            "scope": self.scope,
            "effect": self.effect,
            "relation_type": self.relation_type.value if self.relation_type else None,
            "conditions": self.conditions,
        }


@dataclass
class MeasurementTrace:
    """
    Measurement Layer output - how the measurement was performed
    
    This is the CRITICAL layer - without measurement, NO JUDGMENT.
    """
    measurement_id: str
    operators: List[Operator]
    applications: List[Dict[str, Any]]  # Sequence of operator applications
    conflicts: List[Dict[str, Any]]  # Conflicts and resolutions
    final_assignments: Dict[str, Any]  # Final case marks / values
    layer: str = "measurement"
    timestamp: str = field(default_factory=lambda: datetime.utcnow().isoformat())
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "measurement_id": self.measurement_id,
            "operators": [op.to_dict() for op in self.operators],
            "applications": self.applications,
            "conflicts": self.conflicts,
            "final_assignments": self.final_assignments,
            "layer": self.layer,
            "timestamp": self.timestamp,
        }


class JudgmentType(Enum):
    """Types of judgments"""
    PROPOSITION = "proposition"  # قضية
    DIRECTIVE = "directive"  # أمر/نهي
    QUESTION = "question"  # سؤال
    CONDITIONAL = "conditional"  # شرطي


@dataclass
class JudgmentObject:
    """
    Judgment Layer output - the final judgment
    
    A judgment is NOT a prediction - it's a structured claim with scope.
    """
    judgment_id: str
    judgment_type: JudgmentType
    content: str
    structure: Dict[str, Any]
    epistemic_weight: EpistemicWeight
    scope: Dict[str, Any]  # Validity domain
    conditions: List[str]
    measurement_trace_id: str  # MUST link back to measurement
    layer: str = "judgment"
    timestamp: str = field(default_factory=lambda: datetime.utcnow().isoformat())
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "judgment_id": self.judgment_id,
            "judgment_type": self.judgment_type.value,
            "content": self.content,
            "structure": self.structure,
            "epistemic_weight": self.epistemic_weight.to_dict(),
            "scope": self.scope,
            "conditions": self.conditions,
            "measurement_trace_id": self.measurement_trace_id,
            "layer": self.layer,
            "timestamp": self.timestamp,
        }


@dataclass
class WhyChain:
    """
    Why-chain explaining a decision
    
    Format: "Why X? Because Y. How do we know Y? Because Z..."
    """
    question: str  # "Why this meaning?"
    answer: str  # "Because of this evidence"
    evidence: List[str]  # References to prior traces
    next_why: Optional["WhyChain"] = None  # Recursive chain
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "question": self.question,
            "answer": self.answer,
            "evidence": self.evidence,
            "next_why": self.next_why.to_dict() if self.next_why else None,
        }


@dataclass
class BeforeAfterChain:
    """
    What comes before and what follows from this judgment
    
    Tracks logical/causal dependencies.
    """
    judgment_id: str
    preconditions: List[str]  # What must be true before
    consequences: List[str]  # What follows from this
    invalidating_conditions: List[str]  # What would invalidate this
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "judgment_id": self.judgment_id,
            "preconditions": self.preconditions,
            "consequences": self.consequences,
            "invalidating_conditions": self.invalidating_conditions,
        }


@dataclass
class ExplanationReport:
    """
    Explanation Layer output - complete explanation of the judgment
    
    This answers ALL why-questions about the judgment.
    """
    judgment_id: str
    why_this_meaning: WhyChain
    why_this_relation: WhyChain
    why_this_measurement: WhyChain
    why_this_judgment: WhyChain
    before_after: BeforeAfterChain
    full_trace: List[str]  # Complete trace from input to judgment
    alternative_paths: List[Dict[str, Any]]  # Paths not taken (and why)
    layer: str = "explanation"
    timestamp: str = field(default_factory=lambda: datetime.utcnow().isoformat())
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "judgment_id": self.judgment_id,
            "why_this_meaning": self.why_this_meaning.to_dict(),
            "why_this_relation": self.why_this_relation.to_dict(),
            "why_this_measurement": self.why_this_measurement.to_dict(),
            "why_this_judgment": self.why_this_judgment.to_dict(),
            "before_after": self.before_after.to_dict(),
            "full_trace": self.full_trace,
            "alternative_paths": self.alternative_paths,
            "layer": self.layer,
            "timestamp": self.timestamp,
        }


@dataclass
class XAIResult:
    """
    Complete XAI engine output - ALL layers
    
    This is what the engine returns: full transparency from input to judgment.
    """
    input_text: str
    domain: str
    parse_tree: ParseTree
    semantic_candidates: List[SemanticCandidates]
    relation_graph: RelationGraph
    measurement_trace: MeasurementTrace
    judgment: JudgmentObject
    explanation: ExplanationReport
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "input_text": self.input_text,
            "domain": self.domain,
            "parse_tree": self.parse_tree.to_dict(),
            "semantic_candidates": [sc.to_dict() for sc in self.semantic_candidates],
            "relation_graph": self.relation_graph.to_dict(),
            "measurement_trace": self.measurement_trace.to_dict(),
            "judgment": self.judgment.to_dict(),
            "explanation": self.explanation.to_dict(),
            "metadata": self.metadata,
        }
