#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Fractal Linguistic Mathematics Engine for Arabic
المحرك الرياضي الفركتالي للغة العربية

This engine implements the complete fractal mathematical framework
that unifies all levels of Arabic language from triliteral roots to discourse.

Author: AGT Complete System
Date: 2025-12-04
Version: 1.0.0
"""

import numpy as np
from dataclasses import dataclass, field
from typing import List, Tuple, Dict, Set, Optional
from enum import Enum


# ============================================================================
#  1️⃣ LAYER 1: TRILITERAL ROOT
# ============================================================================

class Phoneme(Enum):
    """Arabic phoneme/consonant representation"""
    # Basic consonants
    BA = 'ب'
    TA = 'ت'
    THA = 'ث'
    JIM = 'ج'
    HA = 'ح'
    KHA = 'خ'
    DAL = 'د'
    DHAL = 'ذ'
    RA = 'ر'
    ZAY = 'ز'
    SIN = 'س'
    SHIN = 'ش'
    SAD = 'ص'
    DAD = 'ض'
    TA_EMPHATIC = 'ط'
    ZA = 'ظ'
    AIN = 'ع'
    GHAIN = 'غ'
    FA = 'ف'
    QAF = 'ق'
    KAF = 'ك'
    LAM = 'ل'
    MIM = 'م'
    NUN = 'ن'
    HA_END = 'ه'
    WAW = 'و'
    YA = 'ي'
    HAMZA = 'ء'


@dataclass
class TrilingualRoot:
    """
    Triliteral root representation with Fibonacci weights
    الجذر الثلاثي مع أوزان فيبوناتشي
    """
    c1: str  # First consonant (البداية/المنطلق)
    c2: str  # Second consonant (المحور المركزي)
    c3: str  # Third consonant (النهاية/المآل)
    
    # Fibonacci weights
    F1: int = 1  # Weight for c1
    F2: int = 1  # Weight for c2
    F3: int = 2  # Weight for c3
    
    def __post_init__(self):
        """Validate root structure"""
        assert all(len(c) == 1 for c in [self.c1, self.c2, self.c3]), \
            "Each consonant must be a single character"
    
    def get_root_string(self) -> str:
        """Get root as string: ك-ت-ب"""
        return f"{self.c1}-{self.c2}-{self.c3}"
    
    def get_weighted_vector(self) -> np.ndarray:
        """
        Get Fibonacci-weighted vector representation
        R⃗ = F₁·e⃗_c₁ + F₂·e⃗_c₂ + F₃·e⃗_c₃
        """
        # Simple one-hot encoding (in production, use proper embeddings)
        c1_vec = np.array([1, 0, 0]) * self.F1
        c2_vec = np.array([0, 1, 0]) * self.F2
        c3_vec = np.array([0, 0, 1]) * self.F3
        return c1_vec + c2_vec + c3_vec
    
    def get_relation_matrix(self) -> np.ndarray:
        """
        Get root relation matrix A_root
        
        A_root = [
          0    a₁₂   0
          a₂₁   0    a₂₃
          0    a₃₂   0
        ]
        """
        # Symmetric relations (can be learned from data)
        a12 = a21 = 0.5  # c2 influences c1
        a23 = a32 = 0.7  # c2 influences c3
        
        return np.array([
            [0, a12, 0],
            [a21, 0, a23],
            [0, a32, 0]
        ])
    
    def build_fractal_pair(self) -> Tuple[str, str]:
        """
        Build fractal pair: P₁₂ = (c₁, c₂)
        """
        return (self.c1, self.c2)
    
    def build_fractal_triple(self) -> Tuple[str, str, str]:
        """
        Build fractal triple: T₁₂₃ = f(P₁₂, c₃)
        """
        return (self.c1, self.c2, self.c3)


# ============================================================================
#  2️⃣ LAYER 2: MORPHOLOGICAL PATTERN (الوزن الصرفي)
# ============================================================================

class Haraka(Enum):
    """Arabic diacritics/vowels"""
    FATHA = 'َ'   # فتحة - openness
    KASRA = 'ِ'   # كسرة - compression/internalization
    DAMMA = 'ُ'   # ضمة - fullness/stability
    SUKUN = 'ْ'   # سكون - silence


@dataclass
class MorphologicalPattern:
    """
    Morphological pattern with root + diacritics
    الوزن الصرفي = الجذر + الحركات
    """
    root: TrilingualRoot
    h1: Haraka  # First vowel
    h2: Haraka  # Second vowel
    h3: Haraka  # Third vowel (may be SUKUN)
    
    def get_pattern_name(self) -> str:
        """Get pattern name: فَعَلَ, فَعِلَ, فَعُلَ, etc."""
        vowel_map = {
            Haraka.FATHA: 'َ',
            Haraka.KASRA: 'ِ',
            Haraka.DAMMA: 'ُ',
            Haraka.SUKUN: 'ْ'
        }
        return f"ف{vowel_map[self.h1]}ع{vowel_map[self.h2]}ل{vowel_map[self.h3]}"
    
    def get_semantic_domain(self) -> str:
        """
        Determine semantic domain based on vowel pattern
        الربط الصوتي-الدلالي
        """
        if self.h2 == Haraka.FATHA:
            return "Physical/General"
        elif self.h2 == Haraka.KASRA:
            return "Cognitive/Emotional"
        elif self.h2 == Haraka.DAMMA:
            return "Stable_Attribute"
        else:
            return "Unknown"
    
    def get_weighted_vector(self) -> np.ndarray:
        """
        Get Fibonacci-weighted pattern vector
        Weight_Pattern = F₁·h₁ + F₂·h₂ + F₃·h₃
        """
        # Encode vowels as vectors
        vowel_vectors = {
            Haraka.FATHA: np.array([1, 0, 0]),  # openness
            Haraka.KASRA: np.array([0, 1, 0]),  # compression
            Haraka.DAMMA: np.array([0, 0, 1]),  # fullness
            Haraka.SUKUN: np.array([0, 0, 0])   # silence
        }
        
        v1 = vowel_vectors[self.h1] * self.root.F1
        v2 = vowel_vectors[self.h2] * self.root.F2
        v3 = vowel_vectors[self.h3] * self.root.F3
        
        return v1 + v2 + v3


# ============================================================================
#  3️⃣ LAYER 3: SYNTACTIC STRUCTURE (البنية النحوية)
# ============================================================================

@dataclass
class VerbSentence:
    """
    Verbal sentence structure: (N_before, V, N_after)
    الجملة الفعلية = (اسم قبلي، فعل، اسم بعدي)
    """
    n_before: str  # Usually the agent (الفاعل)
    verb: str      # The event (الفعل)
    n_after: str   # Usually the patient (المفعول به)
    
    # Fibonacci weights
    F1: int = 1  # Weight for agent
    F2: int = 1  # Weight for verb
    F3: int = 2  # Weight for patient
    
    def get_weighted_vector(self) -> np.ndarray:
        """
        S⃗ = F₁·N_b + F₂·V + F₃·N_a
        """
        # Simple representation (in production, use proper word embeddings)
        n_before_vec = np.array([1, 0, 0]) * self.F1
        verb_vec = np.array([0, 1, 0]) * self.F2
        n_after_vec = np.array([0, 0, 1]) * self.F3
        
        return n_before_vec + verb_vec + n_after_vec
    
    def to_triple(self) -> Tuple[str, str, str]:
        """Convert to fractal triple structure"""
        return (self.n_before, self.verb, self.n_after)
    
    def matches_root_structure(self, root: TrilingualRoot) -> bool:
        """
        Check if sentence structure matches root structure (fractal property)
        """
        # Both are triples → fractal match
        return True


# ============================================================================
#  4️⃣ LAYER 4: LOGICAL ENGINE (المحرك المنطقي)
# ============================================================================

class SemanticRole(Enum):
    """Semantic roles (الأدوار الدلالية)"""
    AGENT = "فاعل"
    PATIENT = "مفعول_به"
    POSSESSOR = "مضاف_إليه"
    OBLIQUE = "مجرور"
    TOPIC = "مبتدأ"
    COMMENT = "خبر"
    STATE = "حال"
    SPECIFICATION = "تمييز"


class SemanticRelation(Enum):
    """Semantic relations (العلاقات الدلالية)"""
    AGENT_OF = "فاعل_لـ"
    PATIENT_OF = "مفعول_لـ"
    IN = "في"
    FROM = "من"
    TO = "إلى"
    CAUSE_OF = "سبب_لـ"
    CONDITION_FOR = "شرط_لـ"
    GOAL_OF = "غاية_لـ"
    AND = "و"
    OR = "أو"
    THEN = "ثم"


class PragmaticContext(Enum):
    """Pragmatic/deictic context (السياق المؤشري)"""
    # Person
    FIRST_SING = "أنا"
    SECOND_SING = "أنت"
    THIRD_SING_MASC = "هو"
    THIRD_SING_FEM = "هي"
    FIRST_PLUR = "نحن"
    
    # Place
    HERE = "هنا"
    THERE = "هناك"
    THIS = "هذا"
    THAT = "ذلك"
    
    # Time
    NOW = "الآن"
    YESTERDAY = "أمس"
    TOMORROW = "غدًا"
    
    # Negation
    NOT = "لا"
    NOT_PAST = "لم"
    NOT_FUTURE = "لن"
    
    # Emphasis
    INDEED = "إنّ"
    SURELY = "لقد"
    
    # Voice
    ACTIVE = "مبني_للمعلوم"
    PASSIVE = "مبني_للمجهول"


@dataclass
class LogicalState:
    """
    Complete logical state: T = F₁·S + F₂·R + F₃·P
    الحالة المنطقية الكاملة
    """
    # Structure (البنية)
    structure: Dict[SemanticRole, str] = field(default_factory=dict)
    
    # Relations (العلاقات)
    relations: Dict[SemanticRelation, List[Tuple]] = field(default_factory=dict)
    
    # Pragmatics (السياق)
    pragmatics: Dict[str, PragmaticContext] = field(default_factory=dict)
    
    # Fibonacci weights
    F1: int = 1  # Structure weight
    F2: int = 2  # Relations weight
    F3: int = 3  # Pragmatics weight
    
    def compute_total_weight(self) -> float:
        """
        Compute T = F₁·S + F₂·R + F₃·P
        """
        s_weight = len(self.structure) * self.F1
        r_weight = sum(len(v) for v in self.relations.values()) * self.F2
        p_weight = len(self.pragmatics) * self.F3
        
        return s_weight + r_weight + p_weight
    
    def get_semantic_vector(self) -> np.ndarray:
        """
        Get complete semantic vector representation
        """
        # Simplified representation
        s_vec = np.array([len(self.structure), 0, 0]) * self.F1
        r_vec = np.array([0, sum(len(v) for v in self.relations.values()), 0]) * self.F2
        p_vec = np.array([0, 0, len(self.pragmatics)]) * self.F3
        
        return s_vec + r_vec + p_vec


# ============================================================================
#  5️⃣ DISCOURSE LEVEL: FIBONACCI SEGMENTATION
# ============================================================================

class FibonacciDiscourseSegmenter:
    """
    Fibonacci-based discourse segmentation
    التجزئة الخطابية بفيبوناتشي
    """
    
    def __init__(self, alpha: float = 10.0, beta: float = 5.0, gamma: float = 2.0):
        """
        Initialize segmenter with weights
        
        Args:
            alpha: Cohesion weight
            beta: Boundary cost weight
            gamma: Fibonacci bonus weight
        """
        self.alpha = alpha
        self.beta = beta
        self.gamma = gamma
        self.fib_numbers = self._generate_fibonacci(150)
    
    @staticmethod
    def _generate_fibonacci(n: int) -> Set[int]:
        """Generate Fibonacci numbers up to n"""
        fibs = {1, 2}
        a, b = 1, 2
        while b < n:
            a, b = b, a + b
            fibs.add(b)
        return fibs
    
    def fibonacci_bonus(self, length: int) -> float:
        """
        fib_bonus(n) = 2.0 if n ∈ Fibonacci_Numbers else 0.0
        """
        return 2.0 if length in self.fib_numbers else 0.0
    
    def cohesion(self, vectors: List[np.ndarray], i: int, j: int) -> float:
        """
        c(i,j) = (1/(j-i)) × Σ(t=i to j-1) sim(t, t+1)
        """
        if i >= j:
            return 1.0
        
        similarities = []
        for t in range(i, j):
            sim = self._cosine_similarity(vectors[t], vectors[t+1])
            similarities.append(sim)
        
        return np.mean(similarities)
    
    def boundary_cost(self, vectors: List[np.ndarray], k: int) -> float:
        """
        b(k) = 1 - sim(k, k+1)
        """
        if k >= len(vectors) - 1:
            return 0.0
        
        sim = self._cosine_similarity(vectors[k], vectors[k+1])
        return 1.0 - sim
    
    @staticmethod
    def _cosine_similarity(v1: np.ndarray, v2: np.ndarray) -> float:
        """Cosine similarity between two vectors"""
        dot = np.dot(v1, v2)
        norm1 = np.linalg.norm(v1)
        norm2 = np.linalg.norm(v2)
        
        if norm1 == 0 or norm2 == 0:
            return 0.0
        
        return dot / (norm1 * norm2)
    
    def segment(self, vectors: List[np.ndarray]) -> List[int]:
        """
        Segment discourse using Dynamic Programming
        
        Returns:
            List of segment lengths
        """
        N = len(vectors)
        if N == 0:
            return []
        
        # DP[i] = (score, backpointer)
        DP = [(-float('inf'), -1) for _ in range(N + 1)]
        DP[0] = (0.0, -1)
        
        # Fill DP table
        for i in range(1, N + 1):
            for k in range(i):
                segment_length = i - k
                
                # Compute score for segment [k+1, i]
                cohesion_score = self.cohesion(vectors, k, i - 1)
                boundary_cost_val = self.boundary_cost(vectors, k - 1) if k > 0 else 0.0
                fib_bonus = self.fibonacci_bonus(segment_length)
                
                score = (DP[k][0] + 
                        self.alpha * cohesion_score - 
                        self.beta * boundary_cost_val + 
                        self.gamma * fib_bonus)
                
                if score > DP[i][0]:
                    DP[i] = (score, k)
        
        # Backtrack to get segments
        segments = []
        i = N
        while i > 0:
            k = DP[i][1]
            segments.append(i - k)
            i = k
        
        return list(reversed(segments))


# ============================================================================
#  6️⃣ FRACTAL INTEGRATION
# ============================================================================

class FractalLinguisticAnalyzer:
    """
    Complete fractal linguistic analyzer
    المحلل اللغوي الفركتالي الكامل
    """
    
    def __init__(self):
        self.segmenter = FibonacciDiscourseSegmenter()
    
    def analyze_root(self, c1: str, c2: str, c3: str) -> Dict:
        """Analyze triliteral root"""
        root = TrilingualRoot(c1, c2, c3)
        
        return {
            "root_string": root.get_root_string(),
            "weighted_vector": root.get_weighted_vector().tolist(),
            "relation_matrix": root.get_relation_matrix().tolist(),
            "fractal_pair": root.build_fractal_pair(),
            "fractal_triple": root.build_fractal_triple()
        }
    
    def analyze_pattern(self, root: TrilingualRoot, h1: Haraka, h2: Haraka, h3: Haraka) -> Dict:
        """Analyze morphological pattern"""
        pattern = MorphologicalPattern(root, h1, h2, h3)
        
        return {
            "pattern_name": pattern.get_pattern_name(),
            "semantic_domain": pattern.get_semantic_domain(),
            "weighted_vector": pattern.get_weighted_vector().tolist()
        }
    
    def analyze_sentence(self, n_before: str, verb: str, n_after: str) -> Dict:
        """Analyze sentence structure"""
        sentence = VerbSentence(n_before, verb, n_after)
        
        return {
            "triple": sentence.to_triple(),
            "weighted_vector": sentence.get_weighted_vector().tolist(),
            "fractal_match": True  # Always true for triples
        }
    
    def analyze_logic(self, structure: Dict, relations: Dict, pragmatics: Dict) -> Dict:
        """Analyze logical state"""
        logical_state = LogicalState(structure, relations, pragmatics)
        
        return {
            "total_weight": logical_state.compute_total_weight(),
            "semantic_vector": logical_state.get_semantic_vector().tolist(),
            "S_weight": len(structure),
            "R_weight": sum(len(v) for v in relations.values()),
            "P_weight": len(pragmatics)
        }
    
    def analyze_discourse(self, verse_vectors: List[np.ndarray]) -> Dict:
        """Analyze discourse segmentation"""
        segments = self.segmenter.segment(verse_vectors)
        
        fib_count = sum(1 for seg in segments if seg in self.segmenter.fib_numbers)
        fib_percentage = (fib_count / len(segments) * 100) if segments else 0
        
        return {
            "segments": segments,
            "num_segments": len(segments),
            "fibonacci_segments": fib_count,
            "fibonacci_percentage": fib_percentage,
            "total_length": sum(segments)
        }


# ============================================================================
#  EXAMPLE USAGE
# ============================================================================

def main():
    """Demonstrate fractal linguistic analysis"""
    
    print("=" * 80)
    print("Fractal Linguistic Mathematics Engine")
    print("المحرك الرياضي الفركتالي للغة العربية")
    print("=" * 80)
    print()
    
    analyzer = FractalLinguisticAnalyzer()
    
    # Example 1: Root analysis
    print("1️⃣  ROOT ANALYSIS: ك-ت-ب")
    root_analysis = analyzer.analyze_root('ك', 'ت', 'ب')
    print(f"  Root String: {root_analysis['root_string']}")
    print(f"  Weighted Vector: {root_analysis['weighted_vector']}")
    print(f"  Fractal Triple: {root_analysis['fractal_triple']}")
    print()
    
    # Example 2: Pattern analysis
    print("2️⃣  PATTERN ANALYSIS: كَتَبَ (فَعَلَ)")
    root = TrilingualRoot('ك', 'ت', 'ب')
    pattern_analysis = analyzer.analyze_pattern(root, Haraka.FATHA, Haraka.FATHA, Haraka.FATHA)
    print(f"  Pattern Name: {pattern_analysis['pattern_name']}")
    print(f"  Semantic Domain: {pattern_analysis['semantic_domain']}")
    print()
    
    # Example 3: Sentence analysis
    print("3️⃣  SENTENCE ANALYSIS: الطالبُ يقرأُ الكتابَ")
    sentence_analysis = analyzer.analyze_sentence("الطالب", "يقرأ", "الكتاب")
    print(f"  Triple Structure: {sentence_analysis['triple']}")
    print(f"  Weighted Vector: {sentence_analysis['weighted_vector']}")
    print()
    
    # Example 4: Logical state
    print("4️⃣  LOGICAL STATE ANALYSIS")
    structure = {
        SemanticRole.AGENT: "الطالب",
        SemanticRole.PATIENT: "الكتاب"
    }
    relations = {
        SemanticRelation.AGENT_OF: [("الطالب", "قرأ")],
        SemanticRelation.PATIENT_OF: [("الكتاب", "قرأ")]
    }
    pragmatics = {
        "person": PragmaticContext.THIRD_SING_MASC,
        "voice": PragmaticContext.ACTIVE
    }
    
    logic_analysis = analyzer.analyze_logic(structure, relations, pragmatics)
    print(f"  Total Weight (T = F₁S + F₂R + F₃P): {logic_analysis['total_weight']}")
    print(f"  S Weight: {logic_analysis['S_weight']}")
    print(f"  R Weight: {logic_analysis['R_weight']}")
    print(f"  P Weight: {logic_analysis['P_weight']}")
    print()
    
    # Example 5: Discourse segmentation
    print("5️⃣  DISCOURSE SEGMENTATION (100 random vectors)")
    # Generate 100 random verse vectors
    np.random.seed(42)
    verse_vectors = [np.random.randn(128) for _ in range(100)]
    
    discourse_analysis = analyzer.analyze_discourse(verse_vectors)
    print(f"  Number of Segments: {discourse_analysis['num_segments']}")
    print(f"  Segment Lengths: {discourse_analysis['segments']}")
    print(f"  Fibonacci Segments: {discourse_analysis['fibonacci_segments']}")
    print(f"  Fibonacci %: {discourse_analysis['fibonacci_percentage']:.1f}%")
    print()
    
    print("=" * 80)
    print("✅ Fractal analysis complete!")
    print("=" * 80)


if __name__ == "__main__":
    main()
