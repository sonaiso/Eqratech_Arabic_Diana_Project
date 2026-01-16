"""
C0 Phonological Layer - Arabic Phonology and Syllable Structure

This module implements the lowest level of the consciousness kernel (C0),
focusing on phonological representation and rules for Arabic text.

Components:
- Segment classification (Consonant/Vowel/Sukun)
- Syllable structure building and validation
- OCP (Obligatory Contour Principle) enforcement
- Phonological gates and well-formedness checking

Based on classical Arabic phonology and النبهاني's epistemology.
"""

from __future__ import annotations
from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional, Set, Tuple
from enum import Enum


# ===========================
# Segment Types
# ===========================

class SegmentType(Enum):
    """Basic phonological segment types"""
    CONSONANT = "C"  # صامت
    VOWEL = "V"      # صائت (short vowel)
    LONG_VOWEL = "VV"  # مد
    SUKUN = "S"      # سكون (no vowel)
    GEMINATE = "CC"  # شدة (geminated consonant)
    

class VowelQuality(Enum):
    """Vowel qualities in Arabic"""
    FATHA = "a"     # فتحة
    DAMMA = "u"     # ضمة
    KASRA = "i"     # كسرة
    FATHA_LONG = "aa"  # مد بالألف
    DAMMA_LONG = "uu"  # مد بالواو
    KASRA_LONG = "ii"  # مد بالياء


class ConsonantPlace(Enum):
    """Place of articulation for Arabic consonants"""
    LABIAL = "labial"           # شفوي (ب، م)
    DENTAL = "dental"           # أسناني (ت، د، ط، ض)
    ALVEOLAR = "alveolar"       # لثوي (ن، ر، ل)
    PALATAL = "palatal"         # غاري (ج، ش، ي)
    VELAR = "velar"             # طبقي (ك، غ)
    UVULAR = "uvular"           # لهوي (ق، خ)
    PHARYNGEAL = "pharyngeal"   # حلقي (ع، ح)
    GLOTTAL = "glottal"         # حنجري (ء، هـ)


# ===========================
# Phonological Segment
# ===========================

@dataclass(frozen=True)
class PhonologicalSegment:
    """
    Atomic phonological unit in C0 layer.
    
    Represents a single sound segment with its features.
    """
    seg_id: str
    seg_type: SegmentType
    char: str  # Unicode character
    vowel_quality: Optional[VowelQuality] = None
    place: Optional[ConsonantPlace] = None
    features: Dict[str, Any] = field(default_factory=dict)
    
    def is_consonant(self) -> bool:
        return self.seg_type in (SegmentType.CONSONANT, SegmentType.GEMINATE)
    
    def is_vowel(self) -> bool:
        return self.seg_type in (SegmentType.VOWEL, SegmentType.LONG_VOWEL)
    
    def is_sukun(self) -> bool:
        return self.seg_type == SegmentType.SUKUN


# ===========================
# Syllable Structure
# ===========================

class SyllableShape(Enum):
    """Standard Arabic syllable shapes"""
    CV = "CV"          # كَ
    CVC = "CVC"        # كَتْ
    CVV = "CVV"        # كَا
    CVVC = "CVVC"      # كَاتْ
    CVCC = "CVCC"      # كَتْبْ (rare, word-final)


@dataclass
class Syllable:
    """
    A syllable unit built from phonological segments.
    
    Arabic syllables follow specific patterns (CV, CVC, CVV, CVVC, CVCC).
    """
    syl_id: str
    shape: SyllableShape
    segments: List[PhonologicalSegment]
    onset: List[PhonologicalSegment]  # Initial consonant(s)
    nucleus: List[PhonologicalSegment]  # Vowel(s)
    coda: List[PhonologicalSegment]  # Final consonant(s)
    weight: str  # "light" or "heavy"
    
    def is_heavy(self) -> bool:
        """Heavy syllables: CVV or CVC"""
        return self.weight == "heavy"
    
    def is_light(self) -> bool:
        """Light syllables: CV"""
        return self.weight == "light"


# ===========================
# Phonological Constraints
# ===========================

@dataclass
class OCPViolation:
    """Obligatory Contour Principle violation"""
    position: int
    seg1: PhonologicalSegment
    seg2: PhonologicalSegment
    feature: str
    description: str


class PhonologicalConstraintChecker:
    """
    Checks phonological well-formedness constraints.
    
    Implements:
    - OCP (Obligatory Contour Principle): No adjacent identical features
    - Syllable structure constraints
    - Arabic-specific phonotactic rules
    """
    
    def __init__(self):
        self.violations: List[OCPViolation] = []
    
    def check_ocp(self, segments: List[PhonologicalSegment]) -> List[OCPViolation]:
        """
        Check for OCP violations (adjacent identical segments).
        
        In Arabic, gemination (شدة) is the only allowed identical adjacency.
        """
        violations = []
        
        for i in range(len(segments) - 1):
            seg1 = segments[i]
            seg2 = segments[i + 1]
            
            # Allow gemination (marked explicitly)
            if seg2.seg_type == SegmentType.GEMINATE:
                continue
            
            # Check for identical consonants
            if seg1.is_consonant() and seg2.is_consonant():
                if seg1.char == seg2.char:
                    violations.append(OCPViolation(
                        position=i,
                        seg1=seg1,
                        seg2=seg2,
                        feature="consonant",
                        description=f"OCP violation: identical consonants '{seg1.char}' at position {i}"
                    ))
            
            # Check for identical vowels (rarely allowed)
            if seg1.is_vowel() and seg2.is_vowel():
                if seg1.vowel_quality == seg2.vowel_quality:
                    violations.append(OCPViolation(
                        position=i,
                        seg1=seg1,
                        seg2=seg2,
                        feature="vowel",
                        description=f"OCP violation: identical vowels at position {i}"
                    ))
        
        return violations
    
    def check_syllable_structure(self, syllable: Syllable) -> List[str]:
        """Check if syllable structure is valid for Arabic"""
        errors = []
        
        # Validate shape matches segments
        expected_pattern = {
            SyllableShape.CV: ["C", "V"],
            SyllableShape.CVC: ["C", "V", "C"],
            SyllableShape.CVV: ["C", "V", "V"],
            SyllableShape.CVVC: ["C", "V", "V", "C"],
            SyllableShape.CVCC: ["C", "V", "C", "C"],
        }
        
        pattern = expected_pattern.get(syllable.shape, [])
        actual = []
        
        for seg in syllable.segments:
            if seg.is_consonant():
                actual.append("C")
            elif seg.is_vowel():
                actual.append("V")
            elif seg.is_sukun():
                actual.append("S")
        
        if actual != pattern:
            errors.append(f"Syllable shape {syllable.shape.value} mismatch: expected {pattern}, got {actual}")
        
        # Check onset (must have at least one consonant)
        if not syllable.onset or not syllable.onset[0].is_consonant():
            errors.append("Arabic syllables must start with a consonant")
        
        # Check nucleus (must have vowel)
        if not syllable.nucleus or not any(seg.is_vowel() for seg in syllable.nucleus):
            errors.append("Syllable must have a vocalic nucleus")
        
        return errors


# ===========================
# Syllabification Engine
# ===========================

class SyllabificationEngine:
    """
    Builds syllables from phonological segments.
    
    Implements maximal onset principle and Arabic syllable patterns.
    """
    
    def __init__(self):
        self.constraint_checker = PhonologicalConstraintChecker()
    
    def syllabify(self, segments: List[PhonologicalSegment]) -> List[Syllable]:
        """
        Segment a sequence of phonological segments into syllables.
        
        Uses maximal onset principle: syllable boundaries maximize onset.
        """
        syllables: List[Syllable] = []
        i = 0
        syl_counter = 0
        
        while i < len(segments):
            syllable = self._build_syllable(segments, i, syl_counter)
            if syllable:
                syllables.append(syllable)
                i += len(syllable.segments)
                syl_counter += 1
            else:
                # Skip problematic segment
                i += 1
        
        return syllables
    
    def _build_syllable(self, segments: List[PhonologicalSegment], 
                       start: int, syl_id: int) -> Optional[Syllable]:
        """Build a single syllable starting at position start"""
        if start >= len(segments):
            return None
        
        # Onset: must start with consonant
        if not segments[start].is_consonant():
            return None
        
        onset = [segments[start]]
        i = start + 1
        
        # Nucleus: must have vowel
        if i >= len(segments) or not segments[i].is_vowel():
            return None
        
        nucleus = [segments[i]]
        i += 1
        
        # Check for long vowel
        if i < len(segments) and segments[i].is_vowel():
            nucleus.append(segments[i])
            i += 1
        
        # Coda: optional consonant(s)
        coda = []
        if i < len(segments) and segments[i].is_consonant():
            coda.append(segments[i])
            i += 1
            
            # Check for second coda consonant (rare, word-final)
            if i < len(segments) and segments[i].is_consonant():
                # Only allow CVCC at word end
                if i == len(segments) - 1:
                    coda.append(segments[i])
                    i += 1
        
        # Determine shape and weight
        all_segs = onset + nucleus + coda
        
        if len(nucleus) == 2:  # CVV or CVVC
            if len(coda) == 0:
                shape = SyllableShape.CVV
            else:
                shape = SyllableShape.CVVC
            weight = "heavy"
        elif len(coda) == 1:  # CVC
            shape = SyllableShape.CVC
            weight = "heavy"
        elif len(coda) == 2:  # CVCC
            shape = SyllableShape.CVCC
            weight = "heavy"
        else:  # CV
            shape = SyllableShape.CV
            weight = "light"
        
        return Syllable(
            syl_id=f"SYL:{syl_id}",
            shape=shape,
            segments=all_segs,
            onset=onset,
            nucleus=nucleus,
            coda=coda,
            weight=weight
        )


# ===========================
# Phonological Gates
# ===========================

@dataclass
class PhonologicalGateResult:
    """Result from a phonological gate"""
    gate_name: str
    passed: bool
    violations: List[str]
    repairs: List[str]
    output: Any


class PhonologicalGates:
    """
    Collection of phonological well-formedness gates.
    
    Gates enforce constraints and can suggest repairs.
    """
    
    def __init__(self):
        self.constraint_checker = PhonologicalConstraintChecker()
        self.syllabifier = SyllabificationEngine()
    
    def gate_segment_wellformed(self, segments: List[PhonologicalSegment]) -> PhonologicalGateResult:
        """
        P0: Check if segments are well-formed.
        
        - No orphan vowels without carrier
        - No illegal sequences
        - Proper diacritics
        """
        violations = []
        repairs = []
        
        for i, seg in enumerate(segments):
            # Check vowel without consonant carrier
            if seg.is_vowel() and (i == 0 or not segments[i-1].is_consonant()):
                violations.append(f"Vowel at position {i} without consonant carrier")
                repairs.append(f"Insert hamzat wasl before position {i}")
        
        # Check OCP
        ocp_violations = self.constraint_checker.check_ocp(segments)
        for v in ocp_violations:
            violations.append(v.description)
        
        return PhonologicalGateResult(
            gate_name="G_SEGMENT_WF",
            passed=len(violations) == 0,
            violations=violations,
            repairs=repairs,
            output=segments if len(violations) == 0 else None
        )
    
    def gate_syllable_structure(self, syllables: List[Syllable]) -> PhonologicalGateResult:
        """
        P1: Check if syllable structures are valid.
        
        - Valid Arabic syllable shapes
        - Proper onset/nucleus/coda
        - Weight correctly assigned
        """
        violations = []
        repairs = []
        
        for syl in syllables:
            errors = self.constraint_checker.check_syllable_structure(syl)
            violations.extend(errors)
            
            if errors:
                repairs.append(f"Re-syllabify around {syl.syl_id}")
        
        return PhonologicalGateResult(
            gate_name="G_SYLLABLE_STRUCTURE",
            passed=len(violations) == 0,
            violations=violations,
            repairs=repairs,
            output=syllables if len(violations) == 0 else None
        )
    
    def gate_phonotactic_constraints(self, segments: List[PhonologicalSegment]) -> PhonologicalGateResult:
        """
        P2: Check Arabic-specific phonotactic constraints.
        
        - No initial clusters
        - No triple consonants
        - Proper gemination marking
        """
        violations = []
        repairs = []
        
        # Check for initial cluster (not allowed in Arabic)
        if len(segments) >= 2:
            if segments[0].is_consonant() and segments[1].is_consonant():
                if segments[1].seg_type != SegmentType.GEMINATE:
                    violations.append("Initial consonant cluster not allowed")
                    repairs.append("Insert epenthetic vowel or hamzat wasl")
        
        # Check for triple consonant sequences
        for i in range(len(segments) - 2):
            if (segments[i].is_consonant() and 
                segments[i+1].is_consonant() and 
                segments[i+2].is_consonant()):
                violations.append(f"Triple consonant sequence at position {i}")
                repairs.append(f"Insert vowel after position {i+1}")
        
        return PhonologicalGateResult(
            gate_name="G_PHONOTACTIC",
            passed=len(violations) == 0,
            violations=violations,
            repairs=repairs,
            output=segments if len(violations) == 0 else None
        )


# ===========================
# C0 Phonological Processor
# ===========================

class C0PhonologicalProcessor:
    """
    Complete C0 layer processor.
    
    Converts Unicode text to phonological representation,
    builds syllables, and enforces constraints.
    """
    
    def __init__(self):
        self.gates = PhonologicalGates()
        self.syllabifier = SyllabificationEngine()
    
    def process(self, text: str) -> Dict[str, Any]:
        """
        Full C0 processing pipeline.
        
        Returns:
            Dictionary with segments, syllables, gates results, and violations
        """
        # Step 1: Convert to segments (simplified)
        segments = self._text_to_segments(text)
        
        # Step 2: Check segment well-formedness
        seg_result = self.gates.gate_segment_wellformed(segments)
        
        # Step 3: Build syllables
        syllables = []
        if seg_result.passed:
            syllables = self.syllabifier.syllabify(segments)
        
        # Step 4: Check syllable structures
        syl_result = self.gates.gate_syllable_structure(syllables) if syllables else None
        
        # Step 5: Check phonotactic constraints
        phon_result = self.gates.gate_phonotactic_constraints(segments)
        
        return {
            "text": text,
            "segments": segments,
            "syllables": syllables,
            "gates": {
                "segment_wf": seg_result,
                "syllable_structure": syl_result,
                "phonotactic": phon_result
            },
            "all_passed": (seg_result.passed and 
                          (syl_result.passed if syl_result else True) and 
                          phon_result.passed)
        }
    
    def _text_to_segments(self, text: str) -> List[PhonologicalSegment]:
        """Convert Unicode text to phonological segments (simplified)"""
        segments = []
        seg_id = 0
        
        # Simplified conversion (real implementation would use codec_v2)
        for char in text:
            if char in "بتثجحخدذرزسشصضطظعغفقكلمنهوي":
                segments.append(PhonologicalSegment(
                    seg_id=f"SEG:{seg_id}",
                    seg_type=SegmentType.CONSONANT,
                    char=char
                ))
                seg_id += 1
            elif char in "َُِ":  # Short vowels
                vowel_map = {"َ": VowelQuality.FATHA, "ُ": VowelQuality.DAMMA, "ِ": VowelQuality.KASRA}
                segments.append(PhonologicalSegment(
                    seg_id=f"SEG:{seg_id}",
                    seg_type=SegmentType.VOWEL,
                    char=char,
                    vowel_quality=vowel_map[char]
                ))
                seg_id += 1
            elif char == "ْ":  # Sukun
                segments.append(PhonologicalSegment(
                    seg_id=f"SEG:{seg_id}",
                    seg_type=SegmentType.SUKUN,
                    char=char
                ))
                seg_id += 1
        
        return segments


# ===========================
# Exports
# ===========================

__all__ = [
    'SegmentType',
    'VowelQuality',
    'ConsonantPlace',
    'PhonologicalSegment',
    'SyllableShape',
    'Syllable',
    'OCPViolation',
    'PhonologicalConstraintChecker',
    'SyllabificationEngine',
    'PhonologicalGateResult',
    'PhonologicalGates',
    'C0PhonologicalProcessor',
]
