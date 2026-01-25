# خطة المحرك اللغوي الفراكتالي | Fractal Linguistic Engine Plan

**النسخة | Version**: 1.0  
**التاريخ | Date**: 2026-01-25  
**الحالة | Status**: جاهز للتنفيذ | Ready for Implementation  
**المدة المتوقعة | Expected Duration**: 12-16 أسبوع | 12-16 weeks

---

## ملخص تنفيذي | Executive Summary

### العربية

هذه الوثيقة تقدم خطة شاملة لبناء **محرك لغوي فراكتالي** يربط الجذور الثلاثية العربية (C1-C2-C3) على مستوى المقاطع الصوتية مع البنية الصرفية والنحوية والدلالية. المحرك يطبق مبدأ "الاقتصاد الصوتي" ويتكامل مع معمارية FractalHub المُتحقق منها رسميًا.

**الأهداف الرئيسية**:
1. نموذج مقطعي صوتي كامل للعربية (CV, CVC, CVV, CVCC...)
2. ربط فراكتالي بين الجذر والوزن والبنية النحوية
3. تحقق رسمي باستخدام Coq (50+ مبرهنة جديدة)
4. تكامل سلس مع FractalHub Kernel v1.2
5. 200+ اختبار شامل

**المخرجات المتوقعة**:
- ~8,000 سطر كود Python جديد
- ~2,000 سطر كود Coq جديد
- 200+ اختبار (unit + integration + property-based)
- 30,000+ كلمة توثيق

### English

This document presents a comprehensive plan for building a **Fractal Linguistic Engine** that links Arabic triliteral roots (C1-C2-C3) at the syllable level with morphological, syntactic, and semantic structures. The engine applies the principle of "phonetic economy" and integrates with the formally verified FractalHub architecture.

**Main Objectives**:
1. Complete syllabic phonetic model for Arabic (CV, CVC, CVV, CVCC...)
2. Fractal linking between root, pattern, and syntactic structure
3. Formal verification using Coq (50+ new theorems)
4. Seamless integration with FractalHub Kernel v1.2
5. 200+ comprehensive tests

**Expected Deliverables**:
- ~8,000 LOC new Python code
- ~2,000 LOC new Coq code
- 200+ tests (unit + integration + property-based)
- 30,000+ words documentation

---

## جدول المحتويات | Table of Contents

1. [المعمارية العامة | Overall Architecture](#architecture)
2. [نموذج المقاطع الصوتية | Syllable Model](#syllable-model)
3. [ربط C1-C2-C3 | C1-C2-C3 Linking](#c123-linking)
4. [القواعد الصرفية | Morphological Rules](#morphology)
5. [القواعد النحوية | Syntactic Rules](#syntax)
6. [الدلالة والتحولات | Semantics and Transformations](#semantics)
7. [التحقق الرسمي | Formal Verification](#verification)
8. [خطة التنفيذ | Implementation Plan](#implementation)
9. [الاختبارات | Testing Strategy](#testing)
10. [التكامل مع FractalHub | FractalHub Integration](#integration)
11. [الأداء والتحسين | Performance and Optimization](#performance)
12. [المراجع | References](#references)

---

<a name="architecture"></a>
## 1. المعمارية العامة | Overall Architecture

### 1.1 البنية الطبقية | Layered Structure

```
┌─────────────────────────────────────────────────────────┐
│  C3: Semantic Layer (الطبقة الدلالية)                    │
│  - Meaning transformations (تحولات المعنى)               │
│  - Agent roles (أدوار الفاعل/المفعول)                   │
│  - Causativity (السببية/المسببية)                       │
└─────────────────────────────────────────────────────────┘
                           ↑
┌─────────────────────────────────────────────────────────┐
│  C2: Syntactic Layer (الطبقة النحوية)                   │
│  - Word patterns (الأوزان)                              │
│  - Derivation (الاشتقاق)                                │
│  - Inflection (التصريف)                                 │
└─────────────────────────────────────────────────────────┘
                           ↑
┌─────────────────────────────────────────────────────────┐
│  C1: Phonological Layer (الطبقة الصوتية)                │
│  - Syllables (المقاطع)                                  │
│  - Vowels & Diacritics (الحركات والتشكيل)               │
│  - Phonotactic constraints (القيود الصوتية)             │
└─────────────────────────────────────────────────────────┘
                           ↑
┌─────────────────────────────────────────────────────────┐
│  C0: Atomic Layer (الطبقة الذرية)                       │
│  - Root radicals (حروف الجذر: C1, C2, C3)               │
│  - Phonemes (الفونيمات)                                 │
│  - Features (الصفات الصوتية)                            │
└─────────────────────────────────────────────────────────┘
```

### 1.2 مبدأ C2 كعقدة انتقالية | C2 as Transition Node

**القاعدة المركزية**: C2 ليس مجرد حرف، بل **عقدة انتقالية** تربط C1 بـ C3.

```python
class TransitionNode:
    """
    C2 as a transition node in syllabic structure.
    """
    def __init__(self, c2_radical: str):
        self.radical = c2_radical
        self.role: TransitionRole = None  # CODA | ONSET | GEMINATED
        
    def determine_role(self, context: SyllableContext) -> TransitionRole:
        """
        Determine C2's role based on syllabic context:
        1. Coda: closes preceding syllable (مقطع مغلق)
        2. Onset: starts following syllable (بداية مقطع)
        3. Geminated: شدة/تضعيف
        """
        if context.has_shadda():
            return TransitionRole.GEMINATED
        elif context.is_coda_position():
            return TransitionRole.CODA
        else:
            return TransitionRole.ONSET
```

### 1.3 الربط الفراكتالي | Fractal Linking

**الفرضية**: نفس القوانين تتكرر على مستويات مختلفة:
- المقطع ↔ الكلمة
- الكلمة ↔ الجملة  
- الجذر ↔ المشتقات

```
Root (k-t-b) ───┐
                ├─→ Pattern (فَعَلَ) ───┐
                │                        ├─→ Word (كَتَبَ) ───┐
                │                        │                     ├─→ Sentence
                │                        ├─→ Word (كُتِبَ)     │
                │                        │                     │
                ├─→ Pattern (فاعِل) ────┤                     │
                │                        ├─→ Word (كاتِب) ────┘
                │                        │
                └─→ Pattern (مَفعول) ───┘
                                         └─→ Word (مَكتوب)
```

---

<a name="syllable-model"></a>
## 2. نموذج المقاطع الصوتية | Syllable Model

### 2.1 أنواع المقاطع | Syllable Types

العربية تستخدم 6 أنماط مقطعية أساسية:

| النمط | البنية | مثال | الوصف |
|-------|--------|------|--------|
| CV | صامت + حركة قصيرة | كَ (ka) | مقطع قصير مفتوح |
| CVV | صامت + حركة طويلة | كا (kā) | مقطع طويل مفتوح |
| CVC | صامت + حركة + صامت | كَتْ (kat) | مقطع قصير مغلق |
| CVVC | صامت + حركة طويلة + صامت | كاتْ (kāt) | مقطع طويل مغلق |
| CVCC | صامت + حركة + صامتان | كَتْبْ (katb) | مقطع فائق الإغلاق |
| CVVCC | صامت + حركة طويلة + صامتان | كاتْبْ (kātb) | نادر |

### 2.2 القيود الصوتية | Phonotactic Constraints

```python
class PhonotacticRules:
    """
    Phonotactic constraints for Arabic syllables.
    """
    
    @staticmethod
    def validate_syllable(syllable: Syllable) -> Tuple[bool, List[str]]:
        """
        Validate syllable against Arabic phonotactic rules.
        
        Returns:
            (is_valid, error_messages)
        """
        errors = []
        
        # Rule 1: No syllable can start with a vowel
        if syllable.onset is None:
            errors.append("Syllable must start with a consonant")
        
        # Rule 2: Nucleus must be a vowel (short or long)
        if not syllable.has_nucleus():
            errors.append("Syllable must have a vowel nucleus")
        
        # Rule 3: Maximum 2 consonants in coda (CVC or CVCC)
        if len(syllable.coda) > 2:
            errors.append(f"Coda too long: {len(syllable.coda)} consonants")
        
        # Rule 4: No more than 2 consonants adjacent without vowel
        if syllable.has_consonant_cluster_violation():
            errors.append("Illegal consonant cluster")
        
        # Rule 5: Apply Obligatory Contour Principle (OCP)
        if syllable.violates_ocp():
            errors.append("OCP violation: identical adjacent elements")
        
        return (len(errors) == 0, errors)
```

### 2.3 الحركات والشدة | Vowels and Gemination

```python
class ArabicVowel(Enum):
    """Arabic short and long vowels."""
    FATHA = "َ"        # /a/ - فتحة
    DAMMA = "ُ"        # /u/ - ضمة
    KASRA = "ِ"        # /i/ - كسرة
    FATHA_LONG = "ا"   # /ā/ - ألف (فتحة طويلة)
    DAMMA_LONG = "و"   # /ū/ - واو (ضمة طويلة)
    KASRA_LONG = "ي"   # /ī/ - ياء (كسرة طويلة)
    SUKUN = "ْ"        # سكون (no vowel)

class Diacritic(Enum):
    """Arabic diacritics."""
    SHADDA = "ّ"       # شدة (gemination/doubling)
    TANWEEN_FATH = "ً" # تنوين فتح
    TANWEEN_DAMM = "ٌ" # تنوين ضم
    TANWEEN_KASR = "ٍ" # تنوين كسر
```

### 2.4 مقطعة النص | Text Syllabification

```python
class SyllabifierEngine:
    """
    Syllabify Arabic text into valid syllable structures.
    """
    
    def syllabify(self, text: str) -> List[Syllable]:
        """
        Break Arabic text into syllables.
        
        Algorithm:
        1. Identify consonants and vowels
        2. Apply maximal onset principle
        3. Respect phonotactic constraints
        4. Handle gemination (shadda)
        5. Validate each syllable
        """
        syllables = []
        
        # Step 1: Normalize and tokenize
        tokens = self.tokenize(text)
        
        # Step 2: Identify syllable boundaries
        boundaries = self.find_boundaries(tokens)
        
        # Step 3: Construct syllables
        for start, end in boundaries:
            syllable = self.construct_syllable(tokens[start:end])
            
            # Step 4: Validate
            is_valid, errors = PhonotacticRules.validate_syllable(syllable)
            if not is_valid:
                raise PhonologicalError(f"Invalid syllable: {errors}")
            
            syllables.append(syllable)
        
        return syllables
```

---

<a name="c123-linking"></a>
## 3. ربط C1-C2-C3 | C1-C2-C3 Linking

### 3.1 نموذج الجذر | Root Model

```python
@dataclass
class TriconsonantalRoot:
    """
    Arabic triliteral root with C1-C2-C3 radicals.
    """
    c1: str  # First radical (الحرف الأول)
    c2: str  # Second radical (الحرف الثاني) - TRANSITION NODE
    c3: str  # Third radical (الحرف الثالث)
    
    root_type: RootType  # صحيح، مثال، أجوف، ناقص، لفيف، مهموز، مضعّف
    
    def __post_init__(self):
        """Validate root and classify type."""
        self.root_type = self.classify_root()
        self.validate()
    
    def classify_root(self) -> RootType:
        """
        Classify root based on radicals:
        - صحيح (sound): all radicals are strong consonants
        - مثال (assimilated): C1 is و or ي
        - أجوف (hollow): C2 is و or ي
        - ناقص (defective): C3 is و or ي
        - لفيف (doubly weak): two weak radicals
        - مهموز (hamzated): contains همزة
        - مضعّف (geminate): C2 == C3
        """
        weak_consonants = {'و', 'ي', 'ا'}
        
        c1_weak = self.c1 in weak_consonants
        c2_weak = self.c2 in weak_consonants
        c3_weak = self.c3 in weak_consonants
        
        if not any([c1_weak, c2_weak, c3_weak]):
            if 'ء' in [self.c1, self.c2, self.c3]:
                return RootType.HAMZATED
            elif self.c2 == self.c3:
                return RootType.GEMINATE
            else:
                return RootType.SOUND
        
        if c1_weak and c2_weak:
            return RootType.DOUBLY_WEAK
        elif c2_weak and c3_weak:
            return RootType.DOUBLY_WEAK
        elif c1_weak:
            return RootType.ASSIMILATED
        elif c2_weak:
            return RootType.HOLLOW
        elif c3_weak:
            return RootType.DEFECTIVE
        
        return RootType.SOUND
```

### 3.2 C2 كعقدة انتقالية | C2 as Transition

```python
class C2TransitionRules:
    """
    Rules governing C2's behavior as a transition node.
    """
    
    @staticmethod
    def can_skip_c2(root: TriconsonantalRoot, pattern: Pattern) -> bool:
        """
        Determine if C2 can be skipped in certain contexts.
        
        Examples:
        - قال (qāla): C2 (و) → ا in فَعَلَ pattern
        - باع (bāʿa): C2 (ي) → ا in فَعَلَ pattern
        """
        if root.root_type == RootType.HOLLOW:
            # Hollow roots: C2 can become long vowel
            return pattern.allows_c2_vocalization()
        return False
    
    @staticmethod
    def apply_c2_gemination(root: TriconsonantalRoot, 
                           pattern: Pattern) -> bool:
        """
        Determine if C2 should be geminated (شدة).
        
        Examples:
        - فَعَّلَ pattern: C2 is geminated
        - كَتَّبَ from ك-ت-ب
        """
        return pattern.requires_c2_gemination()
    
    @staticmethod
    def c2_syllabic_role(root: TriconsonantalRoot,
                        pattern: Pattern,
                        position: int) -> SyllableRole:
        """
        Determine C2's role in syllable structure.
        
        Returns: ONSET | CODA | NUCLEUS | GEMINATED
        """
        if pattern.has_shadda_on_c2():
            return SyllableRole.GEMINATED
        
        # Analyze surrounding vowels
        prev_vowel = pattern.get_vowel_before_c2()
        next_vowel = pattern.get_vowel_after_c2()
        
        if prev_vowel and not next_vowel:
            return SyllableRole.CODA
        elif not prev_vowel and next_vowel:
            return SyllableRole.ONSET
        elif root.root_type == RootType.HOLLOW:
            return SyllableRole.NUCLEUS  # C2 → long vowel
        else:
            # Default: onset of new syllable
            return SyllableRole.ONSET
```

### 3.3 الأوزان الصرفية | Morphological Patterns

```python
class MorphologicalPattern:
    """
    Arabic morphological pattern (وزن).
    """
    
    def __init__(self, template: str, semantics: SemanticType):
        """
        Args:
            template: Pattern using ف-ع-ل notation
                     Example: "فَعَلَ", "فاعِل", "مَفعول"
            semantics: Semantic category (verb, active participle, etc.)
        """
        self.template = template
        self.semantics = semantics
        self.c1_pos, self.c2_pos, self.c3_pos = self.locate_radicals()
        self.vowels = self.extract_vowels()
        self.affixes = self.extract_affixes()
    
    def apply_to_root(self, root: TriconsonantalRoot) -> str:
        """
        Apply pattern to root, respecting root type.
        
        Example:
            Pattern: فَعَلَ (faCala)
            Root: ك-ت-ب
            Result: كَتَبَ (kataba)
        """
        # Handle special cases based on root type
        if root.root_type == RootType.HOLLOW:
            return self.apply_hollow_root_rules(root)
        elif root.root_type == RootType.DEFECTIVE:
            return self.apply_defective_root_rules(root)
        elif root.root_type == RootType.GEMINATE:
            return self.apply_geminate_root_rules(root)
        
        # Standard application
        result = self.template
        result = result.replace('ف', root.c1)
        result = result.replace('ع', root.c2)
        result = result.replace('ل', root.c3)
        
        return result
```

---

<a name="morphology"></a>
## 4. القواعد الصرفية | Morphological Rules

### 4.1 الاشتقاق | Derivation

```python
class DerivationEngine:
    """
    Derive words from triliteral roots using patterns.
    """
    
    VERB_PATTERNS = {
        # Verb forms (أوزان الأفعال)
        "Form_I": "فَعَلَ",      # Basic form
        "Form_II": "فَعَّلَ",    # Causative/intensive
        "Form_III": "فاعَلَ",    # Reciprocal
        "Form_IV": "أَفْعَلَ",   # Causative
        "Form_V": "تَفَعَّلَ",   # Reflexive of II
        "Form_VI": "تَفاعَلَ",   # Reflexive of III
        "Form_VII": "انْفَعَلَ", # Passive/reflexive
        "Form_VIII": "افْتَعَلَ", # Reflexive
        "Form_IX": "افْعَلَّ",   # Colors/defects
        "Form_X": "اسْتَفْعَلَ", # Request/consider
    }
    
    NOUN_PATTERNS = {
        # Active participle (اسم الفاعل)
        "active_participle": "فاعِل",
        # Passive participle (اسم المفعول)
        "passive_participle": "مَفعول",
        # Verbal noun (مصدر)
        "verbal_noun_I": "فَعْل",
        # Instrument (اسم الآلة)
        "instrument": "مِفْعَل",
        # Place/time (اسم المكان/الزمان)
        "place_time": "مَفْعَل",
    }
    
    def derive(self, root: TriconsonantalRoot, 
               pattern_name: str) -> DerivedWord:
        """
        Derive a word from root using specified pattern.
        """
        if pattern_name in self.VERB_PATTERNS:
            pattern = MorphologicalPattern(
                self.VERB_PATTERNS[pattern_name],
                SemanticType.VERB
            )
        elif pattern_name in self.NOUN_PATTERNS:
            pattern = MorphologicalPattern(
                self.NOUN_PATTERNS[pattern_name],
                SemanticType.NOUN
            )
        else:
            raise ValueError(f"Unknown pattern: {pattern_name}")
        
        # Apply pattern to root
        surface_form = pattern.apply_to_root(root)
        
        # Syllabify result
        syllables = self.syllabifier.syllabify(surface_form)
        
        # Validate phonotactics
        for syllable in syllables:
            is_valid, errors = PhonotacticRules.validate_syllable(syllable)
            if not is_valid:
                raise PhonologicalError(
                    f"Derivation produced invalid syllable: {errors}"
                )
        
        return DerivedWord(
            root=root,
            pattern=pattern,
            surface_form=surface_form,
            syllables=syllables
        )
```

### 4.2 التصريف | Inflection

```python
class InflectionEngine:
    """
    Inflect words for person, number, gender, tense, mood, voice.
    """
    
    def conjugate_verb(self, 
                       verb: DerivedWord,
                       person: Person,  # أنا، أنتَ، هو...
                       number: Number,  # مفرد، مثنى، جمع
                       gender: Gender,  # مذكر، مؤنث
                       tense: Tense,    # ماضٍ، مضارع، أمر
                       mood: Mood,      # مرفوع، منصوب، مجزوم
                       voice: Voice     # معلوم، مجهول
                      ) -> InflectedVerb:
        """
        Full verb conjugation with all parameters.
        """
        # Start with base form
        base = verb.surface_form
        
        # Apply voice transformation
        if voice == Voice.PASSIVE:
            base = self.apply_passive_voice(base, verb.pattern)
        
        # Apply tense transformation
        if tense == Tense.PRESENT:
            base = self.to_present_tense(base)
        elif tense == Tense.IMPERATIVE:
            base = self.to_imperative(base)
        
        # Apply person/number/gender affixes
        prefixes, suffixes = self.get_verb_affixes(
            person, number, gender, tense, mood
        )
        
        inflected = prefixes + base + suffixes
        
        # Re-syllabify
        syllables = self.syllabifier.syllabify(inflected)
        
        return InflectedVerb(
            base_word=verb,
            inflected_form=inflected,
            syllables=syllables,
            features={
                'person': person,
                'number': number,
                'gender': gender,
                'tense': tense,
                'mood': mood,
                'voice': voice
            }
        )
```

---

<a name="syntax"></a>
## 5. القواعد النحوية | Syntactic Rules

### 5.1 الإعراب | Case Marking

```python
class CaseMarkingSystem:
    """
    Arabic case marking (إعراب) system.
    """
    
    def assign_case(self, 
                    word: Word, 
                    syntactic_position: SyntacticPosition) -> CaseMarking:
        """
        Assign case based on syntactic position.
        
        Cases:
        - مرفوع (nominative): فاعل، مبتدأ، خبر
        - منصوب (accusative): مفعول به، حال، تمييز
        - مجرور (genitive): مضاف إليه، مجرور بحرف
        - مبني (invariable): لا يتغير
        """
        if word.is_indeclinable():
            return CaseMarking.INDECLINABLE
        
        if syntactic_position in [Position.SUBJECT, Position.PREDICATE]:
            return CaseMarking.NOMINATIVE
        elif syntactic_position == Position.OBJECT:
            return CaseMarking.ACCUSATIVE
        elif syntactic_position == Position.GENITIVE:
            return CaseMarking.GENITIVE
        
        # Default for unspecified positions
        return CaseMarking.NOMINATIVE
```

### 5.2 العدد والمعدود | Number and Counted Noun

```python
class NumberCountedSystem:
    """
    Complex rules for Arabic numerals and counted nouns.
    """
    
    def construct_number_phrase(self, 
                                 number: int, 
                                 counted_noun: Noun) -> NumberPhrase:
        """
        Construct grammatically correct number + noun phrase.
        
        Rules (simplified):
        - 1: المعدود مفرد (singular noun)
        - 2: المعدود مثنى (dual noun)
        - 3-10: المعدود جمع مجرور (plural genitive)
        - 11-99: rules vary
        - 100+: more complex rules
        """
        if number == 1:
            return NumberPhrase(
                number_word=None,  # Usually omitted
                counted_noun=counted_noun,
                noun_number=Number.SINGULAR,
                noun_case=CaseMarking.NOMINATIVE  # or contextual
            )
        
        elif number == 2:
            return NumberPhrase(
                number_word=None,  # Usually omitted
                counted_noun=counted_noun,
                noun_number=Number.DUAL,
                noun_case=CaseMarking.NOMINATIVE
            )
        
        elif 3 <= number <= 10:
            # Numeral + plural genitive counted noun
            # Gender polarity: masculine number → feminine noun
            number_word = self.get_number_word(number, counted_noun.gender)
            
            return NumberPhrase(
                number_word=number_word,
                counted_noun=counted_noun,
                noun_number=Number.PLURAL,
                noun_case=CaseMarking.GENITIVE
            )
        
        # More complex rules for 11-99, 100+
        # ...
```

---

<a name="semantics"></a>
## 6. الدلالة والتحولات | Semantics and Transformations

### 6.1 التحولات الدلالية | Semantic Transformations

```python
class SemanticTransformations:
    """
    Semantic transformations encoded in morphological patterns.
    """
    
    TRANSFORMATIONS = {
        # Form I → Form II: Causative/Intensive
        ("Form_I", "Form_II"): Transformation.CAUSATIVE,
        # Example: كَتَبَ → كَتَّبَ (wrote → made write/dictate)
        
        # Form I → Form III: Reciprocal
        ("Form_I", "Form_III"): Transformation.RECIPROCAL,
        # Example: كَتَبَ → كاتَبَ (wrote → corresponded)
        
        # Form I → Form IV: Causative
        ("Form_I", "Form_IV"): Transformation.CAUSATIVE,
        # Example: نَزَلَ → أَنْزَلَ (descended → caused to descend)
        
        # Form I → Form VII: Passive/Reflexive
        ("Form_I", "Form_VII"): Transformation.PASSIVE_REFLEXIVE,
        # Example: كَسَرَ → انْكَسَرَ (broke → was broken)
    }
    
    def get_transformation(self, 
                          source_form: str, 
                          target_form: str) -> Transformation:
        """Get semantic transformation between verb forms."""
        return self.TRANSFORMATIONS.get((source_form, target_form))
```

### 6.2 الأدوار الدلالية | Semantic Roles

```python
class SemanticRoles:
    """
    Semantic roles (theta roles) in Arabic.
    """
    
    def assign_roles(self, verb: Verb, arguments: List[NP]) -> RoleAssignment:
        """
        Assign semantic roles to arguments.
        
        Roles:
        - فاعل (agent): doer of action
        - مفعول به (patient): receiver of action
        - مفعول لأجله (benefactive): for whose benefit
        - مفعول فيه (locative/temporal): where/when
        """
        roles = {}
        
        # Agent role
        if verb.voice == Voice.ACTIVE:
            roles['agent'] = arguments[0]  # فاعل
        else:
            # Passive: نائب الفاعل (passive agent)
            roles['patient_as_subject'] = arguments[0]
        
        # Patient role (if transitive)
        if verb.is_transitive() and len(arguments) > 1:
            roles['patient'] = arguments[1]  # مفعول به
        
        # Additional roles for ditransitive verbs
        if verb.is_ditransitive() and len(arguments) > 2:
            roles['recipient'] = arguments[2]  # مفعول به ثانٍ
        
        return RoleAssignment(verb, roles)
```

---

<a name="verification"></a>
## 7. التحقق الرسمي | Formal Verification

### 7.1 مبرهنات Coq الجديدة | New Coq Theorems

```coq
(* coq/theories/FractalEngine.v *)

(** Syllable well-formedness *)
Theorem syllable_wellformed : forall (syl : Syllable),
  valid_syllable syl -> 
  has_onset syl /\ has_nucleus syl.
Proof.
  (* Every valid syllable has onset and nucleus *)
Qed.

(** C2 transition invariant *)
Theorem c2_transition_invariant : forall (root : Root) (pattern : Pattern),
  apply_pattern root pattern = Some word ->
  exists (role : SyllableRole),
    c2_role word = role /\
    role <> InvalidRole.
Proof.
  (* C2 always has a valid role in derived words *)
Qed.

(** Phonotactic preservation *)
Theorem phonotactic_preservation : forall (root : Root) (pattern : Pattern),
  valid_root root ->
  valid_pattern pattern ->
  match derive root pattern with
  | Some word => forall syl, In syl (syllables word) -> valid_syllable syl
  | None => True
  end.
Proof.
  (* Derivation preserves phonotactic constraints *)
Qed.

(** Morphological reversibility *)
Theorem morphological_reversibility : forall (word : Word),
  valid_word word ->
  exists (root : Root) (pattern : Pattern),
    derive root pattern = Some word /\
    extract_root word = root /\
    extract_pattern word = pattern.
Proof.
  (* Words can be decomposed back to root and pattern *)
Qed.

(** Semantic compositionality *)
Theorem semantic_compositionality : forall (root : Root) (pattern : Pattern),
  meaning (derive root pattern) = 
  combine_meaning (root_semantics root) (pattern_semantics pattern).
Proof.
  (* Meaning is compositional *)
Qed.
```

### 7.2 خصائص المحافظة | Conservation Properties

```coq
(** Root radical preservation *)
Theorem root_preservation : forall (root : Root) (pattern : Pattern),
  match derive root pattern with
  | Some word => 
      contains_radical word (c1 root) /\
      contains_radical word (c2 root) \/ c2_vocalized word /\
      contains_radical word (c3 root)
  | None => True
  end.
Proof.
  (* Derived words contain (or vocalize) root radicals *)
Qed.

(** Syllable count bounds *)
Theorem syllable_bounds : forall (word : Word),
  let n := num_syllables word in
  1 <= n <= 10.  (* Reasonable bounds for Arabic words *)
Proof.
  (* Arabic words have bounded syllable count *)
Qed.
```

---

<a name="implementation"></a>
## 8. خطة التنفيذ | Implementation Plan

### المرحلة 1 (الأسبوع 1-2): البنية التحتية | Phase 1 (Week 1-2): Infrastructure

**الأهداف**:
- نموذج المقاطع الأساسي
- قواعد الصوتيات
- مقطعة النص

**المخرجات**:
- `fractalhub/phonology/syllable.py` (500 LOC)
- `fractalhub/phonology/phonotactics.py` (400 LOC)
- `fractalhub/phonology/syllabifier.py` (600 LOC)
- `tests/test_syllable.py` (30 tests)

**Coq**:
- `coq/theories/Phonology.v` (200 LOC)
- 5 theorems

---

### المرحلة 2 (الأسبوع 3-4): الجذور والأوزان | Phase 2 (Week 3-4): Roots and Patterns

**الأهداف**:
- نموذج الجذر الثلاثي
- تصنيف أنواع الجذور
- الأوزان الصرفية

**المخرجات**:
- `fractalhub/morphology/root.py` (600 LOC)
- `fractalhub/morphology/pattern.py` (700 LOC)
- `tests/test_root.py` (25 tests)
- `tests/test_pattern.py` (30 tests)

**Coq**:
- `coq/theories/Root.v` (250 LOC)
- `coq/theories/Pattern.v` (300 LOC)
- 10 theorems

---

### المرحلة 3 (الأسبوع 5-6): الاشتقاق | Phase 3 (Week 5-6): Derivation

**الأهداف**:
- محرك الاشتقاق
- قواعد C2 الانتقالية
- معالجة الجذور الضعيفة

**المخرجات**:
- `fractalhub/morphology/derivation.py` (800 LOC)
- `fractalhub/morphology/c2_rules.py` (500 LOC)
- `tests/test_derivation.py` (40 tests)

**Coq**:
- `coq/theories/Derivation.v` (350 LOC)
- 12 theorems

---

### المرحلة 4 (الأسبوع 7-8): التصريف | Phase 4 (Week 7-8): Inflection

**الأهداف**:
- تصريف الأفعال
- تصريف الأسماء
- الإعراب

**المخرجات**:
- `fractalhub/morphology/inflection.py` (900 LOC)
- `fractalhub/syntax/case.py` (400 LOC)
- `tests/test_inflection.py` (35 tests)

**Coq**:
- `coq/theories/Inflection.v` (300 LOC)
- 8 theorems

---

### المرحلة 5 (الأسبوع 9-10): الدلالة | Phase 5 (Week 9-10): Semantics

**الأهداف**:
- التحولات الدلالية
- الأدوار الدلالية
- التركيب الدلالي

**المخرجات**:
- `fractalhub/semantics/transformations.py` (600 LOC)
- `fractalhub/semantics/roles.py` (500 LOC)
- `tests/test_semantics.py` (30 tests)

**Coq**:
- `coq/theories/Semantics.v` (400 LOC)
- 10 theorems

---

### المرحلة 6 (الأسبوع 11-12): التكامل والتحسين | Phase 6 (Week 11-12): Integration & Optimization

**الأهداف**:
- التكامل مع FractalHub Kernel
- تحسين الأداء
- اختبارات شاملة
- التوثيق النهائي

**المخرجات**:
- `fractalhub/fractal_engine.py` (400 LOC) - Main engine
- Performance benchmarks
- Integration tests (50 tests)
- Documentation (10,000+ words)

**Coq**:
- Final theorem proofs
- Extraction configuration
- OCaml bridge

---

<a name="testing"></a>
## 9. الاختبارات | Testing Strategy

### 9.1 اختبارات الوحدة | Unit Tests

```python
# tests/test_syllable.py
class TestSyllableModel:
    """Unit tests for syllable model."""
    
    def test_cv_syllable(self):
        """Test basic CV syllable."""
        syl = Syllable(onset='ك', nucleus='َ')
        assert syl.is_valid()
        assert syl.structure() == 'CV'
    
    def test_cvc_syllable(self):
        """Test CVC syllable."""
        syl = Syllable(onset='ك', nucleus='َ', coda='ت')
        assert syl.is_valid()
        assert syl.structure() == 'CVC'
    
    def test_illegal_vv_onset(self):
        """Test that syllables can't start with vowels."""
        with pytest.raises(PhonologicalError):
            Syllable(onset=None, nucleus='ا')
    
    def test_ocp_violation(self):
        """Test Obligatory Contour Principle."""
        # Same consonant adjacent should trigger OCP
        # (implementation-dependent)
        pass

# Total: 30+ unit tests for syllables
# Total: 25+ unit tests for roots
# Total: 30+ unit tests for patterns
# Total: 40+ unit tests for derivation
# Total: 35+ unit tests for inflection
# Total: 30+ unit tests for semantics
```

### 9.2 اختبارات التكامل | Integration Tests

```python
# tests/test_integration_fractal_engine.py
class TestFractalEngineIntegration:
    """Integration tests for complete engine."""
    
    def test_end_to_end_derivation(self):
        """Test complete derivation pipeline."""
        # Root: ك-ت-ب
        root = TriconsonantalRoot('ك', 'ت', 'ب')
        
        # Pattern: فَعَلَ
        pattern = MorphologicalPattern("فَعَلَ", SemanticType.VERB)
        
        # Derive
        word = engine.derive(root, "Form_I")
        
        # Verify
        assert word.surface_form == "كَتَبَ"
        assert len(word.syllables) == 2
        assert word.syllables[0].structure() == 'CV'
        assert word.syllables[1].structure() == 'CV'
    
    def test_hollow_root_derivation(self):
        """Test hollow root special handling."""
        # Root: ق-و-ل
        root = TriconsonantalRoot('ق', 'و', 'ل')
        assert root.root_type == RootType.HOLLOW
        
        # Derive فَعَلَ
        word = engine.derive(root, "Form_I")
        
        # قال (qāla): و → ا
        assert word.surface_form == "قالَ"
        assert 'و' not in word.surface_form
        assert 'ا' in word.surface_form

# Total: 50+ integration tests
```

### 9.3 اختبارات الخصائص | Property-Based Tests

```python
# tests/test_properties.py
from hypothesis import given, strategies as st

class TestMorphologicalProperties:
    """Property-based tests using Hypothesis."""
    
    @given(
        c1=st.sampled_from(ARABIC_CONSONANTS),
        c2=st.sampled_from(ARABIC_CONSONANTS),
        c3=st.sampled_from(ARABIC_CONSONANTS)
    )
    def test_any_valid_root_derives(self, c1, c2, c3):
        """Any valid root should derive words."""
        root = TriconsonantalRoot(c1, c2, c3)
        
        # Should be able to derive Form I
        word = engine.derive(root, "Form_I")
        
        # Result should be valid
        assert word is not None
        assert all(
            PhonotacticRules.validate_syllable(syl)[0] 
            for syl in word.syllables
        )
    
    @given(word=st.from_regex(ARABIC_WORD_PATTERN, fullmatch=True))
    def test_syllabification_always_succeeds(self, word):
        """Any Arabic word should syllabify."""
        syllables = syllabifier.syllabify(word)
        
        # Should produce at least one syllable
        assert len(syllables) >= 1
        
        # All syllables should be valid
        for syl in syllables:
            is_valid, _ = PhonotacticRules.validate_syllable(syl)
            assert is_valid

# Total: 20+ property-based tests
```

---

<a name="integration"></a>
## 10. التكامل مع FractalHub | FractalHub Integration

### 10.1 ربط مع نواة FractalHub | Kernel Integration

```python
# fractalhub/fractal_engine.py
from fractalhub.kernel import Trace, FormCodec, MeaningCodec
from fractalhub.dictionary import get_dictionary

class FractalLinguisticEngine:
    """
    Main engine integrating with FractalHub Kernel v1.2.
    """
    
    def __init__(self):
        self.syllabifier = SyllabifierEngine()
        self.derivation_engine = DerivationEngine()
        self.inflection_engine = InflectionEngine()
        self.dictionary = get_dictionary()
    
    def process_text(self, text: str, 
                     trace_id: Optional[str] = None) -> ProcessedText:
        """
        Process Arabic text through complete pipeline.
        
        Integration with FractalHub:
        1. Create trace (C2) for processing
        2. Link to dictionary entries (prior_ids)
        3. Enforce provenance tracking
        """
        # Create trace if not provided
        if trace_id is None:
            trace = Trace()
            trace.add_gate("G_PHONOLOGY:001")  # Phonological processing
            trace.add_gate("G_MORPHOLOGY:001")  # Morphological analysis
            trace_id = trace.trace_id
        else:
            trace = Trace.load(trace_id)
        
        # Step 1: Syllabify (C0 → C1)
        syllables = self.syllabifier.syllabify(text)
        trace.add_prior_id("syllables", [s.to_id() for s in syllables])
        
        # Step 2: Extract roots (C1 → C2)
        roots = self.extract_roots(syllables)
        trace.add_prior_id("roots", [r.to_id() for r in roots])
        
        # Step 3: Derive meanings (C2 → C3)
        meanings = []
        for root in roots:
            # Lookup in dictionary
            entries = self.dictionary.lookup_root(root)
            
            # Create meaning with trace
            for entry in entries:
                meaning = MeaningCodec().encode_meaning(
                    concept=entry['meaning'],
                    trace_id=trace_id,
                    prior_ids={
                        "lexicon_ids": [entry['id']],
                        "root_ids": [root.to_id()]
                    },
                    provenance=[{
                        "source_id": "FRACTAL_ENGINE",
                        "confidence": 0.95
                    }]
                )
                meanings.append(meaning)
        
        return ProcessedText(
            original=text,
            syllables=syllables,
            roots=roots,
            meanings=meanings,
            trace_id=trace_id
        )
```

### 10.2 إضافة إلى القاموس | Dictionary Extension

```yaml
# fractalhub/data/fractal_engine_dictionary.yaml
version: "02"
metadata:
  name: "Fractal Engine Morphology Dictionary"
  description: "Morphological patterns and roots for Fractal Linguistic Engine"
  language: "ar"
  provenance:
    - source: "Traditional Arabic Grammar"
    - source: "Modern Computational Linguistics"

# Root entries
roots:
  - id: "ROOT:KTB"
    type: "signifier"
    radicals:
      c1: "ك"
      c2: "ت"
      c3: "ب"
    root_type: "sound"
    base_meaning: "writing, correspondence"
    
  - id: "ROOT:QWL"
    type: "signifier"
    radicals:
      c1: "ق"
      c2: "و"
      c3: "ل"
    root_type: "hollow"
    base_meaning: "saying, speech"

# Pattern entries
patterns:
  - id: "PATTERN:FACALA"
    type: "signifier"
    template: "فَعَلَ"
    form: "I"
    semantics: "basic verb"
    
  - id: "PATTERN:FACCALA"
    type: "signifier"
    template: "فَعَّلَ"
    form: "II"
    semantics: "causative/intensive"
```

---

<a name="performance"></a>
## 11. الأداء والتحسين | Performance and Optimization

### 11.1 أهداف الأداء | Performance Targets

| العملية | الهدف | الطريقة |
|---------|--------|---------|
| مقطعة كلمة واحدة | <100µs | Caching, optimized regex |
| اشتقاق من جذر واحد | <500µs | Pattern precompilation |
| تصريف فعل واحد | <200µs | Lookup tables |
| معالجة نص (100 كلمة) | <50ms | Batch processing |

### 11.2 تقنيات التحسين | Optimization Techniques

```python
class PerformanceOptimizations:
    """
    Performance optimizations for Fractal Engine.
    """
    
    def __init__(self):
        # Caches
        self.syllable_cache = LRUCache(maxsize=10000)
        self.derivation_cache = LRUCache(maxsize=5000)
        self.pattern_cache = {}  # Precompiled patterns
        
        # Precompile common patterns
        self._precompile_patterns()
    
    def _precompile_patterns(self):
        """Precompile morphological patterns for fast application."""
        for name, template in DerivationEngine.VERB_PATTERNS.items():
            self.pattern_cache[name] = MorphologicalPattern(
                template, SemanticType.VERB
            )
    
    @lru_cache(maxsize=10000)
    def cached_syllabify(self, text: str) -> Tuple[Syllable, ...]:
        """Cached syllabification."""
        return tuple(self.syllabifier.syllabify(text))
    
    def batch_process(self, texts: List[str]) -> List[ProcessedText]:
        """Batch processing for better performance."""
        # Process in parallel using multiprocessing
        with Pool(processes=cpu_count()) as pool:
            results = pool.map(self.process_text, texts)
        return results
```

---

<a name="references"></a>
## 12. المراجع | References

### الكتب والأبحاث | Books and Papers

**العربية**:
1. سيبويه، "الكتاب" - أساس النحو العربي
2. ابن جني، "الخصائص" - نظرية اللغة العربية
3. محمد عيد، "الصرف العربي" - المرجع الحديث

**English**:
1. McCarthy, John J. (1979). "Formal Problems in Semitic Phonology and Morphology"
2. Holes, Clive (2004). "Modern Arabic: Structures, Functions, and Varieties"
3. Ryding, Karin C. (2005). "A Reference Grammar of Modern Standard Arabic"

### الأدوات والمكتبات | Tools and Libraries

1. **CAMeL Tools** - Columbia Arabic Morphological and Lexical Tools
2. **MADAMIRA** - Morphological Analysis and Disambiguation for Arabic
3. **AraMorph** - Arabic Morphological Analyzer

### الأوراق البحثية | Research Papers

1. Beesley, K. R., & Karttunen, L. (2000). "Finite-State Morphology: Xerox Tools and Techniques"
2. Habash, N., & Rambow, O. (2005). "Arabic Tokenization, Part-of-Speech Tagging and Morphological Disambiguation"
3. Kiraz, G. A. (2001). "Computational Nonlinear Morphology with Emphasis on Semitic Languages"

---

## خاتمة | Conclusion

هذا المستند يقدم خطة شاملة لبناء محرك لغوي فراكتالي متكامل للعربية. التنفيذ سيتم على مراحل متزايدة مع اختبارات مستمرة وتكامل مع FractalHub.

**الحالة**: جاهز للتنفيذ  
**الأولوية**: عالية  
**الصعوبة**: متوسطة إلى عالية  
**المدة**: 12-16 أسبوع

This document provides a comprehensive plan for building an integrated fractal linguistic engine for Arabic. Implementation will proceed in incremental phases with continuous testing and integration with FractalHub.

**Status**: Ready for Implementation  
**Priority**: High  
**Difficulty**: Medium to High  
**Duration**: 12-16 weeks

---

**التوقيع | Signature**: FractalHub Team  
**التاريخ | Date**: 2026-01-25
