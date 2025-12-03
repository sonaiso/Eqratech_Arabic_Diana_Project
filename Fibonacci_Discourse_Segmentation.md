# الهندسة العكسية للخطاب باستخدام متتالية فيبوناتشي
# Fibonacci-Based Discourse Reverse Engineering

## نظرة عامة / Overview

هذا النظام يقوم بتحليل خطاب طويل وتقسيمه إلى مقاطع متماسكة دلاليًا، حيث تقارب أطوال هذه المقاطع أعداد فيبوناتشي (3، 5، 8، 13، 21، ...).

This system analyzes long discourse and segments it into semantically coherent chunks whose lengths approximate Fibonacci numbers.

---

## 1️⃣ البيانات الأساسية / Data Structures

### 1.1 المدخلات

لدينا خطاب مكوّن من N جملة:

```
S₁, S₂, ..., Sₙ
```

لكل جملة متجه تمثيل:
- **vᵢ ∈ ℝᵈ** : vector representation of sentence Sᵢ
- يمكن استخدام: BERT, Sentence-BERT, OpenAI embeddings, etc.

### 1.2 التشابه الكوسيني

```python
def cosine_similarity(vi, vj):
    """
    Compute cosine similarity between two vectors
    
    sim(i,j) = (vᵢ · vⱼ) / (|vᵢ| · |vⱼ|)
    
    Returns: float in range [-1, 1], typically [0, 1]
    """
    dot_product = np.dot(vi, vj)
    norm_i = np.linalg.norm(vi)
    norm_j = np.linalg.norm(vj)
    return dot_product / (norm_i * norm_j)
```

---

## 2️⃣ مقياس التماسك c(i,j) / Cohesion Metric

### 2.1 التعريف الرياضي

لمقطع من الجملة i إلى الجملة j (حيث i < j):

```
c(i,j) = (1/(j-i)) × Σ(t=i to j-1) sim(t, t+1)
```

**المعنى:**
- نحسب التشابه بين كل زوج متجاور داخل المقطع
- نأخذ المتوسط الحسابي
- قيمة عالية ⇒ مقطع متماسك موضوعيًا
- قيمة منخفضة ⇒ قفزات موضوعية داخل المقطع

### 2.2 التطبيق البرمجي

```python
def cohesion(vectors, i, j):
    """
    Calculate cohesion score for segment [i, j]
    
    Args:
        vectors: list of sentence embeddings
        i: start index (inclusive)
        j: end index (inclusive)
    
    Returns:
        float: cohesion score in [0, 1]
    """
    if i >= j:
        return 1.0  # single sentence is perfectly cohesive
    
    similarities = []
    for t in range(i, j):
        sim = cosine_similarity(vectors[t], vectors[t+1])
        similarities.append(sim)
    
    return np.mean(similarities)
```

---

## 3️⃣ تكلفة القطع b(k) / Boundary Cost

### 3.1 التعريف الرياضي

التكلفة (أو الجاذبية) للقطع بعد الجملة Sₖ:

```
b(k) = 1 - sim(k, k+1)    for k < N
```

**المعنى:**
- تشابه منخفض بين Sₖ و Sₖ₊₁ ⇒ b(k) عالية ⇒ **نقطة قطع جيدة**
- تشابه عالي ⇒ b(k) منخفضة ⇒ **لا يُفضّل القطع**

### 3.2 التطبيق البرمجي

```python
def boundary_cost(vectors, k):
    """
    Calculate boundary cost for cutting after sentence k
    
    Args:
        vectors: list of sentence embeddings
        k: index to cut after (0 to N-2)
    
    Returns:
        float: boundary cost in [0, 1]
    """
    if k >= len(vectors) - 1:
        return 0.0  # cannot cut after last sentence
    
    sim = cosine_similarity(vectors[k], vectors[k+1])
    return 1.0 - sim
```

---

## 4️⃣ الخوارزمية الكاملة / Complete Algorithm

### 4.1 متتالية فيبوناتشي

```python
def fibonacci_sequence(max_n):
    """
    Generate Fibonacci numbers up to max_n
    
    Returns: [1, 1, 2, 3, 5, 8, 13, 21, 34, ...]
    """
    fib = [1, 1]
    while fib[-1] < max_n:
        fib.append(fib[-1] + fib[-2])
    return fib
```

### 4.2 البرمجة الديناميكية للتقسيم الأمثل

```python
def fibonacci_segmentation(vectors, min_segment=3):
    """
    Segment discourse into Fibonacci-length chunks using dynamic programming
    
    Args:
        vectors: list of sentence embeddings (length N)
        min_segment: minimum segment size (default 3)
    
    Returns:
        boundaries: list of segment boundaries [0, i₁, i₂, ..., N]
        score: total segmentation quality score
    """
    N = len(vectors)
    fib_nums = fibonacci_sequence(N)
    fib_set = set(fib_nums[2:])  # Start from 2 (skip 1,1)
    
    # DP arrays
    # dp[i] = best score for segmenting sentences [0, i)
    dp = [-float('inf')] * (N + 1)
    dp[0] = 0.0
    
    # parent[i] = where the last segment started that ends at i
    parent = [-1] * (N + 1)
    
    # Fill DP table
    for i in range(1, N + 1):
        # Try all possible segment lengths
        for length in range(min_segment, i + 1):
            start = i - length
            
            # Calculate segment quality
            if start < 0:
                continue
            
            # Bonus if length is Fibonacci number
            fib_bonus = 2.0 if length in fib_set else 0.0
            
            # Cohesion within segment
            coh = cohesion(vectors, start, i - 1)
            
            # Boundary quality (if not first segment)
            bound_quality = 0.0
            if start > 0:
                bound_quality = boundary_cost(vectors, start - 1)
            
            # Total score for this segmentation
            segment_score = coh + fib_bonus + bound_quality
            total_score = dp[start] + segment_score
            
            # Update if better
            if total_score > dp[i]:
                dp[i] = total_score
                parent[i] = start
    
    # Backtrack to find boundaries
    boundaries = []
    current = N
    while current > 0:
        boundaries.append(current)
        current = parent[current]
    boundaries.append(0)
    boundaries.reverse()
    
    return boundaries, dp[N]
```

### 4.3 دالة مساعدة لعرض النتائج

```python
def display_segmentation(sentences, boundaries):
    """
    Display segmentation results with Fibonacci annotations
    """
    fib_nums = set(fibonacci_sequence(len(sentences)))
    
    print("=" * 60)
    print("FIBONACCI DISCOURSE SEGMENTATION")
    print("=" * 60)
    
    for i in range(len(boundaries) - 1):
        start = boundaries[i]
        end = boundaries[i + 1]
        length = end - start
        is_fib = "✓ Fibonacci" if length in fib_nums else ""
        
        print(f"\n[Segment {i+1}] Length: {length} {is_fib}")
        print("-" * 60)
        for j in range(start, end):
            print(f"  S{j+1}: {sentences[j][:70]}...")
    
    print("\n" + "=" * 60)
    print(f"Total segments: {len(boundaries) - 1}")
    print(f"Segment lengths: {[boundaries[i+1] - boundaries[i] for i in range(len(boundaries)-1)]}")
```

---

## 5️⃣ مثال عملي / Practical Example

### 5.1 نص تجريبي (15 جملة)

```python
sentences = [
    # Introduction (3 sentences - Fibonacci)
    "الذكاء الاصطناعي يشهد تطورًا سريعًا في السنوات الأخيرة.",
    "التعلم العميق أصبح من أهم فروع الذكاء الاصطناعي.",
    "الشبكات العصبية تحاكي عمل الدماغ البشري.",
    
    # Deep Learning Details (5 sentences - Fibonacci)
    "تتكون الشبكات العصبية من طبقات متعددة.",
    "كل طبقة تتعلم مستوى مختلفًا من التجريد.",
    "التدريب يتم باستخدام البيانات الضخمة.",
    "خوارزمية الانتشار الخلفي تحدّث الأوزان.",
    "النتائج تتحسن مع زيادة البيانات والطبقات.",
    
    # Applications (3 sentences - Fibonacci)
    "التطبيقات متعددة في مجالات مختلفة.",
    "معالجة اللغة الطبيعية من أهم التطبيقات.",
    "التعرف على الصور يستخدم الشبكات التلافيفية.",
    
    # Challenges (2 sentences - Fibonacci)
    "التحديات تشمل الحاجة لبيانات ضخمة.",
    "الشفافية والتفسير مشاكل معروفة.",
    
    # Conclusion (2 sentences - Fibonacci)
    "المستقبل واعد لهذا المجال.",
    "البحث مستمر لتطوير نماذج أفضل."
]
```

### 5.2 تنفيذ التقسيم

```python
# Mock embeddings (in practice, use real model)
import numpy as np

# Simulate embeddings with topic clustering
np.random.seed(42)
embeddings = []

# Topic 1: AI intro (sentences 0-2)
for _ in range(3):
    base = np.array([1.0, 0.0, 0.0])
    noise = np.random.normal(0, 0.1, 3)
    embeddings.append(base + noise)

# Topic 2: Deep learning (sentences 3-7)
for _ in range(5):
    base = np.array([0.7, 1.0, 0.0])
    noise = np.random.normal(0, 0.1, 3)
    embeddings.append(base + noise)

# Topic 3: Applications (sentences 8-10)
for _ in range(3):
    base = np.array([0.3, 0.5, 1.0])
    noise = np.random.normal(0, 0.1, 3)
    embeddings.append(base + noise)

# Topic 4: Challenges (sentences 11-12)
for _ in range(2):
    base = np.array([0.0, 0.3, 0.7])
    noise = np.random.normal(0, 0.1, 3)
    embeddings.append(base + noise)

# Topic 5: Conclusion (sentences 13-14)
for _ in range(2):
    base = np.array([0.5, 0.0, 0.5])
    noise = np.random.normal(0, 0.1, 3)
    embeddings.append(base + noise)

# Run segmentation
boundaries, score = fibonacci_segmentation(embeddings, min_segment=2)
display_segmentation(sentences, boundaries)
```

### 5.3 النتيجة المتوقعة

```
============================================================
FIBONACCI DISCOURSE SEGMENTATION
============================================================

[Segment 1] Length: 3 ✓ Fibonacci
------------------------------------------------------------
  S1: الذكاء الاصطناعي يشهد تطورًا سريعًا في السنوات الأخيرة....
  S2: التعلم العميق أصبح من أهم فروع الذكاء الاصطناعي....
  S3: الشبكات العصبية تحاكي عمل الدماغ البشري....

[Segment 2] Length: 5 ✓ Fibonacci
------------------------------------------------------------
  S4: تتكون الشبكات العصبية من طبقات متعددة....
  S5: كل طبقة تتعلم مستوى مختلفًا من التجريد....
  S6: التدريب يتم باستخدام البيانات الضخمة....
  S7: خوارزمية الانتشار الخلفي تحدّث الأوزان....
  S8: النتائج تتحسن مع زيادة البيانات والطبقات....

[Segment 3] Length: 3 ✓ Fibonacci
------------------------------------------------------------
  S9: التطبيقات متعددة في مجالات مختلفة....
  S10: معالجة اللغة الطبيعية من أهم التطبيقات....
  S11: التعرف على الصور يستخدم الشبكات التلافيفية....

[Segment 4] Length: 2 ✓ Fibonacci
------------------------------------------------------------
  S12: التحديات تشمل الحاجة لبيانات ضخمة....
  S13: الشفافية والتفسير مشاكل معروفة....

[Segment 5] Length: 2 ✓ Fibonacci
------------------------------------------------------------
  S14: المستقبل واعد لهذا المجال....
  S15: البحث مستمر لتطوير نماذج أفضل....

============================================================
Total segments: 5
Segment lengths: [3, 5, 3, 2, 2]
Fibonacci numbers: [3, 5, 3, 2, 2] ← All Fibonacci!
============================================================
```

---

## 6️⃣ التكامل مع AGT / Integration with AGT

### 6.1 الربط مع المصادر الدلالية

```python
def enrich_with_semantic_domains(segments, masdar_engine):
    """
    Enrich each segment with semantic domain analysis
    
    Uses MasdarSemanticEngine from masdar_semantic_enhanced_engine.py
    """
    for seg_id, segment in enumerate(segments):
        # Extract verbs from segment
        verbs = extract_verbs_from_arabic(segment)
        
        # Classify each verb
        domains = []
        for verb in verbs:
            domain = masdar_engine.classify_semantic_domain(verb)
            domains.append(domain)
        
        # Dominant domain for segment
        segment['dominant_domain'] = max(set(domains), key=domains.count)
        segment['domain_distribution'] = Counter(domains)
```

### 6.2 الربط مع أوزان المزيد

```python
def analyze_augmented_forms_in_segments(segments, mazid_engine):
    """
    Analyze augmented verb forms within each segment
    
    Uses MazidPatternsEngine from augmented_verb_forms_engine.py
    """
    for segment in segments:
        augmented_verbs = extract_augmented_verbs(segment)
        
        for verb in augmented_verbs:
            form = mazid_engine.identify_form(verb)
            semantic_function = mazid_engine.get_semantic_function(form)
            
            segment['augmented_forms'].append({
                'verb': verb,
                'form': form,
                'function': semantic_function
            })
```

### 6.3 الربط مع DL₀

```python
def translate_segment_to_dl0(segment, dl0_compiler):
    """
    Translate discourse segment to DL₀ formal representation
    
    Integrates with DL0_Proof_of_Concept.md
    """
    dl0_programs = []
    
    for sentence in segment['sentences']:
        # Parse sentence structure
        parsed = parse_arabic_sentence(sentence)
        
        # Generate DL₀ program
        dl0_prog = dl0_compiler.compile(parsed)
        dl0_programs.append(dl0_prog)
    
    # Combine into segment-level DL₀ representation
    segment_dl0 = dl0_compiler.compose_segment(dl0_programs)
    return segment_dl0
```

---

## 7️⃣ خوارزمية متقدمة / Advanced Algorithm

### 7.1 إضافة وزن للحدود الموضوعية

```python
def advanced_segmentation(vectors, topic_shift_scores):
    """
    Enhanced segmentation with explicit topic shift detection
    
    Args:
        vectors: sentence embeddings
        topic_shift_scores: pre-computed topic shift probabilities
    
    Returns:
        optimized boundaries
    """
    N = len(vectors)
    fib_nums = set(fibonacci_sequence(N)[2:])
    
    dp = [-float('inf')] * (N + 1)
    dp[0] = 0.0
    parent = [-1] * (N + 1)
    
    for i in range(1, N + 1):
        for length in range(2, i + 1):
            start = i - length
            
            # Fibonacci bonus (stronger weight)
            fib_bonus = 5.0 if length in fib_nums else 0.0
            
            # Internal cohesion
            coh = cohesion(vectors, start, i - 1)
            
            # Boundary quality with topic shift
            bound_quality = 0.0
            if start > 0:
                bound_cost = boundary_cost(vectors, start - 1)
                topic_shift = topic_shift_scores[start - 1]
                bound_quality = (bound_cost + topic_shift) / 2.0
            
            # Penalize very short or very long segments
            length_penalty = 0.0
            if length < 3:
                length_penalty = -2.0
            elif length > 21:  # Max reasonable Fibonacci
                length_penalty = -1.0
            
            # Total score
            segment_score = (2.0 * coh + 
                           fib_bonus + 
                           bound_quality + 
                           length_penalty)
            
            total_score = dp[start] + segment_score
            
            if total_score > dp[i]:
                dp[i] = total_score
                parent[i] = start
    
    # Backtrack
    boundaries = []
    current = N
    while current > 0:
        boundaries.append(current)
        current = parent[current]
    boundaries.append(0)
    boundaries.reverse()
    
    return boundaries, dp[N]
```

---

## 8️⃣ تطبيق كامل مع AGT / Complete AGT Application

```python
#!/usr/bin/env python3
"""
Fibonacci Discourse Segmentation - Complete System
Integrates with AGT Arabic NLP Pipeline
"""

import numpy as np
from sentence_transformers import SentenceTransformer
from typing import List, Tuple, Dict

# Import AGT modules
from masdar_semantic_enhanced_engine import MasdarSemanticEngine
from augmented_verb_forms_engine import MazidPatternsEngine


class FibonacciDiscourseSegmenter:
    """
    Complete Fibonacci-based discourse segmentation system
    """
    
    def __init__(self, model_name='paraphrase-multilingual-MiniLM-L12-v2'):
        self.encoder = SentenceTransformer(model_name)
        self.masdar_engine = MasdarSemanticEngine()
        self.mazid_engine = MazidPatternsEngine()
    
    def segment_discourse(self, sentences: List[str]) -> Dict:
        """
        Main segmentation pipeline
        """
        # 1. Encode sentences
        vectors = self.encoder.encode(sentences)
        
        # 2. Compute similarities
        sim_matrix = self._compute_similarity_matrix(vectors)
        
        # 3. Detect topic shifts
        topic_shifts = self._detect_topic_shifts(sim_matrix)
        
        # 4. Run Fibonacci segmentation
        boundaries, score = advanced_segmentation(vectors, topic_shifts)
        
        # 5. Create segments with metadata
        segments = self._create_segments(sentences, boundaries)
        
        # 6. Enrich with semantic analysis
        self._enrich_semantics(segments)
        
        return {
            'segments': segments,
            'boundaries': boundaries,
            'score': score,
            'num_segments': len(segments)
        }
    
    def _compute_similarity_matrix(self, vectors):
        """Compute pairwise similarities"""
        N = len(vectors)
        sim_matrix = np.zeros((N, N))
        for i in range(N):
            for j in range(N):
                sim_matrix[i, j] = cosine_similarity(vectors[i], vectors[j])
        return sim_matrix
    
    def _detect_topic_shifts(self, sim_matrix):
        """Detect topic boundaries using sliding window"""
        N = len(sim_matrix)
        shifts = np.zeros(N)
        
        window = 2
        for i in range(window, N - window):
            before = sim_matrix[i-window:i, i-window:i].mean()
            after = sim_matrix[i:i+window, i:i+window].mean()
            cross = sim_matrix[i-window:i, i:i+window].mean()
            
            # High shift if within-group similarity high but cross low
            shifts[i] = (before + after) / 2.0 - cross
        
        return shifts
    
    def _create_segments(self, sentences, boundaries):
        """Create segment objects"""
        segments = []
        fib_nums = set(fibonacci_sequence(len(sentences))[2:])
        
        for i in range(len(boundaries) - 1):
            start = boundaries[i]
            end = boundaries[i + 1]
            length = end - start
            
            segment = {
                'id': i + 1,
                'start': start,
                'end': end,
                'length': length,
                'is_fibonacci': length in fib_nums,
                'sentences': sentences[start:end],
                'dominant_domain': None,
                'augmented_forms': []
            }
            segments.append(segment)
        
        return segments
    
    def _enrich_semantics(self, segments):
        """Add semantic domain and morphological analysis"""
        for segment in segments:
            # Analyze semantic domains
            enrich_with_semantic_domains(segment, self.masdar_engine)
            
            # Analyze augmented forms
            analyze_augmented_forms_in_segments(segment, self.mazid_engine)


# Main execution
if __name__ == "__main__":
    segmenter = FibonacciDiscourseSegmenter()
    
    # Example discourse
    text = """
    الذكاء الاصطناعي يشهد تطورًا سريعًا. التعلم العميق من أهم فروعه.
    الشبكات العصبية تحاكي الدماغ. التدريب يحتاج بيانات ضخمة.
    التطبيقات متعددة في مجالات مختلفة. المستقبل واعد للمجال.
    """
    
    sentences = [s.strip() for s in text.strip().split('.') if s.strip()]
    
    result = segmenter.segment_discourse(sentences)
    
    print(f"Segmented into {result['num_segments']} segments")
    for seg in result['segments']:
        fib_mark = "✓" if seg['is_fibonacci'] else " "
        print(f"[{fib_mark}] Segment {seg['id']}: {seg['length']} sentences")
```

---

## 9️⃣ الخلاصة / Summary

### المزايا الرئيسية:

1. **تقسيم طبيعي**: يتبع الأنماط الطبيعية في الخطاب
2. **تماسك دلالي**: كل مقطع متماسك موضوعيًا
3. **بنية جمالية**: أطوال فيبوناتشي تعطي توازنًا بصريًا
4. **قابل للتطبيق**: خوارزمية DP فعّالة O(N² × F) حيث F عدد أرقام فيبوناتشي

### التكامل مع AGT:

- **المصادر الدلالية**: تصنيف الأفعال في كل مقطع
- **أوزان المزيد**: تحليل الأنماط الصرفية
- **DL₀**: تمثيل منطقي للمقاطع
- **الطبقات الست**: دمج التحليل الصوتي→الدلالي

### الاستخدامات المحتملة:

1. تلخيص النصوص الطويلة
2. تحليل بنية الخطاب الأكاديمي
3. تقسيم الكتب والمقالات
4. أنظمة الترجمة الآلية
5. محركات البحث الدلالي

---

## 🔟 المراجع / References

1. **Fibonacci in Nature**: Vogel, H. (1979). "A better way to construct the sunflower head"
2. **Discourse Segmentation**: Hearst, M. A. (1997). "TextTiling: Segmenting text into multi-paragraph subtopic passages"
3. **Semantic Similarity**: Reimers, N., & Gurevych, I. (2019). "Sentence-BERT: Sentence Embeddings using Siamese BERT-Networks"
4. **Arabic NLP**: Farghaly, A., & Shaalan, K. (2009). "Arabic natural language processing: Challenges and solutions"

---

**تاريخ الإنشاء**: 2025-12-03
**الإصدار**: 1.0
**المطورون**: AGT Arabic NLP Research Team
