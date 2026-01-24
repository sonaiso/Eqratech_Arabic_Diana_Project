# Mathematics Domain Dataset

## Overview

This dataset contains **500 samples** (350 train, 75 validation, 75 test) for evaluating the XAI Engine's mathematics domain processing capabilities with domain-specific CTE Gate conditions.

## Dataset Structure

```
mathematics/
├── train.jsonl          # 350 training samples (10 provided, 340 to generate)
├── validation.jsonl     # 75 validation samples (2 provided, 73 to generate)
├── test.jsonl          # 75 test samples (2 provided, 73 to generate)
├── README.md           # This file
└── statistics.json     # Dataset statistics (to be generated)
```

## Sample Format

```json
{
  "id": "math_train_001",
  "text": "2 + 2 = 4",
  "subdomain": "arithmetic",
  "proof": {
    "completeness": 1.0,
    "steps": ["البديهية: جمع عددين صحيحين", "2 + 2 = 4 (حساب مباشر)"],
    "axioms_used": ["Peano arithmetic"]
  },
  "cte_conditions": {
    "no_axiom_violation": true,
    "no_proof_gap": true,
    "no_domain_restriction": true,
    "no_notation_ambiguity": true,
    "no_computational_error": true
  },
  "epistemic_level": "certain",
  "explanation": "عملية حسابية أساسية مثبتة"
}
```

## Fields Description

- **id**: Unique identifier (`math_{split}_{number}`)
- **text**: Arabic mathematical statement
- **subdomain**: Mathematics subdomain
- **proof**: Proof structure
  - `completeness`: 0.0-1.0 (0% to 100% complete)
  - `steps`: Proof steps in Arabic
  - `axioms_used`: Mathematical axioms/theorems used
- **cte_conditions**: Domain-specific CTE Gate conditions (M1-M5)
  - `no_axiom_violation`: No axiom violation
  - `no_proof_gap`: Complete logical chain (quantitative: completeness %)
  - `no_domain_restriction`: Valid across full domain
  - `no_notation_ambiguity`: Clear notation
  - `no_computational_error`: Verified computation
- **epistemic_level**: `certain`, `probable`, `possible`, or `rejected`
- **explanation**: Arabic explanation

## Subdomain Distribution

Target distribution for 500 samples:

| Subdomain | Train | Val | Test | Total |
|-----------|-------|-----|------|-------|
| Arithmetic | 70 (20%) | 15 | 15 | 100 (20%) |
| Algebra | 105 (30%) | 22 | 23 | 150 (30%) |
| Calculus | 70 (20%) | 15 | 15 | 100 (20%) |
| Geometry | 52 (15%) | 11 | 12 | 75 (15%) |
| Number Theory | 35 (10%) | 8 | 7 | 50 (10%) |
| Set Theory | 18 (5%) | 4 | 3 | 25 (5%) |
| **Total** | **350** | **75** | **75** | **500** |

## Epistemic Level Distribution

Target distribution based on proof completeness:

- **Certain (يقين)**: 65% - Completeness = 100%, all conditions pass
- **Probable (ظن)**: 20% - Completeness 80-99%, minor gaps
- **Possible (احتمال)**: 10% - Completeness 50-79%, significant gaps
- **Rejected (مرفوض)**: 5% - Completeness <50% or critical error

## CTE Condition Validation

### M1: NO_AXIOM_VIOLATION (لا انتهاك للبديهيات)
- **Pass**: Uses only stated axioms correctly
- **Fail**: Violates or assumes unstated axioms
- **Severity**: HIGH (-0.15 penalty)

### M2: NO_PROOF_GAP (لا فجوة في البرهان)
- **Pass**: Complete logical chain (100% completeness)
- **Fail**: Missing steps or logical jumps
- **Quantitative**: Proof completeness percentage tracked

### M3: NO_DOMAIN_RESTRICTION (لا تقييد المجال)
- **Pass**: Valid across stated domain
- **Fail**: Has unstated domain restrictions

### M4: NO_NOTATION_AMBIGUITY (لا غموض في الترميز)
- **Pass**: Clear, standard mathematical notation
- **Fail**: Ambiguous or non-standard notation

### M5: NO_COMPUTATIONAL_ERROR (لا خطأ حسابي)
- **Pass**: All computations verified correct
- **Fail**: Arithmetic or algebraic error
- **Severity**: HIGH (-0.15 penalty)

## Quality Criteria

1. **Mathematical Rigor**:
   - Correct mathematical statements
   - Valid proofs or explicitly marked as incomplete
   - Proper use of mathematical terminology

2. **Proof Quality**:
   - Clear logical structure
   - Appropriate level of detail
   - Cites relevant axioms/theorems

3. **Linguistic Quality**:
   - Grammatically correct Arabic
   - Standard mathematical terminology in Arabic
   - Clear and unambiguous phrasing

4. **CTE Coverage**:
   - Each condition tested ≥60 times
   - Range of completeness levels (0-100%)
   - Mix of elementary to advanced topics

## Usage with XAI Engine

```python
from xai_engine import XAIEngine
from xai_engine.ctegate_domains import Domain, evaluate_with_domain
import json

# Load dataset
with open('datasets/mathematics/train.jsonl', 'r', encoding='utf-8') as f:
    samples = [json.loads(line) for line in f]

# Process with XAI Engine
engine = XAIEngine.for_mathematics()

for sample in samples:
    result = engine.process(sample['text'])
    
    gate_result = evaluate_with_domain(
        {
            "proof_completeness": sample['proof']['completeness'],
            "axioms_used": sample['proof']['axioms_used'],
            "semantic_candidates": result.semantic,
            "relations": result.relations
        },
        domain=Domain.MATHEMATICS
    )
    
    # Evaluate proof completeness impact
    if sample['proof']['completeness'] < 1.0:
        print(f"{sample['id']}: Proof gap of {(1-sample['proof']['completeness'])*100:.0f}%")
```

## Extension Guidelines

1. **Coverage**: Include statements from all major math branches
2. **Difficulty Levels**: Elementary to advanced (balanced distribution)
3. **Proof Types**: Direct, contradiction, induction, construction
4. **Completeness Range**: Full spectrum from 0% to 100%
5. **Notation**: Use standard Arabic mathematical terminology
6. **Validation**: Expert mathematician review for correctness

## Statistics

Current: 14 samples (10 train, 2 validation, 2 test)
Target: 500 samples (350 train, 75 validation, 75 test)
Completion: 2.8%

## Notable Examples

- **Arithmetic**: Basic operations, properties
- **Algebra**: Equations, inequalities, functions
- **Calculus**: Limits, derivatives, integrals
- **Geometry**: Euclidean and non-Euclidean
- **Number Theory**: Primes, divisibility, famous theorems
- **Set Theory**: Cardinals, ordinals, Cantor's work

## References

- XAI Engine Documentation: `../xai_engine/README.md`
- CTE Gate Domains Guide: `../CTE_GATE_DOMAINS_GUIDE.md`
- Academic Publication Standards: `../ACADEMIC_PUBLICATION_STANDARDS_V2.md`

## License

Same as parent project.

## Contributors

Generated as part of the XAI Engine academic evaluation framework.
