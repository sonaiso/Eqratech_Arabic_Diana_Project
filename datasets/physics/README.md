# Physics Domain Dataset

## Overview

This dataset contains **500 samples** (350 train, 75 validation, 75 test) for evaluating the XAI Engine's physics domain processing capabilities with domain-specific CTE Gate conditions.

## Dataset Structure

```
physics/
├── train.jsonl          # 350 training samples (10 provided, 340 to generate)
├── validation.jsonl     # 75 validation samples (2 provided, 73 to generate)
├── test.jsonl          # 75 test samples (2 provided, 73 to generate)
├── README.md           # This file
└── statistics.json     # Dataset statistics (to be generated)
```

## Sample Format

Each sample is a JSON object with the following structure:

```json
{
  "id": "phys_train_001",
  "text": "السرعة تساوي 10 متر في الثانية",
  "subdomain": "mechanics",
  "measurement": {
    "value": 10,
    "unit": "m/s",
    "error_margin": 0.0
  },
  "cte_conditions": {
    "no_measurement_error": true,
    "no_unit_ambiguity": true,
    "no_experimental_contradiction": true,
    "no_observer_dependence": true,
    "no_scale_violation": true
  },
  "epistemic_level": "certain",
  "explanation": "قياس دقيق للسرعة بوحدات واضحة"
}
```

## Fields Description

- **id**: Unique identifier (`phys_{split}_{number}`)
- **text**: Arabic physics statement
- **subdomain**: Physics subdomain (`mechanics`, `thermodynamics`, `electromagnetism`, `optics`)
- **measurement**: Quantitative measurement data
  - `value`: Numerical value
  - `unit`: Physical unit
  - `error_margin`: Measurement error (0.0-1.0, where 0.05 = 5% error)
  - Additional fields as needed (direction, formula, etc.)
- **cte_conditions**: Domain-specific CTE Gate conditions (P1-P5)
  - `no_measurement_error`: Error ≤5% threshold
  - `no_unit_ambiguity`: Clear units specified
  - `no_experimental_contradiction`: No experimental conflict
  - `no_observer_dependence`: Frame-independent where needed
  - `no_scale_violation`: Valid in stated regime
- **epistemic_level**: `certain`, `probable`, `possible`, or `rejected`
- **explanation**: Arabic explanation of the epistemic level

## Subdomain Distribution

Target distribution for 500 samples:

| Subdomain | Train | Val | Test | Total |
|-----------|-------|-----|------|-------|
| Mechanics | 140 (40%) | 30 | 30 | 200 (40%) |
| Thermodynamics | 105 (30%) | 22 | 23 | 150 (30%) |
| Electromagnetism | 70 (20%) | 15 | 15 | 100 (20%) |
| Optics | 35 (10%) | 8 | 7 | 50 (10%) |
| **Total** | **350** | **75** | **75** | **500** |

## Epistemic Level Distribution

Target distribution:

- **Certain (يقين)**: 60% - Error ≤2%, all conditions pass
- **Probable (ظن)**: 25% - Error 2-5%, most conditions pass
- **Possible (احتمال)**: 10% - Error 5-10%, some conditions pass
- **Rejected (مرفوض)**: 5% - Error >10% or critical violation

## CTE Condition Validation

Each sample tests one or more of the 5 physics-specific CTE conditions:

### P1: NO_MEASUREMENT_ERROR (لا خطأ قياس)
- **Pass**: Error margin ≤5%
- **Fail**: Error margin >5%
- **Quantitative**: Actual error percentage tracked

### P2: NO_UNIT_AMBIGUITY (لا غموض في الوحدات)
- **Pass**: Units clearly specified and standard
- **Fail**: Ambiguous or missing units

### P3: NO_EXPERIMENTAL_CONTRADICTION (لا تعارض تجريبي)
- **Pass**: Consistent with experimental data
- **Fail**: Contradicts established experimental results
- **Severity**: HIGH (-0.15 penalty)

### P4: NO_OBSERVER_DEPENDENCE (لا اعتماد على المراقب)
- **Pass**: Frame-independent or frame explicitly stated
- **Fail**: Improper observer dependence

### P5: NO_SCALE_VIOLATION (لا انتهاك النطاق)
- **Pass**: Valid in stated physical regime
- **Fail**: Applied outside valid scale/regime
- **Severity**: HIGH (-0.15 penalty)

## Quality Criteria

Each sample must meet:

1. **Linguistic Quality**:
   - Grammatically correct Standard Arabic
   - Clear and unambiguous phrasing
   - Appropriate technical terminology

2. **Physics Accuracy**:
   - Physically correct or explicitly marked as incorrect
   - Proper units and magnitudes
   - Realistic measurement errors

3. **CTE Condition Coverage**:
   - Each condition tested multiple times
   - Mix of pass/fail scenarios
   - Quantitative tracking where applicable

4. **Domain Coverage**:
   - Balanced across 4 subdomains
   - Range of complexity levels
   - Both classical and modern physics

## Usage with XAI Engine

```python
from xai_engine import XAIEngine
from xai_engine.ctegate_domains import Domain, evaluate_with_domain
import json

# Load dataset
with open('datasets/physics/train.jsonl', 'r', encoding='utf-8') as f:
    samples = [json.loads(line) for line in f]

# Process with XAI Engine
engine = XAIEngine.for_physics()

for sample in samples:
    # Process through engine
    result = engine.process(sample['text'])
    
    # Validate with CTE Gate
    gate_result = evaluate_with_domain(
        {
            "measurement": sample['measurement'],
            "semantic_candidates": result.semantic,
            "relations": result.relations,
            "operators": result.measurement.operators
        },
        domain=Domain.PHYSICS
    )
    
    # Compare expected vs actual epistemic level
    expected = sample['epistemic_level']
    actual = gate_result.gate_level.value.lower()
    
    print(f"Sample {sample['id']}: Expected={expected}, Actual={actual}")
```

## Extension Guidelines

To extend this dataset to the full 500 samples:

1. **Maintain Distribution**: Follow subdomain and epistemic level distributions
2. **Vary Complexity**: Include simple to complex physics statements
3. **Cover Conditions**: Ensure each CTE condition is tested ≥50 times
4. **Avoid Leakage**: No overlapping content between train/val/test
5. **Quality Control**: Expert validation for physics accuracy
6. **Annotation**: Minimum 2 annotators, inter-annotator agreement ≥0.80

## Statistics

Current: 14 samples (10 train, 2 validation, 2 test)
Target: 500 samples (350 train, 75 validation, 75 test)
Completion: 2.8%

## References

- XAI Engine Documentation: `../xai_engine/README.md`
- CTE Gate Domains Guide: `../CTE_GATE_DOMAINS_GUIDE.md`
- Academic Publication Standards: `../ACADEMIC_PUBLICATION_STANDARDS_V2.md`

## License

Same as parent project.

## Contributors

Generated as part of the XAI Engine academic evaluation framework.
