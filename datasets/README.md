# Domain-Specific Datasets for XAI Engine Evaluation

## Overview

This directory contains domain-specific datasets for evaluating the XAI Engine with CTE Gate domain extensions. The datasets cover three scientific domains: **Physics**, **Mathematics**, and **Chemistry**.

## Directory Structure

```
datasets/
├── physics/
│   ├── train.jsonl (350 samples target, 10 provided)
│   ├── validation.jsonl (75 samples target, 2 provided)
│   ├── test.jsonl (75 samples target, 2 provided)
│   └── README.md
├── mathematics/
│   ├── train.jsonl (350 samples target, 10 provided)
│   ├── validation.jsonl (75 samples target, 2 provided)
│   ├── test.jsonl (75 samples target, 2 provided)
│   └── README.md
├── chemistry/
│   ├── train.jsonl (350 samples target, 10 provided)
│   ├── validation.jsonl (75 samples target, 2 provided)
│   ├── test.jsonl (75 samples target, 2 provided)
│   └── README.md
└── README.md (this file)
```

## Dataset Statistics

### Overall Summary

| Domain | Train | Val | Test | Total | Completion |
|--------|-------|-----|------|-------|------------|
| Physics | 10/350 | 2/75 | 2/75 | 14/500 | 2.8% |
| Mathematics | 10/350 | 2/75 | 2/75 | 14/500 | 2.8% |
| Chemistry | 10/350 | 2/75 | 2/75 | 14/500 | 2.8% |
| **Total** | **30/1050** | **6/225** | **6/225** | **42/1500** | **2.8%** |

### Current Status

✅ **Completed**:
- Dataset structure and format defined
- High-quality example samples for each domain
- Comprehensive README documentation
- Clear CTE condition mapping
- Usage examples and integration code

🚧 **In Progress**:
- Full dataset generation (1500 samples)
- Automated validation scripts
- Statistics generation
- Inter-annotator agreement measurement

## Domain-Specific CTE Conditions

### Physics (P1-P5)

1. **P1: NO_MEASUREMENT_ERROR** (لا خطأ قياس)
   - Threshold: Error ≤5%
   - Quantitative tracking: Actual error percentage

2. **P2: NO_UNIT_AMBIGUITY** (لا غموض في الوحدات)
   - Clear unit specification (m, kg, s, etc.)

3. **P3: NO_EXPERIMENTAL_CONTRADICTION** (لا تعارض تجريبي)
   - Severity: HIGH (-0.15 penalty)

4. **P4: NO_OBSERVER_DEPENDENCE** (لا اعتماد على المراقب)
   - Frame-independence or explicit frame

5. **P5: NO_SCALE_VIOLATION** (لا انتهاك النطاق)
   - Severity: HIGH (-0.15 penalty)

### Mathematics (M1-M5)

1. **M1: NO_AXIOM_VIOLATION** (لا انتهاك للبديهيات)
   - Severity: HIGH (-0.15 penalty)

2. **M2: NO_PROOF_GAP** (لا فجوة في البرهان)
   - Quantitative tracking: Proof completeness %

3. **M3: NO_DOMAIN_RESTRICTION** (لا تقييد المجال)
   - Valid across full stated domain

4. **M4: NO_NOTATION_AMBIGUITY** (لا غموض في الترميز)
   - Clear mathematical notation

5. **M5: NO_COMPUTATIONAL_ERROR** (لا خطأ حسابي)
   - Severity: HIGH (-0.15 penalty)

### Chemistry (C1-C5)

1. **C1: NO_STOICHIOMETRY_ERROR** (لا خطأ تفاعل كيميائي)
   - Severity: HIGH (-0.15 penalty)

2. **C2: NO_CONDITION_VIOLATION** (لا انتهاك الشروط)
   - T, P, catalyst specifications

3. **C3: NO_THERMODYNAMIC_IMPOSSIBILITY** (لا استحالة ثرموديناميكية)
   - Severity: HIGH (-0.15 penalty)

4. **C4: NO_MECHANISM_AMBIGUITY** (لا غموض في الآلية)
   - Clear reaction mechanism

5. **C5: NO_PHASE_AMBIGUITY** (لا غموض في الحالة)
   - Phase states (s, l, g, aq) specified

## Epistemic Level Distribution

Target distribution across all domains:

- **Certain (يقين)**: 65% - All conditions pass
- **Probable (ظن)**: 20% - Minor violations
- **Possible (احتمال)**: 10% - Moderate violations
- **Rejected (مرفوض)**: 5% - Critical violations

## Quality Assurance

### Sample Quality Criteria

Each sample must meet:

1. **Linguistic Quality**:
   - Grammatically correct Standard Arabic
   - Clear and unambiguous phrasing
   - Appropriate domain terminology

2. **Domain Accuracy**:
   - Scientifically correct statements
   - Proper notation and units
   - Realistic scenarios

3. **CTE Coverage**:
   - Each condition tested multiple times
   - Mix of pass/fail scenarios
   - Quantitative tracking where applicable

4. **Annotation Quality**:
   - Minimum 2 expert annotators per domain
   - Inter-annotator agreement ≥0.80
   - Conflict resolution process

### Data Split Integrity

- **No Leakage**: Zero overlapping content between train/val/test
- **N-gram Check**: No overlapping n-grams (n≥3) between splits
- **Balanced Distribution**: Maintained across all splits
- **Random Sampling**: Stratified by subdomain and epistemic level

## Usage

### Loading Datasets

```python
import json

def load_domain_dataset(domain, split='train'):
    """Load domain-specific dataset split."""
    path = f'datasets/{domain}/{split}.jsonl'
    samples = []
    with open(path, 'r', encoding='utf-8') as f:
        for line in f:
            samples.append(json.loads(line))
    return samples

# Load physics training data
physics_train = load_domain_dataset('physics', 'train')
print(f"Loaded {len(physics_train)} physics training samples")
```

### Evaluation with CTE Gate

```python
from xai_engine import XAIEngine
from xai_engine.ctegate_domains import Domain, evaluate_with_domain

# Process physics samples
engine = XAIEngine.for_physics()
samples = load_domain_dataset('physics', 'test')

results = []
for sample in samples:
    # Process through XAI Engine
    xai_result = engine.process(sample['text'])
    
    # Evaluate with domain-specific CTE Gate
    gate_result = evaluate_with_domain(
        {
            "measurement": sample.get('measurement', {}),
            "semantic_candidates": xai_result.semantic,
            "relations": xai_result.relations,
            "operators": xai_result.measurement.operators
        },
        domain=Domain.PHYSICS
    )
    
    results.append({
        'id': sample['id'],
        'expected': sample['epistemic_level'],
        'actual': gate_result.gate_level.value.lower(),
        'score': gate_result.gate_score,
        'violations': len(gate_result.domain_violations)
    })
    
# Calculate accuracy
correct = sum(1 for r in results if r['expected'] == r['actual'])
accuracy = correct / len(results)
print(f"Epistemic Level Accuracy: {accuracy:.2%}")
```

## Extension Plan

### Phase 1: Foundation (Complete ✅)
- ✅ Dataset structure defined
- ✅ Sample format specified
- ✅ High-quality examples created (42 samples)
- ✅ Documentation complete

### Phase 2: Expansion (Target: 1-2 months)
- 🚧 Generate full 1500 samples
- 🚧 Expert validation
- 🚧 Inter-annotator agreement measurement
- 🚧 Automated statistics generation

### Phase 3: Validation (Target: 2-3 weeks)
- ⏳ Baseline implementations
- ⏳ Ablation studies
- ⏳ Human evaluation
- ⏳ Publication preparation

## Generation Guidelines

### Automated Generation

For each domain, a generator script should:

1. **Maintain Distributions**:
   - Subdomain balance
   - Epistemic level balance
   - CTE condition coverage

2. **Ensure Quality**:
   - Scientific accuracy
   - Linguistic correctness
   - No duplication

3. **Track Metadata**:
   - Generation method
   - Validation status
   - Annotation history

4. **Prevent Leakage**:
   - Check n-gram overlap
   - Verify content uniqueness
   - Confirm split integrity

### Manual Validation

Expert validators should check:

1. **Domain Accuracy**: Scientific correctness
2. **CTE Condition Alignment**: Correct condition labels
3. **Epistemic Level**: Appropriate certainty assignment
4. **Linguistic Quality**: Grammar and terminology
5. **Completeness**: All required fields present

## Statistics Scripts

Generate comprehensive statistics:

```python
def generate_statistics(domain):
    """Generate dataset statistics."""
    stats = {
        'total_samples': 0,
        'subdomain_distribution': {},
        'epistemic_level_distribution': {},
        'cte_condition_coverage': {},
        'split_distribution': {}
    }
    
    for split in ['train', 'validation', 'test']:
        samples = load_domain_dataset(domain, split)
        stats['total_samples'] += len(samples)
        stats['split_distribution'][split] = len(samples)
        
        # Count subdomain distribution
        for sample in samples:
            subdomain = sample.get('subdomain', 'unknown')
            stats['subdomain_distribution'][subdomain] = \
                stats['subdomain_distribution'].get(subdomain, 0) + 1
            
            # Count epistemic levels
            level = sample.get('epistemic_level', 'unknown')
            stats['epistemic_level_distribution'][level] = \
                stats['epistemic_level_distribution'].get(level, 0) + 1
            
            # Count CTE condition violations
            for condition, passed in sample.get('cte_conditions', {}).items():
                if condition not in stats['cte_condition_coverage']:
                    stats['cte_condition_coverage'][condition] = {'pass': 0, 'fail': 0}
                if passed:
                    stats['cte_condition_coverage'][condition]['pass'] += 1
                else:
                    stats['cte_condition_coverage'][condition]['fail'] += 1
    
    return stats
```

## References

- **XAI Engine**: `../xai_engine/README.md`
- **CTE Gate Core**: `../CTE_GATE_GUIDE.md`
- **CTE Gate Domains**: `../CTE_GATE_DOMAINS_GUIDE.md`
- **Academic Standards**: `../ACADEMIC_PUBLICATION_STANDARDS_V2.md`
- **Scientific Evaluation**: `../SCIENTIFIC_EVALUATION.md`

## Citation

If you use these datasets in your research, please cite:

```bibtex
@dataset{xai_engine_domains_2026,
  title={Domain-Specific Datasets for XAI Engine with CTE Gate},
  author={Eqratech Arabic Diana Project},
  year={2026},
  note={Physics, Mathematics, and Chemistry domains with epistemic validation}
}
```

## License

Same as parent project.

## Contributors

Generated as part of the XAI Engine academic evaluation framework.

## Contact

For questions or contributions, please refer to the main project repository.
