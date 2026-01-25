# Chemistry Domain Dataset

## Overview

This dataset contains **500 samples** (350 train, 75 validation, 75 test) for evaluating the XAI Engine's chemistry domain processing capabilities with domain-specific CTE Gate conditions.

## Dataset Structure

```
chemistry/
├── train.jsonl          # 350 training samples (10 provided, 340 to generate)
├── validation.jsonl     # 75 validation samples (2 provided, 73 to generate)
├── test.jsonl          # 75 test samples (2 provided, 73 to generate)
├── README.md           # This file
└── statistics.json     # Dataset statistics (to be generated)
```

## Sample Format

```json
{
  "id": "chem_train_001",
  "text": "2H₂ + O₂ → 2H₂O",
  "subdomain": "general_chemistry",
  "reaction": {
    "balanced": true,
    "reactants": [
      {"formula": "H₂", "coefficient": 2},
      {"formula": "O₂", "coefficient": 1}
    ],
    "products": [
      {"formula": "H₂O", "coefficient": 2}
    ],
    "conditions": {"temperature": "ambient", "pressure": "1 atm"},
    "thermodynamics": {"feasible": true, "ΔG": -237.1, "unit": "kJ/mol"}
  },
  "cte_conditions": {
    "no_stoichiometry_error": true,
    "no_condition_violation": true,
    "no_thermodynamic_impossibility": true,
    "no_mechanism_ambiguity": true,
    "no_phase_ambiguity": true
  },
  "epistemic_level": "certain",
  "explanation": "تفاعل احتراق الهيدروجين متوازن وممكن"
}
```

## Fields Description

- **id**: Unique identifier (`chem_{split}_{number}`)
- **text**: Arabic chemical equation or statement
- **subdomain**: Chemistry subdomain
- **reaction**: Chemical reaction details
  - `balanced`: Boolean indicating stoichiometric balance
  - `reactants`: Array of reactant objects
  - `products`: Array of product objects
  - `conditions`: Reaction conditions (temperature, pressure, catalyst, etc.)
  - `thermodynamics`: Thermodynamic feasibility data
- **cte_conditions**: Domain-specific CTE Gate conditions (C1-C5)
  - `no_stoichiometry_error`: Balanced equations
  - `no_condition_violation`: Conditions specified
  - `no_thermodynamic_impossibility`: Thermodynamically feasible
  - `no_mechanism_ambiguity`: Clear reaction mechanism
  - `no_phase_ambiguity`: Phase states clearly defined
- **epistemic_level**: `certain`, `probable`, `possible`, or `rejected`
- **explanation**: Arabic explanation

## Subdomain Distribution

Target distribution for 500 samples:

| Subdomain | Train | Val | Test | Total |
|-----------|-------|-----|------|-------|
| General Chemistry | 140 (40%) | 30 | 30 | 200 (40%) |
| Organic Chemistry | 105 (30%) | 22 | 23 | 150 (30%) |
| Inorganic Chemistry | 70 (20%) | 15 | 15 | 100 (20%) |
| Physical Chemistry | 35 (10%) | 8 | 7 | 50 (10%) |
| **Total** | **350** | **75** | **75** | **500** |

## Epistemic Level Distribution

Target distribution:

- **Certain (يقين)**: 70% - Balanced, feasible, clear conditions, all pass
- **Probable (ظن)**: 15% - Minor ambiguity in conditions or mechanism
- **Possible (احتمال)**: 10% - Unclear conditions or mechanism
- **Rejected (مرفوض)**: 5% - Unbalanced or thermodynamically impossible

## CTE Condition Validation

### C1: NO_STOICHIOMETRY_ERROR (لا خطأ تفاعل كيميائي)
- **Pass**: Equation balanced (mass & charge conservation)
- **Fail**: Stoichiometric imbalance
- **Severity**: HIGH (-0.15 penalty) - violates fundamental chemistry law

### C2: NO_CONDITION_VIOLATION (لا انتهاك الشروط)
- **Pass**: All necessary conditions specified (T, P, catalyst, etc.)
- **Fail**: Missing or inappropriate conditions

### C3: NO_THERMODYNAMIC_IMPOSSIBILITY (لا استحالة ثرموديناميكية)
- **Pass**: ΔG indicates reaction is thermodynamically feasible
- **Fail**: Thermodynamically impossible under stated conditions
- **Severity**: HIGH (-0.15 penalty)

### C4: NO_MECHANISM_AMBIGUITY (لا غموض في الآلية)
- **Pass**: Reaction mechanism clear or standard
- **Fail**: Ambiguous or non-standard mechanism

### C5: NO_PHASE_AMBIGUITY (لا غموض في الحالة)
- **Pass**: Phase states (s, l, g, aq) clearly indicated
- **Fail**: Missing or ambiguous phase information

## Quality Criteria

1. **Chemical Accuracy**:
   - Correct chemical formulas
   - Balanced equations or explicitly marked as unbalanced
   - Realistic reaction conditions
   - Thermodynamically sound

2. **Notation Standards**:
   - Standard chemical formula notation
   - Proper use of subscripts and superscripts
   - Phase indicators where relevant
   - Arrows and equilibrium symbols

3. **Linguistic Quality**:
   - Grammatically correct Arabic
   - Standard chemistry terminology
   - Clear and unambiguous phrasing

4. **CTE Coverage**:
   - Each condition tested ≥60 times
   - Mix of balanced/unbalanced equations
   - Range of reaction types
   - Various thermodynamic scenarios

## Reaction Types Covered

- **Synthesis**: A + B → AB
- **Decomposition**: AB → A + B
- **Single Replacement**: A + BC → AC + B
- **Double Replacement**: AB + CD → AD + CB
- **Combustion**: Hydrocarbon + O₂ → CO₂ + H₂O
- **Redox**: Electron transfer reactions
- **Acid-Base**: Neutralization reactions
- **Precipitation**: Formation of solid product

## Usage with XAI Engine

```python
from xai_engine import XAIEngine
from xai_engine.ctegate_domains import Domain, evaluate_with_domain
import json

# Load dataset
with open('datasets/chemistry/train.jsonl', 'r', encoding='utf-8') as f:
    samples = [json.loads(line) for line in f]

# Process with XAI Engine
engine = XAIEngine.for_chemistry()

for sample in samples:
    result = engine.process(sample['text'])
    
    gate_result = evaluate_with_domain(
        {
            "reaction": sample['reaction'],
            "semantic_candidates": result.semantic,
            "relations": result.relations
        },
        domain=Domain.CHEMISTRY
    )
    
    # Check stoichiometric balance
    if not sample['reaction']['balanced']:
        print(f"{sample['id']}: Unbalanced equation - REJECTED")
    
    # Check thermodynamic feasibility
    if not sample['reaction']['thermodynamics']['feasible']:
        print(f"{sample['id']}: Thermodynamically impossible - REJECTED")
```

## Extension Guidelines

1. **Balance**: Include both balanced and unbalanced equations
2. **Complexity**: Elementary to advanced reactions
3. **Domains**: Cover all major chemistry branches
4. **Conditions**: Vary T, P, catalysts, solvents
5. **Thermodynamics**: Include ΔG, ΔH data where relevant
6. **Validation**: Expert chemist review for accuracy
7. **Phase States**: Always specify phases where relevant

## Statistics

Current: 14 samples (10 train, 2 validation, 2 test)
Target: 500 samples (350 train, 75 validation, 75 test)
Completion: 2.8%

## Notable Reactions Included

- **Water Formation**: 2H₂ + O₂ → 2H₂O
- **Haber Process**: N₂ + 3H₂ → 2NH₃
- **Combustion**: CH₄ + 2O₂ → CO₂ + 2H₂O
- **Neutralization**: HCl + NaOH → NaCl + H₂O
- **Electrolysis**: 2H₂O → 2H₂ + O₂
- **Precipitation**: AgNO₃ + NaCl → AgCl↓ + NaNO₃
- **Redox**: Fe + CuSO₄ → FeSO₄ + Cu
- **Decomposition**: CaCO₃ → CaO + CO₂

## References

- XAI Engine Documentation: `../xai_engine/README.md`
- CTE Gate Domains Guide: `../CTE_GATE_DOMAINS_GUIDE.md`
- Academic Publication Standards: `../ACADEMIC_PUBLICATION_STANDARDS_V2.md`

## License

Same as parent project.

## Contributors

Generated as part of the XAI Engine academic evaluation framework.
