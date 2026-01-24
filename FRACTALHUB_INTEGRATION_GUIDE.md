# FractalHub Dictionary v02 Integration Guide

**Complete integration between XAI Engine and FractalHub Dictionary v02**

Version: 1.0  
Status: Production Ready  
Compatible with: FractalHub v1.2, XAI Engine v1.0

---

## Table of Contents

1. [Overview](#overview)
2. [Installation](#installation)
3. [Quick Start](#quick-start)
4. [Core Concepts](#core-concepts)
5. [API Reference](#api-reference)
6. [Integration Patterns](#integration-patterns)
7. [Evidence Validation](#evidence-validation)
8. [Examples](#examples)
9. [Best Practices](#best-practices)

---

## Overview

The FractalHub Dictionary v02 integration provides seamless access to dictionary data for the XAI Engine, enabling:

- **Dictionary-based lexicon lookup** for form and semantic layers
- **Provenance tracking** with source types and confidence levels
- **Evidence-based validation** using attestation counts and references
- **Epistemic weight mapping** between FractalHub (يقين/ظن/شك) and CTE Gate (CERTAIN/PROBABLE/POSSIBLE)
- **Integration with CTE Gate** for evidence requirements validation

### Key Benefits

✅ **Evidence-Based Processing**: Every lexicon entry has provenance metadata  
✅ **Confidence Tracking**: Epistemic levels (يقين/ظن/شك) with numeric scores  
✅ **Source Transparency**: Track corpus, grammar books, expert validation  
✅ **CTE Gate Integration**: Validate evidence requirements automatically  
✅ **Anti-Hallucination**: No unsupported meanings - dictionary-backed only  

---

## Installation

### Prerequisites

```bash
# FractalHub module must be available
pip install pyyaml  # Required for dictionary loading
```

### Verify Installation

```python
from xai_engine.fractalhub_integration import is_fractalhub_available

if is_fractalhub_available():
    print("✅ FractalHub integration ready")
else:
    print("❌ FractalHub module not found")
```

---

## Quick Start

### Basic Usage

```python
from xai_engine.fractalhub_integration import load_fractalhub_integration

# Load dictionary v02
integration = load_fractalhub_integration(version="v02")

# Get lexicon entry
entry = integration.get_lexicon_entry("U:DIACRITIC:FATHA")

print(f"Form: {entry.form['arabic']}")  # "َ"
print(f"Name: {entry.form['name_ar']}")  # "فتحة"
print(f"Confidence: {entry.provenance.confidence}")  # "yaqin"
print(f"Score: {entry.provenance.confidence_score}")  # 1.0
```

### With XAI Engine

```python
from xai_engine import XAIEngine
from xai_engine.fractalhub_integration import load_fractalhub_integration

# Initialize both
engine = XAIEngine.for_language()
integration = load_fractalhub_integration()

# Process text
result = engine.process("محمد طالب")

# Validate lexicon entries using dictionary
lexicon_ids = ["U:DIACRITIC:FATHA", "U:DIACRITIC:KASRA"]
chain = integration.get_evidence_chain(lexicon_ids)

print(f"Average Confidence: {chain['avg_confidence']:.2f}")
```

---

## Core Concepts

### 1. Lexicon Entries

Every dictionary entry is a `LexiconEntry` with:

- **lexicon_id**: Unique identifier (e.g., "U:DIACRITIC:FATHA")
- **entry_type**: Type classification
  - `signifier_only`: Form without meaning (C0/C1 layer)
  - `signified_entity`: Form with meaning (C3 layer)
- **layer**: Processing layer (C0, C1, C2, C3)
- **form**: Form data (Arabic, unicode, IPA, names)
- **meaning**: Optional meaning data (for signified entities)
- **features**: Linguistic features list
- **provenance**: Evidence metadata
- **status**: Entry status (active, deprecated)

### 2. Provenance Metadata

Every entry has provenance information:

```python
ProvenanceInfo:
    source_type: "corpus" | "grammar_book" | "expert_validation" | "derived"
    confidence: "yaqin" | "zann" | "shakk"  # Arabic epistemic levels
    confidence_score: 0.0-1.0  # Numeric score
    attestation_count: int  # Corpus occurrences
    references: List[str]  # Source references
```

### 3. Epistemic Levels

FractalHub uses Arabic epistemic framework:

| Arabic | English | Score | XAI Gate Level |
|--------|---------|-------|----------------|
| يقين | Certainty | 1.0 | CERTAIN |
| ظن | Probability | 0.7 | PROBABLE |
| شك | Doubt | 0.4 | POSSIBLE |

### 4. Evidence Chains

Evidence chains aggregate data from multiple entries:

```python
chain = integration.get_evidence_chain(lexicon_ids)
# Returns:
{
    "entries": List[dict],  # All entry data
    "min_confidence": float,  # Minimum score
    "max_confidence": float,  # Maximum score
    "avg_confidence": float,  # Average score
    "total_attestations": int,  # Sum of attestations
    "sources": List[str]  # Unique source types
}
```

---

## API Reference

### FractalHubIntegration Class

#### Constructor

```python
FractalHubIntegration(
    dictionary_version: str = "v02",
    dictionary_path: Optional[str] = None
)
```

Initialize integration with dictionary v02 (default) or v01.

#### Core Methods

##### get_lexicon_entry()

```python
def get_lexicon_entry(lexicon_id: str) -> Optional[LexiconEntry]
```

Get lexicon entry by ID. Returns `None` if not found.

**Example:**
```python
entry = integration.get_lexicon_entry("U:DIACRITIC:FATHA")
if entry:
    print(entry.form["name_ar"])  # "فتحة"
```

##### search_by_form()

```python
def search_by_form(
    form_arabic: str,
    layer: Optional[str] = None
) -> List[LexiconEntry]
```

Search entries by Arabic form, optionally filtered by layer.

**Example:**
```python
entries = integration.search_by_form("َ")  # Find fatha
entries_c1 = integration.search_by_form("َ", layer="C1")  # C1 only
```

##### get_provenance()

```python
def get_provenance(lexicon_id: str) -> Optional[ProvenanceInfo]
```

Get provenance metadata for an entry.

**Example:**
```python
prov = integration.get_provenance("U:DIACRITIC:FATHA")
print(f"Confidence: {prov.confidence}")  # "yaqin"
print(f"Sources: {prov.references}")  # ["Sibawayh", "Al-Kitab"]
```

##### get_confidence_score()

```python
def get_confidence_score(lexicon_id: str) -> float
```

Get numeric confidence score (0.0-1.0).

**Example:**
```python
score = integration.get_confidence_score("U:DIACRITIC:FATHA")
print(score)  # 1.0
```

##### get_evidence_chain()

```python
def get_evidence_chain(lexicon_ids: List[str]) -> Dict[str, Any]
```

Generate aggregated evidence chain from multiple entries.

**Example:**
```python
chain = integration.get_evidence_chain([
    "U:DIACRITIC:FATHA",
    "U:DIACRITIC:KASRA"
])

print(f"Average: {chain['avg_confidence']:.2f}")  # 0.95
print(f"Sources: {chain['sources']}")  # ["grammar_book"]
```

##### validate_evidence()

```python
def validate_evidence(
    lexicon_ids: List[str],
    min_confidence: float = 0.7
) -> Tuple[bool, str]
```

Validate evidence meets minimum confidence threshold.

**Example:**
```python
valid, reason = integration.validate_evidence(
    ["U:DIACRITIC:FATHA"],
    min_confidence=0.7
)

if valid:
    print(f"✅ {reason}")  # "All evidence meets minimum confidence..."
```

##### get_dictionary_stats()

```python
def get_dictionary_stats() -> Dict[str, Any]
```

Get comprehensive dictionary statistics.

**Example:**
```python
stats = integration.get_dictionary_stats()
print(f"Total units: {stats['total_units']}")
print(f"C1 units: {stats['units_by_layer']['C1']}")
print(f"Yaqin: {stats['confidence_distribution']['yaqin']}")
```

### Convenience Functions

```python
# Quick integration loading
integration = load_fractalhub_integration(version="v02")

# Check availability
if is_fractalhub_available():
    # FractalHub module is available
    pass
```

---

## Integration Patterns

### Pattern 1: Form Layer Validation

Validate form layer tokens using dictionary:

```python
from xai_engine import XAIEngine
from xai_engine.fractalhub_integration import load_fractalhub_integration

engine = XAIEngine.for_language()
integration = load_fractalhub_integration()

# Process text
result = engine.process("محمد طالب")

# Validate each token has dictionary entry
for token in result.form.tokens:
    entries = integration.search_by_form(token.text)
    if entries:
        print(f"✅ {token.text}: {len(entries)} dictionary entries")
    else:
        print(f"⚠️  {token.text}: Not in dictionary")
```

### Pattern 2: Semantic Layer with Provenance

Enrich semantic candidates with provenance:

```python
# Get semantic candidates
candidates = result.semantic.sense_candidates

# Enrich with provenance
for candidate in candidates:
    if hasattr(candidate, 'lexicon_id'):
        prov = integration.get_provenance(candidate.lexicon_id)
        if prov:
            candidate.confidence = prov.confidence_score
            candidate.sources = prov.references
```

### Pattern 3: CTE Gate Evidence Validation

Integrate with CTE Gate for evidence requirements:

```python
from xai_engine.ctegate import TextualCertaintyGate

gate = TextualCertaintyGate()

# Extract lexicon IDs from analysis
lexicon_ids = extract_lexicon_ids(result)

# Validate evidence
chain = integration.get_evidence_chain(lexicon_ids)
valid, reason = integration.validate_evidence(lexicon_ids, min_confidence=0.7)

if not valid:
    # Evidence insufficient - downgrade gate level
    print(f"⚠️  Evidence insufficient: {reason}")
```

### Pattern 4: Domain-Specific Validation

Use confidence scores for domain-specific conditions:

```python
from xai_engine.ctegate_domains import DomainSpecificGate, Domain

gate = DomainSpecificGate(domain=Domain.LANGUAGE)

# Get evidence
chain = integration.get_evidence_chain(lexicon_ids)

# Check for NO_DIALECT_VARIATION
if chain['avg_confidence'] >= 0.9:
    # High confidence = standard Arabic
    pass_condition = True
else:
    # Lower confidence may indicate dialectal variation
    pass_condition = False
```

---

## Evidence Validation

### Evidence Requirements for CTE Gate Conditions

Different CTE Gate conditions have different evidence requirements:

#### NO_HOMONYMY (لا اشتراك)

**Requirement:** Single unambiguous meaning  
**Dictionary Check:**
- High attestation count (>100)
- Single entry for form
- High confidence (yaqin)

```python
entries = integration.search_by_form(word)
if len(entries) == 1 and entries[0].provenance.attestation_count > 100:
    # Likely no homonymy
    pass
```

#### NO_TRANSFER (لا نقل)

**Requirement:** Stable, non-transferred meaning  
**Dictionary Check:**
- Source type: corpus or grammar_book
- High attestation count
- Confidence: yaqin

```python
prov = integration.get_provenance(lexicon_id)
if prov.source_type in ["corpus", "grammar_book"] and prov.confidence == "yaqin":
    # Likely no semantic transfer
    pass
```

#### NO_METAPHOR (لا مجاز)

**Requirement:** Literal meaning only  
**Dictionary Check:**
- Entry type: signifier_only or literal signified
- No metaphorical features
- High confidence

```python
entry = integration.get_lexicon_entry(lexicon_id)
if "metaphor" not in entry.features and entry.provenance.confidence == "yaqin":
    # Likely literal meaning
    pass
```

### Confidence Threshold Guidelines

| CTE Gate Level | Min Confidence | Arabic Term | Use Case |
|----------------|----------------|-------------|----------|
| CERTAIN (يقين) | ≥0.95 | يقين | Gate10 pass |
| PROBABLE (ظن) | ≥0.70 | ظن | Gate5 pass |
| POSSIBLE (احتمال) | ≥0.40 | احتمال | Partial pass |
| REJECTED (مرفوض) | <0.40 | مرفوض | Gate fail |

---

## Examples

### Example 1: Basic Dictionary Access

```python
integration = load_fractalhub_integration()

# Get diacritic
entry = integration.get_lexicon_entry("U:DIACRITIC:FATHA")
print(f"Form: {entry.form['arabic']}")  # "َ"
print(f"Confidence: {entry.provenance.confidence}")  # "yaqin"
```

### Example 2: Evidence Chain

```python
lexicon_ids = ["U:DIACRITIC:FATHA", "U:DIACRITIC:KASRA"]
chain = integration.get_evidence_chain(lexicon_ids)

print(f"Average Confidence: {chain['avg_confidence']:.2f}")
print(f"Total Attestations: {chain['total_attestations']}")
```

### Example 3: Form Search

```python
# Search for all entries with fatha diacritic
entries = integration.search_by_form("َ")

for entry in entries:
    print(f"{entry.lexicon_id}: {entry.form['name_ar']}")
```

### Example 4: Dictionary Statistics

```python
stats = integration.get_dictionary_stats()

print(f"Total Units: {stats['total_units']}")
print(f"Yaqin Confidence: {stats['confidence_distribution']['yaqin']}")
```

For complete working examples, see:
- `xai_engine/examples_fractalhub_integration.py` (7 comprehensive examples)

---

## Best Practices

### 1. Cache Integration Instance

```python
# ✅ Good: Reuse integration
integration = load_fractalhub_integration()
for lexicon_id in ids:
    entry = integration.get_lexicon_entry(lexicon_id)

# ❌ Bad: Create new integration each time
for lexicon_id in ids:
    integration = load_fractalhub_integration()  # Expensive!
    entry = integration.get_lexicon_entry(lexicon_id)
```

### 2. Use Evidence Chains for Validation

```python
# ✅ Good: Aggregate evidence
chain = integration.get_evidence_chain(all_lexicon_ids)
avg_conf = chain['avg_confidence']

# ❌ Bad: Check individually
for lid in all_lexicon_ids:
    score = integration.get_confidence_score(lid)  # Multiple lookups
```

### 3. Handle Missing Entries Gracefully

```python
# ✅ Good: Check for None
entry = integration.get_lexicon_entry(lexicon_id)
if entry:
    use_entry(entry)
else:
    handle_missing(lexicon_id)

# ❌ Bad: Assume entry exists
entry = integration.get_lexicon_entry(lexicon_id)
print(entry.form)  # May raise AttributeError!
```

### 4. Map Confidence Appropriately

```python
# ✅ Good: Use numeric scores for thresholds
score = integration.get_confidence_score(lexicon_id)
if score >= 0.7:
    accept_as_probable()

# ✅ Good: Use string levels for display
prov = integration.get_provenance(lexicon_id)
print(f"Confidence: {prov.confidence}")  # "yaqin"
```

### 5. Leverage Provenance for Debugging

```python
# ✅ Good: Include provenance in traces
entry = integration.get_lexicon_entry(lexicon_id)
trace = {
    "lexicon_id": entry.lexicon_id,
    "confidence": entry.provenance.confidence,
    "sources": entry.provenance.references,
    "attestations": entry.provenance.attestation_count,
}
```

---

## See Also

- **CTE Gate Guide**: `CTE_GATE_GUIDE.md`
- **Domain-Specific CTE Guide**: `CTE_GATE_DOMAINS_GUIDE.md`
- **FractalHub README**: `FRACTALHUB_README.md`
- **XAI Engine Summary**: `XAI_ENGINE_SUMMARY.md`

---

**Status:** Production Ready ✅  
**Version:** 1.0  
**Last Updated:** 2026-01-24
