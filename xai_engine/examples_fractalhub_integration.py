"""
Examples: FractalHub Dictionary v02 Integration with XAI Engine

Demonstrates:
    1. Loading dictionary and accessing entries
    2. Extracting provenance metadata
    3. Evidence chain generation
    4. Integration with CTE Gate
    5. Confidence validation
    6. Form-based search
    7. Dictionary statistics

Usage:
    python xai_engine/examples_fractalhub_integration.py
"""

import sys
from pathlib import Path

# Add parent directory to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from xai_engine.fractalhub_integration import (
    load_fractalhub_integration,
    is_fractalhub_available,
)


def example_1_basic_dictionary_access():
    """
    Example 1: Load dictionary and access basic entries.
    
    Demonstrates:
        - Loading FractalHub Dictionary v02
        - Accessing lexicon entries by ID
        - Viewing form and provenance data
    """
    print("="*80)
    print("Example 1: Basic Dictionary Access")
    print("="*80)
    
    if not is_fractalhub_available():
        print("❌ FractalHub module not available. Skipping example.")
        return
    
    # Load integration
    integration = load_fractalhub_integration(version="v02")
    print(f"✅ Loaded FractalHub Dictionary {integration.dictionary_version}")
    
    # Access a diacritic entry
    print("\n📖 Accessing Fatha Diacritic (فتحة):")
    entry = integration.get_lexicon_entry("U:DIACRITIC:FATHA")
    
    if entry:
        print(f"  Lexicon ID: {entry.lexicon_id}")
        print(f"  Type: {entry.entry_type}")
        print(f"  Layer: {entry.layer}")
        print(f"  Form (Arabic): {entry.form.get('arabic', 'N/A')}")
        print(f"  Form (Name AR): {entry.form.get('name_ar', 'N/A')}")
        print(f"  Form (Name EN): {entry.form.get('name_en', 'N/A')}")
        print(f"  Form (IPA): {entry.form.get('ipa', 'N/A')}")
        print(f"  Status: {entry.status}")
        print(f"  Features: {', '.join(entry.features)}")
    else:
        print("  Entry not found in dictionary")
    
    print("\n" + "="*80 + "\n")


def example_2_provenance_metadata():
    """
    Example 2: Extract and analyze provenance metadata.
    
    Demonstrates:
        - Provenance information extraction
        - Confidence levels (yaqin/zann/shakk)
        - Source types and references
        - Attestation counts
    """
    print("="*80)
    print("Example 2: Provenance Metadata")
    print("="*80)
    
    if not is_fractalhub_available():
        print("❌ FractalHub module not available. Skipping example.")
        return
    
    integration = load_fractalhub_integration()
    
    print("\n📊 Provenance Analysis for Fatha (فتحة):")
    prov = integration.get_provenance("U:DIACRITIC:FATHA")
    
    if prov:
        print(f"  Source Type: {prov.source_type}")
        print(f"  Confidence Level: {prov.confidence} ({prov.confidence_score:.1f})")
        
        # Map to Arabic terms
        confidence_ar = {
            "yaqin": "يقين (Certainty)",
            "zann": "ظن (Probability)",
            "shakk": "شك (Doubt)"
        }
        print(f"  Arabic Term: {confidence_ar.get(prov.confidence, 'N/A')}")
        
        print(f"  Attestation Count: {prov.attestation_count}")
        print(f"  References: {', '.join(prov.references)}")
        
        # Interpret confidence
        if prov.confidence_score >= 0.9:
            print(f"  ✅ High Confidence: Well-established entry")
        elif prov.confidence_score >= 0.6:
            print(f"  ⚠️  Moderate Confidence: Reasonably established")
        else:
            print(f"  ⚠️  Low Confidence: Requires validation")
    else:
        print("  Provenance not found")
    
    print("\n" + "="*80 + "\n")


def example_3_evidence_chain():
    """
    Example 3: Generate evidence chains for validation.
    
    Demonstrates:
        - Creating evidence chains from multiple entries
        - Calculating aggregate confidence metrics
        - Identifying evidence sources
    """
    print("="*80)
    print("Example 3: Evidence Chain Generation")
    print("="*80)
    
    if not is_fractalhub_available():
        print("❌ FractalHub module not available. Skipping example.")
        return
    
    integration = load_fractalhub_integration()
    
    print("\n🔗 Evidence Chain for Multiple Diacritics:")
    lexicon_ids = [
        "U:DIACRITIC:FATHA",
        "U:DIACRITIC:KASRA",
        "U:DIACRITIC:DAMMA",
    ]
    
    chain = integration.get_evidence_chain(lexicon_ids)
    
    print(f"  Total Entries: {len(chain['entries'])}")
    print(f"  Min Confidence: {chain['min_confidence']:.2f}")
    print(f"  Max Confidence: {chain['max_confidence']:.2f}")
    print(f"  Avg Confidence: {chain['avg_confidence']:.2f}")
    print(f"  Total Attestations: {chain['total_attestations']}")
    print(f"  Source Types: {', '.join(chain['sources'])}")
    
    # Assess chain quality
    avg_conf = chain['avg_confidence']
    if avg_conf >= 0.9:
        print(f"  ✅ Excellent Evidence: {avg_conf:.0%} average confidence")
    elif avg_conf >= 0.7:
        print(f"  ✅ Good Evidence: {avg_conf:.0%} average confidence")
    elif avg_conf >= 0.5:
        print(f"  ⚠️  Moderate Evidence: {avg_conf:.0%} average confidence")
    else:
        print(f"  ❌ Weak Evidence: {avg_conf:.0%} average confidence")
    
    print("\n" + "="*80 + "\n")


def example_4_confidence_validation():
    """
    Example 4: Validate evidence meets confidence requirements.
    
    Demonstrates:
        - Evidence validation against thresholds
        - Pass/fail scenarios
        - Validation reasons
    """
    print("="*80)
    print("Example 4: Confidence Validation")
    print("="*80)
    
    if not is_fractalhub_available():
        print("❌ FractalHub module not available. Skipping example.")
        return
    
    integration = load_fractalhub_integration()
    
    lexicon_ids = ["U:DIACRITIC:FATHA"]
    
    # Test different thresholds
    thresholds = [0.5, 0.7, 0.9, 1.0]
    
    print("\n🎯 Testing Different Confidence Thresholds:")
    for threshold in thresholds:
        valid, reason = integration.validate_evidence(lexicon_ids, min_confidence=threshold)
        
        status = "✅ PASS" if valid else "❌ FAIL"
        print(f"\n  Threshold: {threshold:.1f} ({threshold*100:.0f}%)")
        print(f"  Result: {status}")
        print(f"  Reason: {reason}")
    
    print("\n" + "="*80 + "\n")


def example_5_form_search():
    """
    Example 5: Search lexicon by Arabic form.
    
    Demonstrates:
        - Searching by Arabic text
        - Layer filtering
        - Handling multiple matches
    """
    print("="*80)
    print("Example 5: Form-Based Search")
    print("="*80)
    
    if not is_fractalhub_available():
        print("❌ FractalHub module not available. Skipping example.")
        return
    
    integration = load_fractalhub_integration()
    
    print("\n🔍 Searching for Fatha Diacritic (َ):")
    entries = integration.search_by_form("َ")
    
    print(f"  Found {len(entries)} matching entries")
    
    for i, entry in enumerate(entries, 1):
        print(f"\n  Match {i}:")
        print(f"    Lexicon ID: {entry.lexicon_id}")
        print(f"    Layer: {entry.layer}")
        print(f"    Type: {entry.entry_type}")
        print(f"    Name: {entry.form.get('name_en', 'N/A')}")
        print(f"    Confidence: {entry.provenance.confidence}")
    
    # Search with layer filter
    print("\n🔍 Searching in C1 Layer Only:")
    entries_c1 = integration.search_by_form("َ", layer="C1")
    print(f"  Found {len(entries_c1)} entries in C1 layer")
    
    print("\n" + "="*80 + "\n")


def example_6_dictionary_statistics():
    """
    Example 6: Analyze dictionary statistics.
    
    Demonstrates:
        - Getting dictionary metadata
        - Analyzing distribution by layer
        - Analyzing distribution by confidence
    """
    print("="*80)
    print("Example 6: Dictionary Statistics")
    print("="*80)
    
    if not is_fractalhub_available():
        print("❌ FractalHub module not available. Skipping example.")
        return
    
    integration = load_fractalhub_integration()
    
    stats = integration.get_dictionary_stats()
    
    print(f"\n📊 FractalHub Dictionary v{stats['version']} Statistics:")
    print(f"\n  Total Units: {stats['total_units']}")
    print(f"  Total Gates: {stats['total_gates']}")
    
    print(f"\n  📚 Units by Layer:")
    for layer, count in sorted(stats['units_by_layer'].items()):
        print(f"    {layer}: {count} units")
    
    print(f"\n  🏷️  Units by Type:")
    for utype, count in sorted(stats['units_by_type'].items()):
        print(f"    {utype}: {count} units")
    
    print(f"\n  🎯 Confidence Distribution:")
    conf_dist = stats['confidence_distribution']
    total = sum(conf_dist.values())
    
    for level in ['yaqin', 'zann', 'shakk']:
        count = conf_dist.get(level, 0)
        pct = (count / total * 100) if total > 0 else 0
        
        level_ar = {
            'yaqin': 'يقين (Certainty)',
            'zann': 'ظن (Probability)',
            'shakk': 'شك (Doubt)'
        }
        
        print(f"    {level_ar[level]}: {count} ({pct:.1f}%)")
    
    print("\n" + "="*80 + "\n")


def example_7_cte_gate_integration():
    """
    Example 7: Integration with CTE Gate for evidence validation.
    
    Demonstrates:
        - Using FractalHub evidence in CTE Gate
        - Mapping confidence levels
        - Evidence-based validation
    """
    print("="*80)
    print("Example 7: CTE Gate Integration")
    print("="*80)
    
    if not is_fractalhub_available():
        print("❌ FractalHub module not available. Skipping example.")
        return
    
    integration = load_fractalhub_integration()
    
    print("\n🚪 CTE Gate Evidence Validation:")
    print("\nScenario: Validating text using dictionary evidence")
    
    # Get lexicon entries for analysis
    lexicon_ids = ["U:DIACRITIC:FATHA", "U:DIACRITIC:KASRA"]
    
    print(f"\n  Lexicon IDs: {', '.join(lexicon_ids)}")
    
    # Get evidence chain
    chain = integration.get_evidence_chain(lexicon_ids)
    
    print(f"  Average Confidence: {chain['avg_confidence']:.2f}")
    
    # Map to CTE Gate levels
    avg_conf = chain['avg_confidence']
    
    if avg_conf >= 0.95:
        gate_level = "CERTAIN (يقين)"
        print(f"  ✅ CTE Gate Level: {gate_level}")
        print(f"  All conditions likely to pass")
    elif avg_conf >= 0.7:
        gate_level = "PROBABLE (ظن)"
        print(f"  ✅ CTE Gate Level: {gate_level}")
        print(f"  Gate5 conditions likely to pass")
    elif avg_conf >= 0.4:
        gate_level = "POSSIBLE (احتمال)"
        print(f"  ⚠️  CTE Gate Level: {gate_level}")
        print(f"  Some conditions may fail")
    else:
        gate_level = "REJECTED (مرفوض)"
        print(f"  ❌ CTE Gate Level: {gate_level}")
        print(f"  Multiple conditions likely to fail")
    
    # Evidence validation for specific conditions
    print(f"\n  🔍 Condition-Specific Validation:")
    
    # NO_HOMONYMY: High attestation count suggests no ambiguity
    attestations = chain['total_attestations']
    if attestations > 100:
        print(f"    ✅ NO_HOMONYMY: High attestation count ({attestations})")
    else:
        print(f"    ⚠️  NO_HOMONYMY: Low attestation count ({attestations})")
    
    # NO_TRANSFER: Established sources suggest stable meaning
    sources = chain['sources']
    if 'grammar_book' in sources or 'corpus' in sources:
        print(f"    ✅ NO_TRANSFER: Established sources ({', '.join(sources)})")
    else:
        print(f"    ⚠️  NO_TRANSFER: Limited sources ({', '.join(sources)})")
    
    print("\n" + "="*80 + "\n")


def run_all_examples():
    """Run all integration examples."""
    print("\n" + "="*80)
    print(" FractalHub Dictionary v02 Integration Examples")
    print("="*80 + "\n")
    
    if not is_fractalhub_available():
        print("❌ FractalHub module not available.")
        print("   Install FractalHub or ensure it's in the Python path.")
        return
    
    example_1_basic_dictionary_access()
    example_2_provenance_metadata()
    example_3_evidence_chain()
    example_4_confidence_validation()
    example_5_form_search()
    example_6_dictionary_statistics()
    example_7_cte_gate_integration()
    
    print("\n" + "="*80)
    print(" All Examples Completed Successfully! ✅")
    print("="*80 + "\n")


if __name__ == "__main__":
    run_all_examples()
