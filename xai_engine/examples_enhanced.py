"""
Enhanced Reporting Example

Demonstrates the new explanatory report format with:
- Executive summary with failure analysis
- Layer-by-layer trace
- Before/After chains
- C1/C2/C3 governance
- Multiple output formats (human-readable, JSON, Markdown)
"""

import sys
sys.path.insert(0, '.')

from xai_engine import XAIEngine
from xai_engine.core import ReportGenerator
import json
import time


def example_enhanced_report():
    """
    Example: Generate enhanced explanatory report
    
    Shows the new structured output format with all components
    """
    print("=" * 80)
    print("ENHANCED EXPLANATORY REPORT EXAMPLE")
    print("=" * 80)
    
    # Create engine
    engine = XAIEngine.for_language()
    report_gen = ReportGenerator()
    
    # Process text
    start_time = time.time()
    result = engine.process("محمد طالب مجتهد")
    processing_time_ms = (time.time() - start_time) * 1000
    
    # Generate enhanced report
    report = report_gen.generate_report(result, processing_time_ms)
    
    # Display human-readable format
    print("\n" + "█" * 80)
    print("FORMAT 1: HUMAN-READABLE (Arabic/English)")
    print("█" * 80)
    print(report.to_human_readable())
    
    # Display markdown format
    print("\n\n" + "█" * 80)
    print("FORMAT 2: MARKDOWN")
    print("█" * 80)
    print(report.to_markdown())
    
    # Display JSON format (excerpt)
    print("\n\n" + "█" * 80)
    print("FORMAT 3: JSON (Structured Data)")
    print("█" * 80)
    json_output = json.dumps(report.to_dict(), ensure_ascii=False, indent=2)
    print(json_output[:1000] + "\n... (truncated)")
    
    return report


def example_failure_analysis():
    """
    Example: Analyze failure points
    
    Shows how the system identifies when/why judgments might fail
    """
    print("\n\n" + "=" * 80)
    print("FAILURE POINT ANALYSIS EXAMPLE")
    print("=" * 80)
    
    engine = XAIEngine.for_language()
    report_gen = ReportGenerator()
    
    # Process text
    result = engine.process("كل الناس")
    report = report_gen.generate_report(result, 0.0)
    
    print(f"\nInput: {result.input_text}")
    print(f"Judgment: {result.judgment.content}")
    print(f"\nIdentified Failure Points: {len(report.executive_summary.failure_points)}")
    
    for i, fp in enumerate(report.executive_summary.failure_points, 1):
        print(f"\n{i}. {fp.condition}")
        print(f"   Reason: {fp.reason}")
        print(f"   Impact: {fp.impact}")
        if fp.mitigation:
            print(f"   Mitigation: {fp.mitigation}")


def example_governance_annotation():
    """
    Example: C1/C2/C3 governance framework
    
    Shows how the system annotates with epistemic framework
    """
    print("\n\n" + "=" * 80)
    print("GOVERNANCE (C1/C2/C3) ANNOTATION EXAMPLE")
    print("=" * 80)
    
    report_gen = ReportGenerator()
    
    # Test all domains
    domains = [
        ("language", "العلم نور"),
        ("physics", "F = ma"),
        ("mathematics", "a² + b² = c²"),
        ("chemistry", "2H₂ + O₂ → 2H₂O"),
    ]
    
    for domain_type, text in domains:
        print(f"\n{'─' * 80}")
        print(f"Domain: {domain_type.upper()}")
        print(f"Input: {text}")
        print(f"{'─' * 80}")
        
        # Create domain-specific engine
        if domain_type == "language":
            engine = XAIEngine.for_language()
        elif domain_type == "physics":
            engine = XAIEngine.for_physics()
        elif domain_type == "mathematics":
            engine = XAIEngine.for_mathematics()
        elif domain_type == "chemistry":
            engine = XAIEngine.for_chemistry()
        
        # Process and generate report
        result = engine.process(text)
        report = report_gen.generate_report(result, 0.0)
        
        gov = report.governance
        print(f"\nC1 (Conceptual Framework):")
        print(f"  {gov.c1_framework}")
        print(f"\nC2 (Representation System):")
        print(f"  {gov.c2_representation}")
        print(f"\nC3 (Verification Rules):")
        print(f"  {gov.c3_verification}")
        
        if gov.epistemic_order:
            print(f"\nEpistemic Order (ترتيب الأدلة):")
            for i, order in enumerate(gov.epistemic_order, 1):
                print(f"  {i}. {order}")


def example_layer_trace_detail():
    """
    Example: Detailed layer-by-layer trace
    
    Shows complete processing trace with decisions
    """
    print("\n\n" + "=" * 80)
    print("DETAILED LAYER TRACE EXAMPLE")
    print("=" * 80)
    
    engine = XAIEngine.for_language()
    report_gen = ReportGenerator()
    
    result = engine.process("الكتاب في المكتبة")
    report = report_gen.generate_report(result, 0.0)
    
    print(f"\nInput: {result.input_text}")
    print(f"\nProcessing through {len(report.layer_traces)} layers:")
    
    for i, trace in enumerate(report.layer_traces, 1):
        print(f"\n{'═' * 80}")
        print(f"LAYER {i}: {trace.layer_name}")
        print(f"{'═' * 80}")
        print(f"\n📥 Input: {trace.input_summary}")
        
        print(f"\n⚙️  Processing Steps:")
        for step in trace.processing_steps:
            print(f"  • {step}")
        
        print(f"\n📤 Output: {trace.output_summary}")
        
        if trace.decisions_made:
            print(f"\n🎯 Key Decisions:")
            for decision in trace.decisions_made:
                print(f"  ✓ {decision['decision']}")
                print(f"    Reason: {decision['reason']}")
        
        if trace.alternatives_rejected:
            print(f"\n❌ Alternatives Rejected:")
            for alt in trace.alternatives_rejected:
                print(f"  • {alt['alternative']}")
                print(f"    Reason: {alt['reason']}")


def example_scope_and_validity():
    """
    Example: Scope definition and validity constraints
    
    Shows how judgments are scoped and constrained
    """
    print("\n\n" + "=" * 80)
    print("SCOPE & VALIDITY CONSTRAINTS EXAMPLE")
    print("=" * 80)
    
    engine = XAIEngine.for_language()
    report_gen = ReportGenerator()
    
    # Test with universal quantification
    result = engine.process("كل إنسان فان")
    report = report_gen.generate_report(result, 0.0)
    
    print(f"\nInput: {result.input_text}")
    print(f"Judgment: {result.judgment.content}")
    
    scope = report.executive_summary.scope
    print(f"\n📏 Scope Definition:")
    print(f"  • Validity Domain: {scope.validity_domain}")
    print(f"  • Quantification: {scope.quantification}")
    print(f"  • Temporal Scope: {scope.temporal_scope}")
    print(f"  • Spatial Scope: {scope.spatial_scope}")
    
    if scope.preconditions:
        print(f"\n✓ Preconditions:")
        for pre in scope.preconditions:
            print(f"  - {pre}")
    
    if scope.exclusions:
        print(f"\n✗ Exclusions:")
        for exc in scope.exclusions:
            print(f"  - {exc}")
    
    # Show epistemic weight with justification
    ew = report.executive_summary.epistemic_weight
    print(f"\n⚖️  Epistemic Weight:")
    print(f"  Level: {ew['level']}")
    print(f"  Confidence: {ew['confidence']:.2f}")
    print(f"  Justification: {ew['justification']}")


def example_complete_workflow():
    """
    Example: Complete workflow from input to formatted output
    
    Shows end-to-end processing with all components
    """
    print("\n\n" + "=" * 80)
    print("COMPLETE WORKFLOW EXAMPLE")
    print("=" * 80)
    
    # Setup
    engine = XAIEngine.for_language()
    report_gen = ReportGenerator()
    
    # Input
    text = "العلم نور والجهل ظلام"
    print(f"\n📝 Input Text: {text}")
    
    # Process
    print(f"\n⚙️  Processing through XAI engine...")
    start_time = time.time()
    result = engine.process(text)
    processing_time_ms = (time.time() - start_time) * 1000
    print(f"   ✓ Completed in {processing_time_ms:.2f}ms")
    
    # Generate report
    print(f"\n📊 Generating enhanced explanatory report...")
    report = report_gen.generate_report(result, processing_time_ms)
    print(f"   ✓ Report generated")
    
    # Summary
    print(f"\n📋 Report Summary:")
    print(f"   • Layers processed: {len(report.layer_traces)}")
    print(f"   • Failure points identified: {len(report.executive_summary.failure_points)}")
    print(f"   • Evidence items: {len(report.executive_summary.key_evidence)}")
    print(f"   • Constraints enforced: {len(report.governance.constraints)}")
    
    # Key findings
    print(f"\n🎯 Key Findings:")
    print(f"   • Judgment: {report.executive_summary.judgment_text}")
    print(f"   • Type: {report.executive_summary.judgment_type}")
    print(f"   • Confidence: {report.executive_summary.epistemic_weight['confidence']:.2f}")
    print(f"   • Scope: {report.executive_summary.scope.validity_domain}")
    
    # Export options
    print(f"\n💾 Available Export Formats:")
    print(f"   • Human-readable (Arabic/English)")
    print(f"   • JSON (structured data)")
    print(f"   • Markdown (documentation)")
    
    return report


if __name__ == "__main__":
    print("\n" + "🎯 ENHANCED XAI REPORTING SYSTEM".center(80))
    print("Architecture: locked_v1 with explanatory enhancements")
    print("Version: 1.0.0\n")
    
    # Run all examples
    try:
        report1 = example_enhanced_report()
        example_failure_analysis()
        example_governance_annotation()
        example_layer_trace_detail()
        example_scope_and_validity()
        report2 = example_complete_workflow()
        
        print("\n" + "=" * 80)
        print("✅ ALL EXAMPLES COMPLETED SUCCESSFULLY")
        print("=" * 80)
        
        print("\n🎉 Enhanced Reporting System Features:")
        print("  ✓ Executive summaries with failure analysis")
        print("  ✓ Detailed layer-by-layer traces")
        print("  ✓ Before/After chains")
        print("  ✓ C1/C2/C3 governance annotations")
        print("  ✓ Multiple output formats (human/JSON/Markdown)")
        print("  ✓ Scope and validity constraints")
        print("  ✓ Epistemic weight justifications")
        print("  ✓ Multi-domain support")
        
    except Exception as e:
        print(f"\n❌ Error: {e}")
        import traceback
        traceback.print_exc()
