#!/bin/bash
# run_all_validations.sh - Master validation script for Phase 2 release
# Runs all Phase 2 validation checks and reports overall status

set -e  # Exit on first error

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

cd "$PROJECT_ROOT"

echo "======================================================================"
echo "Phase 2 Bridge Layer — Complete Validation Suite"
echo "======================================================================"
echo ""

# Track overall status
OVERALL_STATUS=0

# 1. SSOT Validation
echo "▶ Running SSOT Validation..."
if python3 scripts/phase2/validate_ssot.py; then
    echo "✅ SSOT Validation: PASS"
else
    echo "❌ SSOT Validation: FAIL"
    OVERALL_STATUS=1
fi
echo ""

# 2. Coq Module Compilation
echo "▶ Checking Coq Module Compilation..."
if cd coq && make -f ../Makefile clean > /dev/null 2>&1 && make -f ../Makefile all > /dev/null 2>&1; then
    echo "✅ Coq Compilation: PASS"
    cd ..
else
    echo "❌ Coq Compilation: FAIL"
    cd ..
    OVERALL_STATUS=1
fi
echo ""

# 3. Phase 1 Integrity Check
echo "▶ Running Phase 1 Integrity Check..."
if python3 scripts/phase2/verify_phase1_intact.py; then
    echo "✅ Phase 1 Integrity: PASS"
else
    echo "❌ Phase 1 Integrity: FAIL"
    OVERALL_STATUS=1
fi
echo ""

# 4. Python Bridge Functional Tests
echo "▶ Running Python Bridge Tests..."
if python3 scripts/phase2/test_phase2_bridge.py; then
    echo "✅ Python Bridge Tests: PASS"
else
    echo "❌ Python Bridge Tests: FAIL"
    OVERALL_STATUS=1
fi
echo ""

# 5. Documentation Check
echo "▶ Checking Documentation Completeness..."
REQUIRED_DOCS=(
    "docs/PHASE2_INTEGRATION_SPEC.md"
    "docs/PHASE2_RELEASE_CHECKLIST.md"
    "docs/ROADMAP.md"
    "ssot/fractalhub_dictionary_v04_1_awareness.yaml"
)

DOC_STATUS=0
for doc in "${REQUIRED_DOCS[@]}"; do
    if [ -f "$doc" ]; then
        echo "  ✓ $doc"
    else
        echo "  ✗ $doc (missing)"
        DOC_STATUS=1
    fi
done

if [ $DOC_STATUS -eq 0 ]; then
    echo "✅ Documentation: PASS"
else
    echo "❌ Documentation: FAIL (missing files)"
    OVERALL_STATUS=1
fi
echo ""

# 6. CI/CD Workflow Validation
echo "▶ Checking CI/CD Workflow Files..."
WORKFLOWS=(
    ".github/workflows/coq-verification.yml"
    ".github/workflows/full-integration.yml"
)

WORKFLOW_STATUS=0
for workflow in "${WORKFLOWS[@]}"; do
    if [ -f "$workflow" ]; then
        echo "  ✓ $workflow"
    else
        echo "  ✗ $workflow (missing)"
        WORKFLOW_STATUS=1
    fi
done

if [ $WORKFLOW_STATUS -eq 0 ]; then
    echo "✅ CI/CD Workflows: PASS"
else
    echo "❌ CI/CD Workflows: FAIL (missing files)"
    OVERALL_STATUS=1
fi
echo ""

# Final Summary
echo "======================================================================"
if [ $OVERALL_STATUS -eq 0 ]; then
    echo "🎯 Phase 2 Release: CERTIFIED STANDARD-READY"
    echo ""
    echo "✅ SSOT Validation: PASS"
    echo "✅ Coq Compilation: PASS"
    echo "✅ Phase 1 Integrity: PASS"
    echo "✅ Python Bridge: PASS"
    echo "✅ Documentation: PASS"
    echo "✅ CI/CD Integration: PASS"
    echo ""
    echo "Phase 2 Bridge Layer is ready for freeze and production use."
else
    echo "❌ Phase 2 Release: VALIDATION FAILED"
    echo ""
    echo "Please review the errors above and fix issues before freezing."
fi
echo "======================================================================"

exit $OVERALL_STATUS
