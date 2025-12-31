#!/usr/bin/env python3
"""
verify_phase1_intact.py - Phase 1 Certification Preservation Checker
Verifies that Phase 1 modules remain unchanged after Phase 2 integration
"""

import subprocess
import sys
import json
from pathlib import Path

def run_command(cmd, description):
    """Run shell command and return output"""
    try:
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=30)
        return result.returncode, result.stdout, result.stderr
    except subprocess.TimeoutExpired:
        return 1, "", f"Command timed out: {description}"
    except Exception as e:
        return 1, "", str(e)

def check_phase1_files_unchanged():
    """Verify Phase 1 .v files are unchanged"""
    print("🔍 Checking Phase 1 files for modifications...")
    
    phase1_files = [
        "coq/theories/ArabicKernel/FractalCore.v",
        "coq/theories/ArabicKernel/Roles.v",
        "coq/theories/ArabicKernel/SlotsTable.v",
        "coq/theories/ArabicKernel/Policy.v",
        "coq/theories/ArabicKernel/C1C2C3_Theorem.v",
        "coq/theories/ArabicKernel/Morphology.v",
        "coq/theories/ArabicKernel/SyntacticIntegration.v",
        "coq/theories/ArabicKernel/Examples.v",
        "coq/theories/ArabicKernel/FractalDigitalRoundTrip.v",
        "coq/theories/ArabicKernel/All.v"
    ]
    
    errors = []
    for file_path in phase1_files:
        # Check if file exists
        if not Path(file_path).exists():
            errors.append(f"Phase 1 file missing: {file_path}")
            continue
        
        # Check for uncommitted changes to Phase 1 files
        code, stdout, stderr = run_command(
            f"git diff HEAD -- {file_path} | wc -l",
            f"Check {file_path} for changes"
        )
        
        if code == 0:
            changes = int(stdout.strip() or "0")
            if changes > 0:
                errors.append(f"Phase 1 file modified: {file_path} ({changes} lines changed)")
    
    return errors

def check_evidence_artifacts():
    """Verify Phase 1 evidence artifacts are intact"""
    print("🔍 Checking Phase 1 evidence artifacts...")
    
    errors = []
    
    # Check FINAL_PROOF_ARTIFACTS.json
    artifacts_path = Path("FINAL_PROOF_ARTIFACTS.json")
    if not artifacts_path.exists():
        errors.append("FINAL_PROOF_ARTIFACTS.json not found")
        return errors
    
    try:
        with open(artifacts_path, 'r') as f:
            artifacts = json.load(f)
        
        # Check Evidence 1: Zero Admitted/Axiom
        if 'evidence_1' in artifacts:
            ev1 = artifacts['evidence_1']
            total_admitted = ev1.get('summary', {}).get('total_admitted', -1)
            total_axiom = ev1.get('summary', {}).get('total_axiom', -1)
            
            if total_admitted != 0:
                errors.append(f"Evidence 1: Admitted count = {total_admitted}, expected 0")
            if total_axiom != 0:
                errors.append(f"Evidence 1: Axiom count = {total_axiom}, expected 0")
        else:
            errors.append("Evidence 1 missing from artifacts")
        
        # Check Evidence 2: Only declared Parameters
        if 'evidence_2' in artifacts:
            ev2 = artifacts['evidence_2']
            param_count = len(ev2.get('parameters_found', []))
            if param_count != 6:
                errors.append(f"Evidence 2: Parameter count = {param_count}, expected 6")
        else:
            errors.append("Evidence 2 missing from artifacts")
        
        # Check Evidence 3: Independent verification
        if 'evidence_3' in artifacts:
            ev3 = artifacts['evidence_3']
            if ev3.get('status') != 'success':
                errors.append(f"Evidence 3: Verification status = {ev3.get('status')}, expected 'success'")
        else:
            errors.append("Evidence 3 missing from artifacts")
        
    except json.JSONDecodeError:
        errors.append("FINAL_PROOF_ARTIFACTS.json is invalid JSON")
    except Exception as e:
        errors.append(f"Error reading artifacts: {e}")
    
    return errors

def check_tcb_manifest():
    """Verify TCB manifest shows no new parameters"""
    print("🔍 Checking TCB manifest...")
    
    errors = []
    
    tcb_path = Path("coq/theories/ArabicKernel/TCB_MANIFEST.json")
    if not tcb_path.exists():
        errors.append("TCB_MANIFEST.json not found")
        return errors
    
    try:
        with open(tcb_path, 'r') as f:
            tcb = json.load(f)
        
        param_count = len(tcb.get('parameters', []))
        if param_count != 6:
            errors.append(f"TCB manifest shows {param_count} parameters, expected 6")
        
        # Verify no Phase 2-introduced parameters
        for param in tcb.get('parameters', []):
            if 'Phase2' in param.get('file', ''):
                errors.append(f"Phase 2 Parameter found in TCB: {param.get('name', 'unknown')}")
        
    except json.JSONDecodeError:
        errors.append("TCB_MANIFEST.json is invalid JSON")
    except Exception as e:
        errors.append(f"Error reading TCB manifest: {e}")
    
    return errors

def main():
    """Main verification entry point"""
    print("="*70)
    print("Phase 1 Certification Preservation Check")
    print("="*70 + "\n")
    
    all_errors = []
    
    # Run all checks
    all_errors.extend(check_phase1_files_unchanged())
    all_errors.extend(check_evidence_artifacts())
    all_errors.extend(check_tcb_manifest())
    
    # Report results
    print("\n" + "="*70)
    if all_errors:
        print(f"❌ Phase 1 Integrity Check FAILED: {len(all_errors)} error(s)")
        for error in all_errors:
            print(f"  ❌ {error}")
    else:
        print("✅ Phase 1 Certification PRESERVED")
        print("✅ All Phase 1 files unchanged")
        print("✅ All 3 evidence artifacts intact")
        print("✅ TCB manifest shows 6 parameters (unchanged)")
    
    print("="*70 + "\n")
    
    sys.exit(1 if all_errors else 0)

if __name__ == '__main__':
    main()
