#!/usr/bin/env python3
"""
test_phase2_bridge.py - Phase 2 Python Bridge Functional Tests
Tests Python bridge functionality for awareness layer and coupling rules
"""

import sys
from pathlib import Path

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent))

try:
    from coq_bridge_phase2 import (
        FractalHubIds,
        ExistenceCert, StructuralCert, ValidityCert, PreconditionCert,
        CouplingRules,
        create_awareness_node,
        create_coupling_edge,
        create_existence_cert,
        create_structural_cert,
        create_validity_cert,
        create_precondition_cert
    )
except ImportError as e:
    print(f"❌ Failed to import coq_bridge_phase2: {e}")
    sys.exit(1)

def test_fractal_hub_ids():
    """Test FractalHubIds constants are accessible"""
    print("🧪 Testing FractalHubIds constants...")
    
    errors = []
    
    # Test Node constants
    try:
        assert FractalHubIds.Node.NODE_PREMODEL == 16020
        assert FractalHubIds.Node.NODE_SIGNIFIER == 16021
        assert FractalHubIds.Node.NODE_SIGNIFIED == 16022
        assert FractalHubIds.Node.NODE_COUPLED == 16023
    except AssertionError as e:
        errors.append(f"Node constant mismatch: {e}")
    except AttributeError as e:
        errors.append(f"Node constant not found: {e}")
    
    # Test Edge constants
    try:
        assert FractalHubIds.Edge.PRE_TO_SIG == 20210
        assert FractalHubIds.Edge.SIG_TO_SEM == 20211
        assert FractalHubIds.Edge.SEM_TO_WORLD == 20212
        assert FractalHubIds.Edge.COUPLED_OF == 20213
        assert FractalHubIds.Edge.ANCHOR_PREV == 20214
        assert FractalHubIds.Edge.ANCHOR_NEXT == 20215
    except AssertionError as e:
        errors.append(f"Edge constant mismatch: {e}")
    except AttributeError as e:
        errors.append(f"Edge constant not found: {e}")
    
    # Test Feature constants
    try:
        assert hasattr(FractalHubIds.Feature, 'AWARE_PREMODEL')
        assert hasattr(FractalHubIds.Feature, 'AWARE_SIGNIFIER')
        assert hasattr(FractalHubIds.Feature, 'AWARE_SIGNIFIED')
        assert hasattr(FractalHubIds.Feature, 'AWARE_COUPLED')
    except AssertionError as e:
        errors.append(f"Feature constant missing: {e}")
    
    return errors

def test_certificate_types():
    """Test certificate type creation"""
    print("🧪 Testing certificate types...")
    
    errors = []
    
    try:
        # Test ExistenceCert
        cert1 = create_existence_cert(edge_id=1001, target_node=2001)
        assert cert1.edge_id == 1001
        assert cert1.target_node == 2001
        
        # Test StructuralCert
        cert2 = create_structural_cert(node_list=[1, 2, 3])
        assert cert2.node_list == [1, 2, 3]
        
        # Test ValidityCert
        cert3 = create_validity_cert(validated_nodes={1, 2})
        assert cert3.validated_nodes == {1, 2}
        
        # Test PreconditionCert
        cert4 = create_precondition_cert(data_present=True)
        assert cert4.data_present is True
        
    except Exception as e:
        errors.append(f"Certificate creation failed: {e}")
    
    return errors

def test_coupling_rules():
    """Test coupling rules registry"""
    print("🧪 Testing coupling rules...")
    
    errors = []
    
    try:
        # Check all 4 rules exist
        rules = [
            CouplingRules.SignifierRequiresSignified,
            CouplingRules.CouplingBindsThree,
            CouplingRules.AnchorPreservesC2,
            CouplingRules.WorldGroundingRequiresData
        ]
        
        for rule in rules:
            # Check rule has required attributes
            if not hasattr(rule, 'name'):
                errors.append(f"Rule missing 'name' attribute: {rule}")
            if not hasattr(rule, 'certificate_type'):
                errors.append(f"Rule missing 'certificate_type' attribute: {rule}")
            if not hasattr(rule, 'verify'):
                errors.append(f"Rule missing 'verify' method: {rule}")
        
        # Test verification (basic)
        cert = create_existence_cert(edge_id=1001, target_node=2001)
        result = CouplingRules.SignifierRequiresSignified.verify(cert)
        assert isinstance(result, bool)
        
    except Exception as e:
        errors.append(f"Coupling rules test failed: {e}")
    
    return errors

def test_node_creation():
    """Test awareness node creation helpers"""
    print("🧪 Testing node creation...")
    
    errors = []
    
    try:
        # Test creating all 4 awareness node types
        node_types = [
            FractalHubIds.Node.NODE_PREMODEL,
            FractalHubIds.Node.NODE_SIGNIFIER,
            FractalHubIds.Node.NODE_SIGNIFIED,
            FractalHubIds.Node.NODE_COUPLED
        ]
        
        for node_type in node_types:
            node = create_awareness_node(
                node_type=node_type,
                data={"test": "data"}
            )
            
            if not hasattr(node, 'node_id'):
                errors.append(f"Node missing node_id: type {node_type}")
            if not hasattr(node, 'node_type'):
                errors.append(f"Node missing node_type: type {node_type}")
            if node.node_type != node_type:
                errors.append(f"Node type mismatch: expected {node_type}, got {node.node_type}")
        
    except Exception as e:
        errors.append(f"Node creation failed: {e}")
    
    return errors

def main():
    """Run all Phase 2 bridge tests"""
    print("="*70)
    print("Phase 2 Python Bridge Functional Tests")
    print("="*70 + "\n")
    
    all_errors = []
    
    # Run all tests
    all_errors.extend(test_fractal_hub_ids())
    all_errors.extend(test_certificate_types())
    all_errors.extend(test_coupling_rules())
    all_errors.extend(test_node_creation())
    
    # Report results
    print("\n" + "="*70)
    if all_errors:
        print(f"❌ Phase 2 Bridge Tests FAILED: {len(all_errors)} error(s)")
        for error in all_errors:
            print(f"  ❌ {error}")
    else:
        print("✅ All Phase 2 Bridge Tests PASSED")
        print("✅ FractalHubIds constants: OK")
        print("✅ Certificate types: OK")
        print("✅ Coupling rules: OK")
        print("✅ Node creation: OK")
    
    print("="*70 + "\n")
    
    sys.exit(1 if all_errors else 0)

if __name__ == '__main__':
    main()
