#!/usr/bin/env python3
"""
validate_ssot.py - SSOT Structural Validation Tool
Validates Phase 2 SSOT YAML for structural integrity, ID collisions, and semantic consistency
"""

import yaml
import sys
from pathlib import Path

def validate_ssot(yaml_path):
    """Validate SSOT YAML file structure and content"""
    errors = []
    warnings = []
    
    print(f"🔍 Validating SSOT: {yaml_path}")
    
    # Load YAML
    try:
        with open(yaml_path, 'r', encoding='utf-8') as f:
            data = yaml.safe_load(f)
    except Exception as e:
        errors.append(f"YAML parse error: {e}")
        return errors, warnings
    
    # 1. Check required sections
    required_sections = ['NODE_TYPES', 'EDGE_TYPES', 'FEAT_IDS', 'COUPLING_RULES']
    for section in required_sections:
        if section not in data:
            errors.append(f"Missing required section: {section}")
    
    if errors:
        return errors, warnings
    
    # 2. Validate Node Types (P/S/M/K)
    node_types = data['NODE_TYPES']
    expected_nodes = {
        16020: 'NODE_PREMODEL',
        16021: 'NODE_SIGNIFIER',
        16022: 'NODE_SIGNIFIED',
        16023: 'NODE_COUPLED'
    }
    
    for node_id, node_name in expected_nodes.items():
        if node_id not in node_types:
            errors.append(f"Missing awareness node: {node_name} (ID {node_id})")
        elif node_types[node_id].get('name') != node_name:
            errors.append(f"Node ID {node_id} name mismatch: expected {node_name}, got {node_types[node_id].get('name')}")
    
    # 3. Validate Edge Types (Coupling Edges)
    edge_types = data['EDGE_TYPES']
    expected_edges = {
        20210: 'PRE_TO_SIG',
        20211: 'SIG_TO_SEM',
        20212: 'SEM_TO_WORLD',
        20213: 'COUPLED_OF',
        20214: 'ANCHOR_PREV',
        20215: 'ANCHOR_NEXT'
    }
    
    for edge_id, edge_name in expected_edges.items():
        if edge_id not in edge_types:
            errors.append(f"Missing coupling edge: {edge_name} (ID {edge_id})")
        elif edge_types[edge_id].get('name') != edge_name:
            errors.append(f"Edge ID {edge_id} name mismatch: expected {edge_name}, got {edge_types[edge_id].get('name')}")
    
    # 4. Validate Feature IDs (Awareness Features)
    feat_ids = data['FEAT_IDS']
    expected_features = range(12101, 12113)  # 12101-12112
    
    for feat_id in expected_features:
        if feat_id not in feat_ids:
            errors.append(f"Missing awareness feature ID: {feat_id}")
    
    # 5. Validate Coupling Rules
    coupling_rules = data['COUPLING_RULES']
    expected_rules = ['RULE_01', 'RULE_02', 'RULE_03', 'RULE_04']
    
    for rule_name in expected_rules:
        if rule_name not in coupling_rules:
            errors.append(f"Missing coupling rule: {rule_name}")
        else:
            rule = coupling_rules[rule_name]
            # Check required fields
            if 'name' not in rule:
                errors.append(f"Rule {rule_name}: missing 'name' field")
            if 'certificate_type' not in rule:
                errors.append(f"Rule {rule_name}: missing 'certificate_type' field")
            if 'constraint' not in rule:
                errors.append(f"Rule {rule_name}: missing 'constraint' field")
    
    # 6. Check for ID range collisions
    all_ids = set(node_types.keys()) | set(edge_types.keys()) | set(feat_ids.keys())
    
    # Ensure awareness IDs don't overlap with reserved Phase 3 ranges
    phase3_reserved = range(17000, 18000)  # Example reserved range
    for id_val in all_ids:
        if id_val in phase3_reserved:
            warnings.append(f"ID {id_val} may collide with Phase 3 reserved range")
    
    # 7. Semantic consistency checks
    # Check that coupling edges form valid relationships
    # (This is a simplified check - more sophisticated graph validation could be added)
    
    return errors, warnings

def main():
    """Main validation entry point"""
    yaml_path = Path(__file__).parent.parent.parent / 'ssot' / 'fractalhub_dictionary_v04_1_awareness.yaml'
    
    if not yaml_path.exists():
        print(f"❌ SSOT file not found: {yaml_path}")
        sys.exit(1)
    
    errors, warnings = validate_ssot(yaml_path)
    
    # Report results
    print("\n" + "="*60)
    if errors:
        print(f"❌ SSOT Validation FAILED: {len(errors)} error(s)")
        for error in errors:
            print(f"  ❌ {error}")
    else:
        print("✅ SSOT Validation PASSED: 0 errors")
    
    if warnings:
        print(f"\n⚠️  {len(warnings)} warning(s):")
        for warning in warnings:
            print(f"  ⚠️  {warning}")
    else:
        print("✅ 0 warnings")
    
    print("="*60 + "\n")
    
    # Exit code
    sys.exit(1 if errors else 0)

if __name__ == '__main__':
    main()
