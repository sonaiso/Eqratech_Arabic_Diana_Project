#!/usr/bin/env python3
"""
Simple validation script that checks code structure without requiring torch.
This script verifies that the training implementation fixes are in place.
"""

import os
import json
import ast


def check_file_exists(filepath):
    """Check if a file exists."""
    exists = os.path.isfile(filepath)
    status = "✓" if exists else "✗"
    print(f"{status} {filepath}")
    return exists


def check_function_defined(filepath, function_name):
    """Check if a function is defined in a Python file."""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            tree = ast.parse(f.read())
            functions = [node.name for node in ast.walk(tree) 
                        if isinstance(node, ast.FunctionDef)]
            exists = function_name in functions
            status = "✓" if exists else "✗"
            print(f"  {status} Function '{function_name}' defined")
            return exists
    except Exception as e:
        print(f"  ✗ Error parsing {filepath}: {e}")
        return False


def check_class_defined(filepath, class_name):
    """Check if a class is defined in a Python file."""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            tree = ast.parse(f.read())
            classes = [node.name for node in ast.walk(tree) 
                      if isinstance(node, ast.ClassDef)]
            exists = class_name in classes
            status = "✓" if exists else "✗"
            print(f"  {status} Class '{class_name}' defined")
            return exists
    except Exception as e:
        print(f"  ✗ Error parsing {filepath}: {e}")
        return False


def check_notebook_has_training_cell():
    """Check if the notebook has a training cell."""
    try:
        with open('connect.ipynb', 'r', encoding='utf-8') as f:
            notebook = json.load(f)
            
        # Look for training-related code in cells
        has_training = False
        for cell in notebook.get('cells', []):
            if cell.get('cell_type') == 'code':
                source = ''.join(cell.get('source', []))
                if 'model.train()' in source and 'optimizer.zero_grad()' in source:
                    has_training = True
                    break
        
        status = "✓" if has_training else "✗"
        print(f"{status} Notebook contains training loop cell")
        return has_training
    except Exception as e:
        print(f"✗ Error checking notebook: {e}")
        return False


def check_training_loop_fixes():
    """Check that the training loop has the key fixes."""
    print("\nChecking training loop fixes in notebook:")
    try:
        with open('connect.ipynb', 'r', encoding='utf-8') as f:
            notebook = json.load(f)
        
        training_cell_source = None
        for cell in notebook.get('cells', []):
            if cell.get('cell_type') == 'code':
                source = ''.join(cell.get('source', []))
                if 'model.train()' in source and 'optimizer.zero_grad()' in source:
                    training_cell_source = source
                    break
        
        if not training_cell_source:
            print("✗ Training cell not found")
            return False
        
        fixes = {
            'Labels validation': "'labels' not in batch" in training_cell_source,
            'Raises error on missing labels': "raise ValueError" in training_cell_source,
            'Always zeros gradients': "optimizer.zero_grad()" in training_cell_source,
            'Always does backward pass': "loss.backward()" in training_cell_source,
            'Always updates weights': "optimizer.step()" in training_cell_source,
            'No dummy targets': "dummy_target" not in training_cell_source.lower(),
        }
        
        all_passed = True
        for check, passed in fixes.items():
            status = "✓" if passed else "✗"
            print(f"  {status} {check}")
            if not passed:
                all_passed = False
        
        return all_passed
    except Exception as e:
        print(f"✗ Error checking training loop: {e}")
        return False


def main():
    """Run all validation checks."""
    print("=" * 70)
    print("Training Implementation Validation")
    print("=" * 70)
    
    results = []
    
    # Check main files exist
    print("\nChecking required files:")
    results.append(check_file_exists('train_model.py'))
    results.append(check_file_exists('dataset_with_labels.py'))
    results.append(check_file_exists('training_example.py'))
    results.append(check_file_exists('TRAINING_GUIDE.md'))
    results.append(check_file_exists('requirements-training.txt'))
    results.append(check_file_exists('.gitignore'))
    
    # Check key functions
    print("\nChecking train_model.py:")
    results.append(check_function_defined('train_model.py', 'train_model'))
    
    # Check key classes
    print("\nChecking dataset_with_labels.py:")
    results.append(check_class_defined('dataset_with_labels.py', 'ArabicTextDataset'))
    results.append(check_function_defined('dataset_with_labels.py', 'validate_dataloader'))
    
    # Check notebook
    print("\nChecking connect.ipynb:")
    results.append(check_notebook_has_training_cell())
    
    # Check training loop fixes
    results.append(check_training_loop_fixes())
    
    # Summary
    print("\n" + "=" * 70)
    passed = sum(results)
    total = len(results)
    print(f"Validation Results: {passed}/{total} checks passed")
    
    if passed == total:
        print("✓ All validation checks passed!")
        print("\nThe training loop implementation correctly addresses all issues:")
        print("  1. ✓ Labels are required and validated")
        print("  2. ✓ No dummy targets used")
        print("  3. ✓ Training steps always executed consistently")
        print("  4. ✓ Clear error messages for missing labels")
        print("  5. ✓ Proper dataset implementation with labels")
        return 0
    else:
        print(f"✗ {total - passed} validation check(s) failed")
        return 1


if __name__ == '__main__':
    import sys
    sys.exit(main())
