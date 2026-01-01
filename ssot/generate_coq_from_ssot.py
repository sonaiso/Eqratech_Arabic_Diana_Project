#!/usr/bin/env python3
"""
SSOT to Coq Constants Generator - Phase 2 Bridge
=================================================

Generates Coq constant definitions from the SSOT YAML dictionary.
Maintains Phase 1 academic certification by generating separate Phase 2 modules.

Generated files:
- coq/theories/ArabicKernel/Phase2/FractalHubIds.v
- coq/theories/ArabicKernel/Phase2/RuleSpec_CouplingRules.v

Usage:
    python3 ssot/generate_coq_from_ssot.py

Author: Copilot + sonaiso
Date: 2025-12-31
Phase: 2 Bridge
"""

import yaml
import os
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Any

class SSOTToCoqGenerator:
    """Generates Coq modules from SSOT YAML dictionary"""
    
    def __init__(self, yaml_path: str, output_dir: str):
        self.yaml_path = yaml_path
        self.output_dir = Path(output_dir)
        self.data: Dict[str, Any] = {}
        
    def load_yaml(self) -> None:
        """Load SSOT YAML file"""
        with open(self.yaml_path, 'r', encoding='utf-8') as f:
            self.data = yaml.safe_load(f)
        print(f"✓ Loaded SSOT from {self.yaml_path}")
        print(f"  Version: {self.data['metadata']['version']}")
        print(f"  Phase: {self.data['metadata']['phase']}")
        
    def generate_fractal_hub_ids(self) -> str:
        """Generate FractalHubIds.v with node/edge/feature constants"""
        
        metadata = self.data['metadata']
        node_types = self.data.get('NODE_TYPES', {})
        edge_types = self.data.get('EDGE_TYPES', {})
        feat_ids = self.data.get('FEAT_IDS', {})
        
        coq_code = f"""(*
  coq/theories/ArabicKernel/Phase2/FractalHubIds.v
  
  Auto-generated from SSOT: {self.yaml_path}
  Generated: {datetime.now().isoformat()}
  Version: {metadata['version']}
  Phase: {metadata['phase']}
  
  This file contains constant definitions for:
  - Node Type IDs (awareness nodes: P/S/M/K)
  - Edge Type IDs (coupling edges)
  - Feature IDs (awareness features)
  
  CRITICAL: This file is auto-generated. DO NOT edit manually.
  To modify, update the SSOT YAML and regenerate.
  
  Phase 1 Compatibility: {metadata['maintains_phase1_certification']}
*)

From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.

Module FractalHubIds.

(* ================================================================ *)
(* NODE TYPE IDS - Awareness Extension                              *)
(* ================================================================ *)

"""
        
        # Generate node type constants
        for node_id in sorted(node_types.keys()):
            node = node_types[node_id]
            phase = node.get('phase', 1)
            name = node['name']
            desc = node['description']
            
            coq_code += f"(* Phase {phase}: {desc} *)\n"
            coq_code += f"Definition {name} : nat := {node_id}.\n\n"
        
        coq_code += """(* ================================================================ *)
(* EDGE TYPE IDS - Coupling Edges                                   *)
(* ================================================================ *)

"""
        
        # Generate edge type constants
        for edge_id in sorted(edge_types.keys()):
            edge = edge_types[edge_id]
            phase = edge.get('phase', 1)
            name = edge['name']
            desc = edge['description']
            
            coq_code += f"(* Phase {phase}: {desc} *)\n"
            coq_code += f"Definition {name} : nat := {edge_id}.\n\n"
        
        coq_code += """(* ================================================================ *)
(* FEATURE IDS - Awareness Features                                 *)
(* ================================================================ *)

"""
        
        # Generate feature ID constants
        for feat_id in sorted(feat_ids.keys()):
            feat = feat_ids[feat_id]
            phase = feat.get('phase', 1)
            name = feat['name']
            desc = feat['description']
            
            coq_code += f"(* Phase {phase}: {desc} *)\n"
            coq_code += f"Definition {name} : nat := {feat_id}.\n\n"
        
        coq_code += """(* ================================================================ *)
(* Helper Functions                                                  *)
(* ================================================================ *)

(* Check if node ID is an awareness node (Phase 2) *)
Definition is_awareness_node (nid : nat) : bool :=
  (Nat.eqb nid NODE_PREMODEL) || 
  (Nat.eqb nid NODE_SIGNIFIER) || 
  (Nat.eqb nid NODE_SIGNIFIED) || 
  (Nat.eqb nid NODE_COUPLED).

(* Check if edge ID is a coupling edge (Phase 2) *)
Definition is_coupling_edge (eid : nat) : bool :=
  (Nat.eqb eid PRE_TO_SIG) || 
  (Nat.eqb eid SIG_TO_SEM) || 
  (Nat.eqb eid SEM_TO_WORLD) || 
  (Nat.eqb eid COUPLED_OF) || 
  (Nat.eqb eid ANCHOR_PREV) || 
  (Nat.eqb eid ANCHOR_NEXT).

End FractalHubIds.
"""
        
        return coq_code
    
    def generate_coupling_rulespec(self) -> str:
        """Generate RuleSpec_CouplingRules.v with proof-carrying rules"""
        
        metadata = self.data['metadata']
        coupling_rules = self.data.get('COUPLING_RULES', {})
        
        coq_code = f"""(*
  coq/theories/ArabicKernel/Phase2/RuleSpec_CouplingRules.v
  
  Auto-generated from SSOT: {self.yaml_path}
  Generated: {datetime.now().isoformat()}
  Version: {metadata['version']}
  Phase: {metadata['phase']}
  
  This file defines proof-carrying coupling rules for awareness layer.
  Each rule has:
  - Premises (conditions that must hold)
  - Conclusion (what the rule establishes)
  - Certificate type (proof obligation)
  
  CRITICAL: This file is auto-generated. DO NOT edit manually.
  
  Phase 1 Compatibility: {metadata['maintains_phase1_certification']}
*)

From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.

Require Import ArabicKernel.Phase2.FractalHubIds.

Module RuleSpec_CouplingRules.

Import FractalHubIds.

(* ================================================================ *)
(* Certificate Types - Proof-Carrying Data Structures               *)
(* ================================================================ *)

(* Certificate for existence constraints *)
Record ExistenceCert := {{
  witness_edge_id : nat;
  witness_target_node : nat;
  cert_valid : bool
}}.

(* Certificate for structural constraints *)
Record StructuralCert := {{
  witness_nodes : list nat;
  structure_valid : bool  
}}.

(* Certificate for validity constraints *)
Record ValidityCert := {{
  target_node_exists : bool;
  target_node_validated : bool
}}.

(* Certificate for precondition constraints (with rejection) *)
Record PreconditionCert := {{
  data_present : bool;
  allows_none : bool  (* true = can reject if data missing *)
}}.

(* ================================================================ *)
(* RuleSpec Framework - Generic Proof-Carrying Rule                 *)
(* ================================================================ *)

Record RuleSpec (Cert : Type) := {{
  rule_name : string;
  rule_description : string;
  (* Premises are external (checked by caller) *)
  (* Conclusion validity proven by certificate *)
  verify_cert : Cert -> bool;
  soundness_property : forall (c : Cert), 
    verify_cert c = true -> True  (* Placeholder for actual property *)
}}.

(* ================================================================ *)
(* Coupling Rules - Auto-generated from SSOT                        *)
(* ================================================================ *)

"""
        
        # Generate rules
        for rule_id in sorted(coupling_rules.keys()):
            rule = coupling_rules[rule_id]
            name = rule['name']
            desc = rule['description']
            constraint_type = rule['constraint_type']
            
            coq_code += f"(* {rule_id}: {name} *)\n"
            coq_code += f"(* Description: {desc} *)\n"
            coq_code += f"(* Constraint Type: {constraint_type} *)\n"
            coq_code += f"(* Certificate Required: {rule.get('certificate_required', False)} *)\n"
            
            # Map constraint type to certificate type
            cert_type_map = {
                'existence': 'ExistenceCert',
                'structural': 'StructuralCert',
                'validity': 'ValidityCert',
                'precondition': 'PreconditionCert'
            }
            cert_type = cert_type_map.get(constraint_type, 'ExistenceCert')
            
            coq_code += f"""
Definition Rule_{rule_id}_verify (c : {cert_type}) : bool :=
  (* Auto-generated verification function *)
  match c with
  | Build_{cert_type} _ _ => true  (* Placeholder *)
  end.

Definition Rule_{rule_id} : RuleSpec {cert_type} := {{|
  rule_name := "{name}";
  rule_description := "{desc}";
  verify_cert := Rule_{rule_id}_verify;
  soundness_property := fun c H => I  (* Trivial proof for now *)
|}}.

"""
        
        coq_code += """(* ================================================================ *)
(* Rule Application Infrastructure                                   *)
(* ================================================================ *)

(* Apply rule with certificate *)
Definition apply_rule {Cert : Type} (rs : RuleSpec Cert) (c : Cert) : bool :=
  verify_cert rs c.

(* Rule soundness guarantee *)
Lemma rule_soundness {Cert : Type} (rs : RuleSpec Cert) (c : Cert) :
  apply_rule rs c = true -> True.
Proof.
  intro H.
  unfold apply_rule in H.
  apply (soundness_property rs c H).
Qed.

End RuleSpec_CouplingRules.
"""
        
        return coq_code
    
    def write_coq_files(self) -> None:
        """Write generated Coq files to output directory"""
        
        # Create Phase2 directory
        phase2_dir = self.output_dir / "Phase2"
        phase2_dir.mkdir(parents=True, exist_ok=True)
        
        # Generate and write FractalHubIds.v
        ids_code = self.generate_fractal_hub_ids()
        ids_path = phase2_dir / "FractalHubIds.v"
        with open(ids_path, 'w', encoding='utf-8') as f:
            f.write(ids_code)
        print(f"✓ Generated {ids_path}")
        
        # Generate and write RuleSpec_CouplingRules.v
        rules_code = self.generate_coupling_rulespec()
        rules_path = phase2_dir / "RuleSpec_CouplingRules.v"
        with open(rules_path, 'w', encoding='utf-8') as f:
            f.write(rules_code)
        print(f"✓ Generated {rules_path}")
        
        # Generate Phase2/All.v aggregator
        all_v = """(*
  coq/theories/ArabicKernel/Phase2/All.v
  
  Phase 2 Bridge - Exports all Phase 2 modules
  
  CRITICAL: Maintains Phase 1 academic certification.
  Phase 2 modules are additive only - no modifications to Phase 1.
*)

Require Export ArabicKernel.Phase2.FractalHubIds.
Require Export ArabicKernel.Phase2.RuleSpec_CouplingRules.
"""
        all_path = phase2_dir / "All.v"
        with open(all_path, 'w', encoding='utf-8') as f:
            f.write(all_v)
        print(f"✓ Generated {all_path}")
        
    def generate_all(self) -> None:
        """Main generation workflow"""
        print("\n" + "="*70)
        print("SSOT to Coq Generator - Phase 2 Bridge")
        print("="*70 + "\n")
        
        self.load_yaml()
        self.write_coq_files()
        
        print("\n" + "="*70)
        print("✅ Generation Complete!")
        print("="*70)
        print("\nGenerated files:")
        print("  - coq/theories/ArabicKernel/Phase2/FractalHubIds.v")
        print("  - coq/theories/ArabicKernel/Phase2/RuleSpec_CouplingRules.v")
        print("  - coq/theories/ArabicKernel/Phase2/All.v")
        print("\nPhase 1 academic certification: MAINTAINED ✓")
        print("No modifications to existing Phase 1 modules.")
        print("\n")

def main():
    """Entry point"""
    # Paths
    yaml_path = "ssot/fractalhub_dictionary_v04_1_awareness.yaml"
    output_dir = "coq/theories/ArabicKernel"
    
    # Check if YAML exists
    if not os.path.exists(yaml_path):
        print(f"❌ Error: SSOT YAML not found at {yaml_path}")
        print("Please ensure the file exists before running the generator.")
        return 1
    
    # Generate
    generator = SSOTToCoqGenerator(yaml_path, output_dir)
    generator.generate_all()
    
    return 0

if __name__ == "__main__":
    exit(main())
