(*
  coq/theories/ArabicKernel/Phase2/FractalHubIds.v
  
  Auto-generated from SSOT: ssot/fractalhub_dictionary_v04_1_awareness.yaml
  Generated: 2025-12-31T11:28:05.846419
  Version: 04.1
  Phase: Phase 2 Bridge
  
  This file contains constant definitions for:
  - Node Type IDs (awareness nodes: P/S/M/K)
  - Edge Type IDs (coupling edges)
  - Feature IDs (awareness features)
  
  CRITICAL: This file is auto-generated. DO NOT edit manually.
  To modify, update the SSOT YAML and regenerate.
  
  Phase 1 Compatibility: True
*)

From Coq Require Import Arith.Arith.
From Coq Require Import Lists.List.

Module FractalHubIds.

(* ================================================================ *)
(* NODE TYPE IDS - Awareness Extension                              *)
(* ================================================================ *)

(* Phase 1: Basic linguistic token *)
Definition NODE_TOKEN : nat := 16000.

(* Phase 1: Linguistic segment/phrase *)
Definition NODE_SEGMENT : nat := 16001.

(* Phase 1: Abstract concept (C1 layer) *)
Definition NODE_CONCEPT : nat := 16002.

(* Phase 1: Reality anchor (C2 layer) *)
Definition NODE_NUCLEUS : nat := 16003.

(* Phase 2: Pre-Signified (P) - Before semantic fixing *)
Definition NODE_PREMODEL : nat := 16020.

(* Phase 2: Signifier (S) - The linguistic sign (C3) *)
Definition NODE_SIGNIFIER : nat := 16021.

(* Phase 2: Signified (M) - The meaning/concept (C1) *)
Definition NODE_SIGNIFIED : nat := 16022.

(* Phase 2: Coupling (K) - Signifier+Signified with constraints *)
Definition NODE_COUPLED : nat := 16023.

(* ================================================================ *)
(* EDGE TYPE IDS - Coupling Edges                                   *)
(* ================================================================ *)

(* Phase 1: Sequential token connection *)
Definition NEXT_TOKEN : nat := 20000.

(* Phase 1: Sequential segment connection *)
Definition NEXT_SEGMENT : nat := 20001.

(* Phase 1: Language to Concept link *)
Definition C3_TO_C1 : nat := 20002.

(* Phase 1: Concept to Reality link *)
Definition C1_TO_C2 : nat := 20003.

(* Phase 2: P → S transition *)
Definition PRE_TO_SIG : nat := 20210.

(* Phase 2: S → M (Signifier to Meaning) *)
Definition SIG_TO_SEM : nat := 20211.

(* Phase 2: M → World (when measurements available) *)
Definition SEM_TO_WORLD : nat := 20212.

(* Phase 2: K → (P,S,M) relationship *)
Definition COUPLED_OF : nat := 20213.

(* Phase 2: S → P (C2 anchor to previous) *)
Definition ANCHOR_PREV : nat := 20214.

(* Phase 2: S → M (C2 anchor to next) *)
Definition ANCHOR_NEXT : nat := 20215.

(* ================================================================ *)
(* FEATURE IDS - Awareness Features                                 *)
(* ================================================================ *)

(* Phase 1: Root morpheme feature *)
Definition FEAT_ROOT : nat := 12000.

(* Phase 1: Morphological pattern feature *)
Definition FEAT_PATTERN : nat := 12001.

(* Phase 2: Pre-semantic awareness marker *)
Definition AWARE_PREMODEL : nat := 12101.

(* Phase 2: Signifier awareness marker *)
Definition AWARE_SIGNIFIER : nat := 12102.

(* Phase 2: Signified awareness marker *)
Definition AWARE_SIGNIFIED : nat := 12103.

(* Phase 2: Coupling awareness marker *)
Definition AWARE_COUPLED : nat := 12104.

(* Phase 2: C2 anchoring feature (prev/next) *)
Definition COUPLING_ANCHOR_C2 : nat := 12110.

(* Phase 2: Immediate coupling (radius=1) *)
Definition COUPLING_RADIUS_1 : nat := 12111.

(* Phase 2: Extended coupling (radius>1) *)
Definition COUPLING_RADIUS_N : nat := 12112.

(* ================================================================ *)
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
