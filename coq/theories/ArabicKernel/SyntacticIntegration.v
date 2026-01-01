(*
  ArabicKernel.SyntacticIntegration
  
  Syntactic layer: integration of C2Spec with Roles and Morphology
  
  This module bridges morphology and semantics by connecting:
  - Morphological words (with patterns)
  - Syntactic specifications (C2Spec)
  - Semantic roles (from Roles module)
  
  Key theorem: A syntactically valid construction requires
  proper role licensing from C2Spec matching morphological structure.
*)

From Coq Require Import Lists.List Bool.Bool Arith.Arith.
Import ListNotations.

From ArabicKernel Require Import ArabicKernel.FractalCore.
From ArabicKernel Require Import ArabicKernel.Roles.
From ArabicKernel Require Import ArabicKernel.SlotsTable.
From ArabicKernel Require Import ArabicKernel.Morphology.
From ArabicKernel Require Import ArabicKernel.C1C2C3_Theorem.

Module ArabicKernelSyntacticIntegration.
Import ArabicKernelFractalCore.
Import ArabicKernelRoles.
Import ArabicKernelSlotsTable.
Import ArabicKernelMorphology.
Import C1C2C3_Theorem.

(* ============================================
   1) SYNTACTIC CONSTRUCT
   ============================================ *)

(* A syntactic construct combines morphological and semantic layers *)
Record SyntacticConstruct := {
  syn_word : MorphWord;        (* morphological realization *)
  syn_spec : C2Spec;           (* syntactic specification *)
  syn_filled_roles : list KRole  (* roles actually filled *)
}.

(* ============================================
   2) ROLE LICENSING
   ============================================ *)

(* Check if a role is in the list of filled roles *)
Fixpoint role_is_filled (r : KRole) (filled : list KRole) : bool :=
  match filled with
  | [] => false
  | h :: t => if role_eqb r h then true else role_is_filled r t
  end.

(* All filled roles must be licensed by C2Spec *)
Fixpoint all_roles_licensed (filled : list KRole) (licensed : list KRole) : bool :=
  match filled with
  | [] => true
  | r :: rest =>
      if role_is_filled r licensed
      then all_roles_licensed rest licensed
      else false
  end.

(* Syntactic construct validity: roles must be licensed *)
Definition syntactic_construct_valid (sc : SyntacticConstruct) : bool :=
  let word_valid := word_wellformed (syn_word sc) in
  let spec := syn_spec sc in
  let licensed := SlotsOf_base spec in
  let filled := syn_filled_roles sc in
  word_valid && all_roles_licensed filled licensed.

(* ============================================
   3) VERB CONSTRUCTIONS
   ============================================ *)

(* Helper: create C2Spec for active verb *)
Definition make_active_verb_spec (v : Valency) : C2Spec :=
  {| kind := C2_VERB; voice := ACTIVE; valency := v |}.

(* Helper: create C2Spec for passive verb *)
Definition make_passive_verb_spec (v : Valency) : C2Spec :=
  {| kind := C2_VERB; voice := PASSIVE; valency := v |}.

(* Active V1 verb must have AGENT and PATIENT *)
Definition active_v1_requires_agent_patient (roles : list KRole) : bool :=
  role_is_filled AGENT roles && role_is_filled PATIENT roles.

(* Passive V1 verb promotes PATIENT (no explicit AGENT) *)
Definition passive_v1_promotes_patient (roles : list KRole) : bool :=
  role_is_filled PATIENT roles.

(* ============================================
   4) SOUNDNESS THEOREMS
   ============================================ *)

(* Valid syntactic construct implies wellformed morphology *)
Theorem syntactic_valid_implies_morph_valid : forall sc,
  syntactic_construct_valid sc = true ->
  word_wellformed (syn_word sc) = true.
Proof.
  intros sc H.
  unfold syntactic_construct_valid in H.
  apply Bool.andb_true_iff in H.
  destruct H as [Hwf _].
  exact Hwf.
Qed.

(* Valid syntactic construct implies roles are licensed *)
Theorem syntactic_valid_implies_roles_licensed : forall sc,
  syntactic_construct_valid sc = true ->
  all_roles_licensed (syn_filled_roles sc) 
                     (SlotsOf_base (syn_spec sc)) = true.
Proof.
  intros sc H.
  unfold syntactic_construct_valid in H.
  apply Bool.andb_true_iff in H.
  destruct H as [_ Hr].
  exact Hr.
Qed.

(* Active V1 verb licenses AGENT, PATIENT, and TIME *)
Theorem active_v1_licenses_core_roles :
  let spec := make_active_verb_spec V1 in
  let licensed := SlotsOf_base spec in
  role_is_filled AGENT licensed = true /\
  role_is_filled PATIENT licensed = true /\
  role_is_filled TIME licensed = true.
Proof.
  simpl. unfold SlotsOf_base. simpl.
  unfold role_is_filled. simpl.
  split. reflexivity.
  split. reflexivity.
  reflexivity.
Qed.

(* Passive V1 verb licenses PATIENT and TIME (no explicit AGENT) *)
Theorem passive_v1_licenses_patient :
  let spec := make_passive_verb_spec V1 in
  let licensed := SlotsOf_base spec in
  role_is_filled PATIENT licensed = true /\
  role_is_filled TIME licensed = true.
Proof.
  simpl. unfold SlotsOf_base. simpl.
  unfold role_is_filled. simpl.
  split. reflexivity.
  reflexivity.
Qed.

(* ============================================
   5) INTEGRATION FRACTAL SOUNDNESS
   ============================================ *)

(* Main integration soundness theorem:
   A valid syntactic construct ensures:
   - Morphological validity (root + pattern wellformed)
   - Syntactic validity (C2Spec properly formed)
   - Semantic validity (roles properly licensed)
   
   This is the fractal pattern at syntactic level:
   - C1: Morphological constraints (root validity)
   - C2: Syntactic operator (C2Spec)
   - C3: Semantic output (role licensing) *)

Theorem Syntactic_Fractal_Soundness : forall sc,
  syntactic_construct_valid sc = true ->
  (* C1: Morphological layer valid *)
  root_valid (word_root (syn_word sc)) = true /\
  (* C2: Syntactic spec present *)
  (exists k v val, syn_spec sc = {| kind := k; voice := v; valency := val |}) /\
  (* C3: Roles properly licensed *)
  all_roles_licensed (syn_filled_roles sc) (SlotsOf_base (syn_spec sc)) = true.
Proof.
  intros sc H.
  split.
  - (* C1: Morphological validity *)
    apply syntactic_valid_implies_morph_valid in H.
    apply word_wellformed_sound in H.
    destruct H as [Hroot _].
    exact Hroot.
  - split.
    + (* C2: Spec exists *)
      destruct (syn_spec sc) as [k v val].
      exists k, v, val. reflexivity.
    + (* C3: Roles licensed *)
      apply syntactic_valid_implies_roles_licensed. exact H.
Qed.

End ArabicKernelSyntacticIntegration.
