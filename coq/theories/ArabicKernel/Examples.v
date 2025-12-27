(*
  ArabicKernel.Examples
  
  Concrete examples and proofs for specific Arabic constructs
  
  This module demonstrates the formal verification system with
  real Arabic linguistic examples:
  - كَتَبَ (kataba) - "he wrote" - active trilateral verb
  - كُتِبَ (kutiba) - "it was written" - passive form
  - دَحْرَجَ (daHraja) - "he rolled" - quadrilateral verb
*)

From Coq Require Import Lists.List Bool.Bool Arith.Arith String.
Import ListNotations.

From ArabicKernel Require Import ArabicKernel.FractalCore.
From ArabicKernel Require Import ArabicKernel.Roles.
From ArabicKernel Require Import ArabicKernel.SlotsTable.
From ArabicKernel Require Import ArabicKernel.Morphology.
From ArabicKernel Require Import ArabicKernel.SyntacticIntegration.
From ArabicKernel Require Import ArabicKernel.C1C2C3_Theorem.

Module ArabicKernelExamples.
Import ArabicKernelFractalCore.
Import ArabicKernelRoles.
Import ArabicKernelSlotsTable.
Import ArabicKernelMorphology.
Import ArabicKernelSyntacticIntegration.
Import C1C2C3_Theorem.

(* ============================================
   EXAMPLE 1: كَتَبَ (kataba) - "he wrote"
   ============================================ *)

(* Root: ك-ت-ب (K-T-B) - writing *)
Definition root_KTB : Root := {|
  root_consonants := [C_Kaf; C_Ta; C_Ba];
  root_id := 1
|}.

(* Pattern: فَعَلَ (fa3ala) - past tense active *)
Definition pattern_fa3ala : Pattern := {|
  pattern_positions := [
    PP_ROOT_SLOT 1;     (* first root consonant *)
    PP_VOWEL V_Fatha;   (* short 'a' *)
    PP_ROOT_SLOT 2;     (* second root consonant *)
    PP_VOWEL V_Fatha;   (* short 'a' *)
    PP_ROOT_SLOT 3      (* third root consonant *)
  ];
  pattern_name := 100
|}.

(* Surface form: كَتَبَ with phonetic units *)
Definition surface_kataba : list PhoneticUnit := [
  PU_Consonant C_Kaf;
  PU_Vowel V_Fatha;
  PU_Consonant C_Ta;
  PU_Vowel V_Fatha;
  PU_Consonant C_Ba
].

(* Word: كَتَبَ *)
Definition word_kataba : MorphWord := {|
  word_root := root_KTB;
  word_pattern := pattern_fa3ala;
  word_surface := surface_kataba;
  word_id := 1001
|}.

(* Prove that كَتَبَ is morphologically wellformed *)
Theorem kataba_wellformed :
  word_wellformed word_kataba = true.
Proof.
  unfold word_wellformed.
  unfold word_kataba, root_KTB, pattern_fa3ala. simpl.
  unfold root_valid. simpl.
  unfold pattern_valid_for_root. simpl.
  unfold count_root_slots. simpl.
  reflexivity.
Qed.

(* Syntactic construct: كَتَبَ with AGENT and PATIENT *)
Definition construct_kataba : SyntacticConstruct := {|
  syn_word := word_kataba;
  syn_spec := make_active_verb_spec V1;
  syn_filled_roles := [AGENT; PATIENT]
|}.

(* Prove that كَتَبَ is syntactically valid *)
Theorem kataba_syntactically_valid :
  syntactic_construct_valid construct_kataba = true.
Proof.
  unfold syntactic_construct_valid.
  unfold construct_kataba. simpl.
  apply Bool.andb_true_iff.
  split.
  - (* Word wellformed *)
    apply kataba_wellformed.
  - (* Roles licensed *)
    unfold make_active_verb_spec, SlotsOf_base. simpl.
    unfold all_roles_licensed, role_is_filled. simpl.
    reflexivity.
Qed.

(* ============================================
   EXAMPLE 2: كُتِبَ (kutiba) - "it was written"
   ============================================ *)

(* Pattern: فُعِلَ (fu3ila) - past tense passive *)
Definition pattern_fu3ila : Pattern := {|
  pattern_positions := [
    PP_ROOT_SLOT 1;     (* first root consonant *)
    PP_VOWEL V_Damma;   (* short 'u' *)
    PP_ROOT_SLOT 2;     (* second root consonant *)
    PP_VOWEL V_Kasra;   (* short 'i' *)
    PP_ROOT_SLOT 3      (* third root consonant *)
  ];
  pattern_name := 101
|}.

(* Surface form: كُتِبَ *)
Definition surface_kutiba : list PhoneticUnit := [
  PU_Consonant C_Kaf;
  PU_Vowel V_Damma;
  PU_Consonant C_Ta;
  PU_Vowel V_Kasra;
  PU_Consonant C_Ba
].

(* Word: كُتِبَ *)
Definition word_kutiba : MorphWord := {|
  word_root := root_KTB;
  word_pattern := pattern_fu3ila;
  word_surface := surface_kutiba;
  word_id := 1002
|}.

(* Prove that كُتِبَ is morphologically wellformed *)
Theorem kutiba_wellformed :
  word_wellformed word_kutiba = true.
Proof.
  unfold word_wellformed.
  unfold word_kutiba, root_KTB, pattern_fu3ila. simpl.
  unfold root_valid. simpl.
  unfold pattern_valid_for_root. simpl.
  unfold count_root_slots. simpl.
  reflexivity.
Qed.

(* Syntactic construct: كُتِبَ with PATIENT (no explicit AGENT) *)
Definition construct_kutiba : SyntacticConstruct := {|
  syn_word := word_kutiba;
  syn_spec := make_passive_verb_spec V1;
  syn_filled_roles := [PATIENT]
|}.

(* Prove that كُتِبَ is syntactically valid *)
Theorem kutiba_syntactically_valid :
  syntactic_construct_valid construct_kutiba = true.
Proof.
  unfold syntactic_construct_valid.
  unfold construct_kutiba. simpl.
  apply Bool.andb_true_iff.
  split.
  - (* Word wellformed *)
    apply kutiba_wellformed.
  - (* Roles licensed *)
    unfold make_passive_verb_spec, SlotsOf_base. simpl.
    unfold all_roles_licensed, role_is_filled. simpl.
    reflexivity.
Qed.

(* ============================================
   EXAMPLE 3: دَحْرَجَ (daHraja) - "he rolled"
   Quadrilateral verb
   ============================================ *)

(* Root: د-ح-ر-ج (D-H-R-J) - rolling *)
Definition root_DHRJ : Root := {|
  root_consonants := [C_Dal; C_Ha_Huttiya; C_Ra; C_Jim];
  root_id := 2
|}.

(* Pattern for quadrilateral: فَعْلَلَ *)
Definition pattern_fa3lala : Pattern := {|
  pattern_positions := [
    PP_ROOT_SLOT 1;     (* د *)
    PP_VOWEL V_Fatha;
    PP_ROOT_SLOT 2;     (* ح *)
    PP_VOWEL V_Sukun;   (* ْ *)
    PP_ROOT_SLOT 3;     (* ر *)
    PP_VOWEL V_Fatha;
    PP_ROOT_SLOT 4      (* ج *)
  ];
  pattern_name := 200
|}.

(* Word: دَحْرَجَ *)
Definition word_dahraja : MorphWord := {|
  word_root := root_DHRJ;
  word_pattern := pattern_fa3lala;
  word_surface := [];  (* simplified *)
  word_id := 2001
|}.

(* Prove that دَحْرَجَ has valid quadrilateral root *)
Theorem dahraja_has_valid_root :
  root_valid root_DHRJ = true.
Proof.
  unfold root_valid, root_DHRJ. simpl.
  reflexivity.
Qed.

(* Prove it's quadrilateral *)
Theorem dahraja_is_quadrilateral :
  is_quadrilateral root_DHRJ = true.
Proof.
  unfold is_quadrilateral, root_DHRJ. simpl.
  reflexivity.
Qed.

(* ============================================
   EXAMPLE 4: Phonetic constraint demonstration
   ============================================ *)

(* Example: Valid syllable كَ (consonant + vowel) *)
Definition syllable_ka : list PhoneticUnit := [
  PU_Consonant C_Kaf;
  PU_Vowel V_Fatha
].

(* Prove it satisfies consonant-vowel pairing *)
Theorem syllable_ka_valid :
  no_consonant_without_vowel_ok syllable_ka = true.
Proof.
  unfold no_consonant_without_vowel_ok.
  simpl. reflexivity.
Qed.

(* ============================================
   EXAMPLE 5: Complete C1-C2-C3 demonstration
   ============================================ *)

(* Demonstrate the fractal pattern for كَتَبَ *)
Theorem kataba_demonstrates_fractal :
  (* Morphological level *)
  root_valid (word_root word_kataba) = true /\
  pattern_valid_for_root (word_pattern word_kataba) (word_root word_kataba) = true /\
  (* Syntactic level *)
  syntactic_construct_valid construct_kataba = true /\
  (* Phonetic level *)
  no_consonant_without_vowel_ok (word_surface word_kataba) = true.
Proof.
  split.
  - (* Root valid *)
    unfold word_kataba, root_KTB. simpl.
    unfold root_valid. simpl. reflexivity.
  - split.
    + (* Pattern valid for root *)
      unfold word_kataba, pattern_fa3ala, root_KTB. simpl.
      unfold pattern_valid_for_root, count_root_slots. simpl.
      reflexivity.
    + split.
      * (* Syntactic construct valid *)
        apply kataba_syntactically_valid.
      * (* Phonetic constraint satisfied *)
        unfold word_kataba, surface_kataba.
        unfold no_consonant_without_vowel_ok. simpl.
        reflexivity.
Qed.

(* ============================================
   META-THEOREM: All examples are verified
   ============================================ *)

(* This theorem shows that all our examples pass formal verification *)
Theorem all_examples_verified :
  word_wellformed word_kataba = true /\
  word_wellformed word_kutiba = true /\
  syntactic_construct_valid construct_kataba = true /\
  syntactic_construct_valid construct_kutiba = true /\
  root_valid root_DHRJ = true.
Proof.
  split. apply kataba_wellformed.
  split. apply kutiba_wellformed.
  split. apply kataba_syntactically_valid.
  split. apply kutiba_syntactically_valid.
  apply dahraja_has_valid_root.
Qed.

End ArabicKernelExamples.
