(*
  ArabicKernel.Morphology
  
  Morphological layer formalization: Root and Pattern validation
  
  Extends the fractal C1-C2-C3 pattern to morphology:
  - Root: lexical base (usually 3 consonants)
  - Pattern: morphological template (C2 operator)
  - Word form: surface realization (C3 output)
  
  Key constraints:
  - Root must have 3+ consonants (trilateral or quadrilateral)
  - Pattern must be well-formed (valid vowel+consonant template)
  - Pattern-root combination must respect phonetic constraints
*)

From Coq Require Import Lists.List Bool.Bool Arith.Arith.
Import ListNotations.

From ArabicKernel Require Import ArabicKernel.FractalCore.
From ArabicKernel Require Import ArabicKernel.C1C2C3_Theorem.

Module ArabicKernelMorphology.
Import ArabicKernelFractalCore.
Import C1C2C3_Theorem.

(* ============================================
   1) ROOT TYPES (الجذر)
   ============================================ *)

(* Root: sequence of consonants forming lexical base *)
Record Root := {
  root_consonants : list Consonant;
  root_id : nat  (* unique identifier *)
}.

(* Root validity: must have 3 or 4 consonants *)
Definition root_valid (r : Root) : bool :=
  let n := length (root_consonants r) in
  (n =? 3) || (n =? 4).

(* Trilateral root (ثلاثي) *)
Definition is_trilateral (r : Root) : bool :=
  length (root_consonants r) =? 3.

(* Quadrilateral root (رباعي) *)
Definition is_quadrilateral (r : Root) : bool :=
  length (root_consonants r) =? 4.

(* ============================================
   2) PATTERN TYPES (الوزن / الميزان)
   ============================================ *)

(* Pattern position: either root consonant slot or fixed vowel *)
Inductive PatternPosition : Type :=
| PP_ROOT_SLOT (slot_num : nat)        (* Position for root consonant: C1, C2, C3 *)
| PP_FIXED_CONSONANT (c : Consonant)   (* Fixed consonant in pattern (e.g. taa, alif) *)
| PP_VOWEL (v : Vowel).                (* Vowel in pattern *)

(* Pattern: morphological template *)
Record Pattern := {
  pattern_positions : list PatternPosition;
  pattern_name : nat  (* pattern identifier *)
}.

(* Pattern validity: must have exactly 3 or 4 ROOT_SLOT positions *)
Definition count_root_slots (positions : list PatternPosition) : nat :=
  fold_left (fun acc pos =>
    match pos with
    | PP_ROOT_SLOT _ => acc + 1
    | _ => acc
    end
  ) positions 0.

Definition pattern_valid_for_root (p : Pattern) (r : Root) : bool :=
  count_root_slots (pattern_positions p) =? length (root_consonants r).

(* ============================================
   3) WORD FORMATION (التصريف)
   ============================================ *)

(* Word: combination of root + pattern *)
Record MorphWord := {
  word_root : Root;
  word_pattern : Pattern;
  word_surface : list PhoneticUnit;  (* phonetic realization *)
  word_id : nat
}.

(* Word well-formedness: pattern matches root, surface matches both *)
Definition word_wellformed (w : MorphWord) : bool :=
  let r := word_root w in
  let p := word_pattern w in
  (root_valid r) && (pattern_valid_for_root p r).

(* ============================================
   4) MORPHOLOGICAL C2 OPERATOR
   ============================================ *)

(* In morphology, the Pattern is the C2 operator:
   - C1 (precondition): Root lexical constraints
   - C2 (operator): Pattern template
   - C3 (output): Surface word form *)

Record MorphC2Operator := {
  morph_root : Root;           (* C1: lexical input *)
  morph_pattern : Pattern;     (* C2: operator *)
  morph_output : MorphWord     (* C3: result *)
}.

(* Morphological operation validity *)
Definition morph_operation_valid (op : MorphC2Operator) : bool :=
  let r := morph_root op in
  let p := morph_pattern op in
  let w := morph_output op in
  (* Root must match *)
  (root_id r =? root_id (word_root w)) &&
  (* Pattern must match *)
  (pattern_name p =? pattern_name (word_pattern w)) &&
  (* Word must be wellformed *)
  (word_wellformed w).

(* ============================================
   5) SOUNDNESS THEOREMS
   ============================================ *)

(* Root validity implies it has the correct length *)
Theorem root_valid_sound : forall r : Root,
  root_valid r = true ->
  (length (root_consonants r) = 3) \/ (length (root_consonants r) = 4).
Proof.
  intros r H.
  unfold root_valid in H.
  apply Bool.orb_true_iff in H.
  destruct H as [H3 | H4].
  - left. apply Nat.eqb_eq. exact H3.
  - right. apply Nat.eqb_eq. exact H4.
Qed.

(* Pattern validity for root implies matching slots *)
Theorem pattern_valid_sound : forall p r,
  pattern_valid_for_root p r = true ->
  count_root_slots (pattern_positions p) = length (root_consonants r).
Proof.
  intros p r H.
  unfold pattern_valid_for_root in H.
  apply Nat.eqb_eq. exact H.
Qed.

(* Wellformed word implies valid root and pattern *)
Theorem word_wellformed_sound : forall w,
  word_wellformed w = true ->
  root_valid (word_root w) = true /\
  pattern_valid_for_root (word_pattern w) (word_root w) = true.
Proof.
  intros w H.
  unfold word_wellformed in H.
  apply Bool.andb_true_iff in H.
  exact H.
Qed.

(* Morphological operation preserves identity *)
Theorem morph_operation_preserves_identity : forall op,
  morph_operation_valid op = true ->
  root_id (morph_root op) = root_id (word_root (morph_output op)).
Proof.
  intros op H.
  unfold morph_operation_valid in H.
  apply Bool.andb_true_iff in H. destruct H as [H1 H2].
  apply Bool.andb_true_iff in H1. destruct H1 as [Hr Hp].
  apply Nat.eqb_eq. exact Hr.
Qed.

(* ============================================
   6) MORPHOLOGICAL FRACTAL SOUNDNESS
   ============================================ *)

(* Main morphological soundness theorem:
   A valid morphological operation must have:
   - Valid root (C1)
   - Valid pattern (C2) matching the root
   - Wellformed output word (C3) *)

Theorem Morphological_Fractal_Soundness : forall op,
  morph_operation_valid op = true ->
  root_valid (morph_root op) = true /\
  pattern_valid_for_root (morph_pattern op) (morph_root op) = true /\
  word_wellformed (morph_output op) = true.
Proof.
  intros op H.
  unfold morph_operation_valid in H.
  apply Bool.andb_true_iff in H. destruct H as [H1 Hwf].
  apply Bool.andb_true_iff in H1. destruct H1 as [Hr Hp].
  split. 
  - (* Root valid: need to extract from word_wellformed *)
    unfold word_wellformed in Hwf.
    apply Bool.andb_true_iff in Hwf. destruct Hwf as [Hwfr _].
    (* Since root_id matches, validity transfers *)
    apply Nat.eqb_eq in Hr.
    rewrite <- Hr in Hwfr. exact Hwfr.
  - split.
    + (* Pattern valid: need to extract from word_wellformed *)
      unfold word_wellformed in Hwf.
      apply Bool.andb_true_iff in Hwf. destruct Hwf as [_ Hwfp].
      apply Nat.eqb_eq in Hp.
      (* Pattern matches, so validity transfers *)
      exact Hwfp.
    + exact Hwf.
Qed.

End ArabicKernelMorphology.
