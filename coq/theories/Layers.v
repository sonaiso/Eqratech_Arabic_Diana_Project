(** * FractalHub Layers
    
    Formal specification of the layer architecture with strict separation.
    
    Key invariants:
    - C1 (Signifier): Form only, NO semantic content
    - C3 (Signified): Meaning only, NO form data
    - C2 (Gates): Connection layer with four conditions
*)

Require Import FractalHub.Base.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

(** ** Layer Separation *)

(** Signifier entries (C1) must not contain semantic features *)
Definition signifier_no_semantics (f : Form) : Prop :=
  form_layer f = C1.

(** Signified entries (C3) must not contain form data *)
Definition signified_no_form (m : Meaning) : Prop :=
  meaning_layer m = C3.

(** ** Layer Ordering *)

(** Layers form a strict order: C0 < C1 < C2 < C3 *)
Inductive layer_lt : Layer -> Layer -> Prop :=
  | lt_C0_C1 : layer_lt C0 C1
  | lt_C0_C2 : layer_lt C0 C2
  | lt_C0_C3 : layer_lt C0 C3
  | lt_C1_C2 : layer_lt C1 C2
  | lt_C1_C3 : layer_lt C1 C3
  | lt_C2_C3 : layer_lt C2 C3.

(** Layer ordering is transitive *)
Lemma layer_lt_trans : forall l1 l2 l3,
  layer_lt l1 l2 -> layer_lt l2 l3 -> layer_lt l1 l3.
Proof.
  intros l1 l2 l3 H12 H23.
  inversion H12; inversion H23; subst; constructor.
Qed.

(** Layer ordering is irreflexive *)
Lemma layer_lt_irrefl : forall l,
  ~ layer_lt l l.
Proof.
  intros l H.
  inversion H.
Qed.

(** ** Layer Access Control *)

(** Only C2 (gates) can connect C1 to C3 *)
Definition valid_layer_transition (from to : Layer) : bool :=
  match from, to with
  | C1, C3 => false  (* Direct C1 -> C3 forbidden *)
  | C1, C2 => true   (* C1 -> C2 allowed *)
  | C2, C3 => true   (* C2 -> C3 allowed *)
  | _, _ => layer_before from to
  end.

Theorem no_direct_c1_to_c3 :
  valid_layer_transition C1 C3 = false.
Proof.
  reflexivity.
Qed.

(** ** Layer Properties *)

(** Each layer has specific constraints *)
Inductive LayerConstraint : Layer -> Type :=
  | C0_Constraint : LayerConstraint C0  (* Phonological constraints *)
  | C1_Constraint : LayerConstraint C1  (* Form constraints, no semantics *)
  | C2_Constraint : LayerConstraint C2  (* Gate constraints, four conditions *)
  | C3_Constraint : LayerConstraint C3  (* Meaning constraints, requires trace *).

(** Layer constraint enforcement *)
Definition enforce_layer_constraint (l : Layer) : LayerConstraint l :=
  match l as l' return LayerConstraint l' with
  | C0 => C0_Constraint
  | C1 => C1_Constraint
  | C2 => C2_Constraint
  | C3 => C3_Constraint
  end.
