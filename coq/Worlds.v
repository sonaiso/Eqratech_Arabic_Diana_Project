(** * العوالم والإمكان (Worlds & Accessibility)
    
    هذا الملف يحتوي على تعريف العوالم الممكنة وعلاقات
    الوصول بينها والقيود على تسريب الحقيقة.
    
    Consciousness Kernel v1.2 + FractalHub Dictionary v02 + XAI Engine
    2026-01-22
*)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Spaces.
Import ListNotations.

(** ** I. أنواع العوالم *)

(** أنواع العوالم الممكنة *)
Inductive WorldKind :=
| W_Actual        (** العالم الفعلي: الواقع الحالي *)
| W_Counterfactual (** العالم المضاد: لو كان كذا لكان كذا *)
| W_Belief        (** عالم المعتقد: ما يعتقده الفاعل *)
| W_Plan          (** عالم الخطة: ما هو مخطط له *)
| W_Creative.     (** عالم الإبداع: التركيب الجديد *)

(** مساواة أنواع العوالم *)
Definition world_kind_eq (w1 w2 : WorldKind) : bool :=
  match w1, w2 with
  | W_Actual, W_Actual => true
  | W_Counterfactual, W_Counterfactual => true
  | W_Belief, W_Belief => true
  | W_Plan, W_Plan => true
  | W_Creative, W_Creative => true
  | _, _ => false
  end.

Lemma world_kind_eq_refl : forall wk,
  world_kind_eq wk wk = true.
Proof.
  intros wk.
  destruct wk; simpl; reflexivity.
Qed.

(** ** II. بنية العالم *)

(** بنية العالم *)
Record World := {
  wid : nat;                    (** معرّف العالم *)
  wkind : WorldKind;           (** نوع العالم *)
  wspace : Space;              (** الفضاء المرتبط *)
  wtime : option nat;          (** الزمن (إن وُجد) *)
}.

(** مساواة العوالم *)
Definition world_eq (w1 w2 : World) : bool :=
  Nat.eqb (wid w1) (wid w2).

Lemma world_eq_refl : forall w,
  world_eq w w = true.
Proof.
  intros w.
  unfold world_eq.
  apply Nat.eqb_refl.
Qed.

(** ** III. علاقات الوصول *)

(** علاقة الوصول بين العوالم *)
Inductive AccessibleFrom : World -> World -> Prop :=
| Access_Refl : forall w,
    AccessibleFrom w w
| Access_Actual_To_CF : forall w_actual w_cf,
    wkind w_actual = W_Actual ->
    wkind w_cf = W_Counterfactual ->
    AccessibleFrom w_actual w_cf
| Access_Actual_To_Belief : forall w_actual w_bel,
    wkind w_actual = W_Actual ->
    wkind w_bel = W_Belief ->
    AccessibleFrom w_actual w_bel
| Access_Actual_To_Plan : forall w_actual w_plan,
    wkind w_actual = W_Actual ->
    wkind w_plan = W_Plan ->
    AccessibleFrom w_actual w_plan
| Access_Plan_To_Creative : forall w_plan w_creat,
    wkind w_plan = W_Plan ->
    wkind w_creat = W_Creative ->
    AccessibleFrom w_plan w_creat.

(** الوصول انعكاسي *)
Theorem access_reflexive : forall w,
  AccessibleFrom w w.
Proof.
  intros w.
  apply Access_Refl.
Qed.

(** ** IV. القيد الحرج: منع تسريب الحقيقة *)

(** لا تسريب للحقيقة من العوالم غير الفعلية *)
Axiom NoTruthLeakage : forall w1 w2,
  wkind w1 <> W_Actual ->
  AccessibleFrom w1 w2 ->
  wkind w2 = W_Actual ->
  False.

(** نتائج منع التسريب *)
Theorem no_cf_to_actual : forall w_cf w_actual,
  wkind w_cf = W_Counterfactual ->
  wkind w_actual = W_Actual ->
  ~ AccessibleFrom w_cf w_actual.
Proof.
  intros w_cf w_actual H_cf H_actual H_access.
  eapply NoTruthLeakage.
  - intro H_eq.
    rewrite H_cf in H_eq.
    discriminate.
  - apply H_access.
  - apply H_actual.
Qed.

Theorem no_belief_to_actual : forall w_bel w_actual,
  wkind w_bel = W_Belief ->
  wkind w_actual = W_Actual ->
  ~ AccessibleFrom w_bel w_actual.
Proof.
  intros w_bel w_actual H_bel H_actual H_access.
  eapply NoTruthLeakage.
  - intro H_eq.
    rewrite H_bel in H_eq.
    discriminate.
  - apply H_access.
  - apply H_actual.
Qed.

Theorem no_plan_to_actual : forall w_plan w_actual,
  wkind w_plan = W_Plan ->
  wkind w_actual = W_Actual ->
  ~ AccessibleFrom w_plan w_actual.
Proof.
  intros w_plan w_actual H_plan H_actual H_access.
  eapply NoTruthLeakage.
  - intro H_eq.
    rewrite H_plan in H_eq.
    discriminate.
  - apply H_access.
  - apply H_actual.
Qed.

Theorem no_creative_to_actual : forall w_creat w_actual,
  wkind w_creat = W_Creative ->
  wkind w_actual = W_Actual ->
  ~ AccessibleFrom w_creat w_actual.
Proof.
  intros w_creat w_actual H_creat H_actual H_access.
  eapply NoTruthLeakage.
  - intro H_eq.
    rewrite H_creat in H_eq.
    discriminate.
  - apply H_access.
  - apply H_actual.
Qed.

(** ** V. ربط العوالم بالفضاءات *)

(** تحقق من صحة الربط بين العالم والفضاء *)
Definition valid_world_space_binding (w : World) : bool :=
  match wkind w, wspace w with
  | W_Actual, S_C2 => true
  | W_Counterfactual, S_CF => true
  | W_Belief, S_BEL => true
  | W_Plan, S_C3 => true
  | W_Plan, S_STRAT => true
  | W_Creative, S_CREAT => true
  | _, _ => false
  end.

(** ** VI. الحقيقة في العوالم *)

(** قضية في عالم *)
Record Proposition := {
  prop_content : nat;  (** محتوى القضية (مجرد معرّف) *)
  prop_world : World;  (** العالم الذي توجد فيه القضية *)
}.

(** الحقيقة في عالم *)
Definition TruthInWorld (p : Proposition) : Prop :=
  wkind (prop_world p) = W_Actual.

(** لا يمكن أن تكون القضية حقيقية في عالمين مختلفي النوع *)
Theorem no_truth_in_different_worlds :
  forall p1 p2,
    prop_content p1 = prop_content p2 ->
    wkind (prop_world p1) <> wkind (prop_world p2) ->
    TruthInWorld p1 ->
    ~ TruthInWorld p2.
Proof.
  intros p1 p2 H_same_content H_diff_kind H_truth1 H_truth2.
  unfold TruthInWorld in *.
  rewrite H_truth1 in H_diff_kind.
  rewrite H_truth2 in H_diff_kind.
  apply H_diff_kind.
  reflexivity.
Qed.

(** ** VII. دوال مساعدة *)

(** تحويل نوع العالم إلى رقم *)
Definition world_kind_to_nat (wk : WorldKind) : nat :=
  match wk with
  | W_Actual => 0
  | W_Counterfactual => 1
  | W_Belief => 2
  | W_Plan => 3
  | W_Creative => 4
  end.

(** تحويل الرقم إلى نوع عالم *)
Definition nat_to_world_kind (n : nat) : option WorldKind :=
  match n with
  | 0 => Some W_Actual
  | 1 => Some W_Counterfactual
  | 2 => Some W_Belief
  | 3 => Some W_Plan
  | 4 => Some W_Creative
  | _ => None
  end.

Lemma world_kind_nat_roundtrip : forall wk,
  nat_to_world_kind (world_kind_to_nat wk) = Some wk.
Proof.
  intros wk.
  destruct wk; simpl; reflexivity.
Qed.

(** ** VIII. النظريات الأساسية *)

(** العالم الفعلي موجود دائماً *)
Definition actual_world_exists : Prop :=
  exists w, wkind w = W_Actual.

(** كل عالم غير فعلي يمكن الوصول إليه من العالم الفعلي *)
Theorem modal_worlds_accessible_from_actual :
  forall w_modal,
    wkind w_modal <> W_Actual ->
    exists w_actual,
      wkind w_actual = W_Actual /\
      (AccessibleFrom w_actual w_modal \/
       exists w_intermediate,
         AccessibleFrom w_actual w_intermediate /\
         AccessibleFrom w_intermediate w_modal).
Proof.
  intros w_modal H_not_actual.
  destruct (wkind w_modal) eqn:E.
  - contradiction H_not_actual. reflexivity.
  - exists {| wid := 0; wkind := W_Actual; wspace := S_C2; wtime := Some 0 |}.
    split.
    + simpl. reflexivity.
    + left. apply Access_Actual_To_CF; simpl; reflexivity.
  - exists {| wid := 0; wkind := W_Actual; wspace := S_C2; wtime := Some 0 |}.
    split.
    + simpl. reflexivity.
    + left. apply Access_Actual_To_Belief; simpl; reflexivity.
  - exists {| wid := 0; wkind := W_Actual; wspace := S_C2; wtime := Some 0 |}.
    split.
    + simpl. reflexivity.
    + left. apply Access_Actual_To_Plan; simpl; reflexivity.
  - exists {| wid := 0; wkind := W_Actual; wspace := S_C2; wtime := Some 0 |}.
    split.
    + simpl. reflexivity.
    + right.
      exists {| wid := 1; wkind := W_Plan; wspace := S_C3; wtime := Some 1 |}.
      split.
      * apply Access_Actual_To_Plan; simpl; reflexivity.
      * apply Access_Plan_To_Creative; simpl; reflexivity.
Qed.

(** قائمة جميع أنواع العوالم *)
Definition all_world_kinds : list WorldKind :=
  [W_Actual; W_Counterfactual; W_Belief; W_Plan; W_Creative].

Lemma all_world_kinds_complete : forall wk : WorldKind,
  In wk all_world_kinds.
Proof.
  intro wk.
  destruct wk; simpl; auto 5.
Qed.

Lemma world_kinds_count : length all_world_kinds = 5.
Proof.
  simpl. reflexivity.
Qed.

(** نهاية الملف *)
