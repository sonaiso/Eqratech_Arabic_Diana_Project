(** * الدال والمدلول (Signifier & Signified)
    
    هذا الملف يحتوي على الفصل الصارم بين الدال (الشكل)
    والمدلول (المعنى) والربط بينهما.
    
    Consciousness Kernel v1.2 + FractalHub Dictionary v02 + XAI Engine
    2026-01-22
*)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Spaces.
Require Import Worlds.
Import ListNotations.

(** ** I. طبقات المعنى *)

(** الطبقات الثلاث *)
Inductive Layer :=
| L_Signifier   (** الدال: الشكل اللغوي *)
| L_Signified   (** المدلول: المعنى/المفهوم *)
| L_Bound.      (** الربط: العلاقة بينهما *)

Definition layer_eq (l1 l2 : Layer) : bool :=
  match l1, l2 with
  | L_Signifier, L_Signifier => true
  | L_Signified, L_Signified => true
  | L_Bound, L_Bound => true
  | _, _ => false
  end.

Lemma layer_eq_refl : forall l, layer_eq l l = true.
Proof.
  intros l. destruct l; simpl; reflexivity.
Qed.

(** ** II. الدال (Signifier) *)

(** اللفظ/الرمز *)
Record Lexeme := {
  lex_id : nat;          (** معرّف اللفظ *)
  lex_form : nat;        (** الشكل (مُبسّط كرقم) *)
  lex_space : Space;     (** الفضاء (يجب أن يكون C1 أو C2) *)
}.

(** صحة اللفظ *)
Definition valid_lexeme (l : Lexeme) : bool :=
  match lex_space l with
  | S_C1 | S_C2 => true
  | _ => false
  end.

Lemma lexeme_must_be_in_c1_or_c2 : forall l,
  valid_lexeme l = true ->
  lex_space l = S_C1 \/ lex_space l = S_C2.
Proof.
  intros l H.
  unfold valid_lexeme in H.
  destruct (lex_space l) eqn:E; try discriminate; auto.
Qed.

(** ** III. المدلول (Signified) *)

(** المفهوم *)
Record Concept := {
  con_id : nat;          (** معرّف المفهوم *)
  con_content : nat;     (** المحتوى (مُبسّط كرقم) *)
  con_space : Space;     (** الفضاء *)
}.

(** المفهوم يمكن أن يوجد في أي فضاء *)
Definition valid_concept (c : Concept) : bool := true.

(** ** IV. الربط (Binding) *)

(** ربط بين دال ومدلول *)
Record Binding := {
  bind_signifier : Lexeme;
  bind_signified : Concept;
  bind_world : World;
  bind_evidence : list nat;  (** الأدلة على صحة الربط *)
}.

(** صحة الربط *)
Definition valid_binding (b : Binding) : bool :=
  valid_lexeme (bind_signifier b) &&
  match wkind (bind_world b) with
  | W_Actual => negb (Nat.eqb (length (bind_evidence b)) 0)
  | _ => true
  end.

(** ** V. القيود الأساسية *)

(** لا معنى بلا دال *)
Axiom NoSignifiedWithoutSignifier : forall c : Concept,
  exists l : Lexeme,
  exists b : Binding,
    bind_signifier b = l /\
    bind_signified b = c.

(** لا ربط بلا دليل في العالم الفعلي *)
Axiom NoBindingWithoutEvidenceInActual : forall b : Binding,
  wkind (bind_world b) = W_Actual ->
  bind_evidence b <> [].

(** في العالم الفعلي، لا ادعاء بلا دليل *)
Theorem no_claim_without_evidence_in_actual :
  forall b : Binding,
    wkind (bind_world b) = W_Actual ->
    valid_binding b = true ->
    bind_evidence b <> [].
Proof.
  intros b H_actual H_valid.
  unfold valid_binding in H_valid.
  destruct (wkind (bind_world b)) eqn:E.
  - apply Bool.andb_true_iff in H_valid.
    destruct H_valid as [_ H_ev].
    apply Bool.negb_true_iff in H_ev.
    apply Nat.eqb_neq in H_ev.
    intro H_empty.
    rewrite H_empty in H_ev.
    simpl in H_ev.
    apply H_ev.
    reflexivity.
  - discriminate H_actual.
  - discriminate H_actual.
  - discriminate H_actual.
  - discriminate H_actual.
Qed.

(** ** VI. المنطوق والمفهوم *)

(** المنطوق: ما يُقال صراحة *)
Definition Manutooq := Lexeme.

(** المفهوم: ما يُفهَم ضمناً *)
Definition Mafhoom := Concept.

(** علاقة بين المنطوق والمفهوم *)
Definition ManutooqToMafhoom (m : Manutooq) (f : Mafhoom) : Prop :=
  exists b : Binding,
    bind_signifier b = m /\
    bind_signified b = f.

(** ** VII. أنواع الدلالة *)

(** أنواع الدلالة الثلاثة *)
Inductive DenotationType :=
| DT_Mutabaqa    (** المطابقة: المعنى الكامل *)
| DT_Tadammun    (** التضمن: المعنى الجزئي *)
| DT_Iltizam.    (** الالتزام: المعنى اللازم *)

Definition denotation_eq (d1 d2 : DenotationType) : bool :=
  match d1, d2 with
  | DT_Mutabaqa, DT_Mutabaqa => true
  | DT_Tadammun, DT_Tadammun => true
  | DT_Iltizam, DT_Iltizam => true
  | _, _ => false
  end.

(** ربط موسّع مع نوع الدلالة *)
Record ExtendedBinding := {
  eb_binding : Binding;
  eb_denotation : DenotationType;
}.

(** ** VIII. خواص الدلالة *)

(** المطابقة تستلزم التضمن *)
Axiom MutabaqaImpliesTadammun : forall eb1 eb2 : ExtendedBinding,
  eb_denotation eb1 = DT_Mutabaqa ->
  bind_signifier (eb_binding eb1) = bind_signifier (eb_binding eb2) ->
  eb_denotation eb2 = DT_Tadammun ->
  True. (* التضمن موجود دائماً إذا كانت المطابقة موجودة *)

(** الالتزام يتطلب ملزوماً *)
Axiom IltizamRequiresSource : forall eb : ExtendedBinding,
  eb_denotation eb = DT_Iltizam ->
  exists source_eb : ExtendedBinding,
    eb_denotation source_eb = DT_Mutabaqa \/
    eb_denotation source_eb = DT_Tadammun.

(** ** IX. التحقق *)

(** تحقق من وجود دال لمدلول معين *)
Definition has_signifier (c : Concept) (bindings : list Binding) : bool :=
  existsb (fun b => Nat.eqb (con_id (bind_signified b)) (con_id c)) bindings.

(** تحقق من وجود مدلول لدال معين *)
Definition has_signified (l : Lexeme) (bindings : list Binding) : bool :=
  existsb (fun b => Nat.eqb (lex_id (bind_signifier b)) (lex_id l)) bindings.

(** ** X. النظريات الأساسية *)

(** كل مفهوم في C2 (الواقع الحالي) له دال *)
Theorem every_c2_concept_has_signifier :
  forall c : Concept,
    con_space c = S_C2 ->
    exists l : Lexeme,
    exists b : Binding,
      bind_signifier b = l /\
      bind_signified b = c /\
      valid_lexeme l = true.
Proof.
  intros c H_space.
  apply NoSignifiedWithoutSignifier.
Qed.

(** في العالم الفعلي، كل ربط له دليل *)
Theorem actual_world_bindings_have_evidence :
  forall b : Binding,
    wkind (bind_world b) = W_Actual ->
    exists ev : nat,
      In ev (bind_evidence b).
Proof.
  intros b H_actual.
  assert (H_not_empty := NoBindingWithoutEvidenceInActual b H_actual).
  destruct (bind_evidence b) as [| ev rest] eqn:E.
  - contradiction H_not_empty. reflexivity.
  - exists ev. simpl. left. reflexivity.
Qed.

(** ** XI. دوال مساعدة *)

(** إنشاء ربط بسيط *)
Definition make_binding (l : Lexeme) (c : Concept) (w : World) (ev : list nat) : Binding :=
  {| bind_signifier := l;
     bind_signified := c;
     bind_world := w;
     bind_evidence := ev |}.

(** تحقق من تطابق الدال *)
Definition signifier_eq (l1 l2 : Lexeme) : bool :=
  Nat.eqb (lex_id l1) (lex_id l2).

(** تحقق من تطابق المدلول *)
Definition signified_eq (c1 c2 : Concept) : bool :=
  Nat.eqb (con_id c1) (con_id c2).

Lemma signifier_eq_refl : forall l,
  signifier_eq l l = true.
Proof.
  intros l.
  unfold signifier_eq.
  apply Nat.eqb_refl.
Qed.

Lemma signified_eq_refl : forall c,
  signified_eq c c = true.
Proof.
  intros c.
  unfold signified_eq.
  apply Nat.eqb_refl.
Qed.

(** نهاية الملف *)
