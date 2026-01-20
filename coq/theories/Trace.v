(** * FractalHub Trace System
    
    Formal specification of the trace system (C2 layer).
*)

Require Import FractalHub.Base.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

(** ** Trace Validity *)

(** A trace is valid if it has gates and prior_ids *)
Lemma trace_needs_gates : forall t : Trace,
  valid_trace t = true -> trace_gates t <> [].
Proof.
  intros t H.
  unfold valid_trace in H.
  destruct (trace_gates t) eqn:Hg.
  - discriminate H.
  - discriminate.
Qed.

Lemma trace_needs_prior_ids : forall t : Trace,
  valid_trace t = true -> trace_prior_ids t <> [].
Proof.
  intros t H.
  unfold valid_trace in H.
  destruct (trace_gates t) eqn:Hg;
  destruct (trace_prior_ids t) eqn:Hp.
  - discriminate H.
  - discriminate H.
  - discriminate H.
  - discriminate.
Qed.

(** ** Trace Construction *)

(** Building a valid trace requires gates and prior_ids *)
Definition build_trace (id : ID) (gates : list Gate) (prior_ids : list ID) 
                      (strength : EvidenceStrength) (ts : Timestamp) : option Trace :=
  match gates, prior_ids with
  | [], _ => None  (* No gates *)
  | _, [] => None  (* No prior_ids *)
  | _, _ => Some (mkTrace id gates prior_ids strength ts)
  end.

Lemma build_trace_valid : forall id g gs p ps s t tr,
  build_trace id (g :: gs) (p :: ps) s t = Some tr ->
  valid_trace tr = true.
Proof.
  intros id g gs p ps s t tr H.
  unfold build_trace in H.
  injection H as H. subst tr.
  reflexivity.
Qed.

(** ** Trace Properties *)

(** Trace IDs are unique *)
Axiom trace_id_unique : forall t1 t2 : Trace,
  trace_id t1 = trace_id t2 -> t1 = t2.

(** Gates in a trace are ordered by timestamp *)
Definition gates_ordered (gates : list Gate) : Prop :=
  forall i j g1 g2,
    nth_error gates i = Some g1 ->
    nth_error gates j = Some g2 ->
    i < j ->
    gate_timestamp g1 <= gate_timestamp g2.

(** ** Trace Composition *)

(** Appending gates to a trace *)
Definition append_gate (t : Trace) (g : Gate) : Trace :=
  mkTrace
    (trace_id t)
    (trace_gates t ++ [g])
    (trace_prior_ids t)
    (trace_evidence_strength t)
    (trace_timestamp t).

Lemma append_gate_preserves_validity : forall t g,
  valid_trace t = true ->
  valid_trace (append_gate t g) = true.
Proof.
  intros t g H.
  unfold append_gate.
  simpl.
  unfold valid_trace in *.
  destruct (trace_gates t); destruct (trace_prior_ids t); try discriminate.
  - reflexivity.
  - reflexivity.
Qed.
