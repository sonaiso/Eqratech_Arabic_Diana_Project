(** * FractalHub Base Definitions
    
    This file contains the foundational definitions for the FractalHub
    Consciousness Kernel, implementing Al-Nabhani's Theory of Thinking
    with formally verified locked architecture.
    
    Author: FractalHub Project
    Version: 1.2
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

(** ** Layer Types *)

(** The three main layers in FractalHub architecture *)
Inductive Layer : Type :=
  | C0 : Layer  (** Phonological layer *)
  | C1 : Layer  (** Signifier layer - form only *)
  | C2 : Layer  (** Gate and trace layer *)
  | C3 : Layer  (** Signified layer - meaning only *).

(** ** Base Types *)

(** Unique identifiers *)
Definition ID : Type := string.

(** Evidence strength (epistemic confidence) *)
Definition EvidenceStrength : Type := nat.  (* 0-100 representing 0.0-1.0 *)

(** Timestamp *)
Definition Timestamp : Type := nat.

(** Checksum for form codec *)
Definition Checksum : Type := string.

(** ** Form and Meaning *)

(** Form represents the signifier (C1 layer) - no semantic content *)
Record Form : Type := mkForm {
  form_id : ID;
  form_data : list nat;  (* Encoded text as numbers *)
  form_checksum : Checksum;
  form_layer : Layer;
  form_valid : form_layer = C1  (* Forms must be in C1 layer *)
}.

(** Meaning represents the signified (C3 layer) - semantic content only *)
Record Meaning : Type := mkMeaning {
  meaning_id : ID;
  meaning_concept : string;
  meaning_trace_id : ID;  (* Required: NO C3 without C2 *)
  meaning_prior_ids : list ID;  (* Required: NO meaning without evidence *)
  meaning_layer : Layer;
  meaning_valid : meaning_layer = C3  (* Meanings must be in C3 layer *)
}.

(** ** Four Conditions of Mind (Al-Nabhani) *)

(** The four conditions required for valid cognition *)
Record FourConditions : Type := mkFourConditions {
  reality : option (list nat);  (* The form being processed *)
  brain : option ID;  (* The executor *)
  sensing : option string;  (* The channel/modality *)
  prior_knowledge : list ID  (* Evidence from dictionary *)
}.

(** Validity predicate for FourConditions *)
Definition valid_four_conditions (fc : FourConditions) : bool :=
  match (reality fc), (brain fc), (sensing fc) with
  | Some _, Some _, Some _ => 
      match prior_knowledge fc with
      | [] => false  (* NO C2 without prior knowledge *)
      | _ => true
      end
  | _, _, _ => false
  end.

(** ** Provenance *)

Record ProvenanceSource : Type := mkProvenanceSource {
  source_id : ID;
  source_type : string;
  reliability : EvidenceStrength
}.

Record Provenance : Type := mkProvenance {
  prov_source : ProvenanceSource;
  confidence : EvidenceStrength
}.

(** ** Gate Types *)

Inductive GateType : Type :=
  | G_ATTEND : GateType
  | G_CODEC_VERIFY : GateType
  | G_SPEECH_ACT : GateType
  | G_MEMORY_READ : GateType
  | G_MEMORY_WRITE : GateType.

(** Gate with four conditions enforcement *)
Record Gate : Type := mkGate {
  gate_id : ID;
  gate_type : GateType;
  gate_conditions : FourConditions;
  gate_timestamp : Timestamp;
  gate_valid : valid_four_conditions gate_conditions = true
}.

(** ** Trace *)

Record Trace : Type := mkTrace {
  trace_id : ID;
  trace_gates : list Gate;
  trace_prior_ids : list ID;
  trace_evidence_strength : EvidenceStrength;
  trace_timestamp : Timestamp
}.

(** Validity predicate for Trace *)
Definition valid_trace (t : Trace) : bool :=
  match trace_gates t, trace_prior_ids t with
  | [], _ => false  (* Must have at least one gate *)
  | _, [] => false  (* Must have prior_ids evidence *)
  | _, _ => true
  end.

(** ** Helper Functions *)

(** Check if a layer is before another in the architecture *)
Definition layer_before (l1 l2 : Layer) : bool :=
  match l1, l2 with
  | C0, C1 => true
  | C0, C2 => true
  | C0, C3 => true
  | C1, C2 => true
  | C1, C3 => true
  | C2, C3 => true
  | _, _ => false
  end.

(** Equality for layers *)
Definition layer_eq (l1 l2 : Layer) : bool :=
  match l1, l2 with
  | C0, C0 => true
  | C1, C1 => true
  | C2, C2 => true
  | C3, C3 => true
  | _, _ => false
  end.

(** ** Decidability *)

Lemma layer_eq_dec : forall l1 l2 : Layer,
  {l1 = l2} + {l1 <> l2}.
Proof.
  decide equality.
Qed.

Lemma gate_type_eq_dec : forall g1 g2 : GateType,
  {g1 = g2} + {g1 <> g2}.
Proof.
  decide equality.
Qed.
