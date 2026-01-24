(** * Creativity - Novel and Valuable Idea Generation *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Agency.

(** ** Creative Product *)

(** Creativity dimensions *)
Record CreativeProduct : Type := {
  cp_agent : Agent;
  cp_novelty : nat;          (* Novelty score (0-100) *)
  cp_value : nat;            (* Value/usefulness score (0-100) *)
  cp_surprise : nat;         (* Surprise factor (0-100) *)
  cp_domain : nat;           (* Domain identifier *)
  cp_complexity : nat        (* Complexity (0-100) *)
}.

(** Creativity threshold *)
Definition is_creative (cp : CreativeProduct) : Prop :=
  cp_novelty cp >= 70 /\
  cp_value cp >= 50.

(** High creativity *)
Definition highly_creative (cp : CreativeProduct) : Prop :=
  cp_novelty cp >= 90 /\
  cp_value cp >= 80.

(** ** Creative Processes *)

(** Creative process types *)
Inductive CreativeProcessType : Type :=
  | Combination         (* دمج - Combining existing ideas *)
  | Exploration         (* استكشاف - Exploring new territory *)
  | Transformation      (* تحويل - Transforming existing ideas *)
  | Analogy             (* قياس - Analogical reasoning *)
  | Serendipity.        (* صدفة - Happy accident *)

(** Creative process *)
Record CreativeProcess : Type := {
  cproc_agent : Agent;
  cproc_type : CreativeProcessType;
  cproc_input : list nat;    (* Input ideas/concepts *)
  cproc_output : CreativeProduct;
  cproc_intentional : bool   (* Intentional vs spontaneous *)
}.

(** ** Divergent vs Convergent Thinking *)

(** Divergent thinking - generates many ideas *)
Definition divergent_thinking (agent : Agent) (ideas : list CreativeProduct) : Prop :=
  length ideas >= 10 /\
  forall cp, In cp ideas -> cp_agent cp = agent.

(** Convergent thinking - selects best idea *)
Definition convergent_thinking (agent : Agent) (ideas : list CreativeProduct) 
                                (best : CreativeProduct) : Prop :=
  In best ideas /\
  cp_agent best = agent /\
  forall cp, In cp ideas -> cp_value best >= cp_value cp.

(** ** Conceptual Spaces *)

(** Conceptual space *)
Record ConceptualSpace : Type := {
  cs_dimensions : list nat;
  cs_concepts : list nat;
  cs_boundaries : list (nat * nat)
}.

(** Exploration within space *)
Definition explore_space (cs : ConceptualSpace) (cp : CreativeProduct) : Prop :=
  In (cp_domain cp) (cs_dimensions cs).

(** Transformation of space *)
Definition transform_space (cs1 cs2 : ConceptualSpace) : Prop :=
  cs_dimensions cs1 <> cs_dimensions cs2 \/
  cs_boundaries cs1 <> cs_boundaries cs2.

(** ** Combinatorial Creativity *)

(** Conceptual blending *)
Definition conceptual_blend (c1 c2 : nat) (result : nat) : Prop :=
  result <> c1 /\ result <> c2.

(** Bisociation (Koestler) *)
Definition bisociation (domain1 domain2 : nat) (cp : CreativeProduct) : Prop :=
  domain1 <> domain2 /\
  cp_novelty cp >= 80.

(** ** Insight *)

(** Aha moment *)
Record Insight : Type := {
  insight_agent : Agent;
  insight_problem : Prop;
  insight_solution : Prop;
  insight_sudden : bool;     (* Sudden vs gradual *)
  insight_restructuring : bool (* Problem restructuring *)
}.

(** Productive thinking (Wertheimer) *)
Definition productive_thinking (i : Insight) : Prop :=
  insight_restructuring i = true.

(** ** Creative Constraints *)

(** Constraint paradox - constraints enable creativity *)
Definition creative_constraint (constraint : Prop) (cp : CreativeProduct) : Prop :=
  constraint ->
  cp_novelty cp >= 60.

(** Functional fixedness - barrier to creativity *)
Definition functional_fixedness (agent : Agent) (object_use : Prop) : Prop :=
  exists standard_use : Prop,
    standard_use /\ ~object_use.

(** ** Flow State *)

(** Flow experience (Csikszentmihalyi) *)
Record FlowState : Type := {
  flow_agent : Agent;
  flow_challenge_skill_balance : bool;
  flow_clear_goals : bool;
  flow_immediate_feedback : bool;
  flow_concentration : nat;  (* 0-100 *)
  flow_loss_of_self_consciousness : bool
}.

(** Optimal flow *)
Definition optimal_flow (f : FlowState) : Prop :=
  flow_challenge_skill_balance f = true /\
  flow_concentration f >= 80.

(** ** Axioms *)

(** Novelty and value tradeoff *)
Axiom novelty_value_tradeoff :
  forall cp : CreativeProduct,
    cp_novelty cp >= 95 ->
    cp_value cp <= 60.

(** Expertise enables creativity *)
Axiom expertise_enables_creativity :
  forall agent : Agent,
    is_autonomous agent = true ->
    exists cp : CreativeProduct,
      cp_agent cp = agent /\
      is_creative cp.

(** Incubation effect *)
Axiom incubation_effect :
  forall agent : Agent,
  forall problem : Prop,
    exists time : nat,
      time >= 10 ->
      exists cp : CreativeProduct,
        cp_agent cp = agent /\
        cp_novelty cp >= 70.

(** Remote association *)
Axiom remote_association_creative :
  forall c1 c2 : nat,
  forall distance : nat,
    distance >= 80 ->
    forall result : nat,
      conceptual_blend c1 c2 result ->
      exists cp : CreativeProduct,
        cp_novelty cp >= 75.

(** ** Theorems *)

(** Highly creative is creative *)
Theorem highly_creative_is_creative :
  forall cp : CreativeProduct,
    highly_creative cp ->
    is_creative cp.
Proof.
  intros cp H_high.
  unfold highly_creative in H_high.
  unfold is_creative.
  destruct H_high as [H_nov H_val].
  split; omega.
Qed.

(** Creative products have agent *)
Theorem creative_has_agent :
  forall cp : CreativeProduct,
    is_creative cp ->
    exists a : Agent, cp_agent cp = a.
Proof.
  intros cp H_creative.
  exists (cp_agent cp).
  reflexivity.
Qed.

(** Divergent thinking generates multiple ideas *)
Theorem divergent_generates_many :
  forall agent : Agent,
  forall ideas : list CreativeProduct,
    divergent_thinking agent ideas ->
    length ideas >= 10.
Proof.
  intros agent ideas H_div.
  unfold divergent_thinking in H_div.
  destruct H_div as [H_length _].
  exact H_length.
Qed.

(** Convergent thinking selects best *)
Theorem convergent_selects_best :
  forall agent : Agent,
  forall ideas : list CreativeProduct,
  forall best : CreativeProduct,
    convergent_thinking agent ideas best ->
    forall cp, In cp ideas -> cp_value best >= cp_value cp.
Proof.
  intros agent ideas best H_conv cp H_in.
  unfold convergent_thinking in H_conv.
  destruct H_conv as [H_in_best [H_agent H_best]].
  apply H_best.
  exact H_in.
Qed.

(** Conceptual blend creates novelty *)
Theorem blend_creates_novelty :
  forall c1 c2 result : nat,
    conceptual_blend c1 c2 result ->
    result <> c1 /\ result <> c2.
Proof.
  intros c1 c2 result H_blend.
  unfold conceptual_blend in H_blend.
  exact H_blend.
Qed.

(** Bisociation requires different domains *)
Theorem bisociation_different_domains :
  forall domain1 domain2 : nat,
  forall cp : CreativeProduct,
    bisociation domain1 domain2 cp ->
    domain1 <> domain2.
Proof.
  intros domain1 domain2 cp H_bisoc.
  unfold bisociation in H_bisoc.
  destruct H_bisoc as [H_diff _].
  exact H_diff.
Qed.

(** Bisociation is novel *)
Theorem bisociation_is_novel :
  forall domain1 domain2 : nat,
  forall cp : CreativeProduct,
    bisociation domain1 domain2 cp ->
    cp_novelty cp >= 80.
Proof.
  intros domain1 domain2 cp H_bisoc.
  unfold bisociation in H_bisoc.
  destruct H_bisoc as [_ H_nov].
  exact H_nov.
Qed.

(** Productive thinking restructures *)
Theorem productive_restructures :
  forall i : Insight,
    productive_thinking i ->
    insight_restructuring i = true.
Proof.
  intros i H_prod.
  unfold productive_thinking in H_prod.
  exact H_prod.
Qed.

(** Optimal flow requires balance *)
Theorem optimal_flow_balanced :
  forall f : FlowState,
    optimal_flow f ->
    flow_challenge_skill_balance f = true.
Proof.
  intros f H_opt.
  unfold optimal_flow in H_opt.
  destruct H_opt as [H_balance _].
  exact H_balance.
Qed.

(** Optimal flow requires concentration *)
Theorem optimal_flow_concentrated :
  forall f : FlowState,
    optimal_flow f ->
    flow_concentration f >= 80.
Proof.
  intros f H_opt.
  unfold optimal_flow in H_opt.
  destruct H_opt as [_ H_conc].
  exact H_conc.
Qed.

(** Exploration stays within space *)
Theorem exploration_in_space :
  forall cs : ConceptualSpace,
  forall cp : CreativeProduct,
    explore_space cs cp ->
    In (cp_domain cp) (cs_dimensions cs).
Proof.
  intros cs cp H_explore.
  unfold explore_space in H_explore.
  exact H_explore.
Qed.
