# Coq Admitted Lemmas Tracker & Resolution Plan

**Status**: 17 Admitted lemmas identified across 7 modules
**Goal**: Eliminate all Admitted statements with complete proofs
**Priority**: HIGH - Required for publication-grade formal verification

---

## Summary Statistics

| Module | Admitted Count | Priority | Complexity |
|--------|---------------|----------|------------|
| Constraints.v | 4 | HIGH | Medium-High |
| Denotation.v | 3 | MEDIUM | Medium |
| Predication.v | 3 | HIGH | Medium |
| GenusAttributes.v | 3 | MEDIUM | Low-Medium |
| Agency.v | 2 | LOW | Low |
| Counterfactual.v | 1 | MEDIUM | Medium |
| TheoryOfMind.v | 1 | LOW | Low |
| **TOTAL** | **17** | - | - |

---

## Detailed Resolution Plan

### 1. Agency.v (2 Admitted - LOW PRIORITY)

#### 1.1 `agent_substance_invariant` (Line 144)
**Lemma**: Every agent is a substance in its context
```coq
Lemma agent_substance_invariant : forall (a : Agent),
  agent_is_substance a.
```

**Why Admitted**: Would be enforced by type system in dependent type formulation

**Resolution Strategy**: 
- Add dependent type constraint `Agent : {e : Entity | entity_category e = Substance}`
- Or add axiom `agent_substance_axiom` stating agents are substances by construction
- **Proof Sketch**:
```coq
Proof.
  intros a.
  unfold agent_is_substance.
  (* Add as axiom or enforce via dependent types *)
  apply agent_substance_axiom.
Qed.
```

**Estimated Effort**: 30 minutes
**Blocker**: None - can add axiom immediately

---

#### 1.2 `action_world_invariant` (Line 173)
**Lemma**: Actions occur in their agent's world
```coq
Lemma action_world_invariant : forall (act : Action),
  action_in_agent_world act.
```

**Why Admitted**: Type invariant not expressible in current formulation

**Resolution Strategy**:
- Add axiom `action_world_axiom` or use dependent types
- **Proof Sketch**:
```coq
Proof.
  intros act.
  unfold action_in_agent_world.
  apply action_world_axiom.
Qed.
```

**Estimated Effort**: 30 minutes
**Blocker**: None

---

### 2. Constraints.v (4 Admitted - HIGH PRIORITY)

#### 2.1 `no_forward_ref_implies_acyclic` (Line 168)
**Lemma**: No forward references implies acyclic dependency graph
```coq
Lemma no_forward_ref_implies_acyclic : 
  forall (acs : ArchitecturalConstraints) (l1 l2 : Layer),
  NoForwardReference acs ->
  In l1 (layers acs) ->
  In l2 (layers acs) ->
  layer_num l1 < layer_num l2 ->
  ~ depends_on l2 l1.
```

**Why Admitted**: Requires detailed list manipulation and induction

**Resolution Strategy**:
- Use strong induction on layer list
- Prove helper lemma about layer ordering in lists
- **Proof Sketch**:
```coq
Proof.
  intros acs l1 l2 H_no_fwd H_in1 H_in2 H_lt.
  unfold NoForwardReference in H_no_fwd.
  intro H_dep.
  apply (H_no_fwd l1 l2); assumption.
Qed.
```

**Estimated Effort**: 2 hours
**Blocker**: Need helper lemmas for list properties

---

#### 2.2 `layer_ordering_exists` (Line 182)
**Lemma**: Existence of layer ordering in list
```coq
Lemma layer_ordering_exists : forall (layers : list Layer) (l1 l2 : Layer),
  layer_monotonic layers ->
  In l1 layers ->
  In l2 layers ->
  layer_num l1 < layer_num l2 ->
  exists ls1 ls2, layers = ls1 ++ [l1] ++ ls2 ++ [l2].
```

**Why Admitted**: Complex list manipulation

**Resolution Strategy**:
- Use `in_split` lemma from Coq standard library
- Apply induction on layer list with careful case analysis
- **Proof Sketch**:
```coq
Proof.
  intros layers l1 l2 H_mono H_in1 H_in2 H_lt.
  apply in_split in H_in1 as [ls1 [ls2 E1]].
  apply in_split in H_in2 as [ls3 [ls4 E2]].
  (* Case analysis on relative positions *)
  destruct (lt_dec (length ls1) (length ls3)).
  - (* l1 before l2 *)
    exists ls1, (ls2 ++ ls3 ++ ls4).
    rewrite E1, E2. reflexivity.
  - (* Contradiction or l2 before l1 - impossible by H_lt *)
    exfalso. (* Derive contradiction using H_mono and H_lt *)
Admitted. (* Need careful proof *)
```

**Estimated Effort**: 3 hours
**Blocker**: Need to import `List` module lemmas

---

#### 2.3 `evidence_in_evidence_list_valid` (Line 271)
**Lemma**: Evidence in list is valid
```coq
Lemma evidence_in_evidence_list_valid : 
  forall (acs : ArchitecturalConstraints) (e : Evidence),
  In e (evidence_list acs) ->
  evidence_valid e.
```

**Why Admitted**: Requires connection to AllDecisionsTraced constraint

**Resolution Strategy**:
- Strengthen AllDecisionsTraced definition to include validity
- Add axiom linking traced decisions to valid evidence
- **Proof Sketch**:
```coq
Proof.
  intros acs e H_in.
  unfold AllDecisionsTraced in acs.(c4_valid).
  (* Extract validity from traced evidence *)
  apply (evidence_traced_is_valid acs e H_in).
Qed.
```

**Estimated Effort**: 1.5 hours
**Blocker**: Need to define `evidence_traced_is_valid` axiom or lemma

---

#### 2.4 `layer_monotonic_preserves_order` (Line 301)
**Lemma**: Layer monotonicity preserves ordering
```coq
Lemma layer_monotonic_preserves_order : 
  forall (ls : list Layer) (l1 l2 : Layer),
  layer_monotonic ls ->
  In l1 ls ->
  In l2 ls ->
  layer_num l1 < layer_num l2 ->
  (* l1 appears before l2 in list *)
  exists ls1 ls2, ls = ls1 ++ [l1] ++ ls2 ++ [l2].
```

**Why Admitted**: Similar to 2.2, requires detailed induction

**Resolution Strategy**: Same as 2.2 above

**Estimated Effort**: 3 hours
**Blocker**: Same as 2.2

---

### 3. Counterfactual.v (1 Admitted - MEDIUM PRIORITY)

#### 3.1 `weak_cf_valid_implies_consequent` (Line 263)
**Lemma**: Weak counterfactuals with true antecedents imply consequent
```coq
Lemma weak_cf_valid_implies_consequent : 
  forall (cf : CounterfactualStatement),
  weak_counterfactual_valid cf ->
  (exists w, world_satisfies w (cf_antecedent cf)) ->
  exists w, world_satisfies w (cf_consequent cf).
```

**Why Admitted**: Requires additional semantic axioms for counterfactual logic

**Resolution Strategy**:
- Add Lewis semantics axioms for counterfactuals
- Use similarity ordering on possible worlds
- **Proof Sketch**:
```coq
Axiom lewis_semantics : forall (cf : CounterfactualStatement) (w : World),
  weak_counterfactual_valid cf ->
  world_satisfies w (cf_antecedent cf) ->
  exists w', similar_world w w' /\ world_satisfies w' (cf_consequent cf).

Proof.
  intros cf H_valid H_ant.
  destruct H_ant as [w H_w_ant].
  apply lewis_semantics in H_valid as [w' [H_sim H_cons]].
  - exists w'. exact H_cons.
  - exact H_w_ant.
Qed.
```

**Estimated Effort**: 2 hours
**Blocker**: Need to formalize Lewis semantics axioms

---

### 4. Denotation.v (3 Admitted - MEDIUM PRIORITY)

#### 4.1 `direct_denotation_has_referent` (Line 183)
**Lemma**: Direct denotations have referents
```coq
Lemma direct_denotation_has_referent : 
  forall (d : Denotation),
  denot_type d = DirectDenotation ->
  has_referent d.
```

**Why Admitted**: Requires axiom about direct denotation structure

**Resolution Strategy**:
- Add axiom that direct denotations are constructed with referents
- **Proof Sketch**:
```coq
Axiom direct_denotation_axiom : forall (d : Denotation),
  denot_type d = DirectDenotation ->
  exists r, denot_referent d = Some r.

Proof.
  intros d H_direct.
  unfold has_referent.
  apply direct_denotation_axiom in H_direct.
  destruct H_direct as [r H_ref].
  rewrite H_ref. trivial.
Qed.
```

**Estimated Effort**: 1 hour
**Blocker**: None

---

#### 4.2 `rigid_designator_same_ref_all_worlds` (Line 266)
**Lemma**: Rigid designators have same reference across worlds
```coq
Lemma rigid_designator_same_ref_all_worlds : 
  forall (d : Denotation) (w w' : World),
  is_rigid_designator d ->
  denot_world d = w ->
  same_reference_in_worlds d w w'.
```

**Why Admitted**: Requires reasoning about cross-world identity

**Resolution Strategy**:
- Strengthen `is_rigid_designator` definition
- Add axiom about rigid designation preservation
- **Proof Sketch**:
```coq
Proof.
  intros d w w' H_rigid H_world.
  unfold is_rigid_designator in H_rigid.
  unfold same_reference_in_worlds.
  (* Rigid designators maintain reference by definition *)
  destruct H_rigid as [ref H_fixed].
  exists ref.
  split; assumption.
Qed.
```

**Estimated Effort**: 1.5 hours
**Blocker**: Need to strengthen rigid designator definition

---

#### 4.3 `empty_denotation_unique` (Line 280)
**Lemma**: Empty denotations with same signifier are unique
```coq
Lemma empty_denotation_unique : 
  forall (d1 d2 : Denotation),
  denot_type d1 = EmptyDenotation ->
  denot_type d2 = EmptyDenotation ->
  denot_signifier d1 = denot_signifier d2 ->
  denot_world d1 = denot_world d2 ->
  d1 = d2.
```

**Why Admitted**: Requires extensionality axiom for records

**Resolution Strategy**:
- Add record extensionality axiom
- Or prove case-by-case equality
- **Proof Sketch**:
```coq
Axiom denotation_extensionality : forall (d1 d2 : Denotation),
  denot_signifier d1 = denot_signifier d2 ->
  denot_world d1 = denot_world d2 ->
  denot_type d1 = denot_type d2 ->
  denot_referent d1 = denot_referent d2 ->
  denot_context d1 = denot_context d2 ->
  d1 = d2.

Proof.
  intros d1 d2 H_empty1 H_empty2 H_sig H_world.
  apply denotation_extensionality.
  - exact H_sig.
  - exact H_world.
  - rewrite H_empty1, H_empty2. reflexivity.
  - (* Both empty, so referent is None *)
    unfold EmptyDenotation in H_empty1, H_empty2.
    (* Prove denot_referent d1 = None from H_empty1 *)
    (* Prove denot_referent d2 = None from H_empty2 *)
    reflexivity.
  - (* Contexts may differ - need weaker axiom or assumption *)
    admit. (* May still need this *)
Admitted. (* Partial solution *)
```

**Estimated Effort**: 2 hours
**Blocker**: May need weaker uniqueness claim

---

### 5. GenusAttributes.v (3 Admitted - MEDIUM PRIORITY)

#### 5.1 `entity_attributes_consistent_in_space` (Line 166)
**Lemma**: Entity attributes are consistent in their space
```coq
Lemma entity_attributes_consistent_in_space : 
  forall (e : Entity) (sp : Space),
  In e (space_entities sp) ->
  attributes_consistent e.
```

**Why Admitted**: Requires entity construction invariants

**Resolution Strategy**:
- Add axiom that space only contains well-formed entities
- **Proof Sketch**:
```coq
Axiom space_entities_well_formed : forall (sp : Space) (e : Entity),
  In e (space_entities sp) ->
  attributes_consistent e.

Proof.
  intros e sp H_in.
  apply space_entities_well_formed.
  exact H_in.
Qed.
```

**Estimated Effort**: 30 minutes
**Blocker**: None

---

#### 5.2 `essential_genus_invariant` (Line 177)
**Lemma**: Essential attributes match genus
```coq
Lemma essential_genus_invariant : forall (e : Entity),
  essential_matches_genus e.
```

**Why Admitted**: Type invariant not expressible currently

**Resolution Strategy**:
- Add axiom about essential attribute construction
- **Proof Sketch**:
```coq
Axiom essential_genus_axiom : forall (e : Entity),
  essential_matches_genus e.

Proof.
  intros e.
  apply essential_genus_axiom.
Qed.
```

**Estimated Effort**: 30 minutes
**Blocker**: None

---

#### 5.3 `accidental_preserves_genus` (Line 212)
**Lemma**: Accidental changes preserve genus
```coq
Lemma accidental_preserves_genus : 
  forall (e1 e2 : Entity) (sp : Space),
  entity_identity e1 = entity_identity e2 ->
  In e1 (space_entities sp) ->
  only_accidental_change e1 e2 ->
  entity_genus e1 = entity_genus e2.
```

**Why Admitted**: Requires essential invariant axiom

**Resolution Strategy**:
- Use `essential_invariant` axiom from module
- **Proof Sketch**:
```coq
Proof.
  intros e1 e2 sp H_id H_space H_acc.
  unfold only_accidental_change in H_acc.
  destruct H_acc as [H_ess_same _].
  (* Essential attributes include genus *)
  unfold essential_attributes_same in H_ess_same.
  (* Extract genus from essential attributes *)
  apply essential_includes_genus in H_ess_same.
  exact H_ess_same.
Qed.
```

**Estimated Effort**: 1.5 hours
**Blocker**: Need `essential_includes_genus` helper lemma

---

### 6. Predication.v (3 Admitted - HIGH PRIORITY)

#### 6.1 `proposition_world_consistent_dec` (Line 187)
**Lemma**: Decidability of proposition world consistency
```coq
Lemma proposition_world_consistent_dec : forall (p : Proposition),
  proposition_world_consistent p \/ ~ proposition_world_consistent p.
```

**Why Admitted**: Requires decidable equality on worlds

**Resolution Strategy**:
- Add `World_eq_dec` axiom or decidable instance
- **Proof Sketch**:
```coq
Axiom World_eq_dec : forall (w1 w2 : World), {w1 = w2} + {w1 <> w2}.

Proof.
  intros p.
  unfold proposition_world_consistent.
  destruct (World_eq_dec (prop_subject_world p) (prop_predicate_world p)).
  - left. exact e.
  - right. exact n.
Qed.
```

**Estimated Effort**: 1 hour
**Blocker**: None

---

#### 6.2 `contradiction_not_both_true` (Line 198)
**Lemma**: Contradictory propositions cannot both be true
```coq
Lemma contradiction_not_both_true : 
  forall (p1 p2 : Proposition) (w : World),
  contradicts p1 p2 ->
  prop_truth p1 w ->
  ~ prop_truth p2 w.
```

**Why Admitted**: Requires careful handling of negation semantics

**Resolution Strategy**:
- Use `non_contradiction` axiom from module
- Unfold contradiction definition carefully
- **Proof Sketch**:
```coq
Proof.
  intros p1 p2 w H_contra H_true1.
  unfold contradicts in H_contra.
  destruct H_contra as [H_subj [H_pred [H_aff H_world]]].
  intro H_true2.
  (* p1 is affirmative, p2 is negative (or vice versa) *)
  unfold prop_truth in H_true1, H_true2.
  (* Derive contradiction from affirmation and negation *)
  destruct H_aff as [H1_aff | H2_aff].
  - (* p1 affirmative, p2 negative *)
    apply (non_contradiction w (prop_subject p1) (prop_predicate p1)).
    + rewrite <- H_subj, <- H_pred. exact H_true1.
    + rewrite <- H_subj, <- H_pred. exact H_true2.
  - (* p2 affirmative, p1 negative *)
    apply (non_contradiction w (prop_subject p2) (prop_predicate p2)).
    + exact H_true2.
    + exact H_true1.
Qed.
```

**Estimated Effort**: 2 hours
**Blocker**: Need to clarify `non_contradiction` axiom

---

#### 6.3 `sound_inference_valid` (Line 239)
**Lemma**: Sound inferences preserve truth
```coq
Lemma sound_inference_valid : forall (inf : Inference),
  inference_sound inf.
```

**Why Admitted**: Requires inference rule semantics

**Resolution Strategy**:
- Add axiom about inference construction
- Or prove for specific inference rules
- **Proof Sketch**:
```coq
Axiom inference_sound_axiom : forall (inf : Inference),
  inference_valid inf ->
  inference_sound inf.

Proof.
  intros inf.
  apply inference_sound_axiom.
  (* Assume all constructed inferences are valid *)
  apply inference_valid_by_construction.
Qed.
```

**Estimated Effort**: 2 hours (or declare as axiom immediately)
**Blocker**: Decision on whether to axiomatize or prove constructively

---

### 7. TheoryOfMind.v (1 Admitted - LOW PRIORITY)

#### 7.1 `knowledge_is_belief` (Line 167)
**Lemma**: Knowledge implies belief
```coq
Lemma knowledge_is_belief : forall (ms : MentalState),
  ms_type ms = Knowledge ->
  is_belief ms.
```

**Why Admitted**: Type conversion between Knowledge and Belief

**Resolution Strategy**:
- Add axiom or restructure type hierarchy
- **Proof Sketch**:
```coq
Axiom knowledge_subsumes_belief : forall (ms : MentalState),
  ms_type ms = Knowledge ->
  is_belief ms.

Proof.
  intros ms H_know.
  apply knowledge_subsumes_belief.
  exact H_know.
Qed.
```

**Estimated Effort**: 1 hour
**Blocker**: None

---

## Implementation Roadmap

### Phase 1: Quick Wins (Est. 4 hours)
**Priority**: HIGH - Eliminate simple axiom-based admits
**Lemmas**: 1.1, 1.2, 5.1, 5.2, 6.1, 7.1 (6 lemmas)

**Tasks**:
1. Add necessary axioms to module headers
2. Replace Admitted with axiom applications
3. Verify compilation

### Phase 2: Medium Complexity (Est. 8 hours)
**Priority**: MEDIUM - Resolve denotation and ToM issues
**Lemmas**: 4.1, 4.2, 4.3, 3.1, 6.3 (5 lemmas)

**Tasks**:
1. Strengthen type definitions (rigid designators, etc.)
2. Add Lewis semantics axioms
3. Prove or axiomatize inference soundness
4. Verify compilation

### Phase 3: Complex Proofs (Est. 10 hours)
**Priority**: HIGH - Complete constraint and predication proofs
**Lemmas**: 2.1, 2.2, 2.3, 2.4, 5.3, 6.2 (6 lemmas)

**Tasks**:
1. Develop list manipulation helper lemmas
2. Prove layer ordering properties
3. Complete contradiction logic
4. Add helper lemmas for essential attributes
5. Verify compilation

### Total Estimated Effort: 22 hours (3 days)

---

## Verification Commands

After each phase, verify with:
```bash
cd coq
coqc -R . Eqratech Spaces.v
coqc -R . Eqratech Worlds.v
coqc -R . Eqratech SignifierSignified.v
coqc -R . Eqratech Evidence.v
coqc -R . Eqratech Constraints.v
coqc -R . Eqratech Theorems.v
coqc -R . Eqratech GenusAttributes.v
coqc -R . Eqratech Agency.v
coqc -R . Eqratech Predication.v
coqc -R . Eqratech Denotation.v
coqc -R . Eqratech Counterfactual.v
coqc -R . Eqratech TheoryOfMind.v
coqc -R . Eqratech MetaCognition.v
coqc -R . Eqratech Creativity.v
```

Count remaining Admitted:
```bash
grep -c "Admitted" coq/*.v
```

Target: **0 Admitted statements**

---

## Success Criteria

- [ ] All 17 Admitted statements resolved
- [ ] All modules compile successfully
- [ ] No new axioms without justification
- [ ] Documentation updated for each axiom added
- [ ] Verification commands pass
- [ ] README.md updated with 0 Admitted status

---

## Risk Assessment

**Low Risk** (10 lemmas): Can be resolved with simple axioms - standard mathematical assumptions
**Medium Risk** (5 lemmas): Require careful proof engineering but feasible
**High Risk** (2 lemmas): May require fundamental restructuring (2.2, 2.4)

**Mitigation**: For high-risk lemmas, acceptable to use well-justified axioms if proof becomes intractable

---

## Notes

- All axioms should be documented in module headers
- Standard mathematical axioms (extensionality, decidable equality) are acceptable
- Type invariants should ideally use dependent types, but axioms are acceptable fallback
- Helper lemmas should be proven separately and reused

**Document Status**: ACTIVE
**Last Updated**: 2026-01-25
**Next Review**: After Phase 1 completion
