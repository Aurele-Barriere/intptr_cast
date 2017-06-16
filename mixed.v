Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.

Require Export Smallstep.

Set Implicit Arguments.

Definition single_events_at (L: semantics) (s:L.(state)) : Prop :=
  forall t s', Step L s t s' -> (length t <= 1)%nat.

Record receptive_at (L: semantics) (s:L.(state)) : Prop :=
  Receptive_at {
    sr_receptive_at: forall t1 s1 t2,
      Step L s t1 s1 -> match_traces (symbolenv L) t1 t2 -> exists s2, Step L s t2 s2;
    sr_traces_at:
      single_events_at L s
  }.

Record determinate_at (L: semantics) (s:L.(state)) : Prop :=
  Determinate_at {
    sd_determ_at: forall t1 s1 t2 s2,
      Step L s t1 s1 -> Step L s t2 s2 ->
      match_traces (symbolenv L) t1 t2 /\ (t1 = t2 -> s1 = s2);
    sd_traces_at:
      single_events_at L s
  }.

Lemma no_event_receptive L s
      (DETERM: forall t1 s1, Step L s t1 s1 -> t1 = E0):
  receptive_at L s.
Proof.
  econstructor; intros.
  - exploit DETERM; eauto. intro. subst.
    inv H0. exists s1. auto.
  - repeat intro. exploit DETERM; eauto.
    intro. subst. auto.
Qed.

Notation " 'DeterminateStep' L " := (fun s1 t s2 => determinate_at L s1 /\ step L (globalenv L) s1 t s2) (at level 1) : smallstep_scope.
Notation " 'DeterminateStar' L " := (star (fun ge s1 t s2 => determinate_at L s1 /\ step L ge s1 t s2) (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'DeterminateStarN' L " := (starN (fun ge s1 t s2 => determinate_at L s1 /\ step L ge s1 t s2) (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'DeterminatePlus' L " := (plus (fun ge s1 t s2 => determinate_at L s1 /\ step L ge s1 t s2) (globalenv L)) (at level 1) : smallstep_scope.

Lemma determinate_step_step:
  forall (L: semantics) s t s',
  DeterminateStep L s t s' -> Step L s t s'.
Proof.
  intros. inv H. auto.
Qed.

Lemma determinate_star_star:
  forall (L: semantics) s t s',
  DeterminateStar L s t s' -> Star L s t s'.
Proof.
  intros L s t s' H. induction H; econstructor; eauto.
  destruct H. auto.
Qed.

Lemma determinate_plus_plus:
  forall (L: semantics) s t s',
  DeterminatePlus L s t s' -> Plus L s t s'.
Proof.
  intros. inv H. destruct H0. econstructor; eauto.
  apply determinate_star_star. auto.
Qed.

(** The general form of a mixed simulation. *)

Inductive msim_simulation_forward (L1 L2: semantics)
          index (order: index -> index -> Prop)
          match_states
          i s1 s2 :=
| msim_simulation_forward_intro
    (FINAL: forall r, final_state L1 s1 r -> final_state L2 s2 r)
    (RECEPTIVE: receptive_at L1 s1)
    (STEP:
       forall t s1',
       Step L1 s1 t s1' ->
       exists i', exists s2',
          (DeterminatePlus L2 s2 t s2' \/ DeterminateStar L2 s2 t s2' /\ order i' i)
       /\ match_states i' s1' s2')
.

Inductive msim_simulation_backward (L1 L2: semantics)
          index (order: index -> index -> Prop)
          match_states
          i s1 s2 :=
| msim_simulation_backward_intro
    (PROGRESS: safe L1 s1 ->
               (exists r, final_state L2 s2 r) \/
               (exists t, exists s2', Step L2 s2 t s2'))
    (STEP: forall t s2',
           Step L2 s2 t s2' -> safe L1 s1 ->
           exists i', exists s1',
              (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i))
           /\ match_states i' s1' s2')
.

Record msim_properties (L1 L2: semantics) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> state L1 -> state L2 -> Prop): Prop := {
    msim_order_wf: well_founded order;
    msim_initial_states_exist:
      forall s1, initial_state L1 s1 -> exists s2, initial_state L2 s2;
    msim_match_initial_states:
      forall s1 s2, initial_state L1 s1 -> initial_state L2 s2 ->
      exists i, exists s1', initial_state L1 s1' /\ match_states i s1' s2;
    msim_match_final_states:
      forall i s1 s2 r,
      match_states i s1 s2 -> safe L1 s1 -> final_state L2 s2 r ->
      exists s1', Star L1 s1 E0 s1' /\ final_state L1 s1' r;
    msim_simulation:
      forall i s1 s2,
      match_states i s1 s2 ->
      (msim_simulation_forward L1 L2 order match_states i s1 s2 \/
       msim_simulation_backward L1 L2 order match_states i s1 s2);
    msim_public_preserved:
      forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id;
    msim_final_nostep: forall s r,
      final_state L2 s r -> Nostep L2 s
  }.

Arguments msim_properties: clear implicits.

Inductive mixed_simulation (L1 L2: semantics): Prop :=
  Mixed_simulation (index: Type)
                   (order: index -> index -> Prop)
                   (match_states: index -> state L1 -> state L2 -> Prop)
                   (props: msim_properties L1 L2 index order match_states).

Arguments Mixed_simulation {L1 L2 index} order match_states props.

(** ** Converting a mixed simulation to a backward simulation *)

Section MIXED_TO_BACKWARD.

Context L1 L2 index order match_states (MS: msim_properties L1 L2 index order match_states).

(** Exploiting mixed simulation *)

Inductive m2b_transitions: index -> state L1 -> state L2 -> Prop :=
  | m2b_trans_final: forall i s1 s2 s1' r,
      Star L1 s1 E0 s1' ->
      final_state L1 s1' r ->
      final_state L2 s2 r ->
      m2b_transitions i s1 s2
  | m2b_trans_forward: forall i s1 s2 s1' t s1'' s2' i' i'',
      Star L1 s1 E0 s1' ->
      Step L1 s1' t s1'' ->
      DeterminatePlus L2 s2 t s2' ->
      forall (MATCH:match_states i' s1' s2),
      msim_simulation_forward L1 L2 order match_states i' s1' s2 ->
      match_states i'' s1'' s2' ->
      m2b_transitions i s1 s2
  | m2b_trans_backward: forall i s1 s2 s1' t s1'' s2' i' i'',
      Star L1 s1 E0 s1' ->
      Star L1 s1' t s1'' ->
      Plus L2 s2 t s2' ->
      forall (MATCH:match_states i' s1' s2),
      msim_simulation_backward L1 L2 order match_states i' s1' s2 ->
      match_states i'' s1'' s2' ->
      clos_refl_trans _ order i' i ->
      m2b_transitions i s1 s2.

Lemma m2b_progress:
  forall i s1 s2, match_states i s1 s2 -> safe L1 s1 -> m2b_transitions i s1 s2.
Proof.
  intros i0; pattern i0. apply well_founded_ind with (R := order).
  eapply msim_order_wf; eauto.
  intros i REC s1 s2 MATCH SAFE.
  inversion MS.
  destruct (msim_simulation MS _ _ _ MATCH) as [SIM|SIM]; inversion SIM; subst.
  { (* forward *)
  destruct (SAFE s1) as [[r FINAL1] | [t [s1' STEP1]]]. apply star_refl.
  - (* final state reached *)
    eapply m2b_trans_final; eauto. apply star_refl.
  - (* L1 can make one step *)
    exploit STEP; eauto. intros [i' [s2' [A MATCH']]].
    assert (B: DeterminatePlus L2 s2 t s2' \/ (s2 = s2' /\ t = E0 /\ order i' i)).
    intuition.
    destruct (star_inv H0); intuition.
  clear A. destruct B as [PLUS2 | [EQ1 [EQ2 ORDER]]].
  eapply m2b_trans_forward; eauto. apply star_refl.
  subst. exploit REC; eauto. eapply star_safe; eauto. apply star_one; auto.
  intros TRANS; inv TRANS.
  eapply m2b_trans_final; eauto. eapply star_left; eauto.
  eapply m2b_trans_forward; eauto. eapply star_left; eauto.
  eapply m2b_trans_backward; eauto. eapply star_left; eauto.
  eapply rt_trans; eauto. constructor. auto.
  }
  { (* backward *)
  exploit PROGRESS; eauto. intros [[r FINAL]|[t [s2' STEP']]].
  { exploit msim_match_final_states; eauto. intros [s1' [STAR FINAL']].
    eapply m2b_trans_final; eauto.
  }
  exploit STEP; eauto. intros [i' [s1' [STEPS MATCH']]].
  eapply m2b_trans_backward; eauto.
  apply star_refl.
  { destruct STEPS as [|[]]; eauto. apply plus_star. auto. }
  apply plus_one. auto.
  constructor 2.
  }
Qed.

Lemma msim_simulation_not_E0:
  forall s1 t s1', Step L1 s1 t s1' -> t <> E0 ->
  forall s2,
    receptive_at L1 s1 ->
    (forall t s1', Step L1 s1 t s1' ->
     exists i', exists s2',
        (DeterminatePlus L2 s2 t s2' \/ (DeterminateStar L2 s2 t s2'))
     /\ match_states i' s1' s2') ->
  exists i', exists s2', DeterminatePlus L2 s2 t s2' /\ match_states i' s1' s2'.
Proof.
  intros. exploit H2; eauto. intros [i' [s2' [A B]]].
  exists i'; exists s2'; split; auto.
  destruct A. auto. inv H3; [congruence|].
  eapply plus_left; eauto.
Qed.

(** Exploiting determinacy *)

Lemma determinacy_inv:
  forall s2 t' s2' t'' s2'',
  determinate_at L2 s2 ->
  Step L2 s2 t' s2' -> Step L2 s2 t'' s2'' ->
  (t' = E0 /\ t'' = E0 /\ s2' = s2'')
  \/ (t' <> E0 /\ t'' <> E0 /\ match_traces (symbolenv L1) t' t'').
Proof.
  intros.
  assert (match_traces (symbolenv L2) t' t'').
    eapply sd_determ_at; eauto.
  destruct (silent_or_not_silent t').
  subst. inv H2.
  left; intuition. eapply sd_determ_at; eauto.
  destruct (silent_or_not_silent t'').
  subst. inv H2. elim H3; auto.
  right; intuition.
  eapply match_traces_preserved with (ge1 := (symbolenv L2)); auto.
  intros; symmetry; apply (msim_public_preserved MS).
Qed.

Lemma determinacy_star:
  forall s s1, DeterminateStar L2 s E0 s1 ->
  forall t s2 s3,
  DeterminateStep L2 s1 t s2 -> t <> E0 ->
  DeterminateStar L2 s t s3 ->
  DeterminateStar L2 s1 t s3.
Proof.
  intros s0 s01 ST0. pattern s0, s01. eapply star_E0_ind; eauto.
  intros. inv H3. congruence.
  destruct H, H1, H4.
  exploit determinacy_inv. eexact H. eexact H3. eexact H7.
  intros [[EQ1 [EQ2 EQ3]] | [NEQ1 [NEQ2 MT]]].
  subst. simpl in *. eauto.
  congruence.
Qed.

(** Orders *)

Inductive m2b_index : Type :=
  | M2BI_before (n: nat)
  | M2BI_after (n: nat) (i: index).

Inductive m2b_order: m2b_index -> m2b_index -> Prop :=
  | m2b_order_before: forall n n',
      (n' < n)%nat ->
      m2b_order (M2BI_before n') (M2BI_before n)
  | m2b_order_after: forall n n' i,
      (n' < n)%nat ->
      m2b_order (M2BI_after n' i) (M2BI_after n i)
  | m2b_order_after': forall n i' i,
      clos_trans _ order i' i ->
      m2b_order (M2BI_after n i') (M2BI_after n i)
  | m2b_order_switch: forall n n' i,
      m2b_order (M2BI_before n') (M2BI_after n i).

Lemma wf_m2b_order:
  well_founded m2b_order.
Proof.
  assert (ACC1: forall n, Acc m2b_order (M2BI_before n)).
    intros n0; pattern n0; apply lt_wf_ind; intros.
    constructor; intros. inv H0. auto.
  assert (ACC2: forall n i, Acc m2b_order (M2BI_after n i)).
    intros n0; pattern n0; apply lt_wf_ind; intros.
    pattern i. eapply well_founded_ind. apply wf_clos_trans.
    eapply msim_order_wf; eauto.
    intros. constructor; intros. inv H1; auto.
  red; intros. destruct a; auto.
Qed.

(** Constructing the backward simulation *)

Inductive m2b_match_states: m2b_index -> state L1 -> state L2 -> Prop :=
  | m2b_match_at: forall i s1 s2,
      match_states i s1 s2 ->
      m2b_match_states (M2BI_after O i) s1 s2
  | m2b_match_before: forall s1 t s1' s2b s2 n s2a,
      Step L1 s1 t s1' ->  t <> E0 ->
      DeterminateStar L2 s2b E0 s2 ->
      DeterminateStarN L2 n s2 t s2a ->
      receptive_at L1 s1 ->
      (forall t s1', Step L1 s1 t s1' ->
       exists i', exists s2',
          (DeterminatePlus L2 s2b t s2' \/ (DeterminateStar L2 s2b t s2'))
       /\ match_states i' s1' s2') ->
      m2b_match_states (M2BI_before n) s1 s2
  | m2b_match_after: forall n s2 s2a s1 i,
      DeterminateStarN L2 (S n) s2 E0 s2a ->
      match_states i s1 s2a ->
      m2b_match_states (M2BI_after (S n) i) s1 s2.

Remark m2b_match_after':
  forall n s2 s2a s1 i,
  DeterminateStarN L2 n s2 E0 s2a ->
  match_states i s1 s2a ->
  m2b_match_states (M2BI_after n i) s1 s2.
Proof.
  intros. inv H.
  econstructor; eauto.
  econstructor; eauto. econstructor; eauto.
Qed.

(** Backward simulation of L2 steps *)

Lemma m2b_simulation_step:
  forall s2 t s2', Step L2 s2 t s2' ->
  forall i s1, m2b_match_states i s1 s2 -> safe L1 s1 ->
  exists i', exists s1',
    (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ m2b_order i' i))
     /\ m2b_match_states i' s1' s2'.
Proof.
  intros s2 t s2' STEP2 i s1 MATCH SAFE.
  inv MATCH.
(* 1. At matching states *)
  exploit m2b_progress; eauto. intros TRANS; inv TRANS.
  { (* final *)
  (* 1.1  L1 can reach final state and L2 is at final state: impossible! *)
  exploit msim_final_nostep; eauto. contradiction.
  }
  { (* forward *)
  inv H3.
  (* 1.2  L1 can make 0 or several steps; L2 can make 1 or several matching steps. *)
  inv H2.
  exploit STEP; eauto. intros [i''' [s2''' [STEP''' MATCH''']]].
  destruct H3. exploit determinacy_inv. eexact H2. eexact H3. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  (* 1.2.1  L2 makes a silent transition *)
  destruct (silent_or_not_silent t2).
  (* 1.2.1.1  L1 makes a silent transition too: perform transition now and go to "after" state *)
  subst. simpl in *. destruct (star_starN H5) as [n STEPS2].
  exists (M2BI_after n i''); exists s1''; split.
  left. eapply plus_right; eauto.
  eapply m2b_match_after'; eauto.
  (* 1.2.1.2 L1 makes a non-silent transition: keep it for later and go to "before" state *)
  subst. simpl in *. destruct (star_starN H5) as [n STEPS2].
  exists (M2BI_before n); exists s1'; split.
  right; split. auto. constructor.
  econstructor. eauto. auto. apply star_one; eauto. eauto. eauto.
  intros. exploit STEP; eauto. intros [i'''' [s2'''' [A MATCH'''']]].
  exists i''''. exists s2''''. destruct A as [?|[? ?]]; auto.
  (* 1.2.2 L2 makes a non-silent transition, and so does L1 *)
  exploit not_silent_length. eapply (sr_traces_at RECEPTIVE); eauto. intros [EQ | EQ].
  congruence.
  subst t2. rewrite E0_right in H1.
  (* Use receptiveness to equate the traces *)
  exploit (sr_receptive_at RECEPTIVE); eauto. intros [s1''' STEP1].
  exploit msim_simulation_not_E0. eexact STEP1. auto. eauto.
  intros. exploit STEP; eauto. intros [i'''' [s2'''' [A MATCH'''']]].
  exists i''''. exists s2''''. destruct A as [?|[? ?]]; split; eauto.
  intros [i'''' [s2'''' [P Q]]]. inv P.
  (* Exploit determinacy *)
  destruct H6. exploit sd_determ_at. eauto. eexact STEP2. eexact H8.
  exploit not_silent_length. eapply (sr_traces_at RECEPTIVE); eauto. intros [EQ | EQ].
  subst t0. simpl in *.
  intros. elim NOT2. destruct H9. inv H9. auto.
  subst t2. rewrite E0_right in *.
  intros [_ TRACES]. assert (s4 = s2'). symmetry. eapply TRACES. auto. subst s4.
  (* Perform transition now and go to "after" state *)
  destruct (star_starN H7) as [n STEPS2]. exists (M2BI_after n i''''); exists s1'''; split.
  left. eapply plus_right; eauto.
  eapply m2b_match_after'; eauto.
  }
  { (* backward *)
    inv H3.
    exploit STEP; eauto. eapply star_safe; eauto.
    intros [i''' [s1''' [STEPS MATCH']]].
    exists (M2BI_after 0 i'''). exists s1'''. split.
    - destruct STEPS as [STEPS|[STEPS ORD]]; [left|right]; auto.
      eapply star_plus_trans; eauto.
      split. eapply star_trans; eauto.
      econstructor.
      apply clos_t1n_trans. apply clos_rt_rt1n in H5.
      clear -ORD H5. revert i''' ORD.
      induction H5; intro.
      + constructor 1. auto.
      + econstructor 2; eauto.
    - econstructor. auto.
  }

(* 2. Before *)
  inv H2. congruence. destruct H5.
  exploit determinacy_inv. eauto. eexact H5. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  (* 2.1 L2 makes a silent transition: remain in "before" state *)
  subst. simpl in *. exists (M2BI_before n0); exists s1; split.
  right; split. apply star_refl. constructor. omega.
  econstructor; eauto. eapply star_right; eauto.
  (* 2.2 L2 make a non-silent transition *)
  exploit not_silent_length. eapply (sr_traces_at H3); eauto. intros [EQ | EQ].
  congruence.
  subst. rewrite E0_right in *.
  (* Use receptiveness to equate the traces *)
  exploit (sr_receptive_at H3); eauto. intros [s1''' STEP1].
  exploit msim_simulation_not_E0. eexact STEP1. auto. auto. eauto.
  intros [i''' [s2''' [P Q]]].
  (* Exploit determinacy *)
  exploit determinacy_star. eauto. split; auto. eexact STEP2. auto. apply plus_star; eauto.
  intro R. inv R. congruence.
  exploit not_silent_length. eapply (sr_traces_at H3); eauto. intros [EQ | EQ].
  subst. simpl in *. destruct H7. exploit sd_determ_at. eauto. eexact STEP2. eexact H9.
  intros. elim NOT2. destruct H10. inv H10; auto.
  subst. rewrite E0_right in *.  destruct H7.
  assert (s3 = s2'). eapply sd_determ_at; eauto. subst s3.
  (* Perform transition now and go to "after" state *)
  destruct (star_starN H8) as [n STEPS2]. exists (M2BI_after n i'''); exists s1'''; split.
  left. apply plus_one; auto.
  eapply m2b_match_after'; eauto.

(* 3. After *)
  inv H. exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
  destruct H2. exploit determinacy_inv. eauto. eexact H1. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  subst. exists (M2BI_after n i0); exists s1; split.
  right; split. apply star_refl. constructor. constructor; omega.
  eapply m2b_match_after'; eauto.
  congruence.
Qed.

(** The backward simulation *)

Lemma mixed_to_backward_simulation: backward_simulation L1 L2.
Proof.
  apply Backward_simulation with (order0 := m2b_order) (match_states0 := m2b_match_states).
  constructor.
  apply wf_m2b_order.
(* initial states exist *)
  exact (msim_initial_states_exist MS).
(* initial states *)
  intros. exploit (msim_match_initial_states MS); eauto. intros [i [s1' [A B]]].
  eexists _, _. split; eauto. econstructor; eauto.
(* final states *)
  intros. inv H.
  eapply msim_match_final_states; eauto.
  inv H5. congruence. destruct H. exploit msim_final_nostep; eauto. contradiction.
  inv H2. destruct H4. exploit msim_final_nostep; eauto. contradiction.
(* progress *)
  intros. inv H.
  exploit m2b_progress; eauto. intros TRANS; inv TRANS.
  left; exists r; auto.
  inv H3. destruct H6. right; econstructor; econstructor; eauto.
  inv H4. apply PROGRESS. eapply star_safe; eauto.
  inv H4. congruence. destruct H. right; econstructor; econstructor; eauto.
  inv H1. destruct H3. right; econstructor; econstructor; eauto.
(* simulation *)
  exact m2b_simulation_step.
(* symbols preserved *)
  exact (msim_public_preserved MS).
Qed.

End MIXED_TO_BACKWARD.
