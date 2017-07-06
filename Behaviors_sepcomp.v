Require Import Coqlib.
Require Import Smallstep.
Require Import Globalenvs.
Require Import Memory.
Require Import AST.
Require Import Events.
Require Import Values.
Require Import Syntax_sepcomp.
Require Import Semantics_sepcomp.
Require Import sflib.

Set Implicit Arguments.

Record ctx_properties F V (lang:language F V): Type := mk_ctx_properties {
  ctx_match_extends: lang.(lang_state) -> lang.(lang_state) -> Prop;
  ctx_match_inject: meminj -> lang.(lang_state) -> lang.(lang_state) -> Prop;

  ctx_mem_inject_incr:
    forall f f' (INCR: inject_incr f f'),
      ctx_match_inject f <2= ctx_match_inject f';

  ctx_valid_block:
    forall (me: Genv.t F V) s1 s2 m1 t m2 b
           (STEP: lang_step lang me s1 m1 t s2 m2)
           (VB: Mem.valid_block m1 b),
      Mem.valid_block m2 b;

  ctx_max_perm:
    forall (me: Genv.t F V) s1 s2 m1 t m2 b ofs p
           (STEP: lang_step lang me s1 m1 t s2 m2)
           (VB: Mem.valid_block m1 b)
           (PERM: Mem.perm m2 b ofs Max p),
      Mem.perm m1 b ofs Max p;

  ctx_readonly:
    forall (me: Genv.t F V) s1 s2 m1 t m2
           (STEP: lang_step lang me s1 m1 t s2 m2),
      Mem.unchanged_on (loc_not_writable m1) m1 m2;

  ctx_trace_length:
    forall me s1 s2 m t m'
           (STEP: lang_step lang me s1 m t s2 m'),
      (length t <= 1)%nat;

  ctx_mem_extends:
    forall (me: Genv.t F V) s1' m1' m1 s1
           (EXT: Mem.extends m1 m1')
           (MSTATE: ctx_match_extends s1 s1')
           (SAFE: lang_safe lang me s1 m1),
    <<PROGRESS: exists t s2' m2', lang_step lang me s1' m1' t s2' m2'>> /\
    <<STEP:
        forall t s2' m2' (STEP: lang_step lang me s1' m1' t s2' m2'),
        exists s2 m2,
           <<STEP: lang_step lang me s1 m1 t s2 m2>>
        /\ <<MATCH: ctx_match_extends s2 s2'>>
        /\ <<EXTEND: Mem.extends m2 m2'>>
        /\ <<UNCHGD: Mem.unchanged_on (loc_out_of_bounds m1) m1' m2'>>>>;

  ctx_mem_inject:
    forall (me: Genv.t F V) s1' m1' f m1 s1
           (PGLB: meminj_preserves_globals me f)
           (INJ: Mem.inject f m1 m1')
           (MSTATE: ctx_match_inject f s1 s1')
           (SAFE: lang_safe lang me s1 m1),
    <<PROGRESS: exists t s2' m2', lang_step lang me s1' m1' t s2' m2'>> /\
    <<STEP:
        forall t s2' m2' (STEP: lang_step lang me s1' m1' t s2' m2'),
        exists f' s2 m2,
           <<STEP: lang_step lang me s1 m1 t s2 m2>>
        /\ <<MATCH: ctx_match_inject f' s2 s2'>>
        /\ <<INJECT: Mem.inject f' m2 m2'>>
        /\ <<UNCHGD1: Mem.unchanged_on (loc_unmapped f) m1 m2>>
        /\ <<UNCHGD2: Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'>>
        /\ <<INCR: inject_incr f f'>>
        /\ <<SEPR: inject_separated f f' m1 m1'>>>>;

  ctx_valid_block_initial:
    forall me fid sig args s m1 m2 b
           (STEP: lang.(lang_initial_state) me fid sig args s m1 m2)
           (VB: Mem.valid_block m1 b),
    Mem.valid_block m2 b;

  ctx_max_perm_initial:
    forall me fid sig args s m1 m2 b ofs p
           (STEP: lang.(lang_initial_state) me fid sig args s m1 m2)
           (VB: Mem.valid_block m1 b)
           (PERM: Mem.perm m2 b ofs Max p),
      Mem.perm m1 b ofs Max p;

  ctx_readonly_initial:
    forall me fid sig args s m1 m2
           (STEP: lang.(lang_initial_state) me fid sig args s m1 m2),
      Mem.unchanged_on (loc_not_writable m1) m1 m2;

  ctx_mem_extends_initial:
      forall me fid sig args1 args2 mem1 mem2
             (EXTEND: Mem.extends mem1 mem2)
             (ARGS: Val.lessdef_list args1 args2),
      <<PROGRESS:
        forall s1 mem1' (STEP1: lang.(lang_initial_state) me fid sig args1 s1 mem1 mem1'),
        exists s2 mem2', lang.(lang_initial_state) me fid sig args2 s2 mem2 mem2'>> /\
      <<STEP:
        forall s2 mem2' (STEP: lang.(lang_initial_state) me fid sig args2 s2 mem2 mem2'),
        exists s1 mem1',
          <<INIT1: lang.(lang_initial_state) me fid sig args1 s1 mem1 mem1'>> /\
          <<MATCH: ctx_match_extends s1 s2>> /\
          <<EXTEND': Mem.extends mem1' mem2'>> /\
          <<UNCHGN: Mem.unchanged_on (loc_out_of_bounds mem1) mem2 mem2'>>>>;

  ctx_mem_inject_initial:
      forall me fid sig args1 args2 alpha mem1 mem2
             (INJECT: Mem.inject alpha mem1 mem2)
             (ARGS: val_list_inject alpha args1 args2),
      <<PROGRESS:
        forall s1 mem1' (STEP1: lang.(lang_initial_state) me fid sig args1 s1 mem1 mem1'),
        exists s2 mem2', lang.(lang_initial_state) me fid sig args2 s2 mem2 mem2'>> /\
      <<STEP:
        forall s2 mem2' (STEP: lang.(lang_initial_state) me fid sig args2 s2 mem2 mem2'),
        exists alpha' s1 mem1',
          <<INIT1: lang.(lang_initial_state) me fid sig args1 s1 mem1 mem1'>> /\
          <<MATCH: ctx_match_inject alpha' s1 s2>> /\
          <<INJECT': Mem.inject alpha' mem1' mem2'>> /\
          <<PRIVATE: Mem.unchanged_on (loc_unmapped alpha) mem1 mem1'>> /\
          <<PRIVATE': Mem.unchanged_on (loc_out_of_reach alpha mem1) mem2 mem2'>> /\
          <<INCR: inject_incr alpha alpha'>> /\
          <<SEPR: inject_separated alpha alpha' mem1 mem2>>>>;

  ctx_mem_extends_terminal:
      forall me s1 s2 res2
             (MSTATE: ctx_match_extends s1 s2)
             (TERMINAL2: lang.(lang_get_status) me s2 = terminal res2),
      exists res1,
        <<TERMINAL1: lang.(lang_get_status) me s1 = terminal res1>> /\
        <<RES: Val.lessdef res1 res2>>;

  ctx_mem_inject_terminal:
      forall me alpha s1 s2 res2
             (MSTATE: ctx_match_inject alpha s1 s2)
             (TERMINAL2: lang.(lang_get_status) me s2 = terminal res2),
      exists res1,
        <<TERMINAL1: lang.(lang_get_status) me s1 = terminal res1>> /\
        <<RES: val_inject alpha res1 res2>>;

  ctx_mem_extends_external:
      forall me s1 s2 id sig args2
             (MSTATE: ctx_match_extends s1 s2)
             (EXTERNAL1: lang.(lang_get_status) me s2 = external id sig args2),
      exists args1,
        <<EXTERNAL1: lang.(lang_get_status) me s1 = external id sig args1>> /\
        <<RES: Val.lessdef_list args1 args2>>;

  ctx_mem_inject_external:
      forall me alpha s1 s2 id sig args2
             (MSTATE: ctx_match_inject alpha s1 s2)
             (EXTERNAL1: lang.(lang_get_status) me s2 = external id sig args2),
      exists args1,
        <<EXTERNAL1: lang.(lang_get_status) me s1 = external id sig args1>> /\
        <<RES: val_list_inject alpha args1 args2>>;

  ctx_mem_extends_after_external:
    forall (me: Genv.t F V) s1' s1 res res'
           (RES: Val.lessdef res res')
           (MSTATE: ctx_match_extends s1 s1')
           (SAFE: exists s2, lang.(lang_after_external) me res s1 s2),
    <<PROGRESS: exists s2', lang.(lang_after_external) me res' s1' s2'>> /\
    <<STEP:
      forall s2' (STEP: lang.(lang_after_external) me res' s1' s2'),
      exists s2,
         <<STEP: lang.(lang_after_external) me res s1 s2>>
      /\ <<MATCH: ctx_match_extends s2 s2'>>>>;

  ctx_mem_inject_after_external:
    forall (me: Genv.t F V) alpha s1' s1 res res'
           (RES: val_inject alpha res res')
           (MSTATE: ctx_match_inject alpha s1 s1')
           (SAFE: exists s2, lang.(lang_after_external) me res s1 s2),
    <<PROGRESS: exists s2', lang.(lang_after_external) me res' s1' s2'>> /\
    <<STEP:
      forall s2' (STEP: lang.(lang_after_external) me res' s1' s2'),
      exists s2,
         <<STEP: lang.(lang_after_external) me res s1 s2>>
      /\ <<MATCH: ctx_match_inject alpha s2 s2'>>>>
}.

Lemma external_call_mem_extends_backward
      (ef : external_function) (F V : Type) 
      (ge : Genv.t F V) (vargs : list val) (m1 : mem)
      (m1' : mem) (vargs' : list val):
  (exists t vres m2, external_call ef ge vargs m1 t vres m2) ->
  Mem.extends m1 m1' ->
  Val.lessdef_list vargs vargs' ->
  <<PROGRESS: exists t vres' m2', external_call ef ge vargs' m1' t vres' m2'>> /\
  <<STEP:
      forall t vres' m2' (STEP: external_call ef ge vargs' m1' t vres' m2'),
      exists (vres : val) (m2 : mem),
        external_call ef ge vargs m1 t vres m2 /\
        Val.lessdef vres vres' /\
        Mem.extends m2 m2' /\
        Mem.unchanged_on (loc_out_of_bounds m1) m1' m2'>>.
Proof.
  i. des. exploit external_call_mem_extends; eauto. i. des.
  splits.
  { eexists _, _, _. eauto. }
  i. exploit external_call_determ; [apply H2|apply STEP|]. i. des.
  exploit external_call_receptive; [apply H|apply H6|]. i. des.
  exploit external_call_mem_extends; eauto. i. des.
  exploit external_call_determ; [apply STEP|apply H9|]. i. des.
  specialize (H14 eq_refl). des. subst.
  eexists _, _. splits; eauto.
Qed.

Lemma external_call_mem_inject_backward
      (ef : external_function) (F V : Type) 
      (ge : Genv.t F V) (vargs : list val) (m1 : mem) 
      (f : block -> option (block * Z)) (m1' : mem) 
      (vargs' : list val):
  meminj_preserves_globals ge f ->
  (exists t vres m2, external_call ef ge vargs m1 t vres m2) ->
  Mem.inject f m1 m1' ->
  val_list_inject f vargs vargs' ->
  <<PROGRESS: exists t vres' m2', external_call ef ge vargs' m1' t vres' m2'>> /\
  <<STEP:
      forall t vres' m2' (STEP: external_call ef ge vargs' m1' t vres' m2'),
      exists (f' : meminj) (vres : val) (m2 : mem),
        external_call ef ge vargs m1 t vres m2 /\
        val_inject f' vres vres' /\
        Mem.inject f' m2 m2' /\
        Mem.unchanged_on (loc_unmapped f) m1 m2 /\
        Mem.unchanged_on (loc_out_of_reach f m1) m1' m2' /\
        inject_incr f f' /\ inject_separated f f' m1 m1'>>.
Proof.
  i. des. exploit external_call_mem_inject; eauto. i. des.
  splits.
  { eexists _, _, _. eauto. }
  i. exploit external_call_determ; [apply H3|apply STEP|]. i. des.
  exploit external_call_receptive; [apply H0|apply H10|]. i. des.
  exploit external_call_mem_inject; eauto. i. des.
  exploit external_call_determ; [apply STEP|apply H13|]. i. des.
  specialize (H21 eq_refl). des. subst.
  eexists _, _, _. splits; eauto.
Qed.

Inductive ctx_module: forall (md:module), Prop :=
| ctx_module_intro
    F V (lang:language F V) (LANG: ctx_properties lang) md:
    ctx_module (mkmodule lang md)
.

Definition program_simulation prog1 prog2: Prop :=
  forall (SAFE: exists sem1, program_semantics prog1 sem1),
    <<PROGRESS: exists sem2, program_semantics prog2 sem2>> /\
    <<SIM:
        forall sem2 (SEM2: program_semantics prog2 sem2),
        exists sem1,
          <<SEM1: program_semantics prog1 sem1>> /\
          <<SIM: exists (_:backward_simulation sem1 sem2), True>>>>.

Definition ctx_refinement (md1 md2:module): Prop :=
  forall (ctxl ctxr:list module)
         (CTX: List.Forall ctx_module (ctxl ++ ctxr)),
  program_simulation (ctxl ++ md1 :: ctxr) (ctxl ++ md2 :: ctxr).
