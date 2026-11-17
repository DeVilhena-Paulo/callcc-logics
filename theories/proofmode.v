(* proofmode.v. *)

From iris.program_logic Require Import weakestpre lifting.
From iris.proofmode Require Import rocq_tactics reduction.

From callcc_logics Require Export logic class_instances tactics.

From iris.prelude Require Import options.

(** Rewriting with [TCEq] hypotheses (e.g. [intros ->]) needs this scheme. *)
Scheme Rewriting for TCEq.

(** A special version of TCSimpl which also simplies [fill (K1 ++ K2) e] *)
Class TCSimplExpr (e e' : expr) := TCSimplExpr_TCSimpl : TCSimpl e e'.
Global Hint Extern 0 (TCSimplExpr _ _) =>
  repeat rw (fill_app _ _ _); notypeclasses refine TCSimpl_TCEq : typeclass_instances.
Global Hint Mode TCSimplExpr - - : typeclass_instances.

Lemma TCSimplExpr_eq (e e' : expr) : TCSimplExpr e e' ↔ e = e'.
Proof. apply TCSimpl_eq. Qed.

Inductive IntoCtx (e : expr) (P : expr → Prop) (k : ectx) : Prop :=
  Mk_IntoCtx (e' : expr) (_ : e = fill k e') (_ : P e').
Existing Class IntoCtx.
Global Hint Mode IntoCtx ! ! - : typeclass_instances.

Class DoPureStep (φ : Prop) (e e' : expr) : Prop :=
  { do_pure_step : φ → pure_step_ectx e e' }.
Global Hint Mode DoPureStep - ! - : typeclass_instances.

Class DoPureSteps (φ : Prop) (n : nat) (e e' : expr) : Prop :=
  { do_pure_steps : φ → nsteps pure_step_ectx n e e' }.
Global Hint Mode DoPureSteps - - ! - : typeclass_instances.

Inductive DoPureStepsIntoCtx (φ : Prop) (e : expr) (P : expr → Prop) (n : nat) (k : ectx) : Prop :=
  Mk_DoPureStepsIntoCtx (e'  : expr) (_ : DoPureSteps φ n e e') (_ : IntoCtx e' P k).
Existing Class DoPureStepsIntoCtx.
Global Hint Mode DoPureStepsIntoCtx - ! ! - - : typeclass_instances.

Class MakeAnd (P Q PQ : Prop) := make_and : P ∧ Q ↔ PQ.
Global Hint Mode MakeAnd ! ! - : typeclass_instances.

Global Instance make_and_true_l P : MakeAnd True P P.
Proof. rw /MakeAnd. tauto. Qed.
Global Instance make_and_true_r P : MakeAnd P True P.
Proof. rw /MakeAnd. tauto. Qed.
Global Instance make_and_default P Q : MakeAnd P Q (P ∧ Q) | 100.
Proof. by rw /MakeAnd. Qed.

(** [IntoCtx] instances *)
Global Instance into_ctx_nil e P :
  P e → IntoCtx e P [] | 0.
Proof. intros H. by exists e. Qed.

Local Ltac solve_into_ctx :=
  let e := fresh "e" in
  intros [e -> ?]; by exists e.

Global Instance into_ctx_app_r e1 e2 P K :
  IntoCtx e2 P K →
  IntoCtx (App e1 e2) P (AppRCtx e1 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_app_l e1 v2 P K :
  IntoCtx e1 P K →
  IntoCtx (App e1 (Val v2)) P (AppLCtx v2 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_unop op e P K :
  IntoCtx e P K →
  IntoCtx (UnOp op e) P (UnOpCtx op :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_binop_l op e1 v2 P K :
  IntoCtx e1 P K →
  IntoCtx (BinOp op e1 (Val v2)) P (BinOpLCtx op v2 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_binop_r op e1 e2 P K :
  IntoCtx e2 P K →
  IntoCtx (BinOp op e1 e2) P (BinOpRCtx op e1 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_if e1 e2 e3 P K :
  IntoCtx e1 P K →
  IntoCtx (If e1 e2 e3) P (IfCtx e2 e3 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_pairl e1 v2 P K :
  IntoCtx e1 P K →
  IntoCtx (Pair e1 (Val v2)) P (PairLCtx v2 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_pairr e1 e2 P K :
  IntoCtx e2 P K →
  IntoCtx (Pair e1 e2) P (PairRCtx e1 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_fst e P K :
  IntoCtx e P K →
  IntoCtx (Fst e) P (FstCtx :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_snd e P K :
  IntoCtx e P K →
  IntoCtx (Snd e) P (SndCtx :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_injl e P K :
  IntoCtx e P K →
  IntoCtx (InjL e) P (InjLCtx :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_injr e P K :
  IntoCtx e P K →
  IntoCtx (InjR e) P (InjRCtx :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_case e0 e1 e2 P K :
  IntoCtx e0 P K →
  IntoCtx (Case e0 e1 e2) P (CaseCtx e1 e2 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_allocnl e1 v2 P K :
  IntoCtx e1 P K →
  IntoCtx (AllocN e1 (Val v2)) P (AllocNLCtx v2 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_allocnr e1 e2 P K :
  IntoCtx e2 P K →
  IntoCtx (AllocN e1 e2) P (AllocNRCtx e1 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_free e P K :
  IntoCtx e P K →
  IntoCtx (Free e) P (FreeCtx :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_load e P K :
  IntoCtx e P K →
  IntoCtx (Load e) P (LoadCtx :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_storel e1 v2 P K :
  IntoCtx e1 P K →
  IntoCtx (Store e1 (Val v2)) P (StoreLCtx v2 :: K).
Proof. solve_into_ctx. Qed.

Global Instance into_ctx_storer e1 e2 P K :
  IntoCtx e2 P K →
  IntoCtx (Store e1 e2) P (StoreRCtx e1 :: K).
Proof. solve_into_ctx. Qed.


Class MakeApp {A} (k1 k2 l : list A) := make_app : l = k1 ++ k2.
Global Hint Mode MakeApp ! ! ! - : typeclass_instances.

Global Instance make_app_nil_l {A} (l : list A) : MakeApp [] l l.
Proof. by rw /MakeApp. Qed.
Global Instance make_app_nil_r {A} (l : list A) : MakeApp l [] l.
Proof. by rw /MakeApp app_nil_r. Qed.
Global Instance make_app_default {A} (l1 l2 : list A) : MakeApp l1 l2 (l1 ++ l2) | 100.
Proof. by rw /MakeApp. Qed.

Lemma into_ctx_fill e K1 K2 K P :
  IntoCtx e P K2 →
  MakeApp K1 K2 K →
  IntoCtx (fill K1 e) P K.
Proof. intros [? -> ?] ->. exists e'; auto using fill_app. Qed.
Global Hint Extern 10 (IntoCtx (fill _ _) _ _) =>
  notypeclasses refine (into_ctx_fill _ _ _ _ _ _ _) : typeclass_instances.

Lemma tc_eq_fill K e1 e2 :
  IntoCtx e2 (TCEq e1) K →
  TCEq (fill K e1) e2.
Proof. by intros [? -> ->]. Qed.
Global Hint Extern 10 (TCEq (fill _ _) _) =>
  notypeclasses refine (tc_eq_fill _ _ _ _) : typeclass_instances.


(** [PureStep] instances *)
Local Ltac solve_exec_safe k :=
  intros; subst; eexists (fill k _); do 2 eexists;
  eapply (Ectx_prim_step_2 k k); econstructor; eauto.

Local Ltac solve_exec_puredet :=
  simpl; intros ????? Hstep;
  match goal with
  | _ : prim_step' _ _ ?κ _ _ _ |- _ =>
      destruct κ=>//=; simpl in Hstep
  end;
  inversion Hstep;
  match goal with
  | H : fill _ _ = fill ?k' ?e' |- _ =>
      specialize (f_equal get_redex H) as Hget
  end;
  match goal with
  | H : get_redex (fill _ _) = get_redex (fill ?k' ?e') |- _ =>
      erewrite (base_reducible_get_redex' k' e') in H;
      try done
  end;
  match goal with
  | H : get_redex (fill _ _) = _ |- _ =>
      autorewrite with get_redex_fill_db in H;
      injection H as <- <-
  end;
  by inv_base_step.

Local Ltac solve_do_pure_step_with tac :=
  constructor; tac;
    constructor; [solve_exec_safe | solve_exec_puredet].
Local Ltac solve_do_pure_step :=
  constructor; intros _ k; constructor;
    [solve_exec_safe k | solve_exec_puredet].

Lemma DoPureSteps_PureExecEctx φ n e e' :
  DoPureSteps φ n e e' →
  PureExecEctx φ n e e'.
Proof. intros H ?. by apply H. Qed.

Global Instance do_pure_step_rec f x e :
  DoPureStep True (Rec f x e) (Val (RecV f x e)).
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_pair v1 v2 :
  DoPureStep True (Pair (Val v1) (Val v2)) (PairV v1 v2).
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_step_injl v :
  DoPureStep True (InjL (Val v)) (InjLV v).
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_step_injr v :
  DoPureStep True (InjR (Val v)) (InjRV v).
Proof. solve_do_pure_step. Qed.

(** [do_pure_step_app] is not an [Instance], but a [Hint Extern] to enable
syntactic matching instead of unification-based matching. This is important
because it would otherwise unfold definitions. For example, when considering
[wp (swap ...) Φ] where [Definition swap := RecV ...], it should *not* unfold
[swap] to as to preserve abstraction barriers. *)
Lemma do_pure_step_app f x e v e' :
  TCSimpl (subst' x v (subst' f (RecV f x e) e)) e' →
  DoPureStep True (App (Val (RecV f x e)) (Val v)) e'.
Proof. intros ?%TCSimpl_eq. solve_do_pure_step. Qed.
Global Hint Extern 1 (DoPureStep _ (App (Val (RecV _ _ _)) (Val _)) _) =>
  notypeclasses refine (do_pure_step_app _ _ _ _ _ _) : typeclass_instances.

Global Instance do_pure_step_unop op v w :
  TCSimpl (un_op_eval op v) (Some w) →
  DoPureStep True (UnOp op (Val v)) (Val w).
Proof. intros ?%TCSimpl_eq. solve_do_pure_step. Qed.

Global Instance do_pure_step_binop op v1 v2 w :
  TCSimpl (bin_op_eval op v1 v2) (Some w) →
  DoPureStep True (BinOp op (Val v1) (Val v2)) (Val w).
Proof. intros ?%TCSimpl_eq. solve_do_pure_step. Qed.

Global Hint Extern 1 (TCSimpl (un_op_eval ?op ?v) _) =>
  lazymatch goal with
  | H : un_op_eval op v = _ |- _ => rw H
  end : typeclass_instances.

Global Hint Extern 1 (TCSimpl (bin_op_eval ?op ?v1 ?v2) _) =>
  lazymatch goal with
  | H : bin_op_eval op v1 v2 = _ |- _ => rw H
  end : typeclass_instances.

Global Instance do_pure_step_if_true e2 e3 :
  DoPureStep True (If (Val $ LitV $ LitBool true) e2 e3) e2.
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_step_if_false e2 e3 :
  DoPureStep True (If (Val $ LitV $ LitBool false) e2 e3) e3.
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_step_fst v1 v2 :
  DoPureStep True (Fst (PairV v1 v2)) (Val v1).
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_step_snd v1 v2 :
  DoPureStep True (Snd (PairV v1 v2)) (Val v2).
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_step_case_injl v1 e2 e3 :
  DoPureStep True (Case (InjLV v1) e2 e3) (App e2 (Val v1)).
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_step_case_injr v1 e2 e3 :
  DoPureStep True (Case (InjRV v1) e2 e3) (App e3 (Val v1)).
Proof. solve_do_pure_step. Qed.

Global Instance do_pure_steps_0 e : DoPureSteps True 0 e e | 100.
Proof. do 2 constructor. Qed.

Global Instance do_pure_steps_S n K e1 e2 e2' e3 φ1 φ2 φ :
  TCNoBackTrack (IntoCtx e1 (λ e1', DoPureStep φ1 e1' e2') K) →
  TCSimplExpr (fill K e2') e2 →
  DoPureSteps φ2 n e2 e3 →
  MakeAnd φ1 φ2 φ →
  DoPureSteps φ (S n) e1 e3.
Proof.
  intros [[? -> [?]]] <-%TCSimplExpr_eq [?] Hφ.
  split. intros [Hφ1 Hφ2]%Hφ. econstructor; last auto.
  apply pure_step_ectx_fill; auto.
Qed.

Global Instance do_pure_steps_into_ctx_0 e P K :
  IntoCtx e P K → DoPureStepsIntoCtx True e P 0 K | 0.
Proof. exists e; apply _. Qed.

Global Instance do_pure_steps_into_ctx_S e1 e2 e2' P n K K' φ1 φ2 φ :
  TCNoBackTrack (IntoCtx e1 (λ e1', DoPureStep φ1 e1' e2') K') →
  TCSimplExpr (fill K' e2') e2 →
  DoPureStepsIntoCtx φ2 e2 P n K →
  MakeAnd φ1 φ2 φ →
  DoPureStepsIntoCtx φ e1 P (S n) K | 100.
Proof.
  intros [[e1' -> [?]]] <-%TCSimplExpr_eq [e3 [?] ?] Hφ.
  exists e3; last done. split. intros [Hφ1 Hφ2]%Hφ.
  econstructor; last auto. apply pure_step_ectx_fill; auto.
Qed.


(* [gp] is the (explicit) global postcondition threaded through [wpcc];
   the proof-mode plumbing is polymorphic in it, just like the reasoning
   rules in [logic.v]. *)
Class FinalizeWPCC `{!stateGS Σ} (gp : val → Prop) (e : expr) (b : wp_flavour) (R : val -d> iProp Σ) (P : iProp Σ) : Prop :=
  { finalize_ewp : P ⊢ wp/cc ⟨gp⟩ e @ b {{R}} }.
Global Hint Mode FinalizeWPCC + + ! ! ! ! - : typeclass_instances.

(** There are three ways to finalize a SIM.
    First of all, if both expressions are a value
    and the postcondition already contains a update,
    we can just prove the postcondition. *)
Lemma finalize_wpcc_value `{!stateGS Σ} gp b R e v :
  IntoVal e v →
  FinalizeWPCC gp e b R (R v).
Proof. intros <-. constructor. iApply wpcc_value. Qed.
Global Hint Extern 0 (FinalizeWPCC _ _ _ _ _ (λ _ _, |==> _)%I _) =>
  notypeclasses refine (finalize_wpcc_value _ _ _ _ _ _ _ _ _ _) : typeclass_instances.

(** Second, if both expressions are a value
    but the postcondition does NOT already contain an update,
    we introduce it. *)
Global Instance finalize_wpcc_value_upd `{!stateGS Σ} gp b R e v :
  IntoVal e v →
  FinalizeWPCC gp e b R (|==> R v) | 1.
Proof. intros <-. constructor. rw -fupd_wpcc -wpcc_value. by iIntros "?". Qed.

(** Finally, if the expressions aren't both a value,
    we simplify them both. *)
Global Instance finalize_wpcc_simpl `{!stateGS Σ} gp b R e e' :
  TCSimplExpr e e' → FinalizeWPCC gp e b R (wp/cc ⟨gp⟩ e' @ b {{R}})%I | 2.
Proof. intros ->%TCSimplExpr_eq. by constructor. Qed.

(** [NormalizeWP] transforms a goal [P] into another goal of the form [wp (fill K1 e1) (fill K2 e2) X R]
    by performing pure steps. This typeclass is used by [iApply]/[iAssumption] to first perform
    some pure steps, and automatically pick to right evaluation context to apply the lemma.

    Note that [normalize_wp_step] only performs pure steps without side-conditions,
    so in some situations it's still needed to first perform the pure steps using [wp_pures]. *)
Class NormalizeWPCC `{!stateGS Σ} (gp : val → Prop) (P : iProp Σ) (K : ectx) (e : expr) (b : wp_flavour) (R : val -d> iProp Σ) :=
  { normalize_wp : wp/cc ⟨gp⟩ fill K e @ b {{R}} ⊢ P }.
Global Hint Mode NormalizeWPCC + + ! ! - - - - : typeclass_instances.

Global Instance normalize_wpcc_here `{!stateGS Σ} gp e b R :
  NormalizeWPCC gp (wp/cc ⟨gp⟩ e @ b {{R}})%I [] e b R | 0.
Proof. by split. Qed.

Global Instance normalize_wpcc_value `{!stateGS Σ} gp v K e e' b R R' :
  IntoVal e' v →
  NormalizeWPCC gp (R v) K e b R' →
  NormalizeWPCC gp (wp/cc ⟨gp⟩ e' @ b {{R}})%I K e b R' | 1.
Proof. intros Hₜ [HR]. split. by rw HR -Hₜ  -wpcc_value. Qed.

(** We only perform pure steps without a side-condition here. We could let [NormalizeWP]
    also generate side-conditions, but [IntoWand]/[FromAssumption] currently lack the ability
    to handle pure side-conditions. *)
Global Instance normalize_wpcc_step `{!stateGS Σ} gp n e e' K b R :
  DoPureStepsIntoCtx True e (TCEq e') n K →
  NormalizeWPCC gp (wp/cc ⟨gp⟩ e @ b {{R}})%I K e' b R | 10.
Proof.
  intros [? H [? -> <-]]. split.
  assert (PureExecEctx True n e (fill K e')).
  { intros _. by apply H. }
  rw -wpcc_pure_step //.
  rw -bi.laterN_intro. apply bi.wand_intro_r, bi.sep_elim_l. tc_solve.
Qed.

Global Instance from_assumption_wpcc `{!stateGS Σ} gp p K e e' b R R' :
  NormalizeWPCC gp (wp/cc ⟨gp⟩ e @ b {{R}})%I K e' b R' →
  FromAssumption p (wp/cc ⟨gp⟩ (fill K e') @ b {{R'}})%I (wp/cc ⟨gp⟩ e @ b {{R}})%I | 2.
Proof.
  intros [HR].
  rw /FromAssumption bi.intuitionistically_if_elim. by rw HR.
Qed.

Global Instance into_wand_wpcc `{!stateGS Σ} gp p e K e' b R R' S Q :
  NormalizeWPCC gp (wp/cc ⟨gp⟩ e @ b {{R}})%I K e' b R' →
  TCSimpl (□ ∀ v, S v -∗ R' v)%I Q →
  IntoWand p false (wp/cc ⟨gp⟩ (fill K e') @ b {{S}})%I Q (wp/cc ⟨gp⟩ e @ b {{R}})%I | 1.
Proof.
  intros [Hwp] <-%TCSimpl_eq.
  rw /IntoWand /= bi.intuitionistically_if_elim.
  rw -Hwp. iIntros "H #HR".
  iApply (wpcc_mono with "H").
  by destruct b => //=; try iModIntro; iIntros "% ? !>"; iApply "HR".
Qed.

(** This instance should not be needed, but is a workaround for
https://gitlab.mpi-sws.org/iris/iris/-/issues/458 *)
Global Instance into_wand_wand_wpcc `{!stateGS Σ} gp p q e K e' P P' Q b R R' :
  NormalizeWPCC gp (wp/cc ⟨gp⟩ e @ b {{R}})%I K e' b R' →
  FromAssumption q P P' →
  TCSimpl P Q →
  IntoWand p q (P' -∗ wp/cc ⟨gp⟩ fill K e' @ b {{R'}})%I Q (wp/cc ⟨gp⟩ e @ b {{R}})%I.
Proof.
  rw /FromAssumption /IntoWand.
  intros [Hwp] ? <-%TCSimpl_eq.
  rw bi.intuitionistically_if_elim.
  apply bi.wand_mono; [done|]. by rw Hwp.
Qed.

Class IsAppRec (v1 v2 : val) (f x : binder) (e' : expr) (e : expr) := {
  is_app_rec_val : v1 = RecV f x e';
  is_app_rec_expr : e = App (Val v1) (Val v2);
}.
Global Hint Mode IsAppRec - - - - - ! : typeclass_instances.
Global Instance is_app_rec v1 v2 f x e :
  TCEq v1 (RecV f x e) →
  IsAppRec v1 v2 f x e (App (Val v1) (Val v2)).
Proof. rw TCEq_eq=> ->. by constructor. Qed.

Lemma tac_wpcc_pure `{!stateGS Σ} {gp Δ Δ' e e' b R Q φ} n :
  DoPureSteps φ n e e' →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  FinalizeWPCC gp e' b R Q →
  envs_entails Δ' Q →
  envs_entails Δ (wp/cc ⟨gp⟩ e @ b {{R}})%I.
Proof.
  rw envs_entails_unseal=> -[Hsteps] Hφ HΔ [HQ] HΔ'.
  rw into_laterN_env_sound HΔ' HQ {HQ HΔ HΔ'}.
  assert (PureExecEctx φ n e e') by by rw /PureExecEctx.
  rw -wpcc_pure_step //.
  apply bi.laterN_mono. auto.
Qed.

Lemma tac_wpcc_rec `{!stateGS Σ} {gp Δ Δ' e' v1 v2 f x e K b R Q} :
  IntoCtx e (IsAppRec v1 v2 f x e') K →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  FinalizeWPCC gp (fill K (subst' x v2 (subst' f v1 e'))) b R Q →
  envs_entails Δ' Q →
  envs_entails Δ (wp/cc ⟨gp⟩ e @ b {{R}})%I.
Proof.
  rw envs_entails_unseal=> -[? -> [-> ->]] HΔ [HQ] HΔ'.
  rw into_laterN_env_sound HΔ' HQ /=.
  assert (PureExecEctx True 1 (fill K ((rec: f x := e')%V v2)) (fill K (subst' x v2 (subst' f (rec: f x := e') e')))).
  { apply PureExecEctx_fill, DoPureSteps_PureExecEctx. apply _. }
  rw -wpcc_pure_step //.
  apply bi.later_mono. auto.
Qed.

Tactic Notation "wpcc_pures" open_constr(n) :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (wpcc _ _ _ _ _) =>
    notypeclasses refine (tac_wpcc_pure n _ _ _ _ _);
      [ tc_solve || fail 1 "wpcc_pures: no pure steps can be performed"
      | try done (* side-condition *)
      | tc_solve (* into later *)
      | tc_solve (* simpl *)
      | pm_prettify ]
  | |- _ => fail "wpcc_pures: goal not a `wpcc`"
  end.
Tactic Notation "wpcc_pure" := wpcc_pures 1.
Tactic Notation "wpcc_pures" := wpcc_pures (S _).

Tactic Notation "wpcc_rec" :=
  iStartProof;
  lazymatch goal with
  | |- environments.envs_entails _ (wpcc _ _ _ _ _) =>
    notypeclasses refine (tac_wpcc_rec _ _ _ _);
      [ tc_solve || fail 1 "wpcc_rec: no beta reduction step can be performed"
      | tc_solve (* into laters *)
      | tc_solve (* simpl *)
      | pm_prettify]
  | |- _ => fail 1 "wpcc_rec: goal not a `wpcc`"
  end.
