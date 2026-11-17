(* iris_instantiation.v *)

From iris.program_logic Require Import language.
From callcc_logics Require Import syntax notation semantics tactics.


(* ========================================================================== *)
(** * Language. *)

(* Reduction relation in the Iris format. *)
(* To prove that [lambda_blaze] is a language, we must define a reduction
   relation that fits the format formalized by Iris. *)
Definition prim_step' e1 σ1 (obs : list unit) e2 σ2 (efs : list expr) :=
  match obs with _ :: _ => False | [] =>
    prim_step e1 σ1 e2 σ2 efs
  end.

(* [callcc_lang] satisfies the record type [LanguageMixin]. *)
Lemma callcc_lang_mixin : LanguageMixin of_val to_val prim_step'.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val.
  { intros ??. destruct e=>//=. by inversion 1. }
  unfold prim_step'.
  intros e σ obs e' σ' efs.
  case obs; [|done].
  induction 1 as [k1 k2 e1' e2' -> ? ?].
  case k1 as [|f k1].
  - revert H0. apply val_base_stuck.
  - apply fill_frame_val.
Qed.

(* [callcc_lang] is a language in the Iris sense. *)
Canonical Structure callcc_lang : language := Language callcc_lang_mixin.


(* ========================================================================== *)
(** * Pure Steps. *)

Section pure_steps.

  Definition base_reducible (k : ectx) (e : expr) (σ : state) :=
    ∃ k' e' σ' efs, base_step k e σ k' e' σ' efs.
  Definition base_irreducible (k : ectx) (e : expr) (σ : state) :=
    ∀ k' e' σ' efs, ¬ base_step k e σ k' e' σ' efs.
  Definition base_stuck (k : ectx) (e : expr) (σ : state) :=
    to_val e = None ∧ base_irreducible k e σ.

  Definition pure_step_ectx (e1 e2 : expr) :=
    ∀ k, pure_step (fill k e1) (fill k e2).

  Class PureExecEctx (φ : Prop) (n : nat) (e1 e2 : expr) :=
    pure_exec_ectx : φ → relations.nsteps pure_step_ectx n e1 e2.

  Lemma pure_step_ectx_fill k e1 e2 :
    pure_step_ectx e1 e2 →
    pure_step_ectx (fill k e1) (fill k e2).
  Proof. intros He12. intros k'. rw -!fill_app. by apply He12. Qed.

  Lemma pure_step_ectx_pure_step e1 e2 :
    pure_step_ectx e1 e2 →
    pure_step e1 e2.
  Proof. intros He12. by apply (He12 []). Qed.

  Lemma pure_step_ectx_pure_step_fill k e1 e2 :
    pure_step_ectx e1 e2 →
    pure_step (fill k e1) (fill k e2).
  Proof. intros ?. by apply pure_step_ectx_pure_step, pure_step_ectx_fill. Qed.

  Lemma PureExecEctx_fill φ n k e1 e2 :
    PureExecEctx φ n e1 e2 →
    PureExecEctx φ n (fill k e1) (fill k e2).
  Proof.
    intros He12 Hφ. specialize (pure_exec_ectx Hφ) as He12'.
    clear He12. revert e1 e2 k He12'.
    induction n as [|n IH]; intros e1 e2 k He12'.
    - inversion He12'. simplify_eq. by apply nsteps_O.
    - destruct (nsteps_inv_r _ _ _ He12') as (e' & He1e' & He'e2).
      eapply nsteps_r.
      + by apply (IH e1 e' k He1e').
      + by apply pure_step_ectx_fill.
  Qed.

  Lemma PureExecEctx_PureExec φ n e1 e2 :
    PureExecEctx φ n e1 e2 →
    PureExec φ n e1 e2.
  Proof.
    intros He12 Hφ. specialize (pure_exec_ectx Hφ) as He12'.
    clear He12. revert e1 e2 He12'.
    induction n as [|n IH]; intros e1 e2 He12'.
    - inversion He12'. simplify_eq. by apply nsteps_O.
    - destruct (nsteps_inv_r _ _ _ He12') as (e' & He1e' & He'e2).
      eapply nsteps_r.
      + by apply (IH e1 e' He1e').
      + by apply (He'e2 []).
  Qed.

  Lemma base_reducible_get_redex k e σ :
    base_reducible k e σ →
    get_redex (fill k e) = (k, e).
  Proof.
    intros (k' & e' & σ' & efs & Hstep).
    revert k' e' σ' efs Hstep.
    induction 1;
    by rw /get_redex;
      (match goal with
      | |- (let '(k0, e0) := get_ectx (fill ?K ?E) in _) = _ =>
          erewrite (get_ectx_fill' E _ _ _ K)
      end);
      try done; simpl;
      try rw app_nil_r;
      try rw reverse_app //= reverse_involutive.
  Qed.

  Lemma base_reducible_get_redex' k e σ k' e' σ' efs :
    base_step k e σ k' e' σ' efs →
    get_redex (fill k e) = (k, e).
  Proof. intros ?. eapply base_reducible_get_redex. by do 4 eexists. Qed.

  Lemma base_reducible_fill_inj k1 e1 σ1 k2 e2 σ2 :
    base_reducible k1 e1 σ1 →
    base_reducible k2 e2 σ2 →
    fill k1 e1 = fill k2 e2 →
    e1 = e2 ∧ k1 = k2.
  Proof.
    intros He1 He2 Hfill.
    specialize (f_equal get_redex Hfill).
    rw (base_reducible_get_redex _ _ _ He1).
    rw (base_reducible_get_redex _ _ _ He2).
    by intros [= <- <-].
  Qed.

  Lemma base_step_fill_inj k1 e1 σ1 k e σ efs k2 e2 σ2 k' e' σ' efs' :
    base_step k1 e1 σ1 k  e  σ  efs →
    base_step k2 e2 σ2 k' e' σ' efs' →
    fill k1 e1 = fill k2 e2 →
    e1 = e2 ∧ k1 = k2.
  Proof.
    intros H1 H2 Hfill.
    assert (base_reducible k1 e1 σ1 ∧ base_reducible k2 e2 σ2) as [H1' H2'].
    { by unfold base_reducible; split; eauto. }
    by eapply base_reducible_fill_inj.
  Qed.

  Lemma base_reducible_reducible k e σ :
    base_reducible k e σ → reducible (fill k e) σ.
  Proof.
    intros (k' & e' & σ' & efs & Hstep).
    exists [], (fill k' e'), σ', efs.
    by apply Ectx_prim_step_2.
  Qed.

  Lemma base_reducible_prim_step_ctx k1 e1 σ1 e2 σ2 efs :
    base_reducible k1 e1 σ1 →
    prim_step (fill k1 e1) σ1 e2 σ2 efs →
    ∃ k2 e2', e2 = fill k2 e2' ∧ base_step k1 e1 σ1 k2 e2' σ2 efs.
  Proof.
    intros (k2''&e2''&σ2''&efs''&Hstep_k).
    intros [k1' k2' e1' e2' Hk_e1 -> Hstep].
    exists k2', e2'. split; [done|].
    by edestruct base_step_fill_inj as [-> ->]; try done.
  Qed.

  Class AtomicEctx (a : atomicity) (e : expr) : Prop :=
    atomic_ectx k σ e'' σ' efs :
      prim_step (fill k e) σ e'' σ' efs →
        ∃ e',
        e'' = fill k e' ∧
        (if a is WeaklyAtomic then irreducible e' σ' else is_Some (to_val e')) ∧
        (∀ k', prim_step (fill k' e) σ (fill k' e') σ' efs).

  Instance atomic_ectx_atomic s e : AtomicEctx s e → Atomic s e.
  Proof.
    intros Hatomic ????? Hstep. simpl in *.
    destruct κ=>//. simpl in Hstep.
    by destruct (Hatomic [] _ _ _ _ Hstep) as (e2' & -> & ? & _).
  Qed.

  Lemma strongly_atomic_ectx_atomic_ectx e a :
    AtomicEctx StronglyAtomic e → AtomicEctx a e.
  Proof.
    intros Hatomic ????? Hstep.
    destruct (Hatomic _ _ _ _ _ Hstep) as (e' & -> & Hval & Hectx).
    exists e'. by split; [|split]; destruct a; auto using val_irreducible.
  Qed.

  Definition base_atomic (a : atomicity) (e : expr) : Prop :=
    ∀ k σ k' e' σ' efs,
      base_step k e σ k' e' σ' efs →
      k' = k ∧
      if a is WeaklyAtomic then irreducible e' σ' else is_Some (to_val e').

  Definition sub_redexes_are_values (e : expr) :=
    ∀ k e', e = fill k e' → to_val e' = None → k = [].

  Lemma ectx_language_atomic a e :
    base_atomic a e → sub_redexes_are_values e → Atomic a e.
  Proof.
    intros Hatomic_step Hatomic_fill σ e' κ σ' efs. destruct κ=>//=.
    intros [k1 k2 e1' e2' -> -> Hstep].
    assert (k1 = []) as ->.
    { by eauto 10 using val_base_stuck. }
    { simpl. simpl in *.
      by destruct (Hatomic_step _ _ _ _ _ _ Hstep) as [-> ?].
    }
  Qed.

  Lemma ectxi_language_sub_redexes_are_values e :
    (∀ f e', e = fill_frame f e' → is_Some (to_val e')) →
    sub_redexes_are_values e.
  Proof.
    intros Hsub k e' ->. destruct k as [|f k]; try done.
    intros []%eq_None_not_Some.
    destruct (Hsub f (fill k e')) as [v Heq]; first done.
    by destruct (fill_val _ _ _ Heq) as [-> ->].
  Qed.

End pure_steps.

