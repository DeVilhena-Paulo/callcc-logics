(** Two coroutines implemented using call/1cc.
    Source: Xavier Leroy, "Control structures for programming languages",
    last chapter *)

From Coq Require Import ZArith String.
Require Import Separation AST Call1cc.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Coercion VAL : value >-> term.
Coercion VAR : string >-> value.

Definition closed_val (v: value) : Prop :=
  forall x v', subst_val x v' v = v.

Section COROUTINE.

Variable fixpoint: (assertion -> assertion) -> assertion.
Hypothesis unroll_fixpoint: forall F, fixpoint F -->> F (fixpoint F).
Hypothesis roll_fixpoint: forall F, F (fixpoint F) -->> fixpoint F.

Variables f g: value.
Hypothesis f_closed: closed_val f.
Hypothesis g_closed: closed_val g.

Variable P: precond.
Variable Q: postcond.

Hypothesis f_spec: forall yield R,
  ⦃ P ** R ⦄ APP yield VUNIT ⦃ fun _ => P ** R ⦄ ->
  ⦃ P ** R ⦄ APP f yield ⦃ fun v => Q v ** R ⦄.

Hypothesis g_spec: forall yield R,
  ⦃ P ** R ⦄ APP yield VUNIT ⦃ fun _ => P ** R ⦄ ->
  ⦃ P ** R ⦄ APP g yield ⦃ fun v => Q v ** R ⦄.

Definition coroutine :=
     CALLCC (LAM "k0"
      (LET "ready" (REF VUNIT)
      (LET "yield" 
        (LAM "" (CALLCC (LAM "k" 
                  (LET "k'" (GET "ready") (SEQ (SET "ready" "k") (THROW "k'" VUNIT))))))
      (LET "terminate"
        (LAM "x" (SEQ (FREE "ready") (THROW "k0" "x")))
      (SEQ
        (CALLCC (LAM "k" (SEQ (SET "ready" "k")
                              (LET "x" (APP f "yield")
                                       (APP "terminate" "x")))))
        (LET "x" (APP g "yield")
                 (APP "terminate" "x"))))))).

Lemma coroutine_spec:
  ⦃ P ⦄ coroutine ⦃ Q ⦄.
Proof.
  unfold coroutine.
  apply rule_call1cc. intros k0; simpl.
  eapply rule_let. 
  { apply rule_ref'. }
  intros r; simpl; rewrite ! f_closed, ! g_closed.
  apply rule_exists_pre; intros ready; apply rule_pure_pre; intros EQ; subst r.
  eapply rule_let_val. 
  simpl; rewrite ! f_closed, ! g_closed.
  eapply rule_let_val.
  simpl; rewrite ! f_closed, ! g_closed.
  set (yield := (LAM "" (CALLCC (LAM "k" 
                  (LET "k'" (GET (LOC ready)) (SEQ (SET (LOC ready) "k") (THROW "k'" (INT 0)))))))).
  set (terminate := (LAM "x" (SEQ (FREE (LOC ready)) (THROW (LOC k0) "x")))).
  set (R := fixpoint (fun R => aexists (fun k => contains ready (LOC k)
                                              ** iscont k (fun _ => P ** R)
                                              ** iscont k0 Q))).
  assert (YIELD_SPEC:
           ⦃ P ** R ⦄ APP yield VUNIT ⦃ fun _ => P ** R  ⦄).
  { apply rule_app. simpl.
    apply rule_call1cc. intros k; simpl.
    rewrite sepconj_swap3. eapply rule_cons_left.
    2: { apply sepconj_imp_l. apply unroll_fixpoint. }
    fold R. rewrite ! lift_aexists. apply rule_exists_pre. intros k'.
    rewrite ! sepconj_assoc.
    eapply rule_let.
    { apply rule_get'. }
    intros r. apply rule_pure_pre. intros EQ; subst r. simpl.
    eapply rule_seq.
    { apply rule_set'. }
    apply rule_cons_left with (iscont k' (fun _ => P ** R) ** P ** R).
    2: { rewrite sepconj_pick2. apply sepconj_imp_r.
         rewrite sepconj_swap4. apply sepconj_imp_r.
         rewrite sepconj_swap3. rewrite sepconj_pick2. 
         intros h H. apply roll_fixpoint. exists k; auto. }
    apply rule_throw with (Q := fun _ => P ** R).
  }
  assert (TERMINATE_SPEC: forall v,
           ⦃ Q v ** R ⦄ APP terminate v ⦃ fun _ => afalse ⦄).
  { intros. apply rule_app. simpl.
    eapply rule_cons_left.
    2: { apply sepconj_imp_r. apply unroll_fixpoint. }
    rewrite sepconj_comm, lift_aexists. apply rule_exists_pre. intros k. fold R.
    rewrite sepconj_assoc. 
    eapply rule_seq.
    { apply rule_free'. }
    rewrite sepconj_assoc, sepconj_comm.
    eapply rule_cons_right.
    apply rule_frame. apply rule_throw.
    simpl; intros v0 h H. destruct H as (h1 & h2 & U & V & W & X). elim U. } 
  apply rule_seq with (P ** R).
- apply rule_call1cc.
  intros k. simpl; rewrite ! f_closed; fold yield; fold terminate.
  rewrite sepconj_pick2. eapply rule_seq. apply rule_set'.
  rewrite sepconj_swap4.
  apply rule_cons_left with (P ** R).
  2: { apply sepconj_imp_r; intros h H. apply roll_fixpoint; exists k; assumption. }
  eapply rule_let. apply f_spec. exact YIELD_SPEC.
  intros r. simpl. fold terminate. apply TERMINATE_SPEC.
- eapply rule_let. apply g_spec. exact YIELD_SPEC.
  intros r. simpl. fold terminate. apply TERMINATE_SPEC.
Qed.

End COROUTINE.
