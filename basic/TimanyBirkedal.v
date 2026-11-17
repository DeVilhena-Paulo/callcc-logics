(** Example of call/cc, from Timany & Birkedal *)

From Coq Require Import ZArith Lia String.
Require Import Separation AST Callcc.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Coercion VAL : value >-> term.
Coercion VAR : string >-> value.

(** Increment *)

Definition INCR (r: value) (delta: Z) : term :=
  LET "x" (GET r)
    (LET "y" (ADD "x" (INT delta))
      (SET r "y")).

Lemma triple_incr: forall l n P delta,
  ⦃ contains l (INT n) ** P ⦄ INCR (LOC l) delta ⦃ fun _ => contains l (INT (n + delta)) ** P ⦄.
Proof.
  intros. unfold INCR.
  eapply triple_let. apply triple_get. 
  intros v. apply triple_pure_pre. intros EQ. subst v. simpl.
  eapply triple_let. apply triple_add.
  intros v. apply triple_pure_pre. intros EQ. subst v. simpl.
  eapply triple_cons_left. apply triple_set.
  apply sepconj_imp_l. intros h C. exists (INT n); auto.
Qed.

(** Get then free *)

Definition GETFREE (r: value) : term :=
  LET "x" (GET r) (SEQ (FREE r) "x").

Lemma triple_getfree: forall l v P,
  ⦃ contains l v ** P ⦄ GETFREE (LOC l) ⦃ fun r => (r = v) //\\ P ⦄.
Proof.
  intros. unfold GETFREE.
  eapply triple_let. apply triple_get.
  intros v0. apply triple_pure_pre. intros EQ. subst v0. simpl.
  eapply triple_seq. eapply triple_cons_left. apply triple_free.
  apply sepconj_imp_l. intros h C. exists v; auto.
  apply triple_val. red; intros; split; auto.
Qed.

(** The example by Timany and Birkedal *)

Definition Timany_Birkedal :=
  LET "r" (REF (INT 0))
    (LET "f" (CALLCC (LAM "k" (VAL ((LAM "x" (THROW "k" (LAM "y" UNIT)))))))
      (SEQ (INCR "r" 2)
        (SEQ (APP "f" (INT 0))
          (GETFREE "r")))).

Lemma triple_Timany_Birkedal_weak:
  ⦃ emp ⦄ Timany_Birkedal ⦃ fun r => (exists n, r = INT (n * 2)) //\\ emp ⦄.
Proof.
  eapply triple_let. apply triple_ref.
  intros v. apply triple_exists_pre. intros x. apply triple_pure_pre. intros EQ; subst v.
  simpl.
  set (INV := aexists (fun n => contains x (INT (n * 2)))).
  set (SPEC f := ⦃ INV ⦄ APP f VUNIT ⦃ fun _ => INV ⦄).
  set (Q f := SPEC f //\\ INV).
  apply triple_cons_left with INV.
  2: { rewrite sepconj_comm, sepconj_emp. red; intros. exists 0; auto. }
  eapply triple_let with (R := Q).
  eapply triple_callcc.
  intros k. simpl.
  apply triple_val. unfold Q. intros h [P1 P2]. split; auto.
  red. apply triple_app. simpl. eapply triple_cons_left. eapply triple_cons_right.
  apply triple_throw.
  intros v h1; unfold afalse. tauto.
  intros h1; split. eassumption. split; auto.
  red. apply triple_app. simpl. apply triple_val. red; auto.
  intros f; simpl.
  eapply triple_seq with (R := Q f).
  apply triple_pure_pre. intro SP. apply triple_exists_pre. intros n.
  eapply triple_cons_right. rewrite <- (sepconj_emp_r (contains x (INT (n * 2)))). apply triple_incr.
  intros v h. rewrite sepconj_emp_r. intros. split; auto. exists (n + 1). 
  replace ((n + 1) * 2) with (n * 2 + 2) by lia. auto.
  eapply triple_seq with (R := INV).
  apply triple_pure_pre. intro SP. apply SP.
  apply triple_exists_pre. intros n. 
  rewrite <- (sepconj_emp_r (contains x (INT (n * 2)))).
  eapply triple_cons_right. apply triple_getfree.
  intros v h [A B]. split; auto. exists n; auto. 
Qed.
