(** A logic for call/cc.
    Source: Paulo de Vilhena, "Principles of callcc". *)

From Coq Require Import ZArith Lia Bool List String Program.Equality.
From Coq Require Import FunctionalExtensionality PropExtensionality.

Require Import Separation.
Require Import AST.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** Reduction semantics *)

Definition heap := heap value.

Inductive red: term * cont * heap -> term * cont * heap -> Prop :=
  | red_let_focus: forall x a b k h,
      red (LET x a b, k, h) (a, KLET x b k, h)
  | red_let_done: forall v x b k h,
      red (VAL v, KLET x b k, h) (subst x v b, k, h)
  | red_seq_focus: forall a b k h,
      red (SEQ a b, k, h) (a, KSEQ b k, h)
  | red_seq_done: forall v b k h,
      red (VAL v, KSEQ b k, h) (b, k, h)
  | red_ifthenelse: forall n a b k h,
      red (IFTHENELSE (INT n) a b, k, h) ((if n =? 0 then b else a), k, h)
  | red_app: forall x a v k h,
      red (APP (LAM x a) v, k, h) (subst x v a, k, h)
  | red_add: forall i j k h,
      red (ADD (INT i) (INT j), k, h) (VAL (INT (i + j)), k, h)
  | red_ref: forall v k (h: heap) l,
      h l = None ->
      red (REF v, k, h) (VAL (LOC l), k, hupdate l v h)
  | red_get: forall l k (h: heap) v,
      h l = Some v ->
      red (GET (LOC l), k, h) (VAL v, k, h)
  | red_set: forall l v k (h: heap),
      h l <> None ->
      red (SET (LOC l) v, k, h) (UNIT, k, hupdate l v h)
  | red_free: forall l k (h: heap),
      h l <> None ->
      red (FREE (LOC l), k, h) (UNIT, k, hfree l h)
  | red_callcc: forall x a k h,
      red (CALLCC (LAM x a), k, h) (subst x (CONT k) a, k, h)
  | red_throw: forall k' v k h,
      red (THROW (CONT k') v, k, h) (VAL v, k', h).

Definition can_reduce (c: term * cont * heap) : Prop :=
  exists c', red c c'.

(** A configuration is safe if it doesn't crash: either it terminates
    or it runs forever. *)

CoInductive safe: term * cont * heap -> Prop :=
  | safe_done: forall v h,
      safe (VAL v, KSTOP, h)
  | safe_step: forall c,
      can_reduce c ->
      (forall c', red c c' -> safe c') ->
      safe c.

Ltac inv H := inversion H; clear H; subst.

(** Semantic definition of weak Hoare triples *)

Definition assertion := assertion value.
Definition precond := assertion.
Definition postcond := value -> assertion.

Definition triple (P: precond) (a: term) (Q: postcond) : Prop :=
  forall k h,
  P h ->
  (forall v h, Q v h -> safe (VAL v, k, h)) ->
  safe (a, k, h).

Notation "⦃ P ⦄ a ⦃ Q ⦄" := (triple P a Q) (at level 90, a at next level).

(** Hoare rules for control structures *)

Lemma triple_val: forall v (P: precond) (Q: postcond),
  aimp P (Q v) ->
  ⦃ P ⦄ VAL v ⦃ Q ⦄.
Proof.
  intros; red; intros. apply H1. auto.
Qed.

Lemma triple_let: forall x a b P Q R,
  ⦃ P ⦄ a ⦃ R ⦄ ->
  (forall v, ⦃ R v ⦄ subst x v b ⦃ Q ⦄) ->
  ⦃ P ⦄ LET x a b ⦃ Q ⦄.
Proof.
  intros until R; intros Ta Tb; red; intros.
  eapply safe_step.
  + econstructor; apply red_let_focus.
  + intros c' RED; inv RED.
    apply Ta. auto.
    intros v1 h1; intros.
    eapply safe_step.
    * econstructor; apply red_let_done.
    * intros c' RED; inv RED. apply Tb; auto.
Qed.

Lemma triple_seq: forall a b P Q R,
  ⦃ P ⦄ a ⦃ fun _ => R ⦄ ->
  ⦃ R ⦄ b ⦃ Q ⦄ ->
  ⦃ P ⦄ SEQ a b ⦃ Q ⦄.
Proof.
  intros until R; intros Ta Tb; red; intros.
  eapply safe_step.
  + econstructor; apply red_seq_focus.
  + intros c' RED; inv RED.
    apply Ta. auto.
    intros v1 h1; intros.
    eapply safe_step.
    * econstructor; apply red_seq_done.
    * intros c' RED; inv RED. apply Tb; auto.
Qed.

Lemma triple_ifthenelse: forall n a b P Q,
  ⦃ (n <> 0) //\\ P ⦄ a ⦃ Q ⦄ ->
  ⦃ (n = 0) //\\ P ⦄ b ⦃ Q ⦄ ->
  ⦃ P ⦄ IFTHENELSE (INT n) a b ⦃ Q ⦄.
Proof.
  intros until Q; intros Ta Tb. red; intros.
  eapply safe_step.
  + econstructor; apply red_ifthenelse.
  + intros c' RED; inv RED. destruct (Z.eqb_spec n 0).
    - apply Tb. split; auto. auto.
    - apply Ta. split; auto. auto.
Qed.

(** Hoare rules for application and arithmetic. *)

Lemma triple_app: forall x a v P Q,
  ⦃ P ⦄ subst x v a ⦃ Q ⦄ ->
  ⦃ P ⦄ APP (LAM x a) v ⦃ Q ⦄.
Proof.
  intros until Q; intros T; red; intros. apply safe_step.
  + econstructor; apply red_app.
  + intros c' RED; inv RED. apply T; auto.
Qed.

Lemma triple_add: forall i j P,
  ⦃ P ⦄ ADD (INT i) (INT j) ⦃ fun r => (r = INT (i + j)) //\\ P ⦄.
Proof.
  intros; red; intros. apply safe_step.
  + econstructor; apply red_add.
  + intros c' RED; inv RED. apply H0. split; auto.
Qed.

(** Hoare rules for references. *)

Lemma triple_ref: forall v P,
  ⦃ P ⦄ REF v ⦃ fun r => aexists (fun l => (r = LOC l) //\\ contains l v ** P) ⦄.
Proof.
  intros until P; red; intros.
  destruct (isfinite h) as [l0 F].
  apply safe_step.
  + econstructor; apply red_ref with (l := l0). apply F; lia.
  + intros c' RED; inv RED. 
    apply H0. exists l. split; auto.
    exists (hupdate l v hempty), h.
    split. red; auto.
    split. auto.
    split. intros p. simpl. destruct (Z.eq_dec l p); intuition congruence.
    apply heap_extensionality; intros p. simpl. destruct (Z.eq_dec l p); auto.
Qed.

Lemma triple_get: forall l v P,
  ⦃ contains l v ** P ⦄ GET (LOC l) ⦃ fun v' => (v' = v) //\\ contains l v ** P ⦄.
Proof.
  intros until P; red; intros.
  destruct H as (h1 & h2 & A & B & S & U). red in A.
  assert (h l = Some v).
  { subst h h1; simpl. destruct (Z.eq_dec l l); congruence. }
  apply safe_step.
  + econstructor. apply red_get with (v := v). auto.
  + intros c' RED; inv RED. replace v0 with v by congruence. 
    apply H0. split; auto. exists (hupdate l v hempty), h2; unfold contains; auto.
Qed.

Lemma triple_set: forall l v P,
  ⦃ valid l ** P ⦄ SET (LOC l) v ⦃ fun _ => contains l v ** P ⦄.
Proof.
  intros until P; red; intros.
  destruct H as (h1 & h2 & (v0 & A) & B & S & U). red in A.
  assert (h l = Some v0).
  { subst h h1; simpl. destruct (Z.eq_dec l l); congruence. }
  apply safe_step.
  + econstructor; apply red_set. congruence.
  + intros c' RED; inv RED.
    apply H0. exists (hupdate l v hempty), h2.
    split. red; auto.
    split. auto.
    split. intros p; simpl. generalize (S p); simpl.
    destruct (Z.eq_dec l p); intuition congruence.
    apply heap_extensionality; intros p. simpl. destruct (Z.eq_dec l p); auto.
Qed.

Lemma triple_free: forall l P,
  ⦃ valid l ** P ⦄ FREE (LOC l) ⦃ fun _ => P ⦄.
Proof.
  intros until P; red; intros.
  destruct H as (h1 & h2 & (v0 & A) & B & S & U). red in A.
  assert (h l = Some v0).
  { subst h h1; simpl. destruct (Z.eq_dec l l); congruence. }
  apply safe_step.
  + econstructor; apply red_free. congruence.
  + intros c' RED; inv RED. apply H0. replace (hfree l (hunion (hupdate l v0 hempty) h2)) with h2. auto.
    apply heap_extensionality; intros p.
    generalize (S p). simpl. destruct (Z.eq_dec l p); intuition congruence.
Qed.

(** Hoare rules for continuations *)

Definition iscont (k: cont) (Q: postcond) : Prop :=
  forall v h, Q v h -> safe (VAL v, k, h).

Lemma triple_callcc: forall x a P Q,
  (forall k, ⦃ iscont k Q //\\ P ⦄ subst x (CONT k) a ⦃ Q ⦄) ->
  ⦃ P ⦄ CALLCC (LAM x a) ⦃ Q ⦄.
Proof.
  intros until Q; intros T. red; intros. apply safe_step.
  + econstructor; apply red_callcc.
  + intros c' RED; inv RED. apply T; auto. split; auto.
Qed.

Definition afalse : assertion := fun h => False.

Lemma triple_throw: forall k v Q,
  ⦃ iscont k Q //\\ Q v ⦄ THROW (CONT k) v ⦃ fun _ => afalse ⦄.
Proof.
  intros until Q; red; intros. destruct H as [H1 H2].
  apply safe_step.
  + econstructor; apply red_throw.
  + intros c' RED; inv RED. apply H1; auto.
Qed.

(** Logical rules *)

Lemma triple_cons_left: forall a P Q P',
  ⦃ P ⦄ a ⦃ Q ⦄ ->  P' -->> P -> ⦃ P' ⦄ a ⦃ Q ⦄.
Proof.
  intros; red; intros. apply H; auto.
Qed.

Lemma triple_cons_right: forall a P Q Q',
  ⦃ P ⦄ a ⦃ Q ⦄ -> (forall v, Q v -->> Q' v) -> ⦃ P ⦄ a ⦃ Q' ⦄.
Proof.
  intros; red; intros. apply H. auto.
  intros. apply H2; auto. apply H0; auto.
Qed.
Lemma triple_pure_pre: forall a P Q (A: Prop),
  (A -> ⦃ P ⦄ a ⦃ Q ⦄) -> ⦃ A //\\ P ⦄ a ⦃ Q ⦄.
Proof.
  intros; red; intros. destruct H0. apply H; auto.
Qed.

Lemma triple_exists_pre: forall (X: Type) a (P: X -> precond) Q,
  (forall x, ⦃ P x ⦄ a ⦃ Q ⦄) -> ⦃ aexists P ⦄ a ⦃ Q ⦄.
Proof.
  intros; red; intros. destruct H0 as (v & H0). apply (H v); auto.
Qed.
