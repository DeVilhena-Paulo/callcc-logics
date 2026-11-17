(** A logic for call/1cc.
    Source: Xavier Leroy, "Control structures for programming languages",
    last chapter *)

From Coq Require Import ZArith Lia Bool List String Program.Equality.
From Coq Require Import FunctionalExtensionality PropExtensionality.

Require Import Separation.
Require Import AST.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** Reduction semantics *)

(** Compared with Callcc.v, the only difference is that continuations captured
    by CALLCC are always stored in the heap and represented by a location,
    and that THROW deallocates the stored continuation, making it impossible
    to throw a second time.
    Also, the body of CALLCC runs with continuation KABORT, so that it cannot
    return normally. *)

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
(* CALLCC heap-allocates the continuation and prevents the function body from returning normally. *)
  | red_call1cc: forall x a k (h: heap) l,
      h l = None ->
      red (CALLCC (LAM x a), k, h) (subst x (LOC l) a, KABORT, hupdate l (CONT k) h)
(* THROW deallocates the continuation, making sure it's not used a second time *)
  | red_throw: forall l v k (h: heap) k',
      h l = Some (CONT k') ->
      red (THROW (LOC l) v, k, h) (VAL v, k', hfree l h).

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

(** A configuration remains safe if the heap is extended. *)

Lemma can_reduce_extends: forall a k h h0,
  can_reduce (a, k, h) ->
  can_reduce (a, k, hunion h h0).
Proof.
  intros until h0; intros [c' RED]; inv RED; try (econstructor; now constructor).
- (* red_ref *)
  destruct (isfinite (hunion h h0)) as [l' F'].
  econstructor. apply red_ref with (l := l'). apply F'. lia.
- (* red_get *)
  econstructor. apply red_get with (v := v). simpl; rewrite H3; auto.
- (* red set *)
  econstructor. apply red_set with (v := v). simpl. destruct (h l); congruence.
- (* red free *)
  econstructor. apply red_free. simpl. destruct (h l); congruence.
- (* red call1cc *)
  destruct (isfinite (hunion h h0)) as [l' F'].
  econstructor. apply red_call1cc with (l := l'). apply F'. lia.
- (* red throw *)
  econstructor. apply red_throw with (k' := k'). simpl. destruct (h l); congruence.
Qed.

Lemma red_extends: forall h0 a k h a' k' hh,
  can_reduce (a, k, h) ->
  hdisjoint h h0 ->
  red (a, k, hunion h h0) (a', k', hh) ->
  exists h', hh = hunion h' h0 /\ hdisjoint h' h0 /\ red (a, k, h) (a', k', h').
Proof.
  intros until hh; intros [c' RED'] DISJ RED. inv RED; try (exists h; eauto using red; fail).
- (* red_ref *)
  exists (hupdate l v h); split; [|split].
  + apply heap_extensionality; intros p; simpl. destruct (Z.eq_dec l p); auto.
  + intros p; specialize (DISJ p); simpl in *. 
    destruct (Z.eq_dec l p); auto. subst p. destruct (h l); intuition congruence.
  + apply red_ref. simpl in H0; destruct (h l); congruence.
- (* red_get *)
  assert (h l <> None) by (inv RED'; congruence).
  exists h; split; [|split].
  + auto.
  + auto.
  + apply red_get. simpl in H0; destruct (h l); congruence.
- (* red_set *)
  assert (h l <> None) by (inv RED'; auto).
  exists (hupdate l v h); split; [|split].
  + apply heap_extensionality; intros p; simpl. destruct (Z.eq_dec l p); auto.
  + intros p; specialize (DISJ p); simpl in *. destruct (Z.eq_dec l p); intuition congruence.
  + apply red_set. auto.
- (* red_free *)
  assert (h l <> None) by (inv RED'; auto).
  assert (h0 l = None) by (specialize (DISJ l); intuition congruence).
  exists (hfree l h); split; [|split].
  + apply heap_extensionality; intros p; simpl. destruct (Z.eq_dec l p); congruence.
  + intros p; specialize (DISJ p); simpl in *. destruct (Z.eq_dec l p); intuition congruence.
  + apply red_free. auto.
- (* red_callcc *)
  exists (hupdate l (CONT k) h); split; [|split].
  + apply heap_extensionality; intros p; simpl. destruct (Z.eq_dec l p); auto.
  + intros p; specialize (DISJ p); simpl in *. 
    destruct (Z.eq_dec l p); auto. subst p. destruct (h l); intuition congruence.
  + apply red_call1cc. simpl in H0; destruct (h l); congruence.
- (* red_throw *)
  assert (h l <> None) by (inv RED'; congruence).
  assert (h0 l = None) by (specialize (DISJ l); intuition congruence).
  exists (hfree l h); split; [|split].
  + apply heap_extensionality; intros p; simpl. destruct (Z.eq_dec l p); congruence.
  + intros p; specialize (DISJ p); simpl in *. destruct (Z.eq_dec l p); intuition congruence.
  + apply red_throw with (k' := k'). simpl in H0. destruct (h l); congruence.
Qed.

Theorem safe_extends: forall h0 a k h,
  safe (a, k, h) -> hdisjoint h h0 -> safe (a, k, hunion h h0).
Proof.
  intros h0. cofix COINDHYP; intros a k h SAFE DISJ; inv SAFE.
- apply safe_done.
- apply safe_step.
  + apply can_reduce_extends; auto.
  + intros [[a' k'] hh] RED. edestruct red_extends as (h' & A & B & C); eauto.
    subst hh. apply COINDHYP; auto.
Qed.

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

Definition iscont1 (k: cont) (Q: postcond) : assertion :=
  fun h1 => forall v h2, Q v h2 -> hdisjoint h1 h2 -> safe (VAL v, k, hunion h1 h2).

Definition iscont (l: addr) (Q: postcond) : assertion :=
  aexists (fun k => contains l (CONT k) ** iscont1 k Q).

(* Note: the footprint of [iscont l Q] is not empty.  It comprises
   - the memory location where the continuation is stored
   - the resources that the continuation needs and that are not part of the postcondition. *)

Lemma iscont1_monotonic: forall k (Q: postcond) (R: assertion),
  iscont1 k (fun v => Q v ** R) ** R -->> iscont1 k Q.
Proof.
  intros; intro h. intros (h1 & h2 & P1 & P2 & S & U).
  red. intros v h' PRE DISJ. subst h.
  apply hdisjoint_union_l in DISJ. destruct DISJ as [D1 D2]. apply hdisjoint_sym in D2.
  rewrite hunion_assoc. apply P1.
  rewrite hunion_comm by auto. exists h', h2; intuition auto.
  apply hdisjoint_union_r; auto.
Qed.

Lemma iscont_monotonic: forall l (Q: postcond) (R: assertion),
  iscont l (fun v => Q v ** R) ** R -->> iscont l Q.
Proof.
  intros. unfold iscont. rewrite lift_aexists.
  intros h (k & H). rewrite sepconj_assoc in H.
  exists k. revert H. apply sepconj_imp_r. apply iscont1_monotonic.
Qed.

Definition afalse : assertion := fun h => False.

Lemma triple_call1cc_framed: forall x a P Q R,
  (forall l, ⦃ iscont l Q ** P ⦄ subst x (LOC l) a ⦃ fun _ => afalse ⦄) ->
  ⦃ P ** R ⦄ CALLCC (LAM x a) ⦃ fun v => Q v ** R ⦄.
Proof.
  intros until R; intros T. red; intros.
  destruct (isfinite h) as [l0 F].
  apply safe_step.
  + econstructor; apply red_call1cc with (l := l0). apply F; lia.
  + intros c' RED; inv RED.
    apply T.
    assert (X: iscont l (fun v => Q v ** R) ** P ** R -->> iscont l Q ** P).
    { rewrite (sepconj_comm P), <- sepconj_assoc. apply sepconj_imp_l. apply iscont_monotonic. }
    apply X. exists (hupdate l (CONT k) hempty), h.
    split. red. exists k.
    exists (hupdate l (CONT k) hempty), hempty.
    split. red; auto.
    split. red. intros. rewrite hunion_empty. apply H0. auto.
    split. red; auto.
    rewrite hunion_comm, hunion_empty. auto. red; auto.
    split. auto.
    split. intros p. simpl. destruct (Z.eq_dec l p); intuition congruence.
    apply heap_extensionality; intros p. simpl. destruct (Z.eq_dec l p); auto.
    intros. red in H1. tauto.
Qed.

Remark iscont1_safe: forall k Q v h,
  (iscont1 k Q ** Q v) h -> safe (VAL v, k, h).
Proof.
  intros. destruct H as (h1 & h2 & P1 & P2 & D & U). subst h. apply P1; auto.
Qed.

Remark iscont1_safe_extended: forall k Q v R h,
  (iscont1 k Q ** Q v ** R) h -> safe (VAL v, k, h).
Proof.
  intros. rewrite <- sepconj_assoc in H. 
  destruct H as (h1 & h2 & P1 & P2 & D & U). subst h. 
  apply safe_extends; auto. eapply iscont1_safe; eauto.
Qed.

Lemma triple_throw_framed: forall l v Q R,
  ⦃ iscont l Q ** Q v ** R ⦄ THROW (LOC l) v ⦃ fun _ => afalse ⦄.
Proof.
  intros until Q; red; intros.
  unfold iscont in H. rewrite lift_aexists in H. destruct H as (k' & H).
  rewrite sepconj_assoc in H.
  destruct H as (h1 & h2 & P1 & P2 & S & U). red in P1.
  assert (h l = Some (CONT k')).
  { subst h h1; simpl. destruct (Z.eq_dec l l); congruence. }
  apply safe_step.
  + econstructor; apply red_throw with (k' := k'). auto.
  + intros c' RED; inv RED.
    replace k'0 with k' by congruence.
    assert (EQ: hfree l (hunion (hupdate l (CONT k') hempty) h2) = h2).
    { apply heap_extensionality; intros p.
      generalize (S p); simpl. destruct (Z.eq_dec l p); intuition congruence. }
    rewrite EQ. eapply iscont1_safe_extended; eauto.
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

(** Separation logic triples *)

Definition septriple P a Q := forall R, triple (P ** R) a (fun v => Q v ** R).

Notation "⦃ P ⦄ a ⦃ Q ⦄" := (septriple P a Q) (at level 90, a at next level).

Lemma rule_frame: forall P a Q R,
  ⦃ P ⦄ a ⦃ Q ⦄ ->
  ⦃ P ** R ⦄ a ⦃ fun v => Q v ** R ⦄.
Proof.
  intros; intro. rewrite sepconj_assoc. eapply triple_cons_right. apply H.
  simpl; intros. rewrite sepconj_assoc. red; auto.
Qed.

Lemma rule_val: forall v (P: precond) (Q: postcond),
  aimp P (Q v) ->
  ⦃ P ⦄ VAL v ⦃ Q ⦄.
Proof.
  intros; intro. apply triple_val. apply sepconj_imp_l; auto.
Qed.

Lemma rule_let: forall x a b P Q R,
  ⦃ P ⦄ a ⦃ R ⦄ ->
  (forall v, ⦃ R v ⦄ subst x v b ⦃ Q ⦄) ->
  ⦃ P ⦄ LET x a b ⦃ Q ⦄.
Proof.
  intros; intro. apply triple_let with (fun v => R v ** R0); auto. intros; apply H0.
Qed.

Lemma rule_seq: forall a b P Q R,
  ⦃ P ⦄ a ⦃ fun _ => R ⦄ ->
  ⦃ R ⦄ b ⦃ Q ⦄ ->
  ⦃ P ⦄ SEQ a b ⦃ Q ⦄.
Proof.
  intros; intro. apply triple_seq with (R ** R0); auto.
Qed.

Lemma rule_ifthenelse: forall n a b P Q,
  ⦃ (n <> 0) //\\ P ⦄ a ⦃ Q ⦄ ->
  ⦃ (n = 0) //\\ P ⦄ b ⦃ Q ⦄ ->
  ⦃ P ⦄ IFTHENELSE (INT n) a b ⦃ Q ⦄.
Proof.
  intros; intro. apply triple_ifthenelse; rewrite <- lift_pureconj; auto.
Qed.

Lemma rule_app: forall x a v P Q,
  ⦃ P ⦄ subst x v a ⦃ Q ⦄ ->
  ⦃ P ⦄ APP (LAM x a) v ⦃ Q ⦄.
Proof.
  intros; intro. apply triple_app; auto.
Qed.

Lemma rule_add: forall i j P,
  ⦃ P ⦄ ADD (INT i) (INT j) ⦃ fun r => (r = INT (i + j)) //\\ P ⦄.
Proof.
  intros; intro. eapply triple_cons_right. apply triple_add.
  intros; simpl. rewrite lift_pureconj. red; auto.
Qed.

Lemma rule_ref: forall v,
  ⦃ emp ⦄ REF v ⦃ fun r => aexists (fun l => (r = LOC l) //\\ contains l v) ⦄.
Proof.
  intros; intro. rewrite sepconj_emp. eapply triple_cons_right. apply triple_ref.
  intros; simpl. intros h [l X]. rewrite lift_aexists. exists l. rewrite lift_pureconj; auto. 
Qed.

Lemma rule_ref': forall P v,
  ⦃ P ⦄ REF v ⦃ fun r => aexists (fun l => (r = LOC l) //\\ contains l v ** P) ⦄.
Proof.
  intros; intro. eapply triple_cons_right. apply triple_ref.
  intros; simpl. rewrite ! lift_aexists. intros h (l & A). exists l. rewrite ! lift_pureconj, sepconj_assoc. auto. 
Qed.

Lemma rule_get: forall l v,
  ⦃ contains l v ⦄ GET (LOC l) ⦃ fun v' => (v' = v) //\\ contains l v ⦄.
Proof.
  intros; intro. eapply triple_cons_right. apply triple_get.
  simpl. intros v0 h. rewrite lift_pureconj; auto.
Qed.

Lemma rule_get': forall l v P,
  ⦃ contains l v ** P ⦄ GET (LOC l) ⦃ fun v' => (v' = v) //\\ contains l v ** P⦄.
Proof.
  intros; intro. rewrite sepconj_assoc. eapply triple_cons_right. apply triple_get.
  simpl. intros v0 h. rewrite lift_pureconj, sepconj_assoc; auto.
Qed. 

Lemma rule_set: forall l v,
  ⦃ valid l ⦄ SET (LOC l) v ⦃ fun _ => contains l v ⦄.
Proof.
  intros; intro. apply triple_set.
Qed.

Lemma rule_set': forall l v v0 P,
  ⦃ contains l v0 ** P ⦄ SET (LOC l) v ⦃ fun _ => contains l v ** P ⦄.
Proof.
  intros; intro. apply triple_cons_left with (valid l ** P ** R). eapply triple_cons_right.
  apply triple_set.
  simpl; intros. rewrite sepconj_assoc; red; auto.
  unfold valid. rewrite lift_aexists, sepconj_assoc. intros h H. exists v0; auto.
Qed.

Lemma rule_free: forall l,
  ⦃ valid l ⦄ FREE (LOC l) ⦃ fun _ => emp ⦄.
Proof.
  intros; intro. eapply triple_cons_right. apply triple_free.
  simpl; intros. rewrite sepconj_emp. red; auto.
Qed.

Lemma rule_free': forall l v0 P,
  ⦃ contains l v0 ** P ⦄ FREE (LOC l) ⦃ fun _ => P ⦄.
Proof.
  intros; intro. eapply triple_cons_left. apply triple_free.
  unfold valid. rewrite lift_aexists, sepconj_assoc. intros h H. exists v0; auto.
Qed.

Lemma rule_call1cc: forall x a P Q,
  (forall l, ⦃ iscont l Q ** P ⦄ subst x (LOC l) a ⦃ fun _ => afalse ⦄) ->
  ⦃ P ⦄ CALLCC (LAM x a) ⦃ fun v => Q v ⦄.
Proof.
  intros; intro. apply triple_call1cc_framed. intros. simpl. specialize (H l emp).
  rewrite sepconj_comm, sepconj_emp in H.
  eapply triple_cons_right. eexact H. simpl. rewrite sepconj_comm, sepconj_emp. 
  intros; red; auto.
Qed.

Lemma rule_throw: forall l v Q,
  ⦃ iscont l Q ** Q v ⦄ THROW (LOC l) v ⦃ fun _ => afalse ⦄.
Proof.
  intros l v Q R. rewrite sepconj_assoc. 
  eapply triple_cons_right. eapply triple_throw_framed.
  simpl; intros; red; intros. elim H.
Qed.

Lemma rule_cons_left: forall a P Q P',
  ⦃ P ⦄ a ⦃ Q ⦄ -> P' -->> P -> ⦃ P' ⦄ a ⦃ Q ⦄.
Proof.
  intros; intro. eapply triple_cons_left. eapply H. apply sepconj_imp_l; auto.
Qed.

Lemma rule_cons_right: forall a P Q Q',
  ⦃ P ⦄ a ⦃ Q ⦄ -> (forall v, Q v -->> Q' v) -> ⦃ P ⦄ a ⦃ Q' ⦄.
Proof.
  intros; intro. eapply triple_cons_right. eapply H.
  intros; simpl. apply sepconj_imp_l; auto.
Qed.

Lemma rule_cons: forall a P P' Q Q',
  ⦃ P ⦄ a ⦃ Q ⦄ -> P' -->> P -> (forall v, Q v -->> Q' v) -> ⦃ P' ⦄ a ⦃ Q' ⦄.
Proof.
  intros. apply rule_cons_left with P; auto. apply rule_cons_right with Q; auto.
Qed.

Lemma rule_pure_pre: forall a P Q (A: Prop),
  (A -> ⦃ P ⦄ a ⦃ Q ⦄) -> ⦃ A //\\ P ⦄ a ⦃ Q ⦄.
Proof.
  intros; intro. rewrite lift_pureconj. red; intros. destruct H0. eapply H; eauto.
Qed.

Lemma rule_exists_pre: forall (X: Type) a (P: X -> precond) Q,
  (forall x, ⦃ P x ⦄ a ⦃ Q ⦄) -> ⦃ aexists P ⦄ a ⦃ Q ⦄.
Proof.
  intros; intro. rewrite lift_aexists. red; intros. destruct H0 as (v & H0). eapply (H v); eauto.
Qed.

Lemma rule_let_val: forall x v a P Q,
  ⦃ P ⦄ subst x v a ⦃ Q ⦄ ->
  ⦃ P ⦄ LET x (VAL v) a ⦃ Q ⦄.
Proof.
  intros. eapply rule_let with (R := fun x => (x = v) //\\ P).
  apply rule_val. intro; simpl; unfold pureconj. auto.
  intros v0.
 apply rule_pure_pre. intros EQ; subst v0; auto.
Qed.
