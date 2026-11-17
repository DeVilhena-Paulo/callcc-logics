(* class_instances.v *)

(* Adapted from [iris_heap_lang/class_instances.v]. *)

From iris.program_logic Require Export language.
From iris.prelude Require Import options.

From callcc_logics Require Export semantics iris_instantiation tactics notation.

Global Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
Global Instance as_val_val v : AsVal (Val v).
Proof. by eexists. Qed.

Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Global Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
Global Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

(** * Instances of the [Atomic] class *)
Section atomic.

  Ltac solve_atomic_ectx :=
    apply strongly_atomic_ectx_atomic_ectx;
    intros ????? Hstep;
    inversion Hstep;
    match goal with
    | H : fill _ _ = fill ?k' ?e' |- _ =>
        pose proof (f_equal get_redex H) as Hget;
        erewrite (base_reducible_get_redex' k' e') in Hget; [|done];
        autorewrite with get_redex_fill_db in Hget;
        injection Hget as <- <-;
        inv_base_step
    end;
    eexists; split; [|split]; try done;
    intros ?;
    eapply Ectx_prim_step; try done;
    by econstructor.

  Global Instance alloc_atomic_ectx a v w : AtomicEctx a (AllocN (Val v) (Val w)).
  Proof. solve_atomic_ectx. Qed.
  Global Instance store_atomic_ectx a v1 v2 : AtomicEctx a (Store (Val v1) (Val v2)).
  Proof. solve_atomic_ectx. Qed.
  Global Instance free_atomic_ectx s v : AtomicEctx s (Free (Val v)).
  Proof. solve_atomic_ectx. Qed.
  Global Instance load_atomic_ectx s v : AtomicEctx s (Load (Val v)).
  Proof. solve_atomic_ectx. Qed.

  Global Instance fork_atomic_ectx s e : AtomicEctx s (Fork e).
  Proof. solve_atomic_ectx. Qed.
  Global Instance xchg_atomic_ectx s v1 v2 : AtomicEctx s (Xchg (Val v1) (Val v2)).
  Proof. solve_atomic_ectx. Qed.
  Global Instance cmpxchg_atomic_ectx s v0 v1 v2 : AtomicEctx s (CmpXchg (Val v0) (Val v1) (Val v2)).
  Proof. solve_atomic_ectx. Qed.
  Global Instance faa_atomic_ectx s v1 v2 : AtomicEctx s (FAA (Val v1) (Val v2)).
  Proof. solve_atomic_ectx. Qed.

  Global Instance rec_atomic_ectx s f x e : AtomicEctx s (Rec f x e).
  Proof. solve_atomic_ectx. Qed.
  Global Instance pair_atomic_ectx s v1 v2 : AtomicEctx s (Pair (Val v1) (Val v2)).
  Proof. solve_atomic_ectx. Qed.
  Global Instance injl_atomic_ectx s v : AtomicEctx s (InjL (Val v)).
  Proof. solve_atomic_ectx. Qed.
  Global Instance injr_atomic_ectx s v : AtomicEctx s (InjR (Val v)).
  Proof. solve_atomic_ectx. Qed.
  (** The instance below is a more general version of [Skip] *)
  Global Instance beta_atomic_ectx s f x v1 v2 : AtomicEctx s (App (RecV f x (Val v1)) (Val v2)).
  Proof. destruct f, x; solve_atomic_ectx. Qed.
  Global Instance unop_atomic_ectx s op v : AtomicEctx s (UnOp op (Val v)).
  Proof. solve_atomic_ectx. Qed.
  Global Instance binop_atomic_ectx s op v1 v2 : AtomicEctx s (BinOp op (Val v1) (Val v2)).
  Proof. solve_atomic_ectx. Qed.
  Global Instance if_true_atomic_ectx s v1 e2 :
    AtomicEctx s (If (Val $ LitV $ LitBool true) (Val v1) e2).
  Proof. solve_atomic_ectx. Qed.
  Global Instance if_false_atomic_ectx s e1 v2 :
    AtomicEctx s (If (Val $ LitV $ LitBool false) e1 (Val v2)).
  Proof. solve_atomic_ectx. Qed.
  Global Instance fst_atomic_ectx s v : AtomicEctx s (Fst (Val v)).
  Proof. solve_atomic_ectx. Qed.
  Global Instance snd_atomic_ectx s v : AtomicEctx s (Snd (Val v)).
  Proof. solve_atomic_ectx. Qed.

End atomic.

(*
Section pure_exec.
  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_base_step.
  Local Ltac solve_pure_exec :=
    subst; intros ?; apply nsteps_once, iris_instantiation.pure_base_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].

  Global Instance pure_recc f x (erec : expr) :
    PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_pairc (v1 v2 : val) :
    PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_injlc (v : val) :
    PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_injrc (v : val) :
    PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
    PureExec True 1 (App (Val v1) (Val v2)) (val_subst' x v2 (val_subst' f v1 erec)).
  Proof. unfold AsRecV in *. solve_pure_exec. Qed.

  Global Instance pure_unop op v v' :
    PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
  Proof. solve_pure_exec. Qed.

  Global Instance pure_binop op v1 v2 v' :
    PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v') | 10.
  Proof. solve_pure_exec. Qed.
  (* Lower-cost instance for [EqOp]. *)
  Global Instance pure_eqop v1 v2 :
    PureExec (vals_compare_safe v1 v2) 1
      (BinOp EqOp (Val v1) (Val v2))
      (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
  Proof.
    intros Hcompare.
    cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
    { intros. revert Hcompare. solve_pure_exec. }
    rewrite /bin_op_eval /= decide_True //.
  Qed.

  Global Instance pure_if_true e1 e2 :
    PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
  Proof. solve_pure_exec. Qed.
  Global Instance pure_if_false e1 e2 :
    PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_fst v1 v2 :
    PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_snd v1 v2 :
    PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inl v e1 e2 :
    PureExec True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
  Proof. solve_pure_exec. Qed.
  Global Instance pure_case_inr v e1 e2 :
    PureExec True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_kont k v :
    PureExec True 1 (App (Val $ KontV k) (Val v)) (semantics.fill k (Val v)).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_handle_eff hs l k v h r :
    let k' := match hs with Deep => HandleCtx hs MS l h r :: k | Shallow => k end in
    PureExec (l ∉ ectx_labels k) 1
      (Handle hs MS (EffLabel l) (fill k (Do (EffLabel l) (Val v))) h r)
      (App (App h (Val v)) (Val $ KontV k')).
  Proof.
    intros ?. unfold k'.
    subst; intros ?; apply nsteps_once, pure_base_step_pure_step; constructor.
    - intros; subst. do 3 eexists. apply HandleMSEffS; first done. by apply to_of_eff.
    - simpl; intros. inv_base_step.
      + rewrite to_of_eff in H11. by inversion H11.
      + specialize (fill_not_val k (do: l v) eq_refl). by rewrite -H5.
  Qed.

  Global Instance pure_handle_ret hs m l v h r :
    PureExec True 1 (Handle hs m (EffLabel l) (Val v) h r) (App r (Val v)).
  Proof.
    subst; intros ?; apply nsteps_once, pure_base_step_pure_step; constructor.
    - intros; subst. do 3 eexists. by apply HandleRetS.
    - intros; subst. by inv_base_step.
  Qed.

End pure_exec.

*)
