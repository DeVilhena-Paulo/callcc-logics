(* semantics.v *)

From callcc_logics Require Import syntax.


(* ========================================================================= *)
(** * Preliminary Definitions. *)

(* ------------------------------------------------------------------------- *)
(** Values. *)

Notation of_val := Val (only parsing).
Definition to_val (e : expr) : option val :=
  match e with Val v => Some v | _ => None end.


(* ------------------------------------------------------------------------- *)
(** Frames & Evaluation Contexts. *)

Definition fill_frame (f : frame) (e : expr) : expr :=
  match f with
  | AppLCtx v2 =>
      App e (of_val v2)
  | AppRCtx e1 =>
      App e1 e
  | UnOpCtx op =>
      UnOp op e
  | BinOpLCtx op v2 =>
      BinOp op e (of_val v2)
  | BinOpRCtx op e1 =>
      BinOp op e1 e
  | IfCtx e1 e2 =>
      If e e1 e2
  | PairLCtx v2 =>
      Pair e (of_val v2)
  | PairRCtx e1 =>
      Pair e1 e
  | FstCtx =>
      Fst e
  | SndCtx =>
      Snd e
  | InjLCtx =>
      InjL e
  | InjRCtx =>
      InjR e
  | CaseCtx e1 e2 =>
      Case e e1 e2
  | AllocNLCtx v2 =>
      AllocN e (of_val v2)
  | AllocNRCtx e1 =>
      AllocN e1 e
  | FreeCtx =>
      Free e
  | LoadCtx =>
      Load e
  | StoreLCtx v2 =>
      Store e (of_val v2)
  | StoreRCtx e1 =>
      Store e1 e
  | CmpXchgLCtx v1 v2 =>
      CmpXchg e (of_val v1) (of_val v2)
  | CmpXchgMCtx e0 v2 =>
      CmpXchg e0 e (of_val v2)
  | CmpXchgRCtx e0 e1 =>
      CmpXchg e0 e1 e
  | XchgLCtx v2 =>
      Xchg e (of_val v2)
  | XchgRCtx e1 =>
      Xchg e1 e
  | FaaLCtx v2 =>
      FAA e (of_val v2)
  | FaaRCtx e1 =>
      FAA e1 e
  | RunThenAbortCtx =>
      RunThenAbort e
  end.

Fixpoint fill (k : ectx) (e : expr) : expr :=
  match k with [] => e | f :: k => fill_frame f (fill k e) end.

Definition get_frame (e : expr) : option (frame * expr) :=
  match e with
  | Var _ | Val _ | Rec _ _ _ | Callcc _ _ | Call1cc0 _ _  | Call1ccS _ _  | Fork _ =>
      None
  | App e1 e2 =>
      match to_val e2 with
      | None =>
          Some (AppRCtx e1, e2)
      | Some v2 =>
          Some (AppLCtx v2, e1)
      end
  | UnOp op e =>
      Some (UnOpCtx op, e)
  | BinOp op e1 e2 =>
      match to_val e2 with
      | None =>
          Some (BinOpRCtx op e1, e2)
      | Some v2 =>
          Some (BinOpLCtx op v2, e1)
      end
  | If e0 e1 e2 =>
      Some (IfCtx e1 e2, e0)
  | Pair e1 e2 =>
      match to_val e2 with
      | None =>
          Some (PairRCtx e1, e2)
      | Some v2 =>
          Some (PairLCtx v2, e1)
      end
  | Fst e =>
      Some (FstCtx, e)
  | Snd e =>
      Some (SndCtx, e)
  | InjL e =>
      Some (InjLCtx, e)
  | InjR e =>
      Some (InjRCtx, e)
  | Case e0 e1 e2 =>
      Some (CaseCtx e1 e2, e0)
  | AllocN e1 e2 =>
      match to_val e2 with
      | None =>
          Some (AllocNRCtx e1, e2)
      | Some v2 =>
          Some (AllocNLCtx v2, e1)
      end
  | Load e =>
      Some (LoadCtx, e)
  | Free e =>
      Some (FreeCtx, e)
  | Store e1 e2 =>
      match to_val e2 with
      | None =>
          Some (StoreRCtx e1, e2)
      | Some v2 =>
          Some (StoreLCtx v2, e1)
      end
  | CmpXchg e0 e1 e2 =>
      match to_val e2 with
      | None =>
          Some (CmpXchgRCtx e0 e1, e2)
      | Some v2 =>
          match to_val e1 with
          | None =>
              Some (CmpXchgMCtx e0 v2, e1)
          | Some v1 =>
              Some (CmpXchgLCtx v1 v2, e0)
          end
      end
  | Xchg e1 e2 =>
      match to_val e2 with
      | None =>
          Some (XchgRCtx e1, e2)
      | Some v2 =>
          Some (XchgLCtx v2, e1)
      end
  | FAA e1 e2 =>
      match to_val e2 with
      | None =>
          Some (FaaRCtx e1, e2)
      | Some v2 =>
          Some (FaaLCtx v2, e1)
      end
  | RunThenAbort e =>
      Some (RunThenAbortCtx, e)
  end.

Definition sub_expr e e' := ∃ f, Some (f, e) = get_frame e'.

Lemma sub_expr_wf : well_founded sub_expr.
Proof.
  intros e.
  induction e; apply Acc_intro=>y [f' HSome]; simpl in HSome;
  by (repeat match goal with
   | _ : Some _ = match ?e with | _ => _ end |- _ => destruct e
   | H : Some _ = Some _ |- _ => injection H as -> ->
   end).
Qed.

Definition sub_expr_intro f e e' : Some (f, e) = get_frame e' → sub_expr e e' :=
  λ H, @ex_intro frame (λ f, Some (f, e) = get_frame e') f H.

Fixpoint get_ectx (e : expr) : ectx * expr :=
  match e with
  | Var _ | Val _ | Rec _ _ _ | Callcc _ _ | Call1cc0 _ _ | Call1ccS _ _ | Fork _ =>
      ([], e)
  | App e1 e2 =>
      match to_val e2 with
      | None =>
          let (k, e') := get_ectx e2 in (AppRCtx e1 :: k, e')
      | Some v2 =>
          let (k, e') := get_ectx e1 in (AppLCtx v2 :: k, e')
      end
  | UnOp op e =>
      let (k, e') := get_ectx e in (UnOpCtx op :: k, e')
  | BinOp op e1 e2 =>
      match to_val e2 with
      | None =>
          let (k, e') := get_ectx e2 in (BinOpRCtx op e1 :: k, e')
      | Some v2 =>
          let (k, e') := get_ectx e1 in (BinOpLCtx op v2 :: k, e')
      end
  | If e0 e1 e2 =>
      let (k, e') := get_ectx e0 in (IfCtx e1 e2 :: k, e')
  | Pair e1 e2 =>
      match to_val e2 with
      | None =>
          let (k, e') := get_ectx e2 in (PairRCtx e1 :: k, e')
      | Some v2 =>
          let (k, e') := get_ectx e1 in (PairLCtx v2 :: k, e')
      end
  | Fst e =>
      let (k, e') := get_ectx e in (FstCtx :: k, e')
  | Snd e =>
      let (k, e') := get_ectx e in (SndCtx :: k, e')
  | InjL e =>
      let (k, e') := get_ectx e in (InjLCtx :: k, e')
  | InjR e =>
      let (k, e') := get_ectx e in (InjRCtx :: k, e')
  | Case e0 e1 e2 =>
      let (k, e') := get_ectx e0 in (CaseCtx e1 e2 :: k, e')
  | AllocN e1 e2 =>
      match to_val e2 with
      | None =>
          let (k, e') := get_ectx e2 in (AllocNRCtx e1 :: k, e')
      | Some v2 =>
          let (k, e') := get_ectx e1 in (AllocNLCtx v2 :: k, e')
      end
  | Load e =>
      let (k, e') := get_ectx e in (LoadCtx :: k, e')
  | Free e =>
      let (k, e') := get_ectx e in (FreeCtx :: k, e')
  | Store e1 e2 =>
      match to_val e2 with
      | None =>
          let (k, e') := get_ectx e2 in (StoreRCtx e1 :: k, e')
      | Some v2 =>
          let (k, e') := get_ectx e1 in (StoreLCtx v2 :: k, e')
      end
  | CmpXchg e0 e1 e2 =>
      match to_val e2 with
      | None =>
          let (k, e') := get_ectx e2 in (CmpXchgRCtx e0 e1 :: k, e')
      | Some v2 =>
          match to_val e1 with
          | None =>
              let (k, e') := get_ectx e1 in (CmpXchgMCtx e0 v2 :: k, e')
          | Some v1 =>
              let (k, e') := get_ectx e0 in (CmpXchgLCtx v1 v2 :: k, e')
          end
      end
  | Xchg e1 e2 =>
      match to_val e2 with
      | None =>
          let (k, e') := get_ectx e2 in (XchgRCtx e1 :: k, e')
      | Some v2 =>
          let (k, e') := get_ectx e1 in (XchgLCtx v2 :: k, e')
      end

  | FAA e1 e2 =>
      match to_val e2 with
      | None =>
          let (k, e') := get_ectx e2 in (FaaRCtx e1 :: k, e')
      | Some v2 =>
          let (k, e') := get_ectx e1 in (FaaLCtx v2 :: k, e')
      end
  | RunThenAbort e =>
      let (k, e') := get_ectx e in (RunThenAbortCtx :: k, e')
  end.

Definition get_redex (e' : expr) : ectx * expr :=
  let (k, e) := get_ectx e' in
  match to_val e with
  | Some v =>
      match reverse k with
      | f :: k' =>
          (reverse k', fill_frame f (Val v))
      | [] =>
          (k, Val v)
      end
  | None =>
      (k, e)
  end.


(* ------------------------------------------------------------------------- *)
(** Properties. *)

(* -------------------------------------------------------------------------- *)
(* [to_val]. *)

Lemma of_to_val e v : to_val e = Some v → e = of_val v.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? [=]. Qed.

(* ------------------------------------------------------------------------- *)
(* [fill_frame]. *)

Instance fill_frame_inj f : Inj (=) (=) (fill_frame f).
Proof. induction f; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_frame_val f e : to_val (fill_frame f e) = None.
Proof. induction f; simplify_option_eq; eauto. Qed.

Lemma fill_frame_no_val_inj f1 f2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_frame f1 e1 = fill_frame f2 e2 → f1 = f2.
Proof. revert f1. induction f2, f1; naive_solver eauto with f_equal. Qed.

(* ------------------------------------------------------------------------- *)
(* [fill]. *)

Instance fill_inj k : Inj (=) (=) (fill k).
Proof. induction k; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_app k k' e : fill (k ++ k') e = fill k (fill k' e).
Proof. by induction k as [|f k]; simpl; [|rewrite IHk]. Qed.

Lemma fill_val k e v : to_val (fill k e) = Some v → k = [] ∧ e = Val v.
Proof.
  destruct k as [|f k].
  - by intro H; rewrite -(of_to_val _ _ H).
  - by destruct f; naive_solver.
Qed.

Lemma fill_inv k e : get_frame (fill k e) = None → k = [].
Proof.
  induction k as [|f k] =>//=.
  destruct f =>//=; by repeat destruct (to_val _).
Qed.

Lemma fill_inv' k e e' : fill k e = e' → get_frame e' = None → k = [] ∧ e = e'.
Proof. intros <- Hget_frame. by rewrite (fill_inv _ _ Hget_frame). Qed.

Lemma fill_val_inv k e v : fill k e = Val v → k = [] ∧ e = Val v.
Proof. intros ?. by apply fill_inv'. Qed.

Lemma fill_not_val k e : to_val e = None → to_val (fill k e) = None.
Proof. induction k as [|f k]; eauto. intros ?; by apply fill_frame_val. Qed.


(* ------------------------------------------------------------------------- *)
(* [get_frame & get_ectx]. *)

Lemma get_ectx_alt (e : expr) :
  get_ectx e = match get_frame e with None => ([], e) | Some (f, e) =>
                 let (k, e') := get_ectx e in (f :: k, e')
               end.
Proof.
  destruct e=>//=;
    try solve [
      (* Solve the cases where we have a L and R context *)
      by repeat destruct (to_val _)
    ].
Qed.

Lemma get_frame_Some e f e' :
  get_frame e = Some (f , e') → e = fill_frame f e'.
Proof.
  destruct e=>//=;
    try solve [
      (* Solve the simple cases like [Fst] *)
      by inversion 1 |
      (* Solve the cases where we have a L and R context *)
      repeat (destruct (to_val _) eqn:H; [apply of_to_val in H as ->|]); by inv 1
    ].
Qed.

Lemma get_ectx_spec e e' k : get_ectx e = (k, e') → e = fill k e'.
Proof.
  revert e' k.
  induction (sub_expr_wf e).
  intros e' k'.
  rename x into e, H0 into IH, H into Hacc.
  rewrite get_ectx_alt.
  destruct (get_frame e) as [(f, e'')|] eqn:Hget_frame; last
  by injection 1 as <- <-.
  destruct (get_ectx e'') as (k'', e''') eqn:He''.
  injection 1 as <- <-. simpl. rewrite -(IH e''); last done.
  - by apply get_frame_Some.
  - by exists f.
Qed.

Lemma get_frame_fill_frame f e :
  to_val e = None →
  get_frame (fill_frame f e) = Some (f, e).
Proof. by intros He; destruct f=>//=; rewrite He. Qed.

Lemma get_ectx_fill_frame e e' f k :
  to_val e = None →
  (k, e') = get_ectx e →
  get_ectx (fill_frame f e) = (f :: k, e').
Proof.
  intros Hval He.
  rewrite get_ectx_alt get_frame_fill_frame; [|done].
  by rewrite -He.
Qed.

Lemma get_ectx_fill e e' k k' :
  to_val e = None →
  (k, e') = get_ectx e →
  get_ectx (fill k' e) = (k' ++ k, e').
Proof.
  revert e e' k; induction k'; intros ??? Hval Hget_ectx.
  - by rewrite -Hget_ectx.
  - simpl. rewrite (get_ectx_fill_frame _ e' _ (k' ++ k)); first done.
    + by apply fill_not_val.
    + symmetry. by apply IHk'.
Qed.

Lemma get_ectx_fill' e1 e1' e2 k k' :
  to_val e1 = None →
  e2 = fill k' e1 →
  (k, e1') = get_ectx e1 →
  get_ectx e2 = (k' ++ k, e1').
Proof. intros ? ->. by apply get_ectx_fill. Qed.


(* ------------------------------------------------------------------------- *)
(* [get_redex]. *)

Lemma get_redex_spec e e' k : get_redex e = (k, e') → e = fill k e'.
Proof.
  unfold get_redex.
  destruct (get_ectx e) as [k1 e1] eqn:He.
  specialize (get_ectx_spec _ _ _ He) as Hfill.
  destruct (to_val e1) as [|] eqn:He1;
  last by injection 1; intros -> ->.
  induction k1 as [|f k1 _] using rev_ind.
  - simpl. injection 1. intros <- <-.
    simplify_eq. simpl. by apply of_to_val.
  - rewrite reverse_app reverse_singleton. simpl.
    rewrite reverse_involutive.
    injection 1. intros <- <-. simplify_eq.
    rewrite fill_app //=. do 2 f_equal.
    by apply of_to_val.
Qed.

Ltac solve_get_redex_fill :=
  rewrite /get_redex;
  match goal with | |- _ = (?k, _) =>
    erewrite (get_ectx_fill' _ _ (fill k _) _ _), reverse_app; simpl; auto
  end;
  simpl;
  try rewrite reverse_involutive;
  try rewrite app_nil_r.

Lemma get_redex_fill_callcc k x e :
  get_redex (fill k (Callcc x e)) = (k, Callcc x e).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_call1cc0 k x e :
  get_redex (fill k (Call1cc0 x e)) = (k, Call1cc0 x e).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_call1ccS k x e :
  get_redex (fill k (Call1ccS x e)) = (k, Call1ccS x e).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_rec k x f e :
  get_redex (fill k (Rec x f e)) = (k, Rec x f e).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_var k x :
  get_redex (fill k (Var x)) = (k, Var x).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_app k v1 v2 :
  get_redex (fill k (App (Val v1) (Val v2))) = (k, App (Val v1) (Val v2)).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_unop k op v :
  get_redex (fill k (UnOp op (Val v))) = (k, UnOp op (Val v)).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_binop k op v1 v2 :
  get_redex (fill k (BinOp op (Val v1) (Val v2))) = (k, BinOp op (Val v1) (Val v2)).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_if k v e1 e2 :
  get_redex (fill k (If (Val v) e1 e2)) = (k, If (Val v) e1 e2).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_pair k v1 v2 :
  get_redex (fill k (Pair (Val v1) (Val v2))) = (k, Pair (Val v1) (Val v2)).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_fst k v :
  get_redex (fill k (Fst (Val v))) = (k, Fst (Val v)).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_snd k v :
  get_redex (fill k (Snd (Val v))) = (k, Snd (Val v)).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_injl k v :
  get_redex (fill k (InjL (Val v))) = (k, InjL (Val v)).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_injr k v :
  get_redex (fill k (InjR (Val v))) = (k, InjR (Val v)).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_case k v e1 e2 :
  get_redex (fill k (Case (Val v) e1 e2)) = (k, Case (Val v) e1 e2).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_allocn k n v :
  get_redex (fill k (AllocN (Val n) (Val v))) = (k, AllocN (Val n) (Val v)).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_free k v :
  get_redex (fill k (Free (Val v))) = (k, Free (Val v)).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_load k v :
  get_redex (fill k (Load (Val v))) = (k, Load (Val v)).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_store k l v :
  get_redex (fill k (Store (Val l) (Val v))) = (k, Store (Val l) (Val v)).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_fork k e :
  get_redex (fill k (Fork e)) = (k, Fork e).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_cmpxchg k v0 v1 v2 :
  get_redex (fill k (CmpXchg (Val v0) (Val v1) (Val v2))) = (k, CmpXchg (Val v0) (Val v1) (Val v2)).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_faa k v1 v2 :
  get_redex (fill k (FAA (Val v1) (Val v2))) = (k, FAA (Val v1) (Val v2)).
Proof. by solve_get_redex_fill. Qed.

Lemma get_redex_fill_xchg k v0 v1 :
  get_redex (fill k (Xchg (Val v0) (Val v1))) = (k, Xchg (Val v0) (Val v1)).
Proof. by solve_get_redex_fill. Qed.

Hint Rewrite
  get_redex_fill_rec get_redex_fill_app
  get_redex_fill_unop get_redex_fill_binop
  get_redex_fill_pair get_redex_fill_fst get_redex_fill_snd
  get_redex_fill_case get_redex_fill_injl get_redex_fill_injr
  get_redex_fill_if
  get_redex_fill_allocn
  get_redex_fill_free get_redex_fill_load get_redex_fill_store
  get_redex_fill_fork
  get_redex_fill_cmpxchg get_redex_fill_faa get_redex_fill_xchg
  : get_redex_fill_db.


(* -------------------------------------------------------------------------- *)
(** Substitution. *)

Fixpoint subst (x : string) (v : val) (e : expr) : expr :=
  match e with
  | Val _ =>
      e
  | Var y =>
      if decide (x = y) then Val v else Var y
  | Callcc k e =>
      Callcc k $ if decide (x ≠ k) then subst x v e else e
  | Call1cc0 k e =>
      Call1cc0 k $ if decide (x ≠ k) then subst x v e else e
  | Call1ccS k e =>
      Call1ccS k $ if decide (x ≠ k) then subst x v e else e
  | Rec f y e =>
      Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
  | App e1 e2 =>
      App (subst x v e1) (subst x v e2)
  | UnOp op e =>
      UnOp op (subst x v e)
  | BinOp op e1 e2 =>
      BinOp op (subst x v e1) (subst x v e2)
  | If e0 e1 e2 =>
      If (subst x v e0) (subst x v e1) (subst x v e2)
  | Pair e1 e2 =>
      Pair (subst x v e1) (subst x v e2)
  | Fst e =>
      Fst (subst x v e)
  | Snd e =>
      Snd (subst x v e)
  | InjL e =>
      InjL (subst x v e)
  | InjR e =>
      InjR (subst x v e)
  | Case e0 e1 e2 =>
      Case (subst x v e0) (subst x v e1) (subst x v e2)
  | AllocN e1 e2 =>
      AllocN (subst x v e1) (subst x v e2)
  | Free e =>
      Free (subst x v e)
  | Load e =>
      Load (subst x v e)
  | Store e1 e2 =>
      Store (subst x v e1) (subst x v e2)
  | CmpXchg e0 e1 e2 =>
      CmpXchg (subst x v e0) (subst x v e1) (subst x v e2)
  | Xchg e1 e2 =>
      Xchg (subst x v e1) (subst x v e2)
  | FAA e1 e2 =>
      FAA (subst x v e1) (subst x v e2)
  | Fork e =>
      Fork (subst x v e)
  | RunThenAbort e =>
      RunThenAbort (subst x v e)
  end.

Definition subst' (b : binder) (v : val) : expr → expr :=
  match b with BNamed x => subst x v | BAnon => id end.

(* -------------------------------------------------------------------------- *)
(** Unboxed values. *)

Definition val_is_unboxed (v : val) : Prop :=
  match v with
  | LitV l => True
  | InjLV (LitV l) => True
  | InjRV (LitV l) => True
  | _ => False
  end.

Global Instance val_is_unboxed_dec v : Decision (val_is_unboxed v).
Proof. destruct v as [ | | | | | [] | [] ]; simpl; exact (decide _). Defined.

(** We just compare the word-sized representation of two values, without looking
into boxed data.  This works out fine if at least one of the to-be-compared
values is unboxed (exploiting the fact that an unboxed and a boxed value can
never be equal because these are disjoint sets). *)
Definition vals_compare_safe (vl v1 : val) : Prop :=
  val_is_unboxed vl ∨ val_is_unboxed v1.
Global Arguments vals_compare_safe !_ !_ /.

(* ========================================================================== *)
(** * Reduction Relation. *)

(* Operations *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (Z.lnot n)
  | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
  | _, _ => None
  end.

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : option base_lit :=
  match op with
  | PlusOp => Some $ LitInt (n1 + n2)
  | MinusOp => Some $ LitInt (n1 - n2)
  | MultOp => Some $ LitInt (n1 * n2)
  | QuotOp => Some $ LitInt (n1 `quot` n2)
  | RemOp => Some $ LitInt (n1 `rem` n2)
  | AndOp => Some $ LitInt (Z.land n1 n2)
  | OrOp => Some $ LitInt (Z.lor n1 n2)
  | XorOp => Some $ LitInt (Z.lxor n1 n2)
  | ShiftLOp => Some $ LitInt (n1 ≪ n2)
  | ShiftROp => Some $ LitInt (n1 ≫ n2)
  | LeOp => Some $ LitBool (bool_decide (n1 ≤ n2))
  | LtOp => Some $ LitBool (bool_decide (n1 < n2))
  | EqOp => Some $ LitBool (bool_decide (n1 = n2))
  | OffsetOp => None (* Pointer arithmetic *)
  end%Z.

Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  | OffsetOp => None (* Pointer arithmetic *)
  end.

Definition bin_op_eval_loc (op : bin_op) (l1 : loc) (v2 : base_lit) : option base_lit :=
  match op, v2 with
  | OffsetOp, LitInt off => Some $ LitLoc (l1 +ₗ off)
  | LeOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 ≤ₗ l2))
  | LtOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 <ₗ l2))
  | _, _ => None
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then
    (* Crucially, this compares the same way as [CmpXchg]! *)
    if decide (vals_compare_safe v1 v2) then
      Some $ LitV $ LitBool $ bool_decide (v1 = v2)
    else
      None
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => LitV <$> bin_op_eval_int op n1 n2
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | LitV (LitLoc l1), LitV v2 => LitV <$> bin_op_eval_loc op l1 v2
    | _, _ => None
    end.

Definition state_upd_heap (f : gmap loc (option val) → gmap loc (option val)) (σ : state) : state :=
  {| heap := f σ.(heap); |}.
Global Arguments state_upd_heap _ !_ /.

Fixpoint heap_array (l : loc) (vs : list val) : gmap loc (option val) :=
  match vs with
  | [] => ∅
  | v :: vs' => {[l := Some v]} ∪ heap_array (l +ₗ 1) vs'
  end.

Lemma heap_array_singleton l v : heap_array l [v] = {[l := Some v]}.
Proof. by rewrite /heap_array right_id. Qed.

Lemma heap_array_lookup l vs ow k :
  heap_array l vs !! k = Some ow ↔
  ∃ j w, (0 ≤ j)%Z ∧ k = l +ₗ j ∧ ow = Some w ∧ vs !! (Z.to_nat j) = Some w.
Proof.
  revert k l; induction vs as [|v' vs IH]=> l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
  - intros [[-> ?] | (Hl & j & w & ? & -> & -> & ?)].
    { eexists 0, _. rewrite Loc.add_0. naive_solver lia. }
    eexists (1 + j)%Z, _. rewrite Loc.add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & w & ? & -> & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite Loc.add_0; eauto. }
    right. split.
    { rewrite -{1}(Loc.add_0 l). intros ?%(inj (Loc.add _)); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    eexists (j - 1)%Z, _. rewrite Loc.add_assoc Z.add_sub_assoc Z.add_simpl_l.
    auto with lia.
Qed.

Lemma heap_array_map_disjoint (h : gmap loc (option val)) (l : loc) (vs : list val) :
  (∀ i, (0 ≤ i)%Z → (i < length vs)%Z → h !! (l +ₗ i) = None) →
  (heap_array l vs) ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j&w&?&->&?&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
  move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
Qed.

(* [h] is added on the right here to make [state_init_heap_singleton] true. *)
Definition state_init_heap (l : loc) (n : Z) (v : val) (σ : state) : state :=
  state_upd_heap (λ h, heap_array l (replicate (Z.to_nat n) v) ∪ h) σ.

Lemma state_init_heap_singleton l v σ :
  state_init_heap l 1 v σ = state_upd_heap <[l:=Some v]> σ.
Proof.
  destruct σ as [h]. rewrite /state_init_heap /=. f_equiv.
  rewrite right_id insert_union_singleton_l. done.
Qed.

(* Reduction steps independent on the evaluation context. *)
Inductive base_step : ectx → expr → state → ectx → expr → state → list expr → Prop :=
  (* Lambda. *)
  | RecStep f x e σ k :
     base_step k (Rec f x e) σ k (Val $ RecV f x e) σ []

  (* Beta reduction. *)
  | BetaStep f x e1 v2 e' σ k :
     e' = subst' x v2 (subst' f (RecV f x e1) e1) →
     base_step k (App (Val $ RecV f x e1) (Val v2)) σ k e' σ []

  (* Callcc. *)
  | CallccStep k e σ k' :
     base_step k' (Callcc k e) σ k' (subst k (KontV k') e) σ []

  (* Call1cc0. *)
  | Call1cc0Step r k e σ k' :
     σ.(heap) !! r = None →
     base_step k' (Call1cc0 k e) σ
               [RunThenAbortCtx] (subst k (ContV r k') e)
               (state_upd_heap <[r:=Some (LitV $ LitUnit)]> σ) []

  (* Call1ccS. *)
  | Call1ccSStep r k e σ k' :
     σ.(heap) !! r = None →
     base_step k' (Call1ccS k e) σ
               k' (subst k (ContV r k') e)
               (state_upd_heap <[r:=Some (LitV $ LitUnit)]> σ) []

  (* Invoking a one-shot continuation. *)
  | ContStep k r x σ k' :
     σ.(heap) !! r = Some (Some (LitV $ LitUnit)) →
     base_step k' (App (Val (ContV r k)) (Val x)) σ
               k  (Val x) (state_upd_heap <[r:=None]> σ) []

  (* Invoking a multi-shot continuation. *)
  | KontStep k x σ k' :
     base_step k' (App (Val (KontV k)) (Val x)) σ k (Val x) σ []

  (* Operations *)
  | UnOpStep op v v' σ k :
     un_op_eval op v = Some v' →
     base_step k (UnOp op (Val v)) σ k (Val v') σ []
  | BinOpStep op v1 v2 v' σ k :
     bin_op_eval op v1 v2 = Some v' →
     base_step k (BinOp op (Val v1) (Val v2)) σ k (Val v') σ []
  | IfTrueStep e1 e2 σ k :
     base_step k (If (Val $ LitV $ LitBool true) e1 e2) σ k e1 σ []
  | IfFalseStep e1 e2 σ k :
     base_step k (If (Val $ LitV $ LitBool false) e1 e2) σ k e2 σ []

  (* Products*)
  | PairStep v1 v2 σ k :
     base_step k (Pair (Val v1) (Val v2)) σ k (Val $ PairV v1 v2) σ []
  | FstStep v1 v2 σ k :
     base_step k (Fst (Val $ PairV v1 v2)) σ k (Val v1) σ []
  | SndStep v1 v2 σ k :
     base_step k (Snd (Val $ PairV v1 v2)) σ k (Val v2) σ []

  (* Sums *)
  | InjLStep v σ k :
     base_step k (InjL $ Val v) σ k (Val $ InjLV v) σ []
  | InjRStep v σ k :
     base_step k (InjR $ Val v) σ k (Val $ InjRV v) σ []
  | CaseLStep v e1 e2 σ k :
     base_step k (Case (Val $ InjLV v) e1 e2) σ k (App e1 (Val v)) σ []
  | CaseRStep v e1 e2 σ k :
     base_step k (Case (Val $ InjRV v) e1 e2) σ k (App e2 (Val v)) σ []

  (* Heap *)
  | AllocNStep n v σ l k :
     (0 < n)%Z →
     (∀ i, (0 ≤ i)%Z → (i < n)%Z → σ.(heap) !! (l +ₗ i) = None) →
     base_step k (AllocN (Val $ LitV $ LitInt n) (Val v)) σ
               k (Val $ LitV $ LitLoc l) (state_init_heap l n v σ) []
  | FreeStep l v σ k :
     σ.(heap) !! l = Some $ Some v →
     base_step k (Free (Val $ LitV $ LitLoc l)) σ
               k (Val $ LitV LitUnit) (state_upd_heap <[l:=None]> σ) []
  | LoadStep l v σ k :
     σ.(heap) !! l = Some $ Some v →
     base_step k (Load (Val $ LitV $ LitLoc l)) σ k (of_val v) σ []
  | StoreStep l v w σ k :
     σ.(heap) !! l = Some $ Some v →
     base_step k (Store (Val $ LitV $ LitLoc l) (Val w)) σ
               k (Val $ LitV LitUnit) (state_upd_heap <[l:=Some w]> σ) []
  (* Concurrency *)
  | XchgStep l v1 v2 σ k :
     σ.(heap) !! l = Some $ Some v1 →
     base_step k (Xchg (Val $ LitV $ LitLoc l) (Val v2)) σ
               k (Val v1) (state_upd_heap <[l:=Some v2]> σ) []
  | CmpXchgStep l v1 v2 vl σ b k :
     σ.(heap) !! l = Some $ Some vl →
     (* Crucially, this compares the same way as [EqOp]! *)
     vals_compare_safe vl v1 →
     b = bool_decide (vl = v1) →
     base_step k (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) σ
               k (Val $ PairV vl (LitV $ LitBool b)) (if b then state_upd_heap <[l:=Some v2]> σ else σ) []
  | FaaStep l i1 i2 σ k :
     σ.(heap) !! l = Some $ Some (LitV (LitInt i1)) →
     base_step k (FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2)) σ
               k (Val $ LitV $ LitInt i1) (state_upd_heap <[l:=Some $ LitV (LitInt (i1 + i2))]>σ) []
  | ForkStep e σ k :
     base_step k (Fork e) σ k (Val $ LitV $ LitUnit) σ [e].

Lemma base_step_alloc_fresh k v n σ :
  let l := Loc.fresh (dom σ.(heap)) in
  (0 < n)%Z →
  base_step k (AllocN ((Val $ LitV $ LitInt $ n)) (Val v)) σ
            k (Val $ LitV $ LitLoc l) (state_init_heap l n v σ) [].
Proof.
  intros. apply AllocNStep; first done.
  intros. apply not_elem_of_dom.
  by apply Loc.fresh_fresh.
Qed.

Lemma base_step_call1ccS k' k e σ :
  let r := Loc.fresh (dom σ.(heap)) in
  base_step k' (Call1ccS k e) σ k' (subst k (ContV r k') e)
            (state_upd_heap <[r:=Some (LitV $ LitUnit)]> σ) [].
Proof.
  intros. apply Call1ccSStep; try done.
  intros. apply not_elem_of_dom.
  specialize (Loc.fresh_fresh (dom σ.(heap)) 0) as Hnot_in.
  rewrite Loc.add_0 in Hnot_in. by apply Hnot_in.
Qed.

Lemma base_step_call1cc0 k' k e σ :
  let r := Loc.fresh (dom σ.(heap)) in
  base_step k' (Call1cc0 k e) σ
            [RunThenAbortCtx] (subst k (ContV r k') e)
            (state_upd_heap <[r:=Some (LitV $ LitUnit)]> σ) [].
Proof.
  intros. apply Call1cc0Step; try done.
  intros. apply not_elem_of_dom.
  specialize (Loc.fresh_fresh (dom σ.(heap)) 0) as Hnot_in.
  rewrite Loc.add_0 in Hnot_in. by apply Hnot_in.
Qed.

(* Reduction relation. *)
(* [prim_step] is the closure of the head-reduction
   relation [base_step] over evaluation contexts. *)
Inductive prim_step (e1 : expr) (σ1 : state) (e2 : expr) (σ2 : state) (efs : list expr) : Prop :=
  | Ectx_prim_step (k1 k2 : ectx) (e1' e2' : expr) :
     e1 = fill k1 e1' →
     e2 = fill k2 e2' →
     base_step k1 e1' σ1 k2 e2' σ2 efs →
     prim_step e1 σ1 e2 σ2 efs.


(* -------------------------------------------------------------------------- *)
(** Properties of [base_step] and [prim_step]. *)

Lemma Ectx_prim_step_2 k1 k2 e1 e2 σ1 σ2 efs :
  base_step k1 e1 σ1 k2 e2 σ2 efs →
  prim_step (fill k1 e1) σ1 (fill k2 e2) σ2 efs.
Proof. intros ?. by apply (Ectx_prim_step _ _ _ _ _ k1 k2 e1 e2). Qed.

(* If [e1] makes a head step to a value under some state [σ1],
   then any head step from [e1] under any other state [σ1']
   must necessarily be to a value. *)
Lemma base_step_to_val k1 e1 σ1 k2 e2 σ2 k1' σ1' k2' e2' σ2' efs :
  base_step k1  e1 σ1  k2  e2  σ2 efs →
  base_step k1' e1 σ1' k2' e2' σ2' efs →
  is_Some (to_val e2) →
  is_Some (to_val e2').
Proof.
  destruct 1; inversion 1; try naive_solver.
  - destruct e=>//=; by case (decide (k = x)).
  - destruct e=>//=; by case (decide (k = x)).
  - destruct e=>//=; by case (decide (k = x)).
Qed.

(* If [e1] can perform one step, then [e1] is not a value. *)
Lemma val_base_stuck k1 e1 σ1 k2 e2 σ2 efs :
  base_step k1 e1 σ1 k2 e2 σ2 efs →
  to_val e1 = None.
Proof. by destruct 1; eauto. Qed.
