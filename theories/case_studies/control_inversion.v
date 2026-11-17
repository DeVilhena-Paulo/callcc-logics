(* control_inversion.v *)

From iris.proofmode Require Import base proofmode classes.
From callcc_logics Require Import logic state proofmode.


(* ------------------------------------------------------------------------- *)
(* Lazy Sequences. *)

Section lazy_sequences.
  Context `{!stateGS Σ}.

  (* ----------------------------------------------------------------------- *)
  (** Specification of Heads. *)

  (* The predicate [isHead] is defined as [isHead_pre isSeq], where [isSeq] is
     the fixpoint of [isSeq_pre]. *)
  (* A head is either a [Cons] pair or a [Nil] marker. *)
  Definition isHead_pre
    (isSeq :  val -d> list val -d> list val -d> iPropO Σ)
           :  val -d> list val -d> list val -d> iPropO Σ  :=
    λ h us vs,
      match vs with
      | [] =>
          ⌜ h = InjRV #() ⌝
      | v :: vs => ∃ k,
          ⌜ h = InjLV (v, k)%V ⌝ ∗ ▷ isSeq k (us ++ [v]) vs
      end%I.

  (* ----------------------------------------------------------------------- *)
  (** Specification of Sequences. *)

  (* A sequence is a thunk [k] that, when applied to [#()], produces a head
     [h] s.t. [isHead h us vs]. *)
  Definition isSeq_pre
    (isSeq :  val -d> list val -d> list val -d> iPropO Σ)
           :  val -d> list val -d> list val -d> iPropO Σ  :=
    λ k us vs, wp/cc k #() @ WithFrame {{h, isHead_pre isSeq h us vs}}%I.

  (* [isSeq_pre] is contractive, therefore it admits a fixpoint. *)
  Local Instance isSeq_pre_contractive : Contractive isSeq_pre.
  Proof.
    rw /isSeq_pre /isHead_pre => n isSeq isSeq' HisSeq ???.
    f_equiv=>?. simpl. repeat (f_contractive || f_equiv); try by apply HisSeq.
  Qed.
  Definition isSeq_def : val -d> list val -d> list val -d> iPropO Σ :=
    fixpoint (isSeq_pre).
  Definition isSeq_aux : seal isSeq_def. Proof. by eexists. Qed.
  Definition isSeq := isSeq_aux.(unseal).
  Definition isHead := isHead_pre isSeq.
  Definition isSeq_eq : isSeq = isSeq_def := isSeq_aux.(seal_eq).
  Global Lemma isSeq_unfold k us vs : isSeq k us vs ⊣⊢ isSeq_pre isSeq k us vs.
  Proof. by rw isSeq_eq/isSeq_def;apply(fixpoint_unfold isSeq_pre). Qed.
  Global Lemma isHead_unfold :
    isHead = isHead_pre isSeq.
  Proof. done. Qed.

End lazy_sequences.


(* ------------------------------------------------------------------------- *)
(* Iteration Methods. *)

Section iteration_methods.
  Context `{!stateGS Σ}.

  Definition isIter (iter : val) (xs : list val) : iProp Σ :=
    (∀ (I : list val → list val → iProp Σ) (f : val),
    (□ ∀ ys z zs, I ys (z :: zs) -∗ wp/cc f z @ WithFrame {{_, I (ys ++ [z]) zs}}) -∗
    I [] xs -∗ wp/cc iter f @ WithFrame {{ _, I xs [] }}).

End iteration_methods.


(* ------------------------------------------------------------------------- *)
(* Implementation. *)

Section implementation.
  Context `{!stateGS Σ}.

  Definition sCons (x k : expr) : expr := InjL (x, k)%E.
  Definition sNil               : val  := InjRV #().

  Definition yield (r : expr) : expr := (λ: "x", (call/1cc0: "kp",
    throw: (Load r) (sCons "x" (λ: <>, (call/1cc0: "kc",
      r <- "kc";; throw: "kp" #()))))
  )%E.

  Definition invert1cc : val := (λ: "iter", λ: <>, (call/1cc0: "kc",
    let: "r" := ref "kc" in "iter" (yield "r");; throw: (Load "r") sNil)
  )%V.  

End implementation.


(* ------------------------------------------------------------------------- *)
(* Specification & Verification. *)

Section specification_and_verification.
  Context `{!stateGS Σ}.

  Definition invert1cc_spec : iProp Σ :=
    (∀ (xs : list val) (iter : val),
    isIter iter xs -∗ wp/cc invert1cc iter @ WithFrame {{k, (isSeq k [] xs)}})%I.

  Lemma invert1cc_correct : ⊢ invert1cc_spec.
  Proof.
    iIntros (xs iter) "Hiter". rw /invert1cc. wpcc_pures. iModIntro.
    rw !isSeq_unfold isSeq_eq /isSeq_pre. wpcc_pures.
    iApply wpcc_call1cc0.
    iIntros "!> %k Hk". simpl.
    iApply wpcc_alloc. iIntros "!> %r Hr _". wpcc_pures.
    set I : list val → list val → iProp Σ := (λ us vs,
      ∃ (k : val), r ↦ k ∗ isCont k (λ h, isHead h us vs))%I.
    iApply (wpcc_bind _ [_]).
    iApply (wpcc_mono with "[Hiter Hk Hr]").
    { iApply ("Hiter" $! I with "[]").
      { clear k. iIntros "!>" (ys z zs) "[%k [Hr Hk]]".
        wpcc_pures. iApply wpcc_call1cc0. iIntros "!> %k' Hk'".
        wpcc_pures. iApply (wpcc_load with "Hr"). iIntros "!> Hr".
        iApply (wpcc_cont' with "Hk").
        simpl. iExists _. iSplit; [done|].
        iNext.
        rw !isSeq_unfold isSeq_eq /isSeq_pre. wpcc_pures.
        iApply wpcc_call1cc0. iIntros "!> %k'' Hk''". simpl.
        iApply (wpcc_store with "Hr"). iIntros "!> Hr".
        wpcc_pures. iApply (wpcc_cont' with "Hk'").
        iExists k''. rw isHead_unfold isSeq_eq. by iFrame.
      }
      { iExists k. rw isHead_unfold isSeq_eq. by iFrame. }
    }
    simpl.
    iIntros "% [%k' [Hr Hk']] !>". wpcc_pures.
    iApply (wpcc_load with "Hr"). iIntros "!> Hr".
    by iApply (wpcc_cont with "Hk'").
  Qed.

End specification_and_verification.
