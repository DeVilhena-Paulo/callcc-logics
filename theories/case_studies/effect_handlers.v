(* effect_handlers.v *)

From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import frac cmra list agree.
From callcc_logics Require Import logic state proofmode.
From callcc_logics.case_studies Require Import control_inversion stack_lib.


Section implementation.
  Context `{StackLib}.

  Variables (hs : val).

  Definition abort : val := (λ: "res",
    let: "k" := stack_pop hs in "k" "res")%V.

  Definition handle : val := (rec: "handle" "effc" "retc" "comp" :=
    match: call/1cc0: "k",
      stack_push hs "k";;
      let: "y" := "comp" #() in
      abort (InjL "y")
    with
      InjL "y" => "retc" "y"
    | InjR "args" =>
        let: "x" := Fst "args" in
        let: "k" := Snd "args" in
        "effc" "x" (λ: "y", "handle" "effc" "retc" (λ: <>, "k" "y"))
    end
  )%V.

  Definition perform : val := (λ: "x", call/1cc0: "k",
      abort (InjR ("x", "k"))
  )%V.

End implementation.


Section verification.
  Context `{StackLib}.

  Variables (hs : val).

  Notation canAbort_type := (
    list ((val -d> (val -d> iPropO Σ) -d> iPropO Σ) * (val -d> iPropO Σ)) -d>
    iPropO Σ
  ).

  Notation mainPost_type := (
    (val -d> (val -d> iPropO Σ) -d> iPropO Σ) -d>
    (val -d> iPropO Σ) -d>
    list ((val -d> (val -d> iPropO Σ) -d> iPropO Σ) * (val -d> iPropO Σ)) -d> val -d> iPropO Σ
  ).

  Notation isHStack_type := (
    list val -d>
    list ((val -d> (val -d> iPropO Σ) -d> iPropO Σ) * (val -d> iPropO Σ)) -d> iPropO Σ
  ).

  Definition isHStack_pre (mainPost : mainPost_type) : isHStack_type :=
    fix isHStack ks ΨΦs :=
      match ks, ΨΦs with
      | [], [] =>
          True
      | k :: ks, (Ψ, Φ) :: ΨΦs =>
          isHStack ks ΨΦs ∗
          isCont k (λ res,
            mainPost Ψ Φ ΨΦs res ∗
            (∃ ks, is_stack hs ks ∗ isHStack ks ΨΦs)
          )
      | _, _ =>
          False
      end%I.

  Definition canAbort_pre mainPost : canAbort_type := (λ ΨΦs,
    ∃ ks, is_stack hs ks ∗ isHStack_pre mainPost ks ΨΦs
  )%I.

  Definition mainPost_pre mainPost : mainPost_type := (λ Ψ Φ ΨΦs res,
    (((∃ y, ⌜ res = InjLV y ⌝ ∗ Φ y)
        ∨
      (∃ x k Φ',
       ⌜ res = InjRV (x, k) ⌝ ∗
       Ψ x Φ' ∗
       ▷ isCont k (λ y, Φ' y ∗
         canAbort_pre mainPost ((Ψ, Φ) :: ΨΦs)
       )
      )
     )
    )
  )%I.

  Local Instance isHStack_pre_ne : NonExpansive isHStack_pre.
  Proof.
    rewrite /isHStack_pre /isCont /isCont_gen => n isHStack isHStack' Hne ks ΨΦs.
    revert ΨΦs ks.
    induction ΨΦs as [|(Ψ, Φ) ΨΦs].
    - intros ?. by f_equiv.
    - intros ?. repeat f_equiv. apply IHΨΦs.
      + by apply Hne.
      + by apply IHΨΦs.
  Qed.

  Local Instance mainPost_pre_contractive : Contractive mainPost_pre.
  Proof.
    rewrite /mainPost_pre /isCont /isCont_gen /canAbort_pre =>
      n mainPost mainPost' Hne Ψ Φ ΨΦs res.
    do 9 f_equiv. f_contractive.
    do 9 f_equiv. apply isHStack_pre_ne. apply Hne.
  Qed.

  Definition mainPost_def := fixpoint mainPost_pre.
  Definition mainPost_aux : seal mainPost_def. Proof. by eexists. Qed.
  Definition mainPost := mainPost_aux.(unseal).
  Definition mainPost_eq : mainPost = mainPost_def
    := mainPost_aux.(seal_eq).

  Global Lemma mainPost_unfold Ψ Φ ΨΦs res :
    mainPost Ψ Φ ΨΦs res ⊣⊢ mainPost_pre mainPost Ψ Φ ΨΦs res.
  Proof.
    rewrite mainPost_eq /mainPost_def.
    by apply (fixpoint_unfold mainPost_pre).
  Qed.

  Definition canAbort := canAbort_pre mainPost.

  Definition isHStack := isHStack_pre mainPost.

  Definition wphs e ΨΦs Φ' : iProp Σ :=
    canAbort ΨΦs -∗
    wp/cc e @ WithFrame {{ res,
      Φ' res ∗ canAbort ΨΦs
    }}.

  Lemma isHStack_cons ks Ψ Φ ΨΦs :
    isHStack ks ((Ψ, Φ) :: ΨΦs) -∗ ∃ k' ks',
    ⌜ ks = k' :: ks' ⌝ ∗
    isHStack (k' :: ks') ((Ψ, Φ) :: ΨΦs).
  Proof.
    iIntros "Hks".
    destruct ks as [|k' ks']; [done|].
    iExists k', ks'. iSplit; [done|]. by iFrame.
  Qed.

  Lemma abort_spec Ψ Φ ΨΦs res Φ' :
    mainPost Ψ Φ ΨΦs res -∗
    canAbort ((Ψ, Φ) :: ΨΦs) -∗
    wp/cc (abort hs res) @ WithFrame {{ Φ' }}.
  Proof.
    iIntros "HmainPost [%ks [Hhs Hstack]]".
    iDestruct (isHStack_cons with "Hstack")
      as "(% & % & -> & [Hks' Hk'])".
    rewrite /abort.
    wpcc_pures.
    iApply (wpcc_bind _ [AppRCtx _]).
    iApply (stack_pop_spec with "Hhs").
    iIntros "!> Hmc". simpl. wpcc_pures.
    iApply (wpcc_cont with "Hk'"). by iFrame.
  Qed.

  Lemma wphs_perform (Ψ : val → (val → iProp Σ) → iProp Σ) Φ ΨΦs Φ' x :
    Ψ x Φ' -∗
    wphs (perform hs x) ((Ψ, Φ) :: ΨΦs) Φ'.
  Proof.
    rewrite /wphs /perform.
    iIntros "Hx Hraise". wpcc_pures.
    iApply wpcc_call1cc0.
    iIntros "!> %k' Hk'". simpl. wpcc_pures.
    iApply (abort_spec with "[Hx Hk'] Hraise").
    rewrite mainPost_unfold. iRight.
    iExists x, k', Φ'. iFrame. done.
  Qed.

  Lemma wphs_mono (e : expr) ΨΦs Φ1 Φ2 :
    wphs e ΨΦs Φ1 -∗
    (∀ y, Φ1 y ={⊤}=∗ Φ2 y) -∗
    wphs e ΨΦs Φ2.
  Proof.
    iIntros "He HΦ Hraise".
    iApply (wpcc_mono with "[He Hraise]").
    { by iApply ("He" with "Hraise"). }
    simpl. iIntros "%y [Hy Hraise]".
    iMod ("HΦ" with "Hy"). by iFrame.
  Qed.

  Lemma wphs_bind k (e : expr) ΨΦs Φ' :
    wphs e ΨΦs (λ y, wphs (fill k y) ΨΦs Φ') -∗
    wphs (fill k e) ΨΦs Φ'.
  Proof.
    iIntros "He Hraise".
    iSpecialize ("He" with "Hraise").
    iApply (wpcc_bind _ k).
    iApply (wpcc_mono with "He"). simpl.
    iIntros "% [Hfill Hraise] !>".
    by iApply "Hfill".
  Qed.

  Notation deep_handler_type := (
    (val -d> (val -d> iPropO Σ) -d> iPropO Σ) -d>
    (val -d> iPropO Σ) -d>
    val -d> val -d>
    list ((val -d> (val -d> iPropO Σ) -d> iPropO Σ) * (val -d> iPropO Σ)) -d>
    (val -d> iPropO Σ) -d>
    iPropO Σ
  ).

  Definition deep_handler_pre : deep_handler_type → deep_handler_type :=
    (λ deep_handler Ψ Φ effc retc ΨΦs Q,

      (* Correctness of the return branch. *)
      (∀ (y : val), Φ y -∗ wphs (retc y) ΨΦs Q) ∧

      (* Correctness of the effect branch. *)
      (∀ (x k : val) Q',
       Ψ x Q' -∗
       (∀ (y : val) Q'', Q' y -∗
        ▷ deep_handler Ψ Φ effc retc ΨΦs Q'' -∗
        wphs (k y) ΨΦs Q''
       ) -∗
       wphs (effc x k) ΨΦs Q
      )
    )%I.

  Local Instance deep_handler_pre_contractive : Contractive deep_handler_pre.
  Proof.
    rewrite /deep_handler_pre /wphs => n deep deep' Hne Ψ Φ effc retc ΨΦs Q.
    repeat (f_contractive || f_equiv). apply Hne.
  Qed.
  Definition deep_handler_def := fixpoint deep_handler_pre.
  Definition deep_handler_aux : seal deep_handler_def. Proof. by eexists. Qed.
  Definition deep_handler := deep_handler_aux.(unseal).
  Definition deep_handler_eq : deep_handler = deep_handler_def
    := deep_handler_aux.(seal_eq).
  Arguments deep_handler _%_I _%_I _%_V _%_V _%_I.

  Global Lemma deep_handler_unfold Ψ Φ effc retc ΨΦs Q :
    deep_handler Ψ Φ effc retc ΨΦs Q ⊣⊢
      deep_handler_pre deep_handler Ψ Φ effc retc ΨΦs Q.
  Proof.
    rewrite deep_handler_eq /deep_handler_def.
    by apply (fixpoint_unfold deep_handler_pre).
  Qed.

  Lemma wphs_handle (effc retc comp : val) Ψ Φ ΨΦs Q :
    wphs (comp #()) ((Ψ, Φ) :: ΨΦs) Φ -∗
    deep_handler Ψ Φ effc retc ΨΦs Q -∗
    wphs (handle hs effc retc comp) ΨΦs Q.
  Proof.
    iLöb as "IH" forall (comp Q).
    iIntros "Hcomp Hhandler Hraise". rewrite /handle.
    wpcc_pures.
    iApply (wpcc_bind _ [CaseCtx _ _]). simpl.
    iApply (wpcc_mono _ _ _ (λ res,
      (*∃ k' ks',*)
      mainPost Ψ Φ ΨΦs res ∗
      canAbort ΨΦs)%I
      with "[Hcomp Hraise]").
    { iApply wpcc_call1cc0. iIntros "!> %k' Hk'". simpl.
      iDestruct "Hraise" as "[% [Hmc Hkks]]".
      iApply (wpcc_bind _ [AppRCtx _]).
      iApply (stack_push_spec with "Hmc").
      iIntros "!> Hmc". simpl.
      iSpecialize ("Hcomp" with "[Hmc Hkks Hk']").
      { iFrame. iFrame. }
      wpcc_pures.
      iApply (wpcc_bind _ [AppRCtx _]). simpl.
      iApply (wpcc_mono with "Hcomp"). simpl.
      iIntros "%y [Hy Hraise] !>". wpcc_pures.
      iApply (abort_spec with "[Hy] Hraise").
      rewrite mainPost_unfold. iLeft. by iFrame.
    }
    simpl.
    iIntros "%res [Hres Hraise] !>".
    rewrite mainPost_unfold.
    iDestruct "Hres" as
      "[(%y & -> & Hy) | (%x & %k' & %Q' & -> & Hx & Hk')]".
    - wpcc_pures. rewrite deep_handler_unfold.
      iDestruct "Hhandler" as "[Hretc _]".
      by iApply ("Hretc" with "Hy Hraise").
    - wpcc_pures. rewrite deep_handler_unfold.
      iDestruct "Hhandler" as "[_ Heffc]".
      iApply ("Heffc" with "Hx [Hk'] Hraise").
      iIntros "%y %Q'' Hy Hhandler Hraise".
      do 2 wpcc_pure.
      iApply ("IH" with "[Hk' Hy] Hhandler Hraise").
      iIntros "Hraise". wpcc_pures.
      iApply (wpcc_cont with "Hk'"). by iFrame.
  Qed.

End verification.
