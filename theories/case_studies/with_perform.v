(* with_perform.v *)

From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import frac cmra list agree.
From callcc_logics Require Import logic state proofmode.
From callcc_logics.case_studies Require Import control_inversion.


(* ------------------------------------------------------------------------- *)
(* Implementation. *)

Section implementation.
  Context `{!stateGS Σ}.

  Definition option_get : val := λ: "opt",
    match: "opt" with
      InjL <> => assert: #false
    | InjR "x" => "x"
    end%E.

  Definition run_body (r effc retc comp : expr) : expr :=
    match: call/1cc0: "k",
      r <- (InjR "k");;
      let: "y" := comp #() in
      throw: (option_get (Load r)) (InjL "y")
    with
      InjL "y" =>
        retc "y"
    | InjR "args" =>
        let: "x" := Fst "args" in
        let: "k" := Snd "args" in
        effc "x" (λ: "y", "run" (λ: <>, throw: "k" "y"))
    end.

  Definition run (r effc retc : expr) : expr :=
    rec: "run" "comp" := run_body r effc retc "comp".

  Definition handle (r effc retc e : expr) : expr :=
    (RecV "run" "comp" (run_body r effc retc "comp")) e.

  Definition perform (r x : expr) : expr :=
    call/1cc0: "k", throw: (option_get (Load r)) (InjR (x, "k")).

  Definition with_perform : val := λ: "effc" "retc" "main",
    let: "r" := ref (InjL #()) in
    run "r" "effc" "retc" (λ: <>, "main" (λ: "x", perform "r" "x")).

  (* Combinators. *)

  Definition R (r : loc) (e : expr) : expr :=
    RunThenAbort (let: "y" := e in throw: (option_get (Load #r)) (InjL "y")).

  Definition P (r : loc) : val :=
    λ: "x", perform #r "x".

  Definition C (r : loc) (effc retc : val) (l' : loc) (K' : ectx) : val :=
    λ: "y", handle #r effc retc (λ: <>, ContV l' K' "y").

  Definition M (r : loc) (effc retc : val) : frame :=
    CaseCtx
      (λ: "y", retc "y")
      (λ: "args",
        let: "x" := Fst "args" in
        let: "k" := Snd "args" in
         effc "x" (λ: "y",
            handle #r effc retc (λ: <>, throw: "k" "y"))).

  Definition H (r : loc) (effc retc : val) (l : loc) (K : ectx) : val :=
    InjRV (ContV l (K ++ [M r effc retc])).

End implementation.


(* ------------------------------------------------------------------------- *)
(* Derived reduction rules. *)

Section reduction_rules.

  (* One step of reduction without forking. *)
  Definition cstep (c1 c2 : expr * state) : Prop :=
    prim_step c1.1 c1.2 c2.1 c2.2 [].

  (* Reflexive-transitive closure of [cstep]. *)
  Notation "c1 -->* c2" := (rtc cstep c1 c2) (at level 70).


  (* ----------------------------------------------------------------------- *)
  (* Automation. *)

  Lemma cstep_fill K e h k r K2 e2 σ2 :
    get_redex e = (k, r) →
    base_step (K ++ k) r {| heap := h |} K2 e2 σ2 [] →
    cstep (fill K e, {| heap := h |}) (fill K2 e2, σ2).
  Proof.
    intros Hr Hstep. rewrite (get_redex_spec _ _ _ Hr) -fill_app.
    by apply Ectx_prim_step_2.
  Qed.

  Lemma csteps_fill_nil e σ c : (fill [] e, σ) -->* c → (e, σ) -->* c.
  Proof. done. Qed.

  Lemma csteps_fill_app K k e σ c :
    (fill K (fill k e), σ) -->* c → (fill (K ++ k) e, σ) -->* c.
  Proof. by rewrite fill_app. Qed.

  Lemma csteps_refl e e' h h' : e = e' → h = h' → (e, {| heap := h |}) -->* (e', {| heap := h' |}).
  Proof. by intros -> ->. Qed.

  #[local] Arguments option_get : simpl never.

  (* Perform one step of [base_step] at the redex of the current expression. *)
  Local Ltac cstep_with tac :=
    rewrite /handle /Throw;
    lazymatch goal with
    | |- (fill ?K ?e, {| heap := ?h |}) -->* _ =>
        let p := eval cbv [get_redex] in (get_redex e) in
        let p := eval simpl in p in
        lazymatch p with
        | (?k, ?r) =>
            eapply rtc_l; [eapply (cstep_fill K e h k r); [reflexivity|tac r]|]
        end
    | |- (?e, _) -->* _ =>
        apply csteps_fill_nil; cstep_with tac
    end.

  (* Normalize the configuration reached after a step. *)
  Local Ltac cnorm :=
    try lazymatch goal with
    | |- (fill (_ ++ _) _, _) -->* _ => apply csteps_fill_app
    end;
    rewrite ?state_init_heap_singleton ?app_nil_r;
    lazymatch goal with
    | |- (?e, ?σ) -->* ?c =>
        let e' := eval simpl in e in
        let σ' := eval cbn [state_upd_heap heap] in σ in
        change ((e', σ') -->* c)
    end.

  Local Ltac solve_lookup := simpl; by simplify_map_eq.

  (* A step that does not allocate. *)
  Local Ltac base_step_tac r :=
    lazymatch r with
    | Call1cc0 _ _ => fail
    | AllocN _ _ => fail
    | _ => econstructor; first [reflexivity | solve_lookup]
    end.

  Local Ltac csteps := repeat (cstep_with base_step_tac; cnorm).

  Local Ltac cstep_call1cc0 l :=
    cstep_with ltac:(fun _ => apply (Call1cc0Step l); solve_lookup); cnorm.

  Local Ltac cstep_alloc l :=
    cstep_with ltac:(fun _ =>
      apply (AllocNStep _ _ _ l); [lia|];
      intros i ??; assert (i = 0%Z) as -> by lia;
      rewrite Loc.add_0; solve_lookup); cnorm.

  (* ----------------------------------------------------------------------- *)
  (* Rules. *)

  (* K[handle r effc retc comp] / σ[r := _] -->*
       R r (comp ()) / σ[r := H r effc retc l K, l := ()] *)
  Lemma HandleStep K (r : loc) (effc retc comp : val) σ l v :
    σ.(heap) !! r = Some (Some v) →
    σ.(heap) !! l = None →

    (fill K (handle #r effc retc comp), σ) -->*
    (R r (comp #()),
       state_upd_heap (<[r := Some (H r effc retc l K)]>) (
       state_upd_heap (<[l := Some #()]>) σ)
    ).
  Proof.
    rewrite /R /H /M /state_upd_heap. destruct σ. simpl.
    intros Hr Hl. assert (r ≠ l) by congruence. assert (l ≠ r) by congruence.
    csteps. cstep_call1cc0 l. csteps.
    apply csteps_refl; exact eq_refl.
  Qed.

  (* K[with_perform effc retc main] / σ -->*
       R r (main (P r)) / σ[r := H r effc retc l K, l := ()] *)
  Lemma WithPerformStep K (effc retc main : val) σ (r l : loc) :
    σ.(heap) !! r = None →
    σ.(heap) !! l = None →
    r ≠ l →

    (fill K (with_perform effc retc main), σ) -->*
    (R r (main (P r)),
       state_upd_heap (<[r := Some (H r effc retc l K)]>) (
       state_upd_heap (<[l := Some #()]>) σ)
    ).
  Proof.
    rewrite /R /P /H /M /state_upd_heap. destruct σ. simpl.
    intros Hr Hl ?. assert (l ≠ r) by done.
    csteps. cstep_alloc r. csteps. cstep_call1cc0 l. csteps.
    apply csteps_refl; [exact eq_refl|].
    by rewrite (insert_insert_ne _ l r) // insert_insert_eq.
  Qed.

  (* R r v / σ[r := H r effc retc l K, l := ()] -->* K[retc v] / σ[l := ⊥] *)
  Lemma ReturnStep K (r : loc) (effc retc : val) l (v : val) σ :
    σ.(heap) !! r = Some (Some (H r effc retc l K)) →
    σ.(heap) !! l = Some (Some #()) →

    (R r v, σ) -->* (fill K (retc v), state_upd_heap <[l := None]> σ).
  Proof.
    rewrite /R /H /M /state_upd_heap. destruct σ. simpl.
    intros Hr Hl. csteps.
    apply csteps_refl; exact eq_refl.
  Qed.

  (* K'[P r v] / σ[r := H r effc retc l K]), l := ()] -->*
       K[effc v (C r effc retc l' K')] / σ[l := ⊥, l' := ()] *)
  Lemma PerformStep K K' (r : loc) (effc retc : val) l l' (v : val) σ :
    σ.(heap) !! r  = Some (Some (H r effc retc l K)) →
    σ.(heap) !! l  = Some (Some #()) →
    σ.(heap) !! l' = None →

    (fill K' (P r v), σ) -->*
    (fill K (effc v (C r effc retc l' K')),
       state_upd_heap <[l := None]> (
       state_upd_heap <[l' := Some #()]> σ)
    ).
  Proof.
    rewrite /P /C /H /M /state_upd_heap. destruct σ. simpl.
    intros Hr Hl Hl'.
    assert (r ≠ l') by congruence. assert (l' ≠ r) by congruence.
    assert (l ≠ l') by congruence. assert (l' ≠ l) by congruence.
    csteps. cstep_call1cc0 l'. csteps.
    apply csteps_refl; exact eq_refl.
  Qed.

  (* K[(C r effc retc l' K') w] / σ[r := _, l' := ()] -->*
       K'[w] / σ[r := Hr effc retc l K, l := (), l' := ⊥] *)
  Lemma EffContStep K K' (r : loc) (effc retc : val) l l' (w : val) σ v :
    σ.(heap) !! r = Some (Some v) →
    σ.(heap) !! l' = Some (Some #()) →
    σ.(heap) !! l = None →
    r ≠ l' →

    (fill K ((C r effc retc l' K') w), σ) -->*
    (fill K' w,
       state_upd_heap <[l' := None]> (
       state_upd_heap <[r := Some (H r effc retc l K)]> (
       state_upd_heap <[l := Some #()]> σ))
    ).
  Proof.
    rewrite /C /H /M /state_upd_heap. destruct σ. simpl.
    intros Hr Hl' Hl ?. assert (l' ≠ r) by done.
    assert (r ≠ l) by congruence. assert (l ≠ r) by congruence.
    assert (l ≠ l') by congruence. assert (l' ≠ l) by congruence.
    csteps. cstep_call1cc0 l. csteps.
    apply csteps_refl; exact eq_refl.
  Qed.

End reduction_rules.


(* ------------------------------------------------------------------------- *)
(* Handler predicate. *)

Section isHandler_predicate.
  Context `{!stateGS Σ}.

  (* ----------------------------------------------------------------------- *)
  (* Definition. *)

  Notation isHandler_type := (
     (val -d> (val -d> iPropO Σ) -d> iPropO Σ) -d>
     (val -d> iPropO Σ) -d>
     val -d> val -d>
     (val -d> iPropO Σ) -d> iPropO Σ)
    (only parsing).

  Definition isHandler_pre : isHandler_type → isHandler_type :=
    (λ isHandler Ψ Q h r Q',

      (* Correctness of the return branch. *)
      (∀ (y : val), {{Q y}} r y @ WithFrame; Once; ⊤ {{ Q' }}) ∧

      (* Correctness of the effect branch. *)
      (∀ (x k : val) Φ,
         {{ Ψ x Φ ∗
           (∀ w Q'', {{ Φ w ∗ ▷ isHandler Ψ Q h r Q''}} k w @ WithFrame; Once; ⊤ {{ Q'' }})
         }}
           h x k @ WithFrame; Once; ⊤
         {{ Q' }}
      )
    )%I.

  Local Instance isHandler_pre_contractive : Contractive isHandler_pre.
  Proof.
    rewrite /isHandler_pre /triplecc => n deep deep' Hne Ψ Q h r Q'.
    repeat (f_contractive || f_equiv). apply Hne.
  Qed.
  Definition isHandler_def := fixpoint isHandler_pre.
  Definition isHandler_aux : seal isHandler_def. Proof. by eexists. Qed.
  Definition isHandler := isHandler_aux.(unseal).
  Definition isHandler_eq : isHandler = isHandler_def
    := isHandler_aux.(seal_eq).
  Arguments isHandler _%_I _%_I _%_V _%_V _%_I.

  Global Lemma isHandler_unfold Ψ Q h r Q' :
    isHandler Ψ Q h r Q' ⊣⊢ isHandler_pre isHandler Ψ Q h r Q'.
  Proof.
    rewrite isHandler_eq /isHandler_def.
    by apply (fixpoint_unfold isHandler_pre).
  Qed.

End isHandler_predicate.


(* ------------------------------------------------------------------------- *)
(* Verification. *)

Section verification.
  Context `{!stateGS Σ}.

  Definition mainPost_pre :
    (loc -d> (val -d> iPropO Σ) -d> (val -d> (val -d> iPropO Σ) -d> iPropO Σ) -d> (val -d> iPropO Σ)) →
    (loc -d> (val -d> iPropO Σ) -d> (val -d> (val -d> iPropO Σ) -d> iPropO Σ) -d> (val -d> iPropO Σ))
  :=
  (λ mainPost ret Q Ψ res, (∃ v, ret ↦ v) ∗ (
    (∃ y, ⌜ res = InjLV y ⌝ ∗ Q y)
      ∨
    (∃ x k Φ,
     ⌜ res = InjRV (x, k) ⌝ ∗
     Ψ x Φ ∗   
     ▷ isCont k (λ y, (∃ k', ret ↦ InjRV k' ∗ isCont k' (λ res, mainPost ret Q Ψ res)) ∗ Φ y)
    )
  ))%I.

  Local Instance mainPost_pre_contractive : Contractive mainPost_pre.
  Proof.
    rewrite /mainPost_pre /isCont /isCont_gen => n mainPost mainPost' Hne ret Q Ψ res.
    repeat (f_contractive || f_equiv). by apply Hne.
  Qed.
  Definition mainPost_def := fixpoint mainPost_pre.
  Definition mainPost_aux : seal mainPost_def. Proof. by eexists. Qed.
  Definition mainPost := mainPost_aux.(unseal).
  Definition mainPost_eq : mainPost = mainPost_def
    := mainPost_aux.(seal_eq).

  Global Lemma mainPost_unfold ret Q Ψ res :
    mainPost ret Q Ψ res ⊣⊢ mainPost_pre mainPost ret Q Ψ res.
  Proof.
    rewrite mainPost_eq /mainPost_def.
    by apply (fixpoint_unfold mainPost_pre).
  Qed.

  Definition raisePerm (ret : loc) Q Ψ := (∃ k,
    ret ↦ InjRV k ∗ isCont k (mainPost ret Q Ψ)
  )%I.

  Lemma wpcc_with_perform (main effc retc : val) Ψ Q Q' :
    isHandler Ψ Q effc retc Q' -∗

    (∀ (perform : val) R,
      (□ ∀ x Φ, R -∗ Ψ x Φ -∗ wp/cc perform x @ WithFrame {{y, R ∗ Φ y}}) -∗
      R -∗ wp/cc main perform @ WithFrame {{y, R ∗ Q y}}
    ) -∗

    wp/cc with_perform effc retc main @ WithFrame {{Q'}}.
  Proof.
    iIntros "Hhandler Hmain".
    rewrite /with_perform. wpcc_pures.
    iApply wpcc_alloc.
    iIntros "!> %ret Hret _". wpcc_pures.
    iApply (wpcc_bind _ [_]).
    iApply (wpcc_mono _ _ _ (mainPost ret Q Ψ) with "[Hret Hmain]").

    - iApply wpcc_call1cc0.
      iIntros "!> %k Hk". simpl.
      iApply (wpcc_store with "Hret").
      iIntros "!> Hret". wpcc_pures.
      iApply (wpcc_bind _ [_]).
      iApply (wpcc_mono _ _ _ (λ y, raisePerm ret Q Ψ ∗ Q y)%I with "[Hret Hk Hmain]").
      + iApply ("Hmain" with "[] [Hret Hk]"); last by iFrame.
        clear k.
        iIntros "!> %x %Φ [%k' [Hret Hk']] HΨ". wpcc_pures.
        iApply wpcc_call1cc0.
        iIntros "!> %k Hk". simpl.
        iApply (wpcc_load with "Hret"). iIntros "!> Hret".
        rewrite /option_get. wpcc_pures.
        iApply (wpcc_cont with "Hk'").
        rewrite mainPost_unfold.
        iSplitL "Hret"; [iFrame|]. iRight.
        iExists x, k, Φ. iSplit; [done|]. iSplitL "HΨ"; [done|].
        by iNext.
      + simpl. iIntros "%y [[%k' [Hret Hk']] Hy] !>". wpcc_pures.
        iApply (wpcc_load with "Hret"). iIntros "!> Hret".
        rewrite /option_get. wpcc_pures.
        iApply (wpcc_cont with "Hk'").
        rewrite mainPost_unfold.
        iSplitL "Hret"; [iFrame|]. iLeft.
        iExists y. by iFrame.

    - iLöb as "IH" forall (Q').
      simpl. iIntros (res). rewrite mainPost_unfold.
      iIntros "[[%v Hret] [(%y & -> & Hy)|Hy]] !>".
      + wpcc_pures. rewrite isHandler_unfold.
        iDestruct "Hhandler" as "[Hr _]".
        unfold triplecc. simpl. by iApply "Hr".
      + iDestruct "Hy" as "(%x & %k & %Φ & -> & HΨ & Hk)".
        wpcc_pures. rewrite isHandler_unfold.
        iDestruct "Hhandler" as "[_ Hh]".
        unfold triplecc. simpl.
        iApply ("Hh" with "[HΨ Hret Hk]"). iFrame.
        iIntros "%y %Q'' [Hy Hhandler]". wpcc_pures.
        iApply (wpcc_bind _ [_]).
        iApply (wpcc_mono _ _ _ (mainPost ret Q Ψ)%I with "[Hret Hk Hy]");
        last (simpl; by iApply "IH").
        iApply wpcc_call1cc0. iIntros "!> %k' Hk'". simpl.
        iApply (wpcc_store with "Hret"). iIntros "!> Hret". wpcc_pures.
        iApply (wpcc_bind _ [_]).
        iApply (wpcc_cont with "Hk"). by iFrame.
  Qed.

  Lemma triplecc_with_perform (m : logic.mode) (main effc retc : val) Ψ P Q Q' :
    ⊢
    {{
      P ∗ isHandler Ψ Q effc retc Q' ∗
      (∀ (perform : val) R,
      {{
        (∀ x Φ, {{ R ∗ Ψ x Φ }} perform x @ WithFrame; Many; ⊤ {{y, R ∗ Φ y}}) ∗ R ∗ P
      }}
        main perform @ WithFrame; m; ⊤
      {{y, R ∗ Q y}})
    }}
      with_perform effc retc main @ WithFrame; m; ⊤
    {{ Q' }}.
  Proof.
    unfold triplecc; destruct m; simpl; [iModIntro|];
    [iIntros "(HP & Hhr & #Hmain)"|iIntros "(HP & Hhr & Hmain)"];
    iApply (wpcc_with_perform with "Hhr");
    iIntros "%perform %R #Hperform HR"; iApply "Hmain"; iFrame;
    iIntros "%% !> [HR Hx]"; by iApply ("Hperform" with "HR Hx").
  Qed.

End verification.


(* ------------------------------------------------------------------------- *)
(* Control inversion using [with_perform]. *)

Section control_inversion.
  Context `{!stateGS Σ}.

  (* ----------------------------------------------------------------------- *)
  (* Ghost Theory. *)

  (* Resource algebra. *)
  Section ghost_resource.

    Class frac_cell Σ := {
      frac_cell_inG :: inG Σ (prodR fracR (agreeR (listO val)));
    }.

    Definition frac_cellΣ := #[GFunctor (prodR fracR (agreeR (listO val)))].
    Instance subG_frac_cellΣ : subG frac_cellΣ Σ → frac_cell Σ.
    Proof. solve_inG. Qed.

    Definition frac_pointsto `{!frac_cell Σ} (seen : gname) (q : frac) (us : listO val) : iProp Σ :=
      own seen (q, to_agree us).

  End ghost_resource.

  Notation "seen -{ q }-> us" := (frac_pointsto seen q%Qp us)
    (at level 20, format "seen  '-{' q '}->'  us") : bi_scope.

  (* Laws. *)
  Section ghost_theory.
    Context `{!frac_cell Σ}.

    Lemma new_cell us : ⊢ |==> ∃ seen, seen -{1}-> us.
    Proof. by iMod (own_alloc (1%Qp, to_agree us)) as (seen) "H"; eauto. Qed.

    Lemma split_cell seen us :
      seen -{1}-> us ⊣⊢ seen -{1 / 2}-> us ∗ seen -{1 / 2}-> us.
    Proof.
      unfold frac_pointsto.
      have Hequiv: (1%Qp, to_agree us) ≡ ((1 / 2)%Qp ⋅ (1 / 2)%Qp, to_agree us ⋅ to_agree us).
      { by rewrite frac_op Qp.half_half agree_idemp. }
      by rewrite Hequiv pair_op own_op.
    Qed.

    Lemma confront_views seen us vs :
      seen -{1 / 2}-> us -∗ seen -{1 / 2}-> vs -∗ ⌜ us = vs ⌝.
    Proof.
      iIntros "Hseen1 Hseen2".
      iDestruct (own_valid_2 with "Hseen1 Hseen2") as %Hvalid.
      iPureIntro.
      rewrite -pair_op pair_valid in Hvalid.
      destruct Hvalid as [_ Hagree_valid].
      specialize (agree_op_inv _ _ Hagree_valid) as Hequiv.
      specialize (to_agree_inj _ _ Hequiv).
      by apply leibniz_equiv.
    Qed.

    Lemma update_cell seen us vs : seen -{1}-> us ==∗ seen -{1}-> vs.
    Proof.
      iIntros "Hseen".
      iMod (own_update _ _ (1%Qp, to_agree vs) with "Hseen"); [|by iFrame].
      by apply cmra_update_exclusive.
    Qed.

  End ghost_theory.


  (* ----------------------------------------------------------------------- *)
  (* Protocol [YIELD]. *)

  Section protocol.
    Context `{!frac_cell Σ}.

    Definition YIELD (seen : gname) (xs : list val) : val → (val → iProp Σ) → iProp Σ := (λ u Φ,
      ∃ (us vs : list val),
      (seen -{1 / 2}-> us ∗ ⌜ us ++ u :: vs = xs ⌝) ∗
      (seen -{1 / 2}-> (us ++ [u]) -∗ Φ #())
    )%I.

  End protocol.


  (* ----------------------------------------------------------------------- *)
  (* Implementation. *)

  Definition invert : val := (λ: "iter", λ: <>,
    with_perform (λ: "x" "k", sCons "x" "k") (λ: <>, sNil) "iter"
  )%V.


  (* ----------------------------------------------------------------------- *)
  (* Verification. *)

  Section verification.
    Context `{!frac_cell Σ}.

    Lemma silly (P : iProp Σ) : (□?Once P)%I ⊣⊢ P.
    Proof. done. Qed.

    Lemma yield_handler_correct seen xs :
      ∀ us vs,
      ⌜ us ++ vs = xs ⌝ -∗
      seen -{1 / 2}-> us -∗
      isHandler
        (* iter's protocol: *) (YIELD seen xs)
        (* iter's postcondition: *) (λ _, seen -{1 / 2}-> xs)%I
  
        (* effect branch. *) (λ: "x" "k", sCons "x" "k")%V
        (* return branch. *) (λ: <>, sNil)%V

        (* Handler's postcondition: *) (λ y, isHead y us vs)%I.
    Proof.
      iLöb as "IH".
      iIntros (us vs) "<- Hseen1".
      rewrite !isHandler_unfold /isHandler_eq. iSplit;
      try by iIntros (??) "?"; rewrite upcl_bottom.
      (* return branch. *)
      - rewrite /triplecc //=. iIntros (y) "Hseen2".
        iDestruct (confront_views with "Hseen1 Hseen2") as %Heq.
        destruct vs; cycle 1.
        { exfalso. specialize (f_equal length Heq). rewrite length_app //=. lia. }
        rewrite app_nil_r.
        by wpcc_pures.
      (* effect branch. *)
      - rewrite /triplecc.
        iIntros (u k Φ). rewrite silly.
        iIntros "[Hu Hk]".
        iDestruct "Hu" as (us' vs') "[[Hseen2 %Hxs]  HΦ]".
        iDestruct (confront_views with "Hseen1 Hseen2") as %<-.
        iCombine "Hseen1 Hseen2" as "Hseen".
        iApply fupd_wpcc.
        iMod (update_cell _ _ (us ++ [u]) with "Hseen") as "Hseen".
        rewrite split_cell.
        iDestruct "Hseen" as "[Hseen1 Hseen2]".
        iModIntro.
        wpcc_pures. rewrite /isHead /isHead_pre.
        destruct vs.
        { exfalso. specialize (f_equal length Hxs). rewrite !length_app //=. lia. }
        destruct (app_inj_1 us us _ _ eq_refl Hxs) as [_ Heq].
        injection Heq as -> ->.
        iExists k. iModIntro. iSplit; [done|].
        iNext.
        rewrite !isSeq_unfold /isSeq_pre //=.
        iApply "Hk". iSpecialize ("HΦ" with "Hseen1"). iFrame.
        iApply ("IH" with "[] Hseen2").
        by rewrite -app_assoc.
    Qed.

    Lemma invert_spec iter xs :
      ⊢ {{ isIter iter xs }} invert iter @ WithFrame; Many; ⊤ {{ k, isSeq k [] xs }}%I.
    Proof.
      rewrite /triplecc /invert //=. iIntros "!> Hiter".
      wpcc_pures.
      iMod (new_cell ([] : list val)) as (seen) "[Hseen1 Hseen2]".
      iModIntro. rewrite isSeq_unfold /isSeq_pre.
      wpcc_pures.
      iApply (wpcc_with_perform _ _ _ (YIELD seen xs) with "[Hseen1]").
      { by iApply (yield_handler_correct with "[] Hseen1"). }
      { iIntros "%peform %R #Hperform HR".
        iApply (wpcc_mono WithFrame with "[Hseen2 HR Hiter]").
        { iApply ("Hiter" $! (λ us vs, R ∗ seen -{1 / 2}-> us ∗ ⌜ us ++ vs = xs ⌝)%I);
          last by iFrame.
          iIntros "!> %us %u %vs (HR & Hus & <-)".
          iApply ("Hperform" $! u (λ _, seen -{1 / 2}-> (us ++ [u]) ∗ _) with "HR")%I.
          iExists us, vs. iFrame. iSplit; [done|].
          iIntros "$". by rewrite -app_assoc.
        }
        { simpl. iIntros "% (HR & Hxs & _) !>". by iFrame. }
      }
    Qed.

  End verification.

End control_inversion.


(* ------------------------------------------------------------------------- *)
(* Coroutines using [with_perform]. *)

Section coroutines.
  Context `{!stateGS Σ}.

  Definition create : val := (λ: "main",
    let: "r" := ref (InjR (λ: <>,
      with_perform (λ: "x" "k", InjR ("x", "k")) (λ: <>, InjLV #()) "main"))
    in
    "r"
  )%V.

  Definition resume : val := λ: "r",
    let: "g" := option_get !"r" in
    "r" <- InjL #();;    
    match: "g" #() with
      (* sNil *)
      InjL <> =>
        "r" <- InjL #();;
        InjL #()
      (* sCons *)
    | InjR "args" =>
        let: "x" := Fst "args" in
        let: "s" := Snd "args" in
        "r" <- InjR "s";;
        InjR "x"
    end%E.

  Notation isCoroV_type := (
    val -d> (val -d> (val -d> iPropO Σ) -d> iPropO Σ) -d> (val -d> iPropO Σ) -d> iPropO Σ -d> iPropO Σ
  ) (only parsing).

  Definition isCoroV_pre (isCoroV : isCoroV_type) : isCoroV_type := (λ g Ψ Φ Q,
    Φ #() -∗ wp/cc g #() @ WithFrame {{ y,
      match y with
      | InjLV _ =>
          Q
      | InjRV (x, g') =>
          ∃ Φ', Ψ x Φ' ∗ ▷ isCoroV g' Ψ Φ' Q
      | _ =>
          False
      end
    }}
  )%I.

  Local Instance isCoroV_pre_contractive : Contractive isCoroV_pre.
  Proof.
    rewrite /isCoroV_pre => n isCoroV isCoroV' Hne g Ψ Φ Q.
    repeat (f_contractive || f_equiv). intros ?.
    repeat (f_contractive || f_equiv). by apply Hne.
  Qed.
  Definition isCoroV_def := fixpoint isCoroV_pre.
  Definition isCoroV_aux : seal isCoroV_def. Proof. by eexists. Qed.
  Definition isCoroV := isCoroV_aux.(unseal).
  Definition isCoroV_eq : isCoroV = isCoroV_def
    := isCoroV_aux.(seal_eq).
  Global Lemma isCoroV_unfold g Ψ Φ Q :
    isCoroV g Ψ Φ Q ⊣⊢ isCoroV_pre isCoroV g Ψ Φ Q.
  Proof.
    rewrite isCoroV_eq /isCoroV_def.
    by apply (fixpoint_unfold isCoroV_pre).
  Qed.

  Definition isCoro r Ψ Φ Q : iProp Σ :=
    ∃ l g, ⌜ r = #(l : loc) ⌝ ∗ l ↦ InjRV g ∗ isCoroV g Ψ Φ Q.


  Lemma wpcc_resume Ψ Φ Q (r : val) :
    isCoro r Ψ Φ Q -∗
    Φ #() -∗
    wp/cc resume r @ WithFrame {{ y,
      match y with
      | InjLV _ =>
          Q
      | InjRV x =>
          ∃ Φ', Ψ x Φ' ∗ isCoro r Ψ Φ' Q
      | _ =>
          False
      end
    }}.
  Proof.
    iIntros "(%l & %g & (-> & Hl & Hg)) HΦ".
    rewrite /resume /option_get. wpcc_pures.
    iApply (wpcc_load with "Hl").
    iIntros "!> Hl". wpcc_pures.
    iApply (wpcc_store with "Hl").
    iIntros "!> Hl". wpcc_pures.
    iApply (wpcc_bind _ [CaseCtx _ _]).
    iApply (wpcc_mono with "[Hg HΦ]").
    { rewrite isCoroV_unfold. by iApply "Hg". }
    simpl.
    iIntros "%y Hy !>". destruct y => //; try done.
    - wpcc_pures.
      iApply (wpcc_store with "Hl").
      iIntros "!> Hl". by wpcc_pures.
    - destruct y => //; try done.
      rename y1 into x, y2 into g'.
      iDestruct "Hy" as "[%Φ' [Hx Hg']]".
      wpcc_pures.
      iApply (wpcc_store with "Hl").
      iIntros "!> Hl". wpcc_pures. iModIntro.
      by iFrame.
  Qed.

  Lemma wpcc_create Ψ Q (main : val) :

    (* main specification *)
    (∀ (yield : val) R,
      (□ ∀ (x : val) Φ, R -∗ Ψ x Φ -∗ wp/cc yield x @ WithFrame {{_, R ∗ Φ #()}}) -∗
      R -∗ wp/cc main yield @ WithFrame {{_, R ∗ Q}}
    ) -∗

    wp/cc create main @ WithFrame {{ r, isCoro r Ψ (λ _, True) Q }}.

  Proof.
    iIntros "Hmain". rewrite /create.
    wpcc_pures. iApply wpcc_alloc.
    iIntros "!> %l Hl _". wpcc_pures. iModIntro.
    iExists l. iFrame. iSplit; [done|].
    rewrite isCoroV_unfold.
    iIntros "_". wpcc_pures.
    set Ψ' := (λ x Φ, ∃ Φ', Ψ x Φ' ∗ (Φ' #() -∗ Φ #()))%I.
    iApply (wpcc_with_perform _ _ _ Ψ' (λ _, Q) with "[] [Hmain]"); cycle -1.
    { iIntros "%yield %R #Hyield HR". iApply ("Hmain" with "[] HR").
      iIntros "!> %x %Φ HR Hx".
      iApply ("Hyield" $! x (λ _, Φ #())%I with "HR [Hx]").
      iFrame. by auto.
    }
    iLöb as "IH".
    rewrite {-1}isHandler_unfold. iSplit.
    - rewrite /triplecc //=. iIntros "%y HQ". by wpcc_pures.
    - rewrite /triplecc //=. iIntros "%x %k %Φ [[%Φ' [Hx HΦ]] Hk]".
      wpcc_pures. iModIntro. iFrame. iNext.
      rewrite isCoroV_unfold.
      iIntros "HΦ'".
      iApply "Hk". iSplitL; first by iApply "HΦ".
      by iApply "IH".
  Qed.

End coroutines.
