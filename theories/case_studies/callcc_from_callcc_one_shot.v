(* callcc_from_callcc_one_shot.v *)

From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl_auth agree gset gmap agree csum.
From iris.base_logic.lib Require Import invariants.
From callcc_logics Require Import logic state proofmode.


(* ------------------------------------------------------------------------- *)
(* Callcc-one-shot. *)

Section callcc_one_shot.

  Definition diverge : expr := (rec: "f" <> := "f" #())%V #().

  Definition block : expr := (#() #())%E.

  Definition callcc_one_shot (error : expr) : val := (λ: "f",
    let: "r" := ref #false in
    call/cc: "k",
      let: "k-one-shot" := λ: "x",
        if: !"r" then
          error
        else (
          "r" <- #true;;
          throw: "k" "x"
        )
      in
      "f" "k-one-shot"
  )%V.

End callcc_one_shot.

Notation "'call/cc-one-shot-div:' k ',' e" := (callcc_one_shot diverge (Lam k%binder e%E))
  (at level 200, k at level 1, e at level 200,
   format "'[hv' 'call/cc-one-shot-div:'  k ','  '/  ' e ']'") : expr_scope.

Notation "'call/cc-one-shot-block:' k ',' e" := (callcc_one_shot block (Lam k%binder e%E))
  (at level 200, k at level 1, e at level 200,
   format "'[hv' 'call/cc-one-shot-block:'  k ','  '/  ' e ']'") : expr_scope.


(* ------------------------------------------------------------------------- *)
(* Reasoning Rules. *)

Section rules.
  Context `{!stateGS Σ}.

  Lemma wpcc_callcc_one_shot_div (x : binder) e Φ :
    ▷ (∀ k, isKont k Φ -∗ wp/cc (subst' x k e) @ NoFrame {{ Φ }}) -∗
    wp/cc (call/cc-one-shot-div: x, e)%E @ NoFrame {{ Φ }}.
  Proof.
    iIntros "Hwpcc". rewrite /callcc_one_shot //=.
    wpcc_pures. iApply wpcc_alloc.
    iIntros "!> %r Hr _". wpcc_pures.
    iApply fupd_wpcc.
    iMod (inv_alloc (nroot .@ r) ⊤ (∃ (b : bool), r ↦ #b) with "[$]")
        as "#Hinv".
    iModIntro.
    iApply wpcc_callcc.
    iIntros "!> %k #Hk". wpcc_pures.
    iApply "Hwpcc".
    iIntros "!> % %y Hy". wpcc_pures.
    iApply (wpcc_load_inv with "Hinv").
    iIntros "[%b Hr] Hclose". iExists #b. iFrame.
    iIntros "!> Hr".
    destruct b;
    iApply (wpcc_inv_restore with "Hclose [$]");
    wpcc_pure.
    - iLöb as "IH". wpcc_pure. by iApply "IH".
    - iApply (wpcc_store_inv with "Hinv").
      iIntros "[%b Hr] Hclose". iExists #b. iFrame.
      iIntros "!> Hr".
      iApply (wpcc_inv_restore with "Hclose [$]").
      wpcc_pures.
      by iApply ("Hk" with "Hy").
  Qed.

  Lemma wpcc_callcc_one_shot_block x e Φ :
    ▷ (∀ k, isCont k Φ -∗ wp/cc (subst x k e) @ WithFrame {{ _, False }}) -∗
    wp/cc (call/cc-one-shot-block: x, e)%E @ WithFrame  {{ Φ }}.
  Proof.
    iIntros "Hwpcc". rewrite /callcc_one_shot //=.
    wpcc_pures. iApply wpcc_alloc.
    iIntros "!> %r Hr _". wpcc_pures.
    iApply wpcc_callcc_alt.
    iIntros "!> %k Hk". wpcc_pures.
    iApply "Hwpcc".
    iIntros "% %y Hy". wpcc_pures.
    iApply (wpcc_load with "Hr").
    iIntros "!> Hr". wpcc_pures.
    iApply (wpcc_store with "Hr").
    iIntros "!> Hr". wpcc_pures.
    by iApply "Hk".
  Qed.

End rules.


(* ------------------------------------------------------------------------- *)
(* Implementation. *)

Section implementation.
  Context `{!stateGS Σ}.

  Definition callcc_div : val := (λ: "f",
    let: "r" := ref (λ: <>, assert: #false) in
    let: "G" := rec: "G" "f" :=
      let: "x" := (call/cc-one-shot-div: "k",
        "r" <- (λ: "y", throw: "k" "y");;
        "f" (λ: "y", (Load "r") "y")
      )
      in
      (call/cc-one-shot-div: "k", "G" (λ: <>, throw: "k" "x"))
    in
    "G" "f"
  )%V.

End implementation.


(* ------------------------------------------------------------------------- *)
(* Verification. *)

Class callcc_divG Σ := callcc_div_G :: inG Σ (csumR (exclR unitO) (agreeR unitO)).
Definition callcc_divΣ : gFunctors := #[ GFunctor (csumR (exclR unitO) (agreeR unitO)) ].
Global Instance subG_callcc_div {Σ} : subG callcc_divΣ Σ → callcc_divG Σ.
Proof. solve_inG. Qed.

Section verification.
  Context `{!stateGS Σ, !callcc_divG Σ}.

  Lemma wpcc_callcc_div (f : val) Φ :
    (∀ k, isKont k Φ -∗ wp/cc f k @ NoFrame {{Φ}}) -∗
    wp/cc callcc_div f @ NoFrame {{Φ}}.
  Proof.
    iIntros "Hf". unfold callcc_div.
    wpcc_pures.
    iApply wpcc_alloc. iIntros "!> %r Hr _".
    iApply fupd_wpcc.
    iMod (own_alloc (Cinl (Excl (tt : ofe_car unitO)))) as (γ) "Hleft"; [ done|].
    iMod (inv_alloc (nroot .@ r) ⊤ (∃ (v : val), r ↦ v ∗
      (own γ (Cinl (Excl ())) ∨ (own γ (Cinr (to_agree ())) ∗ ∃ k, ⌜ v = k ⌝ ∗ isKont k Φ))
    )%I
    with "[$]") as "#Hinv".
    iModIntro.
    do 6 wpcc_pure.
    iApply (wpcc_bind _ [_]).
    iApply (wpcc_mono _ _ _ (λ y, Φ y ∗ own γ (Cinr (to_agree ())))%I with "[Hf]").
    - iApply wpcc_callcc_one_shot_div.
      iIntros "!> %k #Hk". simpl.
      iApply (wpcc_bind _ [_]).
      iApply (wpcc_mono _ _ _ (λ _, own γ (Cinr (to_agree ())) ∗ _)%I with "[Hf]").
      { iApply (wpcc_store_inv with "Hinv").
        iIntros "[%v [Hr Hinv']] Hclose". iExists v. iFrame.
        iIntros "!> Hr".
        iDestruct "Hinv'" as "[Hleft | [#Hright [%k' [-> Hk']]]]".
        * iApply fupd_wpcc'.
          iMod (own_update _ _ (Cinr (to_agree (tt : ofe_car unitO)))
            with "Hleft") as "#Hright".
          { intros n mf Hm. destruct mf as [[a'|b'|]|]; try by destruct Hm. }
          iModIntro.
          iApply (wpcc_inv_restore with "Hclose [Hr]").
          { iNext. iFrame. iRight. iSplit; [done|].
            iExists (λ: "y", k "y")%V. iSplit; [done|].
            iIntros "!> %k' %y Hy". wpcc_pures. iApply "Hk". by iFrame.
          }
          iApply wpcc_value.
          iFrame "Hright". by iApply "Hf".
        * iApply (wpcc_inv_restore with "Hclose [Hr]").
          { iNext. iFrame. iRight. iSplit; [done|].
            iExists (λ: "y", k "y")%V. iSplit; [done|].
            iIntros "!> %k'' %y Hy". wpcc_pures. iApply "Hk". by iFrame.
          }
          by iApply wpcc_value; iFrame.
      }
      simpl.
      iIntros "!> % [#Hright Hf] !>".
      wpcc_pures.
      iApply (wpcc_mono _ _ _ Φ with "[Hf]"); last by (simpl; auto).
      iApply "Hf".
      iIntros "!> % %x Hx".
      wpcc_pures.
      iApply (wpcc_load_inv with "Hinv").
      iIntros "[%v' [Hr Hinv']] Hclose". iExists v'. iFrame.
      iIntros "!> Hr".
      iDestruct "Hinv'" as "[Hleft | [_ [%k' [-> #Hk']]]]".
      { iDestruct (own_valid_2 with "Hleft Hright") as %Hvalid.
        by revert Hvalid.
      }
      iApply (wpcc_inv_restore with "Hclose [Hr]").
      { iFrame. iRight. iFrame "Hright". by iFrame "Hk'". }
      by iApply (wpcc_kont with "Hk'").
    - simpl. iIntros "!>".
      iLöb as "IH".
      iIntros "%x [Hx #Hright] !>". do 2 wpcc_pure.
      iApply wpcc_callcc_one_shot_div.
      iIntros "!> %k Hk". simpl. do 2 wpcc_pure.
      iApply (wpcc_bind _ [_]).
      iApply (wpcc_mono _ _ _ Φ with "[Hx Hk]"); cycle -1.
      { simpl. by iIntros "!> % H"; iApply "IH"; iFrame. }
      iApply wpcc_callcc_one_shot_div.
      iIntros "!> %k' #Hk'". simpl.
      iApply (wpcc_store_inv with "Hinv").
      iIntros "[%v [Hr Hinv']] Hclose". iExists v. iFrame.
      iIntros "!> Hr".
      iDestruct "Hinv'" as "[Hleft | [_ [%k'' [-> #Hk'']]]]".
      { iDestruct (own_valid_2 with "Hleft Hright") as %Hvalid.
        by revert Hvalid.
      }
      iApply (wpcc_inv_restore with "Hclose [Hr]").
      { iFrame. iRight. iFrame "Hright".
        iExists (λ: "y", k' "y")%V. iNext. iSplit; [done|].
        iIntros "!> % %y Hy". wpcc_pures. iApply "Hk'". by iFrame.
      }
      wpcc_pures.
      by iApply (wpcc_kont with "Hk").
  Qed.

End verification.
