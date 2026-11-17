(* lifting.v *)

From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting.
From callcc_logics Require Import syntax semantics iris_instantiation tactics.

(** Lifting lemmas where we can do a [base_step] under an evaluation context.
    We need these because we cannot easily write down a bind lemma, due to the non-local control flow of effects. *)
Section lifting.
  Context `{!irisGS callcc_lang Σ}.

  Lemma wp_lift_fill_base_step {k1 s E Φ} e1 :
    to_val e1 = None →
    (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E}=∗
      ⌜base_reducible k1 e1 σ1⌝ ∗
      ▷ ∀ k2 e2 σ2 efs, ⌜base_step k1 e1 σ1 k2 e2 σ2 efs⌝ -∗ £ 1 ={E}=∗
        state_interp σ2 (S ns) κs (length efs + nt) ∗
        WP fill k2 e2 @ s; E {{ Φ }} ∗
        [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
    ⊢ WP fill k1 e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (He1) "H". iApply wp_lift_step; first by apply fill_not_val.
    iIntros (σ1 ns κ κs nt) "Hσ1". iMod ("H" with "Hσ1") as "[% H]".
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver; iModIntro.
    iSplit; first destruct s; auto using base_reducible_reducible; try done.
    iNext. iIntros (e2 σ2 efs Hstep) "Hcred". iMod "Hclose" as "_".
    destruct κ as [|??]; last done.
    apply base_reducible_prim_step_ctx in Hstep as (k' & e' & -> & Hstep); last done.
    by iApply "H".
  Qed.

  Lemma wp_lift_fill_base_step_fupd {k1 s E1 E2 Φ} e1 :
    to_val e1 = None →
    (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E1}=∗
      ⌜base_reducible k1 e1 σ1⌝ ∗
      ∀ k2 e2 σ2 efs, ⌜base_step k1 e1 σ1 k2 e2 σ2 efs⌝ -∗ £ 1 ={E1}[E2]▷=∗
        state_interp σ2 (S ns) κs (length efs + nt) ∗
        WP fill k2 e2 @ s; E1 {{ Φ }} ∗
        [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
    ⊢ WP fill k1 e1 @ s; E1 {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_step_fupd; first by apply fill_not_val.
    iIntros (σ1 ns κ κs nt) "Hσ1". iMod ("H" with "Hσ1") as "[% H]".
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver; iModIntro.
    iSplit; first by destruct s; auto using reducible_fill, base_reducible_reducible.
    iIntros (e2 σ2 efs Hstep) "Hcred". iMod "Hclose" as "_".
    destruct κ as [|??]; last done.
    apply base_reducible_prim_step_ctx in Hstep as (k' & e' & -> & Hstep); last done.
    iMod ("H" with "[//] Hcred") as "H".
    iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver; iModIntro.
    iNext. iMod "Hclose" as "_". by iMod "H" as "($ & $ & $)".
  Qed.

  Lemma wp_lift_fill_base_step_no_fork_fupd {k1 s E1 E2 Φ} e1 :
    to_val e1 = None →
    (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E1}=∗
      ⌜base_reducible k1 e1 σ1⌝ ∗
      ∀ k2 e2 σ2 efs, ⌜base_step k1 e1 σ1 k2 e2 σ2 efs⌝ -∗ £ 1 ={E1}[E2]▷=∗
        ⌜efs = []⌝ ∗ state_interp σ2 (S ns) κs nt ∗ WP fill k2 e2 @ s; E1 {{ Φ }})
    ⊢ WP fill k1 e1 @ s; E1 {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_fill_base_step_fupd; [done|].
    iIntros (σ1 ns κ κs nt) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
    iIntros (k2 v2 σ2 efs Hstep) "Hcred".
    iMod ("H" $! k2 v2 σ2 efs with "[# //] Hcred") as "H".
    iIntros "!> !>". iMod "H" as "(-> & ? & ?) /=". by iFrame.
  Qed.

  Lemma wp_lift_fill_base_step_no_fork {k1 s E Φ} e1 :
    to_val e1 = None →
    (∀ σ1 ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E}=∗
      ⌜base_reducible k1 e1 σ1⌝ ∗
      ▷ ∀ k2 e2 σ2 efs, ⌜base_step k1 e1 σ1 k2 e2 σ2 efs⌝ -∗ £ 1 ={E}=∗
        ⌜efs = []⌝ ∗ state_interp σ2 (S ns) κs nt ∗ WP fill k2 e2 @ s; E {{ Φ }})
    ⊢ WP fill k1 e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_fill_base_step; first done.
    iIntros (σ1 ns κ κs nt) "Hσ1". iMod ("H" $! σ1 with "Hσ1") as "[$ H]"; iModIntro.
    iNext; iIntros (k2 v2 σ2 efs Hstep) "Hcred".
    iMod ("H" $! k2 v2 σ2 efs with "[//] Hcred") as "(-> & ? & ?) /=". by iFrame.
  Qed.

End lifting.

