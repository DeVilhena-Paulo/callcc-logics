(* adequacy.v *)

From iris.base_logic.lib Require Import mono_nat gen_inv_heap.
From iris.program_logic Require Export weakestpre adequacy.
From iris.base_logic.lib Require Import iprop wsat.
From iris.prelude Require Import options.
From iris.heap_lang Require Import locations.

From callcc_logics Require Export syntax semantics iris_instantiation.
From callcc_logics Require Import proofmode notation.

Lemma wp_adequacy Σ `{!stateGpreS Σ} s e σ φ :
  (∀ `{!stateGS Σ}, ⊢ WP e @ s; ⊤ {{ v, ⌜ φ v ⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp.
  apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done].
  iIntros (Hinv).
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
  iDestruct (Hwp (StateGS _ _ _)) as "Hwp".
  iModIntro. iExists
    (λ σ _ _ _, gen_heap_interp σ.(heap)).
  iExists [(λ v, ⌜φ v⌝%I)], (λ _, True)%I, _ => /=.
  iFrame. iSplitR. { iSplit; [|done]. by iApply "Hwp". }
  iIntros (es' t2' -> ? ?) " _ H _".
  iApply fupd_mask_intro_discard; [done|]. iSplit; [|done].
  iIntros (v2 t2'' [=]).
  destruct es'; [done|].
  injection H3 as -> ?.
  by iDestruct "H" as "[$ _]".
Qed.

(* The hypothesis uses the explicit-[gp] notation with the global
   postcondition set to [φ] itself; [wpcc_sound] turns that into the plain
   [wp] with postcondition [λ v, ⌜φ v⌝] required by [wp_adequacy]. *)
Lemma wpcc_adequacy Σ `{!stateGpreS Σ} f e σ φ :
  (∀ `{!stateGS Σ}, ⊢ wp/cc ⟨φ⟩ e @ f; ⊤ {{ v, ⌜ φ v ⌝}}) →
  adequate NotStuck e σ (λ v _, φ v).
Proof.
  intros Hwpcc. apply (wp_adequacy Σ). intros HstateGS.
  iApply wpcc_sound. by iApply Hwpcc.
Qed.


(* Uncomment to check there are no axioms.
   (The output should include "Closed under the global context" at the end). *)
(* Print Assumptions wpcc_adequacy. *)
