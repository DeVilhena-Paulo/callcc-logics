(* state_rules.v *)

From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap ghost_map.
From iris.program_logic Require Import weakestpre lifting.

From callcc_logics
Require Import syntax notation semantics iris_instantiation lifting tactics.

Class stateGpreS Σ := {
  stateGpreS_invG :: invGpreS Σ;
  stateGpreS_heapG :: gen_heapGpreS loc (option val) Σ;
}.

Definition stateΣ : gFunctors :=
  #[ invΣ; gen_heapΣ loc (option val) ].

Instance subG_stateGpreS {Σ} : subG stateΣ Σ → stateGpreS Σ.
Proof. solve_inG. Qed.

Class stateGS (Σ : gFunctors) := StateGS {
  stateGS_invGS :: invGS Σ;
  state_heapGS :: gen_heapGS loc (option val) Σ;
}.

Global Program Instance stateGS_irisGS `{!stateGS Σ} : irisGS callcc_lang Σ := {
  iris_invGS := stateGS_invGS;
  state_interp σ _ _ _ := gen_heap_interp σ.(heap);
  fork_post _ := True%I;
  num_laters_per_step n := n;
}.
Next Obligation.
  by iIntros (??????) "/= $".
Qed.

Local Definition pointsto_def `{!stateGS Σ}
    (l : loc) (dq : dfrac) (v : val) : iProp Σ :=
  pointsto l dq (Some v).
Local Definition pointsto_aux : seal (@pointsto_def). Proof. by eexists. Qed.
Definition pointsto := pointsto_aux.(unseal).
Local Definition pointsto_unseal :
  @pointsto = @pointsto_def := pointsto_aux.(seal_eq).
Global Arguments pointsto {Σ _}.

Notation "l ↦ dq v" := (pointsto l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.

Definition unshot `{stateGS Σ} r := pointsto r (DfracOwn 1) #().


Section lifting.
Context `{!stateGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ Ψ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.

(** Heap *)

(** We need to adjust the [gen_heap] and [gen_inv_heap] lemmas because of our
value type being [option val] (and sealing). *)

Global Instance pointsto_timeless l dq v : Timeless (l ↦{dq} v).
Proof. rw pointsto_unseal. apply _. Qed.
Global Instance pointsto_fractional l v : Fractional (λ q, l ↦{#q} v)%I.
Proof. rw pointsto_unseal. apply _. Qed.
Global Instance pointsto_as_fractional l q v :
  AsFractional (l ↦{#q} v) (λ q, l ↦{#q} v)%I q.
Proof. rw pointsto_unseal. apply _. Qed.
Global Instance pointsto_persistent l v : Persistent (l ↦□ v).
Proof. rw pointsto_unseal. apply _. Qed.

Global Instance pointsto_combine_sep_gives l dq1 dq2 v1 v2 :
  CombineSepGives (l ↦{dq1} v1) (l ↦{dq2} v2) ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof.
  rw pointsto_unseal /CombineSepGives. iIntros "[H1 H2]".
  iCombine "H1 H2" gives %[? [=->]]. eauto.
Qed.

Lemma pointsto_combine l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ l ↦{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
Proof.
  rw pointsto_unseal.
  iIntros "Hl1 Hl2". by iCombine "Hl1 Hl2" as "$" gives %[_ [= ->]].
Qed.

Global Instance pointsto_combine_as l dq1 dq2 v1 v2 :
  CombineSepAs (l ↦{dq1} v1) (l ↦{dq2} v2) (l ↦{dq1 ⋅ dq2} v1) | 60.
  (* higher cost than the Fractional instance, which kicks in for #qs *)
Proof.
  rw /CombineSepAs. iIntros "[H1 H2]".
  iDestruct (pointsto_combine with "H1 H2") as "[$ _]".
Qed.

Lemma pointsto_valid l dq v : l ↦{dq} v -∗ ⌜✓ dq⌝.
Proof. rw pointsto_unseal. apply pointsto_valid. Qed.
Lemma pointsto_valid_2 l dq1 dq2 v1 v2 :
  l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
Proof. iIntros "H1 H2". iCombine "H1 H2" gives %[? [= ?]]. done. Qed.
Lemma pointsto_agree l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
Proof. iIntros "H1 H2". iCombine "H1 H2" gives %[_ [= ?]]. done. Qed.

Lemma pointsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
  ¬ ✓(dq1 ⋅ dq2) → l1 ↦{dq1} v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. rw pointsto_unseal. apply pointsto_frac_ne. Qed.
Lemma pointsto_ne l1 l2 dq2 v1 v2 : l1 ↦ v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
Proof. rw pointsto_unseal. apply pointsto_ne. Qed.

Lemma pointsto_persist l dq v : l ↦{dq} v ==∗ l ↦□ v.
Proof. rw pointsto_unseal. apply pointsto_persist. Qed.
Lemma pointsto_unpersist l v : l ↦□ v ==∗ ∃ q, l ↦{#q} v.
Proof. rw pointsto_unseal. apply pointsto_unpersist. Qed.

Global Instance frame_pointsto p l v q1 q2 q :
  FrameFractionalQp q1 q2 q →
  Frame p (l ↦{#q1} v) (l ↦{#q2} v) (l ↦{#q} v) | 5.
Proof. apply: frame_fractional. Qed.

Lemma heap_array_to_seq_meta l vs (n : nat) :
  length vs = n →
  ([∗ map] l' ↦ _ ∈ heap_array l vs, meta_token l' ⊤) -∗
  [∗ list] i ∈ seq 0 n, meta_token (l +ₗ (i : nat)) ⊤.
Proof.
  iIntros (<-) "Hvs". iInduction vs as [|v vs IH] forall (l)=> //=.
  rw big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&w&?&Hjl&?&?)%heap_array_lookup.
    rw Loc.add_assoc -{1}[l']Loc.add_0 in Hjl. simplify_eq; lia. }
  rw Loc.add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-Loc.add_assoc.
  rw big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma heap_array_to_seq_pointsto l v (n : nat) :
  ([∗ map] l' ↦ ov ∈ heap_array l (replicate n v), gen_heap.pointsto l' (DfracOwn 1) ov) -∗
  [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v.
Proof.
  iIntros "Hvs". iInduction n as [|n IH] forall (l); simpl.
  { done. }
  rw big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&w&?&Hjl&_)%heap_array_lookup.
    rw Loc.add_assoc -{1}[l']Loc.add_0 in Hjl. simplify_eq; lia. }
  rw Loc.add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-Loc.add_assoc.
  rw big_opM_singleton pointsto_unseal.
  iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma wp_fork K E e Φ :
  ▷ WP e @ ⊤ {{ fork_post }} -∗
  ▷ WP fill K #() @ E {{ Φ }} -∗
  WP fill K (Fork e) @ E {{ Φ }}.
Proof.
  iIntros "He HΦ". iApply wp_lift_fill_base_step; first done.
  iIntros (σ1 ns κ κs nt) "Hσ". iModIntro.
  iSplit. { iPureIntro. exists K, #(), σ1, [e]. apply ForkStep. }
  iIntros (k2 e2 σ2 efs Hstep). iIntros "!> Hcred !>". inv_base_step. iFrame.
Qed.

Lemma wp_allocN K E Φ (n : Z) v :
  (0 < n)%Z →
  ▷ (∀ l,
      ([∗ list] i ∈ seq 0 (Z.to_nat n), (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤) -∗
      WP fill K #l @ E {{ Φ }}) -∗
  WP fill K (AllocN #n v) @ E {{ Φ }}.
Proof.
  iIntros (?) "HΦ". iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "Hheap !>". iSplit.
  { iPureIntro. set (l := Loc.fresh (dom σ.(heap))).
    exists K, #l, (state_init_heap l n v σ), [].
    by apply base_step_alloc_fresh. }
  iIntros "!>" (k2 e2 σ2 efs Hstep) "Hcred". inv_base_step.
  iMod (gen_heap_alloc_big _ (heap_array _ (replicate (Z.to_nat n) v)) with "Hheap")
    as "(Hheap & Hl & Hm)".
  { apply heap_array_map_disjoint. rw length_replicate Z2Nat.id; auto with lia. }
  iModIntro. iSplit; first done. iFrame.
  iApply "HΦ". iApply big_sepL_sep. iSplitL "Hl".
  - by iApply heap_array_to_seq_pointsto.
  - iApply (heap_array_to_seq_meta with "Hm"). by rw length_replicate.
Qed.

Lemma wp_alloc K E Φ v :
  ▷ (∀ l, l ↦ v -∗ meta_token l ⊤ -∗ WP fill K #l @ E {{ Φ }}) -∗
  WP fill K (ref v) @ E {{ Φ }}.
Proof.
  iIntros "HΦ". iApply wp_allocN; first lia.
  iIntros "!> /=" (l) "[[Hl Hm] _]". rw Loc.add_0.
  iApply ("HΦ" with "Hl Hm").
Qed.

Lemma wp_load K E Φ l dq v :
  ▷ l ↦{dq} v -∗
  ▷ (l ↦{dq} v -∗ WP fill K v @ E {{ Φ }}) -∗
  WP fill K (! #l) @ E {{ Φ }}.
Proof.
  iIntros ">Hl HΦ". iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "Hheap !>".
  rw pointsto_unseal.
  iDestruct (gen_heap_valid with "Hheap Hl") as "%Hl". iSplit.
  { iPureIntro. exists K, v, σ, []. by apply LoadStep. }
  iIntros "!>" (k2 e2 σ2 efs Hstep) "Hcred". inv_base_step.
  iFrame. iModIntro. iSplit; first done.
  iApply ("HΦ" with "Hl").
Qed.

Lemma wp_store K E Φ l v w :
  ▷ l ↦ v -∗
  ▷ (l ↦ w -∗ WP fill K #() @ E {{ Φ }}) -∗
  WP fill K (#l <- w) @ E {{ Φ }}.
Proof.
  iIntros ">Hl HΦ". iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "Hheap !>".
  rw pointsto_unseal.
  iDestruct (gen_heap_valid with "Hheap Hl") as %Hl.
  iSplit.
  { iPureIntro.
    exists K, #(), (state_upd_heap <[ l := Some w ]> σ), [].
    by eapply StoreStep. }
  iIntros "!>" (k2 e2 σ2 efs Hstep) "Hcred". inv_base_step.
  iMod (gen_heap_update  _ _ _ (Some w) with "Hheap Hl") as "[$ Hl]".
  iFrame. iModIntro. iSplit; first done. by iApply "HΦ".
Qed.

Lemma wp_xchg K E Φ l v w :
  ▷ l ↦ v -∗
  ▷ (l ↦ w -∗ WP fill K v @ E {{ Φ }}) -∗
  WP fill K (Xchg #l w) @ E {{ Φ }}.
Proof.
  iIntros ">Hl HΦ". iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "Hheap !>".
  rw pointsto_unseal.
  iDestruct (gen_heap_valid with "Hheap Hl") as %Hl.
  iSplit.
  { iPureIntro.
    exists K, v, (state_upd_heap <[ l := Some w ]> σ), [].
    by eapply XchgStep. }
  iIntros "!>" (k2 e2 σ2 efs Hstep) "Hcred". inv_base_step.
  iMod (gen_heap_update  _ _ _ (Some w) with "Hheap Hl") as "[$ Hl]".
  iFrame. iModIntro. iSplit; first done. by iApply "HΦ".
Qed.

Lemma wp_free K E Φ l v :
  ▷ l ↦ v -∗
  ▷ WP fill K #() @ E {{ Φ }} -∗
  WP fill K (Free #l) @ E {{ Φ }}.
Proof.
  iIntros ">Hl HΦ". iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "Hheap !>".
  rw pointsto_unseal.
  iDestruct (gen_heap_valid with "Hheap Hl") as %Hl.
  iSplit.
  { iPureIntro.
    exists K, #(), (state_upd_heap <[ l := None ]> σ), [].
    by eapply FreeStep. }
  iIntros "!>" (k2 e2 σ2 efs Hstep) "Hcred". inv_base_step.
  iMod (gen_heap_update  _ _ _ None with "Hheap Hl") as "[$ Hl]".
  by iFrame.
Qed.

Lemma wp_faa K E Φ l (n m : Z) :
  ▷ l ↦ #n -∗
  ▷ (l ↦ #(n + m) -∗ WP fill K #n @ E {{ Φ }}) -∗
  WP fill K (FAA #l #m) @ E {{ Φ }}.
Proof.
  iIntros ">Hl HΦ". iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "Hheap !>".
  rw pointsto_unseal.
  iDestruct (gen_heap_valid with "Hheap Hl") as %Hl.
  iSplit.
  { iPureIntro.
    exists K, #n, (state_upd_heap <[ l := Some #(n + m) ]> σ), [].
    by eapply FaaStep. }
  iIntros "!>" (k2 e2 σ2 efs Hstep) "Hcred". inv_base_step.
  iMod (gen_heap_update  _ _ _ (Some #(n + m)) with "Hheap Hl") as "[$ Hl]".
  iFrame. iModIntro. iSplit; first done. by iApply "HΦ".
Qed.

Lemma wp_cmpxchg_fail K E Φ l v1 v2 w :
  w ≠ v1 →
  vals_compare_safe w v1 →
  ▷ l ↦ w -∗
  ▷ (l ↦ w -∗ WP fill K (w, #false)%V @ E {{ Φ }}) -∗
  WP fill K (CmpXchg #l v1 v2) @ E {{ Φ }}.
Proof.
  iIntros (??) ">Hl HΦ". iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "Hheap !>".
  rw pointsto_unseal.
  iDestruct (gen_heap_valid with "Hheap Hl") as %Hl.
  iSplit.
  { iPureIntro.
    exists K, (w, #false)%V, σ, [].
    by apply CmpXchgStep; last rw bool_decide_eq_false_2. }
  iIntros "!>" (k2 e2 σ2 efs Hstep) "Hcred". inv_base_step.
  rw bool_decide_eq_false_2 //.
  iFrame. iModIntro. iSplit; first done. by iApply "HΦ".
Qed.

Lemma wp_cmpxchg_suc K E Φ l v1 v2 w :
  w = v1 →
  vals_compare_safe w v1 →
  ▷ l ↦ w -∗
  ▷ (l ↦ v2 -∗ WP fill K (w, #true)%V @ E {{ Φ }}) -∗
  WP fill K (CmpXchg #l v1 v2) @ E {{ Φ }}.
Proof.
  iIntros (-> ?) ">Hl HΦ". iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "Hheap !>".
  rw pointsto_unseal.
  iDestruct (gen_heap_valid with "Hheap Hl") as %Hl.
  iSplit.
  { iPureIntro.
    exists K, (v1, #true)%V, (state_upd_heap <[l := Some v2]> σ), [].
    by apply CmpXchgStep; last rw bool_decide_eq_true_2. }
  iIntros "!>" (k2 e2 σ2 efs Hstep) "Hcred". inv_base_step.
  rw bool_decide_eq_true_2 //.
  iMod (gen_heap_update  _ _ _ (Some v2) with "Hheap Hl") as "[$ Hl]".
  iFrame. iModIntro. iSplit; first done. by iApply "HΦ".
Qed.

Lemma wp_callcc k x e E Φ :
  ▷ WP fill k (subst x (KontV k) e) @ E {{ Φ }} -∗
  WP fill k (Callcc x e) @ E {{ Φ }}.
Proof.
  iIntros "Hwp".
  iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "Hheap !>". iSplit.
  { iPureIntro.
    exists k, (subst x (KontV k) e), σ, [].
    by eapply CallccStep. }
  iIntros "!>" (k2 e2 σ2 efs Hstep) "Hcred". inv_base_step.
  by iFrame.
Qed.

Lemma wp_call1ccS k x e E Φ :
  (▷ ∀ r, unshot r -∗ WP fill k (subst x (ContV r k) e) @ E {{ Φ }}) -∗
  WP fill k (Call1ccS x e) @ E {{ Φ }}.
Proof.
  iIntros "Hwp".
  iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "Hheap !>". iSplit.
  { iPureIntro.
    set (r := Loc.fresh (dom σ.(heap))).
    exists k, (subst x (ContV r k) e), 
      (state_upd_heap <[r:=Some $ LitV $ LitUnit]> σ), [].
    by apply base_step_call1ccS. }
  iIntros "!>" (k2 e2 σ2 efs Hstep) "Hcred". inv_base_step.
  iMod (gen_heap_alloc σ.(heap) r (Some #()) with "Hheap") as "(Hheap & Hr & Hm)"; first done.
  iPoseProof (heap_array_to_seq_pointsto r #() 1 with "[Hr]") as "[Hr _]".
  { by rw //= map_union_empty big_sepM_singleton //=. }
  rw //= Loc.add_0. iModIntro. iFrame. iSplit; [done|].
  by iApply "Hwp".
Qed.

Lemma wp_call1cc0 k x e E Φ :
  (▷ ∀ r, unshot r -∗ WP RunThenAbort (subst x (ContV r k) e) @ E {{ Φ }}) -∗
  WP fill k (Call1cc0 x e) @ E {{ Φ }}.
Proof.
  iIntros "Hwp".
  iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "Hheap !>". iSplit.
  { iPureIntro.
    set (r := Loc.fresh (dom σ.(heap))).
    exists [RunThenAbortCtx], (subst x (ContV r k) e), 
      (state_upd_heap <[r:=Some $ LitV $ LitUnit]> σ), [].
    by apply base_step_call1cc0. }
  iIntros "!>" (k2 e2 σ2 efs Hstep) "Hcred". inv_base_step.
  iMod (gen_heap_alloc σ.(heap) r (Some #()) with "Hheap") as "(Hheap & Hr & Hm)"; first done.
  iPoseProof (heap_array_to_seq_pointsto r #() 1 with "[Hr]") as "[Hr _]".
  { by rw //= map_union_empty big_sepM_singleton //=. }
  rw //= Loc.add_0. iModIntro. iFrame. iSplit; [done|].
  by iApply "Hwp".
Qed.

Lemma wp_kont k k' v E Φ :
  ▷ WP fill k' v @ E {{ Φ }} -∗
  WP fill k (Throw (KontV k') v) @ E {{ Φ }}.
Proof.
  iIntros "Hwp".
  iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "Hheap !>". iSplit.
  { iPureIntro.
    exists k', v, σ, [].
    by apply KontStep.
  }
  iIntros "!>" (k2 e2 σ2 efs Hstep) "Hcred". inv_base_step.
  by iFrame.
Qed.

Lemma wp_cont k k' v r E Φ :
  ▷ unshot r -∗
  ▷ WP fill k' v @ E {{ Φ }} -∗
  WP fill k (Throw (ContV r k') v) @ E {{ Φ }}.
Proof.
  iIntros ">Hr Hwp".
  iApply wp_lift_fill_base_step_no_fork; first done.
  iIntros (σ ????) "Hheap !>".
  rw /unshot pointsto_unseal.
  iDestruct (gen_heap_valid with "Hheap Hr") as "%Hr". iSplit.
  { iPureIntro.
    exists k', v, (state_upd_heap <[r:=None]> σ), [].
    by apply ContStep.
  }
  iIntros "!>" (k2 e2 σ2 efs Hstep) "Hcred". inv_base_step.
  iMod (gen_heap_update  _ _ _ (None) with "Hheap Hr") as "[$ Hr]".
  by iFrame.
Qed.

End lifting.
