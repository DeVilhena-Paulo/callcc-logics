(* lock_lib.v *)

From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import excl_auth agree gset gmap agree csum.
From iris.base_logic.lib Require Import invariants.
From callcc_logics Require Import logic state proofmode.


(* ------------------------------------------------------------------------- *)
(* Implementation. *)

Section lock_lib.
  Context `{!stateGS Σ}.

  Class LockLib := {
    new_lock : val;
    acquire : val;
    release : val;
    is_lock : val → iProp Σ → iProp Σ;

    lock_pers lk P ::
      Persistent (is_lock lk P);

    new_lock_spec b Φ :
      ▷ (∀ lk, (∀ P, P ={⊤}=∗ is_lock lk P) -∗ Φ lk) -∗
      wp/cc new_lock #() @ b {{Φ}};

    acquire_spec b lk P Φ :
      is_lock lk P -∗
      ▷ (P -∗ Φ #()) -∗
      wp/cc acquire lk @ b {{Φ}};

    release_spec b lk P Φ :
      ▷ is_lock lk P -∗
      ▷ P -∗
      ▷ (Φ #()) -∗
      wp/cc release lk @ b {{Φ}};
  }.

  Section instance.

    Definition new_lock' : val := λ: <>, ref #false.
    Definition acquire' : val := (rec: "try_acquire" "lk" :=
      let: "succeeded?" := Snd (CmpXchg "lk" #false #true) in
      if: "succeeded?" then #() else "try_acquire" "lk").
    Definition release' : val := λ: "lk", "lk" <- #false.

    Definition lockN (lk : val) := nroot .@ "lock" .@ lk.

    Definition is_lock' (lk : val) (P : iProp Σ) : iProp Σ :=
      ∃ (l : loc),
      ⌜ lk = #l ⌝ ∗
      inv (lockN lk) (∃ b : bool, l ↦ #b ∗ if b then True else P).

    Program Definition locklib_instance : LockLib := {|
      new_lock := new_lock';
      acquire := acquire';
      release := release';
      is_lock := is_lock';
    |}.
    Next Obligation.
      (* new_lock_spec. *)
      iIntros "%b %Φ Hwpcc". unfold new_lock'. wpcc_pures.
      iApply wpcc_alloc. iIntros "!> %lk Hlk _". iApply wpcc_value.
      iApply "Hwpcc". iIntros "%P HP".
      iMod (inv_alloc (lockN #lk) ⊤ (∃ (b : bool), lk ↦ #b ∗ if b then True else P) with "[$Hlk $HP]")
        as "#Hinv".
      iModIntro. iExists lk. by eauto with iFrame.
    Qed.
    Next Obligation.
      (* acquire_spec. *)
      iIntros "%b' %lk' %P %Φ [%lk [-> #Hinv]] HΦ". unfold acquire'.
      iLöb as "IH".
      wpcc_pures.
      iApply (wpcc_cmpxchg_inv with "Hinv").
      iIntros "[%b [Hlk HP]] Hclose". iExists #b. iSplit.
      { iPureIntro. by left. }
      iFrame. iSplit.
      - iNext. iIntros "%Heq". injection Heq as ->.
        iIntros "Hlk". iApply (wpcc_inv_restore with "Hclose [Hlk]").
        { by eauto with iFrame. }
        wpcc_pures. iModIntro. by iApply "HΦ".
      - iNext. iIntros "%Hneq".
        iIntros "Hlk". iApply (wpcc_inv_restore with "Hclose [Hlk HP]").
        { by eauto with iFrame. }
        do 4 wpcc_pure. by iApply "IH".
    Qed.
    Next Obligation.
      (* release_spec. *)
      iIntros "%b' %lk' %P %Φ [%lk [Heq #Hinv]] HP HΦ".
      unfold release'.
      wpcc_pures.
      iDestruct "Heq" as "->".
      iApply (wpcc_store_inv with "Hinv").
      iIntros "[%b [Hlk _]] Hclose". iExists #b. iFrame.
      iIntros "!> Hlk".
      iApply (wpcc_inv_restore with "Hclose [Hlk HP]").
      { by eauto with iFrame. }
      by iApply wpcc_value.
    Qed.

  End instance.

End lock_lib.
