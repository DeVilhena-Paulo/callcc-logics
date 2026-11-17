(* list_lib.v *)

From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import frac cmra list agree.
From callcc_logics Require Import logic state proofmode.

Section list_lib.
  Context `{!stateGS Σ}.

  Definition list_nil : val := InjLV #().
  Definition list_cons : val := λ: "x" "xs", InjR ("x", "xs").
  Definition list_singleton : val := λ: "x", list_cons "x" list_nil.
  Definition list_empty : val := λ: "xs",
    match: "xs" with
      InjL <> =>
        #true
    | InjR <> =>
        #false
    end%V.
  Definition list_concat : val := rec: "list_concat" "xs" "ys" :=
    match: "xs" with
      InjL <> =>
        "ys"
    | InjR "args" =>
        let: "x" := Fst "args" in
        let: "xs'" := Snd "args" in
        list_cons "x" ("list_concat" "xs'" "ys")
    end%V.
  Definition list_reverse : val := rec: "list_reverse" "xs" :=
    match: "xs" with
      InjL <> =>
        list_nil
    | InjR "args" =>
        let: "x" := Fst "args" in
        let: "xs'" := Snd "args" in
        list_concat ("list_reverse" "xs'") (list_singleton "x")
    end%V.

  Definition is_list : val → list val → iProp Σ :=
    fix is_list l xs :=
      match xs with
      | [] => ⌜ l = InjLV #() ⌝
      | x :: xs' => ∃ l', ⌜ l = InjRV (x, l')%V ⌝ ∗ is_list l' xs'
      end%I.

  Global Instance is_list_pers l xs : Persistent (is_list l xs).
  Proof. revert l; induction xs as [|x xs IH]; intros l; apply _. Qed.

  Lemma list_nil_spec : ⊢ is_list list_nil [].
  Proof. by iPureIntro. Qed.

  Lemma list_cons_spec l x xs b Q :
    ▷ is_list l xs -∗
    ▷ (∀ l', is_list l' (x :: xs) -∗ Q l') -∗
    wp/cc list_cons x l @ b {{ Q }}.
  Proof.
    destruct xs as [|x' xs'].
    - iIntros "H HQ". rewrite /list_cons //=.
      wpcc_pures. iModIntro. iApply "HQ". by eauto.
    - iIntros "[% Hl] HQ". rewrite /list_cons //=.
      wpcc_pures. iModIntro. iApply "HQ". by eauto.
  Qed.

  Lemma list_singleton_spec x b Q :
    ▷ (∀ l, is_list l [x] -∗ Q l) -∗
    wp/cc list_singleton x @ b {{ Q }}.
  Proof.
    iIntros "HQ". rewrite /list_singleton //=. wpcc_pures.
    by iApply list_cons_spec; first by iApply list_nil_spec.
  Qed.

  Lemma list_concat_spec l1 l2 xs ys b Q :
    ▷ is_list l1 xs -∗
    ▷ is_list l2 ys -∗
    ▷ (∀ l, is_list l (xs ++ ys) -∗ Q l) -∗
    wp/cc list_concat l1 l2 @ b {{ Q }}.
  Proof.
    iInduction xs as [|x xs] "IH" forall (l1 l2 ys Q).
    - iIntros "Hl1 Hl2 HQ". rewrite /list_concat //=.
      wpcc_pures. iDestruct "Hl1" as "->". wpcc_pures.
      by iApply "HQ".
    - iIntros "[%l1' Hl1'] Hl2 HQ". rewrite /list_concat //=.
      wpcc_pures. iDestruct "Hl1'" as "[-> Hl1']".
      do 9 wpcc_pure. iApply (wpcc_bind _ [AppRCtx _]).
      iApply ("IH" with "Hl1' Hl2").
      iIntros "!> %l Hl". simpl. iApply (list_cons_spec with "Hl").
      iIntros "!> %l' Hl'". by iApply "HQ".
  Qed.

  Lemma list_reverse_spec l xs b Q :
    ▷ is_list l xs -∗
    ▷ (∀ l', is_list l' (reverse xs) -∗ Q l') -∗
    wp/cc list_reverse l @ b {{ Q }}.
  Proof.
    iInduction xs as [|x xs] "IH" forall (l Q).
    - iIntros "Hl HQ". rewrite /list_reverse //=.
      wpcc_pures. iDestruct "Hl" as "->". wpcc_pures.
      by iApply "HQ".
    - iIntros "[%l' Hl'] HQ". rewrite /list_reverse //=.
      wpcc_pures. iDestruct "Hl'" as "[-> Hl']".
      do 9 wpcc_pure. iApply (wpcc_bind _ [AppRCtx _]).
      iApply list_singleton_spec.
      iIntros "!> %lx Hlx". simpl.
      iApply (wpcc_bind _ [AppLCtx _; AppRCtx _]).
      iApply ("IH" with "Hl'").
      iIntros "!> %l Hl". simpl.
      iApply (list_concat_spec _ _ _ [x] with "Hl Hlx").
      iIntros "!> %l'' Hl''". iApply "HQ".
      by rewrite reverse_cons.
  Qed.

  Lemma list_empty_spec l xs b Q :
    ▷ is_list l xs -∗
    ▷ Q #(bool_decide (xs = [])) -∗
    wp/cc list_empty l @ b {{ Q }}.
  Proof.
    destruct xs as [|x xs]; rewrite /list_empty //=.
    - iIntros "Hl HQ". wpcc_pures.
      iDestruct "Hl" as "->". by wpcc_pures.
    - iIntros "[% Hl] HQ". wpcc_pures.
      iDestruct "Hl" as "[-> _]". by wpcc_pures.
  Qed.

End list_lib.
