(* queue_lib.v *)

From iris.proofmode Require Import base proofmode classes.
From callcc_logics Require Import logic state proofmode list_lib.

Section queue_lib.
  Context `{!stateGS Σ}.
  
  Class QueueLib := {
    queue_create : val;
    queue_add    : val;
    queue_take   : val;
    queue_empty  : val;

    is_queue : val -d> list val -d> iPropO Σ;

    queue_create_spec b Q :
      ▷ (∀ q, is_queue q [] -∗ Q q) -∗
      wp/cc queue_create #() @ b {{Q}};

    queue_add_spec b Q q v vs :
      ▷ is_queue q vs -∗
      ▷ (is_queue q (v :: vs) -∗ Q #()) -∗
      wp/cc queue_add q v @ b {{Q}};

    queue_take_spec b Q q v vs :
      ▷ is_queue q (vs ++ [v]) -∗
      ▷ (is_queue q vs -∗ Q v) -∗
      wp/cc queue_take q @ b {{Q}};

    queue_empty_spec b Q q vs :
      ▷ is_queue q vs -∗
      ▷ (is_queue q vs -∗
         Q #(bool_decide (length vs = 0%nat))
        ) -∗
      wp/cc queue_empty q @ b {{Q}};
  }.

  Section instance.

    Definition queue_create' : val := λ: <>, ref list_nil.
    Definition queue_add' : val := λ: "q" "x",
      "q" <- list_cons "x" (Load "q").
    Definition queue_take' : val := λ: "q",
      match: list_reverse (Load "q") with
        InjL <> => assert: #false
      | InjR "args" =>
          let: "x" := Fst "args" in
          let: "xs" := Snd "args" in
          "q" <- list_reverse "xs";;
          "x"
      end%V.
    Definition queue_empty' : val := λ: "q",
      list_empty (Load "q").
    Definition is_queue' q vs := (∃ (r : loc) l,
      ⌜ q = #r ⌝ ∗ r ↦ l ∗ is_list l vs)%I.

    Program Definition queue_lib_instance : QueueLib := {|
      queue_create := queue_create';
      queue_add := queue_add';
      queue_take := queue_take';
      queue_empty := queue_empty';
      is_queue := is_queue';
    |}.
    Next Obligation.
      iIntros "% % HQ". rewrite /queue_create'.
      wpcc_pures. iApply wpcc_alloc.
      iIntros "!> %r Hr _". iApply wpcc_value.
      iApply "HQ". iExists r, list_nil. iFrame.
      iSplit; [done|]. by iApply list_nil_spec.
    Qed.
    Next Obligation.
      iIntros "% % % % % Hq HQ".
      rewrite /queue_add'. wpcc_pures.
      iDestruct "Hq" as "(% & % & -> & Hr & Hl)".
      iApply (wpcc_load with "Hr").
      iIntros "!> Hr".
      iApply (wpcc_bind _ [StoreRCtx _]).
      iApply (list_cons_spec with "Hl").
      iIntros "!> %l' Hl'". simpl.
      iApply (wpcc_store with "Hr").
      iIntros "!> Hr". iApply wpcc_value.
      iApply "HQ". iExists r, l'. by iFrame.
    Qed.
    Next Obligation.
      iIntros "% % % % % Hq HQ".
      rewrite /queue_take'. wpcc_pures.
      iDestruct "Hq" as "(% & % & -> & Hr & Hl)".
      iApply (wpcc_load with "Hr").
      iIntros "!> Hr".
      iApply (wpcc_bind _ [CaseCtx _ _]).
      iApply (list_reverse_spec with "Hl").
      iIntros "!> %l' Hl'". simpl. rewrite reverse_app //=.
      iDestruct "Hl'" as "[%l'' [-> Hl'']]". wpcc_pures.
      iApply (wpcc_bind _ [AppRCtx _; StoreRCtx _]).
      iApply (list_reverse_spec with "Hl''").
      iIntros "!> %l' Hl'". simpl.
      iApply (wpcc_store with "Hr").
      iIntros "!> Hr". wpcc_pures.
      iApply "HQ". iExists r, l'.
      rewrite reverse_involutive. by iFrame.
    Qed.
    Next Obligation.
      iIntros "% % % % Hq HQ".
      rewrite /queue_empty'. wpcc_pures.
      iDestruct "Hq" as "(% & % & -> & Hr & #Hl)".
      iApply (wpcc_load with "Hr").
      iIntros "!> Hr".
      iApply (list_empty_spec with "Hl").
      destruct vs as [|v vs].
      - simpl. iApply "HQ". iDestruct "Hl" as "->".
        iExists r, list_nil. iFrame. by iSplit.
      - simpl. iApply "HQ". iExists r, l. iFrame. by iSplit.
    Qed.

  End instance.

End queue_lib.
