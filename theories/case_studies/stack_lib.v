(* stack_lib.v *)

From iris.proofmode Require Import base proofmode classes.
From callcc_logics Require Import logic state proofmode list_lib.

Section stack_lib.
  Context `{!stateGS Σ}.
  
  Class StackLib := {
    stack_create : val;
    stack_push   : val;
    stack_pop    : val;

    is_stack : val -d> list val -d> iPropO Σ;

    stack_create_spec b Q :
      ▷ (∀ q, is_stack q [] -∗ Q q) -∗
      wp/cc stack_create #() @ b {{Q}};

    stack_push_spec b Q q v vs :
      ▷ is_stack q vs -∗
      ▷ (is_stack q (v :: vs) -∗ Q #()) -∗
      wp/cc stack_push q v @ b {{Q}};

    stack_pop_spec b Q q v vs :
      ▷ is_stack q (v :: vs) -∗
      ▷ (is_stack q vs -∗ Q v) -∗
      wp/cc stack_pop q @ b {{Q}};

  }.

  Section instance.

    Definition stack_create' : val := λ: <>, ref list_nil.
    Definition stack_push' : val := λ: "s" "x",
      "s" <- list_cons "x" (Load "s").
    Definition stack_pop' : val := λ: "s",
      match: (Load "s") with
        InjL <> => assert: #false
      | InjR "args" =>
          let: "x" := Fst "args" in
          let: "xs" := Snd "args" in
          "s" <- "xs";;
          "x"
      end%V.
    Definition is_stack' s vs := (∃ (r : loc) l,
      ⌜ s = #r ⌝ ∗ r ↦ l ∗ is_list l vs)%I.

    Program Definition stack_lib_instance : StackLib := {|
      stack_create := stack_create';
      stack_push := stack_push';
      stack_pop := stack_pop';
      is_stack := is_stack';
    |}.
    Next Obligation.
      iIntros "% % HQ". rw /stack_create'.
      wpcc_pures. iApply wpcc_alloc.
      iIntros "!> %r Hr _". iApply wpcc_value.
      iApply "HQ". iExists r, list_nil. iFrame.
      iSplit; [done|]. by iApply list_nil_spec.
    Qed.
    Next Obligation.
      iIntros "% % % % % Hs HQ".
      rw /stack_push'. wpcc_pures.
      iDestruct "Hs" as "(% & % & -> & Hr & Hl)".
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
      iIntros "% % % % % Hs HQ".
      rw /stack_pop'. wpcc_pures.
      iDestruct "Hs" as "(% & % & -> & Hr & Hl)".
      iApply (wpcc_load with "Hr").
      iIntros "!> Hr".
      iDestruct "Hl" as "[%l' [-> Hl']]". wpcc_pures.
      iApply (wpcc_store with "Hr").
      iIntros "!> Hr". wpcc_pures.
      iApply "HQ". iExists r, l'. by iFrame.
    Qed.

  End instance.

End stack_lib.
