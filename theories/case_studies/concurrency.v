(* concurrency.v *)

From iris.proofmode Require Import base tactics classes.
From callcc_logics Require Import logic state proofmode.
From callcc_logics.case_studies Require Import queue_lib.


(* ------------------------------------------------------------------------- *)
(* Implementation. *)

Section implementation.
  Context `{!stateGS Σ} `{QueueLib}.

  Definition with_coop : val := (λ: "main", call/1cc0: "return",
    let: "q" := queue_create #() in
    let: "next" := λ: <>,
      if: queue_empty "q" then
        throw: "return" #()
      else
        let: "k" := queue_take "q" in throw: "k" #()
    in
    let: "fork" := λ: "task", (call/1cc0: "k",
      queue_add "q" "k";;
      "task" #();;
      "next" #()
    )
    in
    let: "yield" := λ: <>, (call/1cc0: "k",
      queue_add "q" "k";;
      "next" #()
    )
    in
    "main" "fork" "yield";;
    "next" #()
  )%V.

End implementation.


(* ------------------------------------------------------------------------- *)
(* Specification. *)

Section specification.
  Context `{QueueLib}.

  Definition with_coop_spec : iProp Σ := (∀ (main : val),
    (∀ (fork yield : val) (I : iProp Σ),

      (* Specification of [fork] (assumption). *)
      (□ ∀ (task : val),
         I -∗
         (I -∗ wp/cc task #() @ WithFrame {{_, I}}) -∗
         wp/cc fork task @ WithFrame {{_, I}}
      ) -∗

      (* Specification of [yield] (assumption). *)
      (□ (I -∗ wp/cc yield #() @ WithFrame {{_, I}})) -∗

      (* Specification of [main] (obligation). *)
      I -∗ wp/cc main fork yield @ WithFrame {{_, I}}

    ) -∗

    wp/cc with_coop main @ WithFrame {{_, True}}
  )%I.

End specification.


(* ------------------------------------------------------------------------- *)
(* Verification. *)

Section verification.
  Context `{QueueLib}.

  Definition inv_pre return' q (inv : iProp Σ) : iProp Σ :=
    (∃ ks,
      isCont return' (λ _, True)%I ∗
      is_queue q ks ∗ [∗ list] k ∈ ks, ▷ isCont k (λ _, inv)
    )%I.

  Local Instance inv_pre_contractive return' q : Contractive (inv_pre return' q).
  Proof.
    rewrite /inv_pre => n inv inv' IH.
    do 7 f_equiv. f_contractive. rewrite /isCont /isCont_gen. do 5 f_equiv.
    by apply IH.
  Qed.
  Definition inv_def return' q : iPropO Σ :=
    fixpoint (inv_pre return' q).
  Definition inv_aux return' q : seal (inv_def return' q). by eexists. Qed.
  Definition inv return' q := (inv_aux return' q).(unseal).
  Definition inv_eq return' q : inv return' q = inv_def return' q :=
    (inv_aux return' q).(seal_eq).
  Global Lemma inv_unfold return' q :
    inv return' q ⊣⊢ inv_pre return' q (inv return' q).
  Proof. by rewrite inv_eq /inv_def;
    apply (fixpoint_unfold (inv_pre return' q)). Qed.

  Lemma inv_intro return' q :
    inv_pre return' q (inv return' q) ⊢ inv return' q.
  Proof. iIntros "?". by rewrite -inv_unfold. Qed.
 
  Lemma with_coop_correct : ⊢ with_coop_spec.
  Proof.
    iIntros "%main Hmain". rewrite /with_coop. wpcc_pures.
    iApply wpcc_call1cc0.
    iIntros "!> %return' Hreturn". simpl.
    iApply (wpcc_bind _ [_]).
    iApply queue_create_spec.
    iIntros "!> %q Hq".
    wpcc_pures.

    (* Verification of [next]. *)
    iAssert (□ ∀ Q,
      inv return' q -∗
      wp/cc if: queue_empty q then
            return' #()
          else
            let: "k" := queue_take q in "k" #()
          @ WithFrame {{Q}}
    )%I as "#Hnext".
    { iIntros "!> %Q Hinv".
      iEval (rewrite inv_unfold) in "Hinv".
      iDestruct "Hinv" as "[%ks' (Hreturn' & Hq & Hks')]".
      iApply (wpcc_bind _ [_]).
      iApply (queue_empty_spec with "Hq").
      iIntros "!> Hq". simpl.
      destruct (ks') as [|k ks] eqn:Heq.
      + simpl. wpcc_pures.
        by iApply (wpcc_cont with "Hreturn'").
      + rewrite length_cons.
        destruct (k :: ks) as [|k'' ks'' _] eqn:Heq' using rev_ind; first done.
        rewrite big_sepL_app. simpl. wpcc_pures.
        iDestruct "Hks'" as "(Hks''&Hk''&_)".
        iApply (wpcc_bind _ [_]).
        iApply (queue_take_spec with "Hq"). iIntros "!> Hq". wpcc_pures.
        iApply (wpcc_cont with "Hk''").
        iEval (rewrite inv_unfold). iExists ks''.
        iFrame.
        iApply big_sepL_mono; last done.
        by iIntros "% % _ ? !>".
    }

    iApply (wpcc_bind _ [_]).
    iApply (wpcc_mono with "[Hmain Hq Hreturn]");
    first iApply ("Hmain" $! _ _ (inv return' q));
    cycle 2.
    { rewrite {-1}inv_unfold. iExists []. by iFrame. }
    { simpl.
      iIntros "% Hinv !>". wpcc_pures.
      by iApply ("Hnext" with "Hinv"). }
    { iIntros "!> %task Hinv Htask". wpcc_pures.
      iApply wpcc_call1cc0. iIntros "!> %k Hk". simpl.
      iEval (rewrite inv_unfold) in "Hinv".
      iDestruct "Hinv" as "[%ks' (Hreturn' & Hq & Hks')]".
      iApply (wpcc_bind _ [_]).
      iApply (queue_add_spec with "Hq").
      iIntros "!> Hq". wpcc_pures.
      iApply (wpcc_bind _ [_]).
      iApply (wpcc_mono with "[Htask Hk Hq Hks' Hreturn']").
      { iApply "Htask". iEval (rewrite inv_unfold).
        iExists (k :: ks'). iFrame.
        iFrame. iApply big_sepL_mono; last done.
        by iIntros "% % _ ? !>".
      }
      simpl.
      iIntros "% Hinv !>". wpcc_pures.
      by iApply ("Hnext" with "Hinv").
    }
    { iIntros "!> Hinv". wpcc_pures.
      iApply wpcc_call1cc0. iIntros "!> %k Hk". simpl.
      iEval (rewrite inv_unfold) in "Hinv".
      iDestruct "Hinv" as "[%ks' (Hreturn' & Hq & Hks')]".
      iApply (wpcc_bind _ [_]).
      iApply (queue_add_spec with "Hq").
      iIntros "!> Hq". wpcc_pures.
      iApply "Hnext".
      iEval (rewrite (inv_unfold return' q)).
      iFrame. iApply big_sepL_mono; last done.
      by iIntros "% % _ ? !>".
    }  
  Qed.

End verification.
