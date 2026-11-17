(* logic.v *)

From iris.proofmode Require Export proofmode.
From iris.prelude Require Import options.

From iris.algebra Require Import list.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting.
From iris.base_logic.lib Require Import invariants.

From callcc_logics Require Import syntax notation semantics
                          iris_instantiation lifting.

From callcc_logics Require Export tactics state class_instances.

Import uPred.


(* ========================================================================= *)
(** Weakest Precondition. *)

Section weakestpre.
  Context `{!stateGS Σ}.

  Inductive wp_flavour := NoFrame | WithFrame.

  Definition wp_flavour_to_bool : wp_flavour → bool :=
  λ f, match f with WithFrame => false | NoFrame => true end.
  Coercion wp_flavour_to_bool : wp_flavour >-> bool.

  Definition wpcc (gp : val → Prop) (f : wp_flavour) :
    coPset -d> expr -d> (val -d> iProp Σ) -d> iProp Σ :=
    (λ E e Φ,
      ∀ k R,
      (match f with WithFrame => R | _ => True end) -∗
      (□ ∀ v, Φ v ∗ (match f with WithFrame => R | _ => True end) -∗ WP fill k v {{ w, ⌜ gp w ⌝ }}) ={E,⊤}=∗
      WP fill k e {{ w, ⌜ gp w ⌝ }}
    )%I.

  (* ----------------------------------------------------------------------- *)
  (* Non-expansiveness. *)

  Global Instance wpcc_ne gp f E e : NonExpansive (wpcc gp f E e).
  Proof. rw /wpcc => n Q Q' Hne. by repeat f_equiv. Qed.

End weakestpre.


(* ========================================================================= *)
(** Hoare Triples. *)

Section triples.
  Context `{!stateGS Σ}.

  Inductive mode := Many | Once.

  Definition mode_to_bool : mode → bool :=
  λ m, match m with Many => true | Once => false end.
  Coercion mode_to_bool : mode >-> bool.

  Definition triplecc (gp : val → Prop) (m : mode) (f : wp_flavour) :
    iProp Σ -d> coPset -d> expr -d> (val -d> iProp Σ) -d> iProp Σ
  :=
    (λ P E e Φ, □?m (P -∗ wpcc gp f E e Φ))%I.

End triples.


(* ========================================================================= *)
(** Notation. *)

(** The trivial global postcondition used by the default notation. *)
Definition gpTrue : val → Prop := λ _, True.

(* Explicit global postcondition [gp]. *)
Notation "'wp/cc' ⟨ gp ⟩ e  @  f ;  E  {{ R } }" :=
  (wpcc gp f E e%E R%I)
  (at level 0, gp, f, E, e, R at level 200, only parsing) : bi_scope.
Notation "'wp/cc' ⟨ gp ⟩ e  @  f ;  E  {{ y , Q } }" :=
  (wpcc gp f E e%E (λ y, Q)%I)
  (at level 0, gp, f, E, e, Q at level 200, y at level 200,
  format "'[hv' 'wp/cc' ⟨ gp ⟩  e  '/' @  f ;  E  '/' {{  '[' y  ,  '/' Q  ']' } } ']'") : bi_scope.

Notation "'wp/cc' ⟨ gp ⟩ e  @  f   {{ R } }" :=
  (wpcc gp f ⊤ e%E R%I)
  (at level 0, gp, f, e, R at level 200, only parsing) : bi_scope.
Notation "'wp/cc' ⟨ gp ⟩ e  @  f   {{ y , Q } }" :=
  (wpcc gp f ⊤ e (λ y, Q)%I)
  (at level 0, gp, f, e, Q at level 200, y at level 200,
  format "'[hv' 'wp/cc' ⟨ gp ⟩  e  '/' @  f '/'  {{  '[' y  ,  '/' Q  ']' } } ']'") : bi_scope.

(* Default notation: the global postcondition is [gpTrue] (i.e. [λ _, True]).
   Declared last so that it is preferred by the pretty-printer. *)
Notation "'wp/cc' e  @  f ;  E  {{ R } }" :=
  (wpcc gpTrue f E e%E R%I)
  (at level 0, f, E, e, R at level 200, only parsing) : bi_scope.
Notation "'wp/cc' e  @  f ;  E  {{ y , Q } }" :=
  (wpcc gpTrue f E e%E (λ y, Q)%I)
  (at level 0, f, E, e, Q at level 200, y at level 200,
  format "'[hv' 'wp/cc'  e  '/' @  f ;  E  '/' {{  '[' y  ,  '/' Q  ']' } } ']'") : bi_scope.

Notation "'wp/cc' e  @  f   {{ R } }" :=
  (wpcc gpTrue f ⊤ e%E R%I)
  (at level 0, f, e, R at level 200, only parsing) : bi_scope.
Notation "'wp/cc' e  @  f   {{ y , Q } }" :=
  (wpcc gpTrue f ⊤ e (λ y, Q)%I)
  (at level 0, f, e, Q at level 200, y at level 200,
  format "'[hv' 'wp/cc'  e  '/' @  f '/'  {{  '[' y  ,  '/' Q  ']' } } ']'") : bi_scope.

Notation "{{ P } } e  @  f  ;  m  ;  E {{ Φ } }" := (triplecc gpTrue m f P%I E e%E Φ%I)
  (at level 20, P, e, Φ at level 200,
   format "{{  P  } }  e  @   f  ;  m  ;  E  {{  Φ  } }") : stdpp_scope.
Notation "{{ P } } e  @  f  ;  m  ;  E {{ v , Q } }" := (triplecc gpTrue m f P%I E e%E (λ v, Q)%I)
  (at level 20, P, e, Q at level 200, v at level 200,
   format "{{  P  } }  e  @  f  ;  m  ;  E  {{  v ,  Q  } }") : stdpp_scope.


(* ========================================================================= *)
(** Reasoning Rules. *)

Section reasoning_rules.
  Context `{!stateGS Σ}.
  (* The rules below are polymorphic in the global postcondition [gp]. *)
  Context {gp : val → Prop}.

  Definition isCont_gen (gp' : val → Prop)
      (k : val) (Φ : val → iProp Σ) : iProp Σ :=
    ∀ Φ' v, Φ v -∗ wp/cc⟨ gp' ⟩ (k v) @ WithFrame {{Φ'}}.

  Definition isCont : val → (val → iProp Σ) → iProp Σ :=
    isCont_gen gpTrue.

  Definition isKont_gen (gp' : val → Prop)
      (k : val) (Φ : val → iProp Σ) : iProp Σ :=
    □ ∀ Φ' v, Φ v -∗ wp/cc⟨ gp' ⟩ (k v) @ WithFrame {{Φ'}}.

  Definition isKont : val → (val → iProp Σ) → iProp Σ :=
    isKont_gen gpTrue.

  Lemma wpcc_sound (gp' : val → Prop) e f :
    wpcc gp' f ⊤ e (λ v, ⌜ gp' v ⌝)%I -∗
    WP e {{ v, ⌜ gp' v ⌝ }}.
  Proof.
    iIntros "He". iApply fupd_wp. iApply ("He" $! [] True%I);
    destruct f; simpl; try done;
    iIntros "!> % [H _]"; iApply wp_value; iApply "H".
  Qed.

  Lemma wpcc_with_frame f e Φ :
    wp/cc ⟨gp⟩ e @ WithFrame {{ Φ }} -∗
    wp/cc ⟨gp⟩ e @ f {{ Φ }}.
  Proof.
    iIntros "He %k %R HR #Hk !>". iApply fupd_wp.
    by iApply ("He" with "HR Hk").
  Qed.

  Lemma wpcc_no_frame f e Φ :
    (∀ R, R -∗ wp/cc ⟨gp⟩ e @ NoFrame {{ y, Φ y ∗ R }}) -∗
    wp/cc ⟨gp⟩ e @ f {{ Φ }}.
  Proof.
    iIntros "He %k %R HR #Hk".
    iSpecialize ("He" with "HR").
    iApply ("He" $! k True%I with "[//]").
    iIntros "!> % [[? ?] _]". iApply "Hk".
    by iFrame.
  Qed.

  Lemma wpcc_pure_step f e e' (φ : Prop) n R :
    φ →
    PureExecEctx φ n e e' →
    ▷^n (£ n -∗ wp/cc ⟨gp⟩ e' @ f {{R}}) ⊢ wp/cc ⟨gp⟩ e @ f {{R}}.
  Proof.
    iIntros (Hφ Hexec).
    iIntros "Hwp %k %P HP #Hk".
    iApply (wp_pure_step_later _ _ (fill k e) (fill k e') φ n).
    { by apply PureExecEctx_PureExec, PureExecEctx_fill. }
    { by apply Hφ. }
    { iModIntro. iIntros "!> H".
      iApply fupd_wp.
      iSpecialize ("Hwp" with "H").
      by iApply ("Hwp" $! k with "HP").
    }
  Qed.

  Lemma wpcc_value (v : val) f R : R v ⊢ wp/cc ⟨gp⟩ v @ f {{ R }}.
  Proof. iIntros "HR %k %P HP #Hk !>". iApply "Hk". by iFrame. Qed.

  Lemma wpcc_bind f k e Φ :
    wp/cc ⟨gp⟩ e @ f {{ v, wp/cc ⟨gp⟩ (fill k v) @ f {{ Φ }} }} -∗
    wp/cc ⟨gp⟩ (fill k e) @ f {{ Φ }}.
  Proof.
    iIntros "He %k' %R HR #Hk'". rw -fill_app.
    iApply ("He" with "HR").
    iIntros "!> % [Hv HR]". iApply fupd_wp. rw fill_app.
    by iApply ("Hv" with "HR").
  Qed.

  Lemma wpcc_mono f E e Φ Φ' :
    wp/cc ⟨gp⟩ e @ f ; E {{ Φ }} -∗
    (□?f ∀ v, Φ v ={⊤}=∗ Φ' v) -∗
    wp/cc ⟨gp⟩ e @ f ; E {{ Φ' }}.
  Proof.
    destruct f; simpl.
    - iIntros "He #HΦ' %k' % _ #Hk'".
      iApply ("He" $! k' True%I with "[//]").
      iIntros "!> % [Hv _]". iApply fupd_wp. iApply "Hk'".
      iMod ("HΦ'" with "Hv") as "HΦ". by iFrame.
    - iIntros "He HΦ' %k' %P HP #Hk'".
      iApply ("He" $! k' (P ∗ (∀ v, Φ v ={⊤}=∗ Φ' v))%I with "[$]").
      iIntros "!> % (Hv & HP & HΦ')". iApply fupd_wp. iApply "Hk'".
      iMod ("HΦ'" with "Hv") as "HΦ". by iFrame.
  Qed.

  Lemma wpcc_frame E e Φ R :
    wp/cc ⟨gp⟩ e @ WithFrame; E {{ Φ }} -∗
    R -∗
    wp/cc ⟨gp⟩ e @ WithFrame; E {{ v, Φ v ∗ R }}.
  Proof.
    iIntros "Hwp HR %k %P HP #Hk".
    iApply ("Hwp" $! k (P ∗ R)%I with "[$]").
    iIntros "!> % (Hv & HP & HR)". iApply "Hk". by iFrame.
  Qed.

  Lemma wpcc_kont f k v Φ Φ' :
    isKont_gen gp k Φ -∗ Φ v -∗ wp/cc ⟨gp⟩ (k v) @ f {{ Φ' }}.
  Proof.
    iIntros "#Hk Hv".
    destruct f; [iApply wpcc_with_frame|];
    by iApply "Hk".
  Qed.

  Lemma wpcc_kont' f k v Φ :
    isKont_gen gp k Φ -∗ Φ v -∗ wp/cc ⟨gp⟩ (k v) @ f {{ _, False }}.
  Proof. apply wpcc_kont. Qed.

  Lemma wpcc_cont f k v Φ Φ' :
    isCont_gen gp k Φ -∗ Φ v -∗ wp/cc ⟨gp⟩ (k v) @ f {{ Φ' }}.
  Proof.
    iIntros "Hk Hv".
    destruct f; [iApply wpcc_with_frame|];
    by iApply "Hk".
  Qed.

  Lemma wpcc_cont' f k v Φ :
    isCont_gen gp k Φ -∗ Φ v -∗ wp/cc ⟨gp⟩ (k v) @ f {{ _, False }}.
  Proof. apply wpcc_cont. Qed.

  Lemma wpcc_call1cc0 x e Φ :
    ▷ (∀ k, isCont_gen gp k Φ -∗ wp/cc ⟨gp⟩ (subst x k e) @ WithFrame {{ _, False }}) -∗
    wp/cc ⟨gp⟩ (call/1cc0: x, e)%E @ WithFrame {{ Φ }}.
  Proof.
    iIntros "Hwpcc %k %R HR #Hk". iModIntro.
    iApply wp_call1cc0.
    iIntros "!> %r Hr". iApply fupd_wp.
    iSpecialize ("Hwpcc" with "[Hk Hr HR]").
    { iIntros "%Φ' %y Hy %k' %P HP #Hk' !>".
      iApply (wp_cont with "Hr").
      iApply "Hk".
      by iFrame.
    }
    iApply ("Hwpcc" $! [RunThenAbortCtx] True%I with "[//]").
    by iIntros "!> % [? _]".
  Qed.

  Lemma wpcc_call1cc x e Φ :
    ▷ (∀ k, isCont_gen gp k Φ -∗ wp/cc ⟨gp⟩ (subst x k e) @ WithFrame {{ y, Φ y ∗ isCont_gen gp k Φ }}) -∗
    wp/cc ⟨gp⟩ (call/1cc: x, e)%E @ WithFrame {{ Φ }}.
  Proof.
    iIntros "Hwpcc".
    iApply wpcc_call1cc0.
    iIntros "!> %k Hk". rw //= decide_True; last done.
    iApply (wpcc_bind _ [AppRCtx k]). simpl.
    iApply (wpcc_mono with "[Hwpcc Hk]").
    { by iApply "Hwpcc". }
    simpl.
    iIntros "%y [Hy Hk] !>".
    by iApply (wpcc_cont' with "Hk").
  Qed.

  Lemma wpcc_call1ccS x e Φ :
    ▷ (∀ k, isCont_gen gp k Φ -∗ wp/cc ⟨gp⟩ (subst x k e) @ NoFrame {{ Φ }}) -∗
    wp/cc ⟨gp⟩ (call/1cc*: x, e)%E @ NoFrame {{ Φ }}.
  Proof.
    iIntros "Hwpcc %k % _ #Hk". iModIntro.
    iApply wp_call1ccS.
    iIntros "!> %r Hr". iApply fupd_wp.
    iSpecialize ("Hwpcc" $! (ContV r k) with "[Hr]").
    { iIntros "%Φ' %y Hy %k' %P HP #Hk' !>".
      iApply (wp_cont with "Hr").
      iApply "Hk".
      by iFrame.
    }
    by iApply ("Hwpcc" $! k True%I with "[//]").
  Qed.

  Lemma wpcc_callcc x e Φ :
    ▷ (∀ k, isKont_gen gp k Φ -∗ wp/cc ⟨gp⟩ (subst x k e) @ NoFrame {{ Φ }}) -∗
    wp/cc ⟨gp⟩ (call/cc: x, e)%E @ NoFrame {{ Φ }}.
  Proof.
    iIntros "Hwpcc %k % _ #Hk". iModIntro.
    iApply wp_callcc.
    iNext. iApply fupd_wp.
    iSpecialize ("Hwpcc" $! (KontV k) with "[]").
    { iIntros "!> % %v Hv %k' %P HP #Hk' !>". iApply wp_kont.
      iNext. iApply "Hk". by iFrame.
    }
    iApply ("Hwpcc" $! k True%I with "[//]").
    iIntros "!> %y [Hy _]".
    iApply "Hk". by iFrame.
  Qed.

  Lemma wpcc_callcc_alt x e Φ :
    ▷ (∀ k, isCont_gen gp k Φ -∗ wp/cc ⟨gp⟩ (subst x k e) @ WithFrame {{ _, False }}) -∗
    wp/cc ⟨gp⟩ (call/cc: x, e)%E @ WithFrame {{ Φ }}.
  Proof.
    iIntros "Hwpcc %k %P HP #Hk".
    iApply wp_callcc.
    iIntros "!> !>". iApply fupd_wp.
    iSpecialize ("Hwpcc" $! (KontV k) with "[Hk HP]").
    { iIntros "%Φ' %y Hy %k' %R HR #Hk' !>".
      iApply wp_kont.
      iApply "Hk".
      by iFrame.
    }
    iApply ("Hwpcc" $! _ True%I with "[//]").
    by iIntros "!> % [? _]".
  Qed.

  (* ----------------------------------------------------------------------- *)
  (* State. *)

  Lemma wpcc_allocN f R k (n : Z) v :
    (0 < n)%Z →
    ▷ (∀ l,
        ([∗ list] i ∈ seq 0 (Z.to_nat n),
          (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤
         ) -∗
        wp/cc ⟨gp⟩ fill k #l @ f {{ R }}) -∗
    wp/cc ⟨gp⟩ fill k (AllocN #n v) @ f {{ R }}.
  Proof.
    iIntros "%Hgt_0 Hwpcc %k' % HP #Hk".
    iEval (rw -fill_app).
    iApply wp_allocN; first done.
    iIntros "!> !> %l Hpoints_to".
    iSpecialize ("Hwpcc" with "Hpoints_to").
    rw fill_app.
    iApply fupd_wp.
    by iApply ("Hwpcc" with "HP Hk").
  Qed.

  Lemma wpcc_alloc f R k v :
    ▷ (∀ l, l ↦ v -∗ meta_token l ⊤ -∗ wp/cc ⟨gp⟩ fill k #l @ f {{ R }}) -∗
    wp/cc ⟨gp⟩ fill k (ref v) @ f {{ R }}.
  Proof.
    iIntros "Hwpcc". iApply wpcc_allocN; first lia.
    iIntros "!> /=" (l) "[[Hl Hm] _]". rw Loc.add_0.
    iApply ("Hwpcc" with "Hl Hm").
  Qed.

  Lemma wpcc_load f R k l dq v :
    ▷ l ↦{dq} v -∗
    ▷ (l ↦{dq} v -∗ wp/cc ⟨gp⟩ fill k v @ f {{ R }}) -∗
    wp/cc ⟨gp⟩ fill k (! #l) @ f {{ R }}.
  Proof.
    iIntros "Hl Hwpcc %k' %P HP #Hk".
    iEval (rw -fill_app).
    iApply (wp_load with "Hl").
    iIntros "!> !> Hl". rw fill_app.
    iApply fupd_wp.
    iApply ("Hwpcc" with "Hl HP Hk").
  Qed.

  Lemma wpcc_store f R k l v w :
    ▷ l ↦ v -∗
    ▷ (l ↦ w -∗ wp/cc ⟨gp⟩ fill k #() @ f {{ R }}) -∗
    wp/cc ⟨gp⟩ fill k (#l <- w) @ f {{ R }}.
  Proof.
    iIntros "Hl Hwpcc %k' %P HP #Hk".
    iEval (rw -fill_app).
    iApply (wp_store with "Hl").
    iIntros "!> !> Hl". rw fill_app.
    iApply fupd_wp.
    iApply ("Hwpcc" with "Hl HP Hk").
  Qed.

  Lemma wpcc_free f R k l v :
    ▷ l ↦ v -∗
    ▷ wp/cc ⟨gp⟩ fill k #() @ f {{ R }} -∗
    wp/cc ⟨gp⟩ fill k (Free #l) @ f {{ R }}.
  Proof.
    iIntros "Hl Hwpcc %k' %P HP #Hk".
    iEval (rw -fill_app).
    iApply (wp_free with "Hl"). iIntros "!> !>".
    rw fill_app.
    iApply fupd_wp.
    iApply ("Hwpcc" with "HP Hk").
  Qed.


  (* Concurrency. *)

  (* The forked thread is verified against the trivial global postcondition
     [λ _, True] (not the ambient [gp]): it only has to be safe, matching what
     [wp_strong_adequacy] requires of forked threads. *)
  Lemma wpcc_fork k e f b' Φ :
    ▷ wpcc gpTrue b' ⊤ e fork_post -∗
    ▷ wp/cc ⟨gp⟩ fill k #() @ f {{ Φ }} -∗
    wp/cc ⟨gp⟩ fill k (Fork e) @ f {{ Φ }}.
  Proof.
    iIntros "He HΦ %k' %P HP #Hk !>".
    iEval (rw -fill_app).
    iApply (wp_fork with "[He]").
    { by iApply (wpcc_sound gpTrue). }
    iModIntro. iApply fupd_wp.
    iEval (rw fill_app).
    by iApply ("HΦ" with "HP Hk").
  Qed.

  Lemma wpcc_faa f R k1 l1 (n1 m1 : Z) :
    ▷ l1 ↦ #n1 -∗
    ▷ (l1 ↦ #(n1 + m1) -∗ wp/cc ⟨gp⟩ fill k1 #n1 @ f {{ R }}) -∗
    wp/cc ⟨gp⟩ fill k1 (FAA #l1 #m1) @ f {{ R }}.
  Proof.
    iIntros "Hl1 Hwpcc %k' %P HP #Hk !>".
    iEval (rw -fill_app).
    iApply (wp_faa with "Hl1").
    iIntros "!> Hl1".
    rw !fill_app.
    iApply fupd_wp. iApply ("Hwpcc" with "Hl1 HP Hk").
  Qed.

  Lemma wpcc_xchg f R k1 l1 v1 w1 :
    ▷ l1 ↦ v1 -∗
    ▷ (l1 ↦ w1 -∗ wp/cc ⟨gp⟩ fill k1 v1 @ f {{ R }}) -∗
    wp/cc ⟨gp⟩ fill k1 (Xchg #l1 w1) @ f {{ R }}.
  Proof.
    iIntros "Hl1 Hwpcc %k' %P HP #Hk !>".
    iEval (rw -fill_app).
    iApply (wp_xchg with "Hl1").
    iIntros "!> Hl1". rw fill_app.
    iApply fupd_wp.
    iApply ("Hwpcc" with "Hl1 HP Hk").
  Qed.

  Lemma wpcc_cmpxchg_fail f R k1 (l1 : loc) (u1 v1 w1 : val) :
    w1 ≠ u1 →
    vals_compare_safe w1 u1 →
    ▷ l1 ↦ w1 -∗
    ▷ (l1 ↦ w1 -∗ wp/cc ⟨gp⟩ fill k1 (w1, #false)%V @ f {{R}}) -∗
    wp/cc ⟨gp⟩ fill k1 (CmpXchg #l1 u1 v1) @ f {{R}}.
  Proof.
    iIntros "%Hneq %Hsafe Hl1 Hwpcc %k' %P HP #Hk".
    iEval (rw -fill_app).
    iApply (wp_cmpxchg_fail with "Hl1"); try done.
    iIntros "!> !> Hl1".
    rw fill_app.
    iApply fupd_wp. iApply ("Hwpcc" with "Hl1 HP Hk").
  Qed.

  Lemma wpcc_cmpxchg_suc f R k l (u v : val) :
    val_is_unboxed u →
    ▷ l ↦ u -∗
    ▷ (l ↦ v -∗ wp/cc ⟨gp⟩ fill k (u, #true)%V @ f {{ R }}) -∗
    wp/cc ⟨gp⟩ fill k (CmpXchg #l u v) @ f {{ R }}.
  Proof.
    iIntros "%Hsafe Hl1 Hwpcc %k' %P HP #Hk".
    iEval (rw -fill_app).
    iApply (wp_cmpxchg_suc with "Hl1"); try done. { by left. }
    iIntros "!> !> Hl1".
    rw !fill_app.
    iApply fupd_wp. iApply ("Hwpcc" with "Hl1 HP Hk").
  Qed.


  (* Support for Invariants. *)

  Definition closeInv N P : iProp Σ := ▷ P ={⊤ ∖ ↑N, ⊤}=∗ True.

  Lemma fupd_wpcc' f E1 E2 e R :
    (|={E1, E2}=> wp/cc ⟨gp⟩ e @ f ; E2 {{ R }}) ⊢ wp/cc ⟨gp⟩ e @ f ; E1 {{ R }}.
  Proof.
    iIntros "Hwpcc %k %P HP Hk".
    iMod "Hwpcc". 
    by iSpecialize ("Hwpcc" with "HP Hk").
  Qed.

  Lemma fupd_wpcc f e R : (|={⊤}=> wp/cc ⟨gp⟩ e @ f {{ R }}) ⊢ wp/cc ⟨gp⟩ e @ f {{ R }}.
  Proof. apply fupd_wpcc'. Qed.

  Lemma wpcc_inv_restore f N P e R :
    closeInv N P -∗
    ▷ P -∗
    wp/cc ⟨gp⟩ e @ f {{ R }} -∗
    wp/cc ⟨gp⟩ e @ f ; (⊤ ∖ ↑N) {{ R }}.
  Proof.
    iIntros "Hclose HP Hwpcc".
    iSpecialize ("Hclose" with "HP").
    iApply (fupd_wpcc' _ (⊤ ∖ ↑N) ⊤).
    iMod "Hclose" as "Hclose".
    by iModIntro.
  Qed.

  Lemma wpcc_inv_alloc f N P e R :
    ▷ P -∗
    (inv N P -∗ wp/cc ⟨gp⟩ e @ f {{ R }}) -∗
    wp/cc ⟨gp⟩ e @ f {{ R }}.
  Proof.
    iIntros "HP Hwpcc".
    iApply fupd_wpcc.
    iMod (inv_alloc N ⊤ P with "HP") as "Hinv".
    iModIntro.
    by iApply "Hwpcc".
  Qed.

  (* Note: We can relax 'StronglyAtomic' to 'WeaklyAtomic', but that
       would complicate the proof slightly. We would need to prove that
         irreducible e σ → WP e {{Φ}} -∗ ∃ v, e = Val v ∧ Φ v.
   *)
  Lemma wp_atomic_bind k E e Φ (Hatomic : AtomicEctx StronglyAtomic e) :
    WP e @ NotStuck; E {{ v, WP fill k (of_val v) @ NotStuck; E {{ Φ }} }}
    ⊢ WP fill k e @ NotStuck; E {{ Φ }}.
  Proof.
    iIntros "Hwp".
    rw wp_unfold /wp_pre.
    destruct (to_val e) as [v|] eqn:He.
    { apply of_to_val in He as ->. simpl. by iApply fupd_wp. }
    rw wp_unfold /wp_pre. simpl.
    rw fill_not_val He //=.
    iIntros (σ1 step κs n) "Hσ".
    iSpecialize ("Hwp" $! σ1 step κs n with "Hσ").
    iMod "Hwp" as "[%Hreducible Hwp]".
    iModIntro; iSplit.
    { iPureIntro. destruct Hreducible as (κ' & e' & σ' & efs & Hstep).
      simpl in *. destruct κ' => //=. simpl in Hstep.
      destruct (Hatomic [] _ _ _ _ Hstep) as (e2' & -> & He2' & Hstep_ectx).
      exists [], (fill k e2'), σ', efs. simpl.
      by apply Hstep_ectx.
    }
    iIntros "%e2 %σ2 %efs %κ %κs' %Hκs %Hstep Hcred".
    destruct κ => //=. simpl in Hstep.
    destruct (Hatomic _ _ _ _ _ Hstep) as (e2' & -> & He2' & Hstep_ectx).
    iSpecialize ("Hwp" $! e2' σ2 efs [] κs' with "[//] []").
    { by iPureIntro; apply (Hstep_ectx []). }
    iMod ("Hwp" with "Hcred") as "Hwp". iIntros "!>!>".
    iMod "Hwp". iModIntro. iApply (step_fupdN_wand with "Hwp"). iIntros "Hwp".
    iMod "Hwp" as "($ & H & $)". iModIntro.
    rw wp_unfold /wp_pre.
    destruct He2' as [v2' Hv2']. simpl.
    apply of_to_val in Hv2' as ->. simpl.
    by iApply fupd_wp.
  Qed.

  Lemma wpcc_atomic f (E : coPset) k e R (Hatomic : AtomicEctx StronglyAtomic e) :
    (|={⊤,E}=> WP e @ E {{ v, wp/cc ⟨gp⟩ fill k (of_val v) @ f ;  E {{ R }} }})%I -∗
    wp/cc ⟨gp⟩ fill k e @ f {{ R }}.
  Proof.
    iIntros "He %k' %P HP #Hk". iModIntro.
    rw -!fill_app.
    iApply wp_atomic_bind.
    iApply wp_atomic; auto.
    { simpl. by apply strongly_atomic_atomic, atomic_ectx_atomic. }
    iMod "He". iModIntro.
    iApply (wp_wand with "He").
    iIntros (v) "He".
    rw !fill_app.
    by iSpecialize ("He" with "HP Hk").
  Qed.

 Lemma wpcc_store_inv' f E R k1 l1 w1 :
    (|={⊤,E}=> ∃ v1,
      (▷ l1 ↦ v1) ∗
      (▷ (l1 ↦ w1 -∗ wp/cc ⟨gp⟩ fill k1 #() @ f ; E {{ R }}))
    ) -∗
    wp/cc ⟨gp⟩ fill k1 (#l1 <- w1) @ f {{ R }}.
  Proof.
    iIntros "Hwpcc".
    iApply (wpcc_atomic _ E). iMod "Hwpcc" as "[%v1 [Hl Hwpcc]]".
    iModIntro.
    iApply (wp_store [] with "Hl"). iNext. iIntros "Hl".
    iApply wp_value. by iApply "Hwpcc".
  Qed.

  Lemma wpcc_store_inv f N P k1 l1 (w1 : val) R :
    inv N P -∗
    (▷ P -∗ closeInv N P -∗
     ∃ v1,
     ▷ l1 ↦ v1 ∗
     ▷ (l1 ↦ w1 -∗ (wp/cc ⟨gp⟩ fill k1 #() @ f ; (⊤ ∖ ↑N) {{ R }}))) -∗
    wp/cc ⟨gp⟩ fill k1 (#l1 <- w1) @ f {{ R }}.
  Proof.
    iIntros "Hinv Hwpcc".
    iApply (wpcc_store_inv' _ (⊤ ∖ ↑N) R k1).
    iMod (inv_acc with "Hinv") as "[HP Hclose]"; auto.
    iModIntro.
    iDestruct ("Hwpcc" with "HP Hclose") as "[%v' [Hl Hwpcc]]".
    iExists v'. by iFrame.
  Qed.

  Lemma wpcc_load_inv' f K E l q R :
    (|={⊤,E}=> ∃ v',
      ▷(l ↦{q} v') ∗
      ▷(l ↦{q} v' -∗ (wp/cc ⟨gp⟩ fill K (of_val v') @ f ; E {{ R }})))%I
    ⊢ wp/cc ⟨gp⟩ fill K (! #l) @ f {{ R }}.
  Proof.
    iIntros "Hwpcc".
    iApply (wpcc_atomic _ E). iMod "Hwpcc" as "[%v [Hl Hwpcc]]". iModIntro.
    iApply (wp_load [] with "Hl"). iNext. iIntros "Hl".
    iApply wp_value. by iApply "Hwpcc".
  Qed.

  Lemma wpcc_load_inv f N P K l q R :
    inv N P -∗
    (▷ P -∗ closeInv N P -∗
     ∃ v',
     ▷ l ↦{q} v' ∗
     ▷ (l ↦{q} v' -∗ (wp/cc ⟨gp⟩ fill K (of_val v') @ f; (⊤ ∖ ↑N) {{ R }}))) -∗
    wp/cc ⟨gp⟩ fill K (! #l) @ f {{ R }}.
  Proof.
    iIntros "Hinv Hwpcc".
    iApply (wpcc_load_inv' _ _ (⊤ ∖ ↑N)).
    iMod (inv_acc with "Hinv") as "[HP Hclose]"; auto.
    iModIntro.
    iDestruct ("Hwpcc" with "HP Hclose") as "[%v' [Hl Hwpcc]]".
    iExists v'. by iFrame.
  Qed.

  Lemma wpcc_faa_inv' f k1 E l1 (m1 : Z) R :
    (|={⊤,E}=> ∃ (n1 : Z),
      ▷ l1 ↦ #n1 ∗
      ▷ (l1 ↦ #(n1 + m1) -∗ (wp/cc ⟨gp⟩ fill k1 #n1 @ f ; E {{ R }})))%I
    ⊢ wp/cc ⟨gp⟩ fill k1 (FAA #l1 #m1) @ f {{ R }}.
  Proof.
    iIntros "Hwpcc".
    iApply (wpcc_atomic _ E). iMod "Hwpcc" as "[%n1 [Hl Hwpcc]]". iModIntro.
    iApply (wp_faa [] with "Hl"). iNext. iIntros "Hl".
    iApply wp_value. by iApply "Hwpcc".
  Qed.

  Lemma wpcc_faa_inv f N P k1 l1 (m1 : Z) R :
    inv N P -∗
    (▷ P -∗ closeInv N P -∗
     ∃ (n1 : Z),
     ▷ l1 ↦ #n1 ∗
     ▷ (l1 ↦ #(n1 + m1) -∗ (wp/cc ⟨gp⟩ fill k1 #n1 @ f ; (⊤ ∖ ↑N) {{ R }}))) -∗
    wp/cc ⟨gp⟩ fill k1 (FAA #l1 #m1) @ f {{ R }}.
  Proof.
    iIntros "Hinv Hwpcc".
    iApply (wpcc_faa_inv' _ _ (⊤ ∖ ↑N)).
    iMod (inv_acc with "Hinv") as "[HP Hclose]"; auto.
    iModIntro.
    iDestruct ("Hwpcc" with "HP Hclose") as "[%n1 [Hl Hwpcc]]".
    iExists n1. by iFrame.
  Qed.

  Lemma wpcc_cmpxchg_inv' f E k l v1 v2 R :
    (|={⊤,E}=> ∃ v : val,
      ⌜ vals_compare_safe v v1 ⌝ ∗
      ▷ l ↦ v ∗
      (▷ (⌜ v = v1 ⌝ -∗ l ↦ v2 -∗ wp/cc ⟨gp⟩ fill k (PairV v1 #true) @ f ; E {{ R }}) ∧
       ▷ (⌜ v ≠ v1 ⌝ -∗ l ↦ v -∗ wp/cc ⟨gp⟩ fill k (PairV v #false) @ f ; E {{ R }}))
    )
    ⊢ wp/cc ⟨gp⟩ fill k (CmpXchg #l v1 v2) @ f {{ R }}.
  Proof.
    iIntros "Hwpcc".
    iApply (wpcc_atomic _ E). iMod "Hwpcc" as "[%v (% & Hl & Hwpcc)]". iModIntro.
    destruct (decide (v = v1)) as [-> | Hneq].
    - iApply (wp_cmpxchg_suc [] with "Hl"); try done.
      iIntros "!> Hl". simpl. iApply wp_value.
      iDestruct "Hwpcc" as "[Hwpcc _]".
      by iApply "Hwpcc".
    - iApply (wp_cmpxchg_fail [] with "Hl"); try done.
      iIntros "!> Hl". simpl. iApply wp_value.
      iDestruct "Hwpcc" as "[_ Hwpcc]".
      by iApply ("Hwpcc" with "[] Hl").
  Qed.

  Lemma wpcc_cmpxchg_inv f N P k l v1 v2 R :
    inv N P -∗
    (▷ P -∗ closeInv N P -∗
      ∃ v : val,
      ⌜ vals_compare_safe v v1 ⌝ ∗
      ▷ l ↦ v ∗
      (▷ (⌜ v = v1 ⌝ -∗ l ↦ v2 -∗ wp/cc ⟨gp⟩ fill k (PairV v1 #true) @ f ; (⊤ ∖ ↑N) {{ R }}) ∧
       ▷ (⌜ v ≠ v1 ⌝ -∗ l ↦ v -∗ wp/cc ⟨gp⟩ fill k (PairV v #false) @ f ; (⊤ ∖ ↑N) {{ R }}))
    ) -∗
    wp/cc ⟨gp⟩ fill k (CmpXchg #l v1 v2) @ f {{ R }}.
  Proof.
    iIntros "Hinv Hwpcc".
    iApply (wpcc_cmpxchg_inv' _ (⊤ ∖ ↑N)).
    iMod (inv_acc with "Hinv") as "[HP Hclose]"; auto.
    iModIntro.
    iDestruct ("Hwpcc" with "HP Hclose") as "[%v (% & Hl & Hwpcc)]".
    iExists v. by iFrame.
  Qed.

End reasoning_rules.


(* ========================================================================= *)
(** Hoare-Style Reasoning Rules. *)

Section reasoning_rules_with_triples.
  Context `{!stateGS Σ}.

  Global Instance triplecc_many_pers f (e : expr) P Φ :
    Persistent ({{ P }} e @ f ; Many ; ⊤ {{ Φ }}).
  Proof. unfold triplecc; simpl; by apply _. Qed.

  Lemma triplecc_return f (m : mode) (v : val) P Φ :
    □?m (P -∗ Φ v) -∗ {{ P }} v @ f ; m ; ⊤ {{ Φ }}.
  Proof.
    rw /triplecc; destruct m; simpl.
    - iIntros "#HΦ !> HP". iApply wpcc_value. by iApply "HΦ".
    - iIntros "HΦ HP". iApply wpcc_value. by iApply "HΦ".
  Qed.

  Lemma triplecc_bind f (m : mode) (e : expr) (k : ectx) P Φ Φ' :
    {{ P }} e @ f ; m ; ⊤ {{ Φ }} -∗
    (∀ v, {{ Φ v }} fill k v @ f ; (if f is NoFrame then Many else m) ; ⊤ {{ Φ' }}) -∗
    {{ P }} fill k e @ f ; m ; ⊤ {{ Φ' }}.
  Proof.
    rw /triplecc; destruct m; simpl.
    - rw (_ : (if f is NoFrame then Many else Many) = Many); [|by destruct f]. simpl.
      iIntros "#He #Hk !> HP". iApply wpcc_bind.
      iApply (wpcc_mono with "[HP]").
      { by iApply "He". }
      destruct f; simpl;
      iIntros "%"; [iModIntro|]; iIntros "Hv !>"; by iApply "Hk".
    - iIntros "He Hk HP". iApply wpcc_bind.
      iApply (wpcc_mono with "[He HP]").
      { by iApply "He". }
      destruct f; simpl;
      iIntros "%"; [iDestruct "Hk" as "#Hk"; iModIntro|];
      iIntros "Hv !>"; by iApply "Hk".
  Qed.

  Lemma triplecc_bind_many f (m : mode) (e : expr) (k : ectx) P Φ Φ' :
    {{ P }} e @ f ; Many ; ⊤ {{ Φ }} -∗
    (∀ v, {{ Φ v }} fill k v @ f ; Many ; ⊤ {{ Φ' }}) -∗
    {{ P }} fill k e @ f ; Many ; ⊤ {{ Φ' }}.
  Proof.
    iIntros "#He #Hk". iApply (triplecc_bind _ Many with "He").
    by rw (_ : (if f is NoFrame then Many else Many) = Many); [|by destruct f].
  Qed.

  Lemma triplecc_callcc (m : mode) (x : string) (e : expr) P Φ :
    (∀ k, {{ P ∗ isKont k Φ }} (subst x k e)%E @ NoFrame ; m ; ⊤ {{ Φ }}) -∗
    {{ P }} (call/cc: x, e)%E @ NoFrame ; m ; ⊤ {{ Φ }}.
  Proof.
    rw /triplecc; destruct m; simpl.
    - iIntros "#He !> HP". iApply wpcc_callcc.
      iIntros "!> %k #Hk". iApply "He". by iFrame.
    - iIntros "He HP". iApply wpcc_callcc.
      iIntros "!> %k #Hk". iApply "He". by iFrame.
  Qed.

  Lemma triplecc_callcc_alt (m : mode) (x : string) (e : expr) P Φ :
    (∀ k, {{ P ∗ isCont k Φ }} (subst x k e)%E @ WithFrame ; m ; ⊤ {{ _, False }}) -∗
    {{ P }} (call/cc: x, e)%E @ WithFrame ; m ; ⊤ {{ Φ }}.
  Proof.
    rw /triplecc; destruct m; simpl.
    - iIntros "#He !> HP". iApply wpcc_callcc_alt.
      iIntros "!> %k Hk". iApply "He". by iFrame.
    - iIntros "He HP". iApply wpcc_callcc_alt.
      iIntros "!> %k Hk". iApply "He". by iFrame.
  Qed.

  Lemma triplecc_call1cc0 (m : mode) (x : string) (e : expr) P Φ :
    (∀ k, {{ P ∗ isCont k Φ }} (subst x k e)%E @ WithFrame ; m ; ⊤ {{ _, False }}) -∗
    {{ P }} (call/1cc0: x, e)%E @ WithFrame ; m ; ⊤ {{ Φ }}.
  Proof.
    rw /triplecc; destruct m; simpl.
    - iIntros "#He !> HP". iApply wpcc_call1cc0.
      iIntros "!> %k Hk". iApply "He". by iFrame.
    - iIntros "He HP". iApply wpcc_call1cc0.
      iIntros "!> %k Hk". iApply "He". by iFrame.
  Qed.

  Lemma triplecc_kont f (m : mode) (k v : val) Φ :
    ⊢ {{ isKont k Φ ∗ Φ v }} (k v)%E @ f ; m ; ⊤ {{ _, False }}.
  Proof.
    rw /triplecc; destruct m; simpl; [iModIntro|];
    iIntros "[#Hk Hv]"; by iApply (wpcc_kont with "Hk Hv").
  Qed.

  Lemma triplecc_cont f (m : mode) (k v : val) Φ :
    ⊢ {{ isCont k Φ ∗ Φ v }} (k v)%E @ f ; m ; ⊤ {{ _, False }}.
  Proof.
    rw /triplecc; destruct m; simpl; [iModIntro|];
    iIntros "[Hk Hv]"; by iApply (wpcc_cont with "Hk Hv").
  Qed.

  Lemma triplecc_frame (m : mode) (e : expr) P R Φ :
    {{ P }} e @ WithFrame ; m ; ⊤ {{ Φ }} -∗
    {{ P ∗ R }} e @ WithFrame ; m ; ⊤ {{ y, Φ y ∗ R }}.
  Proof.
    rw /triplecc; destruct m; simpl;
    [iIntros "#Hk !> [HP HR]"|iIntros "Hk [HP HR]"];
    iApply (wpcc_frame with "[HP Hk] HR"); by iApply "Hk".
  Qed.

  Lemma triplecc_with_frame f (m : mode) (e : expr) P Φ :
    {{ P }} e @ WithFrame ; m ; ⊤ {{ Φ }} -∗
    {{ P }} e @ f ; m ; ⊤ {{ Φ }}.
  Proof.
    rw /triplecc; destruct f; simpl; [|by iIntros "?"].
    destruct m; simpl; [iIntros "#He !> HP"|iIntros "He HP"];
    iApply wpcc_with_frame; by iApply "He".
  Qed.

  Lemma triplecc_no_frame f (m : mode) (e : expr) P Φ :
    (∀ R, {{ P ∗ R }} e @ NoFrame ; m ; ⊤ {{ y, Φ y ∗ R }}) -∗
    {{ P }} e @ f ; m ; ⊤ {{ Φ }}.
  Proof.
    rw /triplecc; destruct f; simpl;
    destruct m; simpl;
    try (iIntros "#He !>"); try iIntros "He";
    iIntros "HP"; iApply wpcc_no_frame;
    iIntros "%R HR"; iApply "He"; by iFrame.
  Qed.

  Lemma triplecc_consequence f (m : mode) (e : expr) P P' Φ Φ' :
    □?m (P' -∗ P) -∗
    {{ P }} e @ f ; m ; ⊤ {{ Φ }} -∗
    □?(if f is NoFrame then Many else m) (∀ y, Φ y -∗ Φ' y) -∗
    {{ P' }} e @ f ; m ; ⊤ {{ Φ' }}.
  Proof.
    rw /triplecc; destruct m; simpl.
    - rw (_ : (if f is NoFrame then true else true) = true); [|by destruct f]. simpl.
      iIntros "#HP #He #HΦ' !> HP'".
      iApply (wpcc_mono with "[HP He HP']").
      { iApply "He"; by iApply "HP". }
      destruct f; simpl; [iModIntro|]; iIntros "% Hv !>";
      by iApply "HΦ'".
    - destruct f; simpl;
      iIntros "HP He"; [iIntros "#HΦ'"|iIntros "HΦ'"];
      iIntros "HP'";
      iApply (wpcc_mono with "[HP He HP']"); simpl;
      try (iApply "He"; by iApply "HP"); try iModIntro;
      iIntros "% Hv !>"; by iApply "HΦ'".
  Qed.

  Lemma triplecc_consequence_many f (e : expr) P P' Φ Φ' :
    □ (P' -∗ P) -∗
    {{ P }} e @ f ; Many ; ⊤ {{ Φ }} -∗
    □ (∀ y, Φ y -∗ Φ' y) -∗
    {{ P' }} e @ f ; Many ; ⊤ {{ Φ' }}.
  Proof.
    iIntros "#HP #He #HΦ'".
    iApply (triplecc_consequence f Many with "[] He"); try by simpl.
    rw (_ : (if f is NoFrame then true else true) = true); [|by destruct f].
    by simpl.
  Qed.    

End reasoning_rules_with_triples.
