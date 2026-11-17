From Coq Require Import ZArith String.

Require Import Separation.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** Terms, values, and continuations *)

Inductive term: Type :=
  | VAL (v: value)
  | LET (x: string) (a b: term)
  | SEQ (a b: term)
  | IFTHENELSE (v: value) (a b: term)
  | APP (v w: value)
  | ADD (v w: value)
  | REF (v: value)
  | GET (l: value)
  | SET (l v: value)
  | FREE (l: value)
  | CALLCC (f: value)
  | THROW (v w: value)

with value: Type :=
  | INT (n: Z)
  | VAR (x: string)
  | LAM (x: string) (a: term)
  | LOC (l: addr)              (** appear only during reductions *)
  | CONT (k: cont)             (** always closed; appear only during reductions *)

with cont: Type :=
  | KSTOP
  | KLET (x: string) (b: term) (k: cont)
  | KSEQ (b: term) (k: cont)
  | KABORT.                    (** prevent a term from returning normally *)

Definition VUNIT := INT 0.
Definition UNIT := VAL VUNIT.

(** Substitution of a variable by a *closed* value.
    (Variable capture can occur if the value has free variables.)
    If we start reduction on a closed program, all values and continuations
    arising during reduction are closed. *)

Fixpoint subst (X: string) (V: value) (a: term) : term :=
  match a with
  | VAL v => VAL (subst_val X V v)
  | LET x a b =>
      LET x (subst X V a) (if string_dec x X then b else subst X V b)
  | SEQ a b =>
      SEQ (subst X V a) (subst X V b)
  | IFTHENELSE v a b =>
      IFTHENELSE (subst_val X V v) (subst X V a) (subst X V b)
  | APP v w => APP (subst_val X V v) (subst_val X V w)
  | ADD v w => ADD (subst_val X V v) (subst_val X V w)
  | REF v => REF (subst_val X V v)
  | GET l => GET (subst_val X V l)
  | SET l v => SET (subst_val X V l) (subst_val X V v)
  | FREE l => FREE (subst_val X V l)
  | CALLCC f => CALLCC (subst_val X V f)
  | THROW v w => THROW (subst_val X V v) (subst_val X V w)
  end

with subst_val (X: string) (V: value) (v: value) : value :=
  match v with
  | INT n => INT n
  | VAR x => if string_dec x X then V else VAR x
  | LAM x a => LAM x (if string_dec x X then a else subst X V a)
  | LOC l => LOC l
  | CONT k => CONT k  (* assumed closed *)
  end.
