From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import all_ssreflect interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype.
From mathcomp Require Import sequences measure lebesgue_measure realfun.
From mathcomp Require Import absolute_continuity.

(**md**************************************************************************)
(* # Banach–Zarecki Theorem (lemma 5)                                         *)
(*                                                                            *)
(* ref: https://archive.org/details/theoryoffunction00nata *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.


Section itv_partition_length.
Context {R : realType}.
Implicit Types (a b : R) (f : R -> R).

Definition itv_partition_length a b s : R := let pnth := nth b (a :: s) in
  \big[maxr/0%R]_(0 <= n < size s) `|pnth n.+1 - pnth n|%R.

Definition itv_partition_set a b l : set (seq R) := [set s | itv_partition a b s /\
  itv_partition_length a b s < l].

End itv_partition_length.

Section lemma5.
Context {R : realType}.
Implicit Types (a b : R) (f : R -> R).

Lemma lemma5' a b f :
  {within `[a, b], continuous f} ->
  forall A : R, (A%:E < total_variation a b f)%E ->
    exists l p, [/\ itv_partition a b p,
              itv_partition_length a b p < l,
              A < variation a b f p &
              ((variation a b f p)%:E < total_variation a b f)%E].
Proof.
Abort.

Lemma lemma5 a b f :
  {within `[a, b], continuous f} ->
  ereal_inf
     [set (variation a b f s)%:E | s in itv_partition_set a b l] @[l --> 0^'+]
       --> total_variation a b f.
Proof.
Abort.

End lemma5.
