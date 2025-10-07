From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import all_ssreflect interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import reals constructive_ereal topology normedtype.
From mathcomp Require Import measure lebesgue_measure realfun.
From mathcomp Require Import absolute_continuity banach_zarecki_lemma3.

(**md**************************************************************************)
(* # Banach–Zarecki Theorem (lemma 6)                                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section lemma6_direct.
Context {R : realType}.
Variables a b : R.
Hypotheses ab : a < b.

Local Notation mu := (@completed_lebesgue_measure R).

Lemma Lusin_total_variation (f : R -> R) :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  lusinN `[a, b] f ->
  lusinN `[a, b] (fun x => fine (total_variation a ^~ f x)).
Proof.
move=> cf bvf lf.
pose H := fun x => fine (total_variation a ^~ f x).
have ndt : {in `[a, b] &, nondecreasing_fun H}.
  move=> x y xab yab xy.
  have axyf := @total_variation_nondecreasing R a b f _ _ xab yab xy.
  rewrite /H fine_le//.
  - apply/bounded_variationP => //.
      by move: xab; rewrite in_itv/= => /andP[].
    move: xab; rewrite in_itv/= => /andP[? ?].
    by move: bvf; apply: bounded_variationl.
  - apply/bounded_variationP => //.
      by move: yab; rewrite in_itv/= => /andP[].
    move: yab; rewrite in_itv/= => /andP[? ?].
    by move: bvf; apply: bounded_variationl.
have cH : {within `[a, b], continuous H}.
  exact: total_variation_continuous.
apply: contrapT => ababsurdo.
have := image_measure0_Lusin_nondecreasing ab cH ndt.
move/contra_not => /(_ ababsurdo).
move/existsNP => [Z /not_implyP [Zab /not_implyP[cZ /not_implyP[muZ0]]]].
move/eqP; rewrite neq_lt ltNge measure_ge0/= => muHZ_gt0.
have compactH : compact (H @` Z).
  have := @continuous_compact _ _ H Z.
  apply.
    apply: continuous_subspaceW.
      exact: Zab.
    assumption.
  exact: cZ.
pose c : R := inf Z.
pose d : R := sup Z.
wlog : Z Zab cZ muZ0 muHZ_gt0 compactH c d / perfect_set Z.
  admit.
move=> perfectZ.

pose TV := (fine \o (total_variation a)^~ f).
have : exists n : nat, (0 < n)%N /\ exists Z_ : `I_ n -> interval R, trivIset setT (fun i => [set` (Z_ i)])
   /\ (0 < mu (TV @` (\bigcup_i [set` Z_ i])))%E
   /\ forall i, [/\ [set` Z_ i] `<=` `[a, b], compact [set` Z_ i] & mu [set` Z_ i] = 0].
  admit.
move=> [n [] n0 [Z_]] [trivZ [Uz0]] /all_and3 [Zab' cZ' Z0].
pose UZ := \bigcup_i [set` Z_ i].
have UZ_not_empty : UZ !=set0.
  admit.
pose l_ i : R := inf [set` Z_ i].
pose r_ i : R := sup [set` Z_ i].
pose alpha := mu [set (fine \o (total_variation a)^~ f) x | x in UZ].
have rct : right_continuous TV.
  admit.
have monot : {in `[a, b]&, {homo TV : x y / x <= y}}.
  admit.
(*
have : exists n, exists I : (R * R)^nat,
 [/\ (forall i, (I i).1 < (I i).2 /\ `[(I i).1, (I i).2] `<=` `[a, b] ),
     trivIset setT (fun i => `[(I i).1, (I i).2]%classic) &
     \bigcup_(0 <= i < n) (`[(I i).1, (I i).2]%classic) = Z].*)
Admitted.

End lemma6_direct.

Section lemma6_converse.
Context {R : realType}.
Variables a b : R.
Hypotheses ab : a < b.

Local Notation mu := (@completed_lebesgue_measure R).

(* lemma6(i) *)
Lemma total_variation_Lusin (f : R -> R) :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  lusinN `[a, b] (fun x => fine ((total_variation a ^~ f) x)) ->
  lusinN `[a, b] f.
Proof.
Admitted.

End lemma6_converse.
