From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import all_ssreflect interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import reals constructive_ereal topology normedtype.
From mathcomp Require Import ereal sequences.
From mathcomp Require Import measure lebesgue_measure numfun realfun.
From mathcomp Require Import absolute_continuity banach_zarecki_lemma2.
From mathcomp Require Import banach_zarecki_lemma3 banach_zarecki_lemma5.
From mathcomp Require Import banach_zarecki_lemma4 (* for contiguous intervals *).

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

From mathcomp Require Import cardinality.
Section lemmas.
Context {R : realType}.
Local Notation mu := (@completed_lebesgue_measure R).

Lemma is_subset1_countable (A : set R) : is_subset1 A -> countable A.
Proof.
move=> A1.
have[->|] := eqVneq A set0.
  done.
move/set0P/is_subset1_set1/(_ A1) ->.
exact: countable1.
Qed.

End lemmas.


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
  apply: (@continuous_compact _ _ H Z).
    exact: (continuous_subspaceW Zab).
  exact: cZ.
pose c : R := inf Z.
pose d : R := sup Z.
have perfectZ : perfect_set Z.
  
  admit. (* wlog *)
pose ab_ := contiguous_intervals Z.
pose alpha := mu (H @` Z).
have alpha_ge0 : (alpha > 0)%E by [].
pose c_ (n : nat) (i : 'I_n.+1) :=
  if nat_of_ord i == 0 then c else fine (contiguous_intervals2 Z i).
pose d_ (n : nat) (i : 'I_n.+1) :=
  if i == @ord_max n then d else fine (contiguous_intervals1 Z i).
pose lambda (n : nat) := \big[Num.max/0%R]_(i < n.+1) (d_ _ i - c_ _ i).
have lambda_cvg0 : lambda n @[n --> \oo] --> 0.
  admit.
have [x_ cdx_] : exists x_ : seq R, itv_partition c d x_ (* NB: p = size (c :: x_) *).
  admit.
pose X_ := c :: x_.
pose p := size X_.
pose S_ (n : nat) := \sum_(1 <= j < p.+1) `|f (nth 0 X_ j) - f (nth 0 X_ (j - 1))|.
pose V_ (n : nat) := \sum_(1 <= i < n.+1) `|f (d_ n (inord i)) - f (c_ n (inord i))|
           +
           \sum_(1 <= i < n) fine (total_variation (fine (contiguous_intervals1 Z i))
                                             (fine (contiguous_intervals2 Z i))
                                             f).
pose V := fine (total_variation c d f).
have S_V_V (n : nat) : S_ n <= V_ n <= V.
  admit.
have S_V : S_ n @[n --> \oo] --> V.
  have cd : c < d.
    apply: has_bound_not_subset1_inf_sup.
    - by exists a => x /Zab/=; rewrite in_itv/= => /andP[].
    - by exists b => x /Zab/=; rewrite in_itv/= => /andP[].
    move=> Z1.
    move: muHZ_gt0.
    rewrite measure_gt0/= => /negP; apply; apply/eqP.
    apply: countable_lebesgue_measure0.
    apply: (@sub_countable _ _ _ Z).
      exact: card_image_le.
    exact: is_subset1_countable.

  have ac : a <= c.
    apply: lb_le_inf; last by move=> x /Zab /=; rewrite in_itv/= => /andP[].
    apply/set0P/negP; move/eqP => Z0.
    have := muHZ_gt0; apply/negP.
    rewrite -leNgt le_eqVlt; apply/predU1P; left.
    by rewrite Z0 image_set0 measure0.
  have db : d <= b.
    apply: ge_sup; last by move=> x /Zab /=; rewrite in_itv/= => /andP[].
    apply/set0P/negP; move/eqP => Z0.
    have := muHZ_gt0; apply/negP.
    rewrite -leNgt le_eqVlt; apply/predU1P; left.
    by rewrite Z0 image_set0 measure0.
  have cdcf : {within `[c, d], continuous f}.
    apply: continuous_subspaceW cf.
    by apply: subset_itv; rewrite bnd_simp.
  have cdbvf : bounded_variation c d f.
    apply: (bounded_variationl (ltW cd) db).
    apply: bounded_variationr ac _ bvf.
    by apply: ltW; exact: (lt_le_trans cd).
  have := lemma5 cd cdcf.
  rewrite -(@fineK _ (total_variation c d f)) -/V; last first.
    by apply/bounded_variationP => //; exact: ltW.
  move/fine_cvgP => [fin_inf].
  move/cvg_at_rightP.
  move/(_ lambda).
  have Hlambda : (forall n : nat, 0 < lambda n) /\ lambda n @[n --> \oo] --> 0.
    split => // n.
    admit.
  move/(_ Hlambda); move{Hlambda} => Hl.
  apply: squeeze_cvgr Hl (cvg_cst V).
  near=> n.
  apply/andP; split; last first.
    rewrite /V/total_variation.
    rewrite -lee_fin fineK; last by apply/bounded_variationP => //; exact: ltW.
    apply: le_ereal_sup_tmp.
    admit.
  rewrite -lee_fin fineK; last first.
    admit.
  apply: ge_ereal_inf.
  admit.
have V_V : V_ n @[n --> \oo]--> V.
  admit.
have [n0 Hn0] : exists n0, forall n, (n >= n0)%N -> V_ n > V - (fine alpha) / 2.
  admit.
have H1 (n : nat) : V = \sum_(1 <= i < n.+1) `|H (d_ n (inord i)) - H (c_ n (inord i))|
           +
           \sum_(1 <= i < n) fine (total_variation (fine (contiguous_intervals1 Z i))
                                             (fine (contiguous_intervals2 Z i))
                                             f).
  admit.
Admitted.

End lemma6_direct.

Section lemma6_converse.
Context {R : realType}.
Variables a b : R.
Hypotheses ab : a < b.

Local Notation mu := (@completed_lebesgue_measure R).

Variable f : R -> R.

Let H := fun x => fine (total_variation a ^~ f x).

(* lemma6(i) *)
Lemma total_variation_Lusin :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  lusinN `[a, b] H -> lusinN `[a, b] f.
Proof.
move=> cf abf.
move=> lusinNH Z Zab/= mZ mZ0.
have muZ_lty : ((wlength idfun)^*%mu Z < +oo)%E.
  move: mZ0.
  rewrite /mu/=.
  (* TODO: lemma to avoid unfold *)
  rewrite /completed_lebesgue_stieltjes_measure.
  by rewrite /completed_measure_extension => ->.
move : muZ_lty => /(@lebesgue_measure_Gdelta_approx R Z)[G [ZG oG Gnonincreasing muZ]].
pose Z1 := `]a, b[ `&` \bigcap_i G i.
suff: mu (f @` Z1) = 0.
  move=> mfZ1.
  apply/eqP; rewrite eq_le measure_ge0 andbT.
  rewrite -mfZ1.
  rewrite le_outer_measure//.
  rewrite /Z1.

  apply: image_subset.
  rewrite -bigcapIr//.
  apply: sub_bigcap => i _.
  rewrite subsetI; split => //.
  admit.
have H1 : mu (H @` Z1) = mu (\bigcap_i (H @` (G i))) /\
       mu (\bigcap_i (H @` (G i))) = 0.
  split.
    rewrite completed_lebesgue_measureE.
    have := @measure_image_nondecreasing_fun R a b H ab _ G.
    (* mismatch Z1 should be an intersection of G's... *)
    admit.

(*      rewrite fine_le//.
      + apply/bounded_variationP => //.
        exact: bounded_variationl abf.
      + apply/bounded_variationP => //.
        exact: bounded_variationl abf.
      + apply: (total_variation_nondecreasing f) => //; rewrite ?in_itv/=.
        by rewrite xa/=; exact: xb.
        by rewrite ya/=; exact: yb.
    - exact: total_variation_continuous.
    - move=> k.*)

  admit.
have H2 : mu (H @` G i) @[i --> \oo] --> 0%E.
  admit.
pose G_ i := \bigcup_j (open_disjointI (oG i) j).
have H3 i :
  mu (f @` Z1) = mu (f @` (\bigcup_j (Z1 `&` (open_disjointI (oG i) j)))).
  admit.
have H4 i :
    (mu (f @` (\bigcup_j (Z1 `&` (open_disjointI (oG i) j)))) <=
    \sum_(j <oo) (mu^*)%mu (f @` (Z1 `&` (open_disjointI (oG i) j))))%E.
  admit.
have H5 i :
    (\sum_(j <oo) (mu^*)%mu (f @` (Z1 `&` (open_disjointI (oG i) j))) <
    \sum_(j <oo) oscillation f (closure (open_disjointI (oG i) j)))%E.
  admit.
have H6 i :
    (\sum_(j <oo) oscillation f (closure (open_disjointI (oG i) j)) =
    mu (H @` G_ i))%E.
  admit.
apply/eqP; rewrite eq_le measure_ge0 andbT.
Admitted.

End lemma6_converse.
