From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import all_ssreflect interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean perm.
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

Lemma omega_max0 (a b : R) f : omega_max a b f [:: b] = oscillation f `[a, b].
Proof. by rewrite/omega_max/= big_nat1. Qed.

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
(* pose ab_ := contiguous_intervals Z. *)

pose a_ n := fine (contiguous_intervals1 Z n).
pose b_ n := fine (contiguous_intervals2 Z n).

pose t_ab n := [tuple (contiguous_intervals Z i) | i < n].

pose ta_ n := [tuple a_ i | i < n].
pose tb_ n := [tuple b_ i | i < n].
have aE n (i : 'I_ n) : a_ i = tnth (ta_ n) i.
  admit.
have bE n (i : 'I_ n) : b_ i = tnth (tb_ n) i.
  admit.
(* (9) *)
have sum_osf_cvg0 :
  \big[+%E/0%E]_(n <= j <oo) oscillation f `[a_ j, b_ j] @[n --> \oo] --> 0%E.
  apply: nneseries_tail_cvg; last first.
    move=> n _.
    exact: oscillation_ge0.
  apply: (@le_lt_trans _ _ (total_variation a b f)); last first.
    rewrite -ge0_fin_numE; last exact: (total_variation_ge0 f (ltW ab)).
    exact/(bounded_variationP f (ltW ab)).
  rewrite /total_variation.
  apply: lime_le.
    apply: is_cvg_nneseries => n _ _.
    exact: oscillation_ge0.
  near=> n.
  apply: le_ereal_sup_tmp.
  have [sort_a sort_aE] : exists (p : {perm 'I_n}), (sort <%R (ta_ n))
         = [tuple tnth (ta_ n) (p i) | i < n].
    apply/tuple_permP.
    by rewrite perm_sort.
  have tbE : sort <%R (tb_ n) = [tuple tnth (tb_ n) i | i < n].
    apply: lt_sorted_eq.
        admit.
      admit.
    admit.

(*
  have := @lemma5' _ _ _ _ ab cf bvf
    (fine (\big[+%R/0%R]_(0 <= k < n) oscillation f `[(a_ k), (b_ k)])).
*)
  admit.
suff HZ2_gt_osf : \forall n \near \oo, (mu [set H x | x in Z] / 2 <
 \big[+%E/0%E]_(n <= j <oo) oscillation f `[a_ j, b_ j])%E. (* (8) *)
  move: muHZ_gt0.
  apply/negP.
  rewrite -leNgt.
  rewrite -(@pmule_lle0 _ 2%:E^-1); last by rewrite inve_gt0.
  have/cvg_lim <- := sum_osf_cvg0; last by [].
  have <- : (limn (fun n : nat => @cst nat _ (mu [set H x | x in Z] / 2)%E n)
      = mu (H @` Z) / 2)%E.
    apply/cvg_lim => //; exact: cvg_cst.
  apply: lee_lim HZ2_gt_osf.
  - exact: eventually_filter.
  - exact: is_cvg_cst.
  - by apply/cvg_ex; exists 0%E.
(* ~ (8) *)
near=> n.

(* old sketch *)
(*
pose c_ (n : nat) (i : 'I_n.+1) :=
  if nat_of_ord i == 0 then c else b_ i. (* left boundary of *)
pose d_ (n : nat) (i : 'I_n.+1) :=
  if i == @ord_max n then d else a_ i.
pose alpha := mu (H @` Z).
have alpha_ge0 : (alpha > 0)%E by [].
pose lambda (n : nat) := \big[Num.max/0%R]_(i < n.+1) (d_ _ i - c_ _ i).
have lambda_cvg0 : lambda n @[n --> \oo] --> 0.
  admit.
have [x_ cdx_] : exists x_ : seq R, itv_partition c d x_ /\
     (itv_partition_max c d x_ < lambda n) (* NB: p = size (c :: x_) *).
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
  apply/cvgrPdist_ltp.
  near=> eps.
  near=> n.
  have/normr_idP -> : 0 <= V - S_ n.
    admit.
  rewrite ltrBlDr -ltrBlDl.
  have -> : S_ n = variation c d f x_.
    admit.
  have cd : c < d.
    admit.
  have cdcf : {within `[c, d], continuous f}.
   admit.
  have cdbvf : bounded_variation c d f.
    admit.
  have veps0 : (0%:E < (V - eps)%:E < total_variation c d f)%E.
    admit.
  have := lemma5' cd cdcf cdbvf veps0.
  move=> [l].
  apply.
    admit.
  apply: (@lt_trans _ _ (lambda n)).
    rewrite /itv_partition_max/lambda.
    admit.

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
*)
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
