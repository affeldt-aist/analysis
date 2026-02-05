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

Lemma nondecreasing_total_variation (a b : R) (f : R -> R) :
bounded_variation a b f ->
let H := fun x => fine (total_variation a ^~ f x) in
 {in `[a, b] &, nondecreasing_fun H}.
Proof.
move=> bvf H x y xab yab xy.
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
Qed.

Lemma itv_partition_max_mem_filter (a b c d : R) (s : seq R) :
  a <= c -> d <= b ->
  itv_partition_max c d [seq x <- s | x \in `[c, d]] <= itv_partition_max a b s.
Proof.
Admitted.

Lemma itv_partition_max_filter (a b : R) (s : seq R) (P : pred R) :
  itv_partition_max a b [seq x <- s | P x] <= itv_partition_max a b s.
Proof.
Admitted.

End lemmas.

Section preliminary.
Context {R : realType}.

Lemma nth_map_iota (x : R) (n : nat) (f : nat -> R) (i : nat) :
  (i < n)%N ->
  nth x [seq f k | k <- iota 0 n] i = f i.
Proof.
by move=> iltn; rewrite (nth_map 0%N) ?nth_iota; last by rewrite size_iota.
Qed.

Lemma nth_cons_map_iota (x y : R) (n : nat) (f : nat -> R) (i : nat) :
  (i < n.+1)%N ->
  nth x (y :: [seq f k | k <- iota 0 n]) i = if i == 0 then y else f i.
Proof.
case: i => //.
Admitted.

Definition lambda_partition (a b : R) (lambda : R) :=
  let n := `|ceil ((b - a) / lambda)|%N in
  [seq (a + (b - a) * i.+1%:R / n%:R) | i <- iota 0 n].

Local Notation lp := lambda_partition.

Lemma lambda_partition_size0_tmp (a b l : R) :
  a < b -> 0 < l ->
  (0 < `|ceil ((b - a) / l)|%N)%N.
Proof.
move=> ab l0.
rewrite absz_gt0 ceil_neq0; apply/orP; right; by rewrite divr_gt0 ?subr_gt0.
Qed.

Lemma lambda_partition_size0 (a b l : R) :
  a < b -> 0 < l ->
  (0 < size (lp a b l))%N.
Proof.
move=> ab l0; by rewrite size_map size_iota lambda_partition_size0_tmp.
Qed.

Lemma lambda_partition_div_width (a b l : R) (i : nat) :
  `|nth b (a :: (lp a b l)) i.+1 - nth b (a :: (lp a b l)) i| < l.
Proof.
Admitted.

Lemma lambda_partition_partition (a b l : R) :
  a < b -> 0 < l ->
  itv_partition a b (lp a b l).
Proof.
move=> ab l0.
split; last first.
- rewrite (last_nth b).
  rewrite -(@prednK (size _))/=; last exact: lambda_partition_size0.
  rewrite nth_map_iota//.
  rewrite prednK; last exact: lambda_partition_size0.
  rewrite size_map size_iota mulfK; first by rewrite subrKC.
  rewrite lt0r_neq0//.
  rewrite (_ : 0 = 0%:R)// ltr_nat.
  exact: lambda_partition_size0_tmp.
- admit.
Admitted.

Lemma lambda_partition_max (a b l : R) :
  0 < l ->
  itv_partition_max a b (lp a b l) < l.
Proof.
move=> l0.
rewrite /itv_partition_max -bigmaxr_morph.
apply: bigmax_lt => // n _.
exact: lambda_partition_div_width.
Qed.

End preliminary.

Section lemma6_direct.
Context {R : realType}.
Local Notation mu := (@completed_lebesgue_measure R).

Variables a b : R.
Hypothesis ab : a < b.
Variable f : R -> R.
Hypotheses (cf : {within `[a, b], continuous f})
           (bvf : bounded_variation a b f)
           (lusinf : lusinN `[a, b] f).
Definition H := fun x => fine (total_variation a ^~ f x).

(* "Clearly, H is increasing and continuous. " *)
Let ndH := nondecreasing_total_variation bvf.
Let cH : {within `[a, b], continuous H}.
Proof. exact: total_variation_continuous. Qed.

Lemma lusinN_contra :
 ~ (lusinN `[a, b] H) ->
 exists Z : set R,
  [/\ Z `<=` `[a, b], compact Z, mu Z = 0 & (0%R < mu [set H x | x in Z])%E].
Proof.
move=> ababsurdo.
have := image_measure0_Lusin_nondecreasing ab cH ndH.
move/contra_not=> /(_ ababsurdo).
move/existsNP=> [Z /not_implyP [Zab /not_implyP[cZ /not_implyP[muZ0]]]].
move/eqP; rewrite neq_lt ltNge measure_ge0/= => muHZ_gt0.
by exists Z.
Qed.

(* wlog *)
Lemma lusinN_contra_wlog :
 ~ (lusinN `[a, b] (fun x => fine (total_variation a ^~ f x))) ->
 exists Z : set R,
 [/\ Z `<=` `[a, b], compact Z, mu Z = 0, (0%R < mu [set H x | x in Z])%E &
  perfect_set Z].
Proof.
move=> ababsurdo.
have := image_measure0_Lusin_nondecreasing ab cH ndH.
move/contra_not=> /(_ ababsurdo).
move/existsNP=> [Z /not_implyP [Zab /not_implyP[cZ /not_implyP[muZ0]]]].
move/eqP; rewrite neq_lt ltNge measure_ge0/= => muHZ_gt0.
Admitted.

Section contra.
Hypothesis (nl : ~ (lusinN `[a, b] H)).
Let Z : set R := sval (cid (lusinN_contra_wlog nl)).

Let Zab : Z `<=` `[a, b].
Proof. by have []:= proj2_sig (cid (lusinN_contra_wlog nl)). Qed.
Let cZ : compact Z.
Proof. by have []:= proj2_sig (cid (lusinN_contra_wlog nl)). Qed.
Let muZ0 : mu Z = 0.
Proof. by have []:= proj2_sig (cid (lusinN_contra_wlog nl)). Qed.
Let muHZ_gt0 : (0%R < mu [set H x | x in Z])%E.
Proof. by have []:= proj2_sig (cid (lusinN_contra_wlog nl)). Qed.

(* wlog *)
Let perfectZ : perfect_set Z.
Proof. by have []:= proj2_sig (cid (lusinN_contra_wlog nl)). Qed.

Lemma compactH : compact (H @` Z).
Proof.
apply: (@continuous_compact _ _ H Z); last exact: cZ.
exact: (continuous_subspaceW Zab).
Qed.

Let c : R := inf Z.
Let d : R := sup Z.

Let cd : c < d.
Proof.
apply: has_bound_not_subset1_inf_sup.
- by exists a => ? /Zab/=; rewrite in_itv/= => /andP[].
- by exists b => ? /Zab/=; rewrite in_itv/= => /andP[].
move=> Z1.
move: muHZ_gt0.
rewrite measure_gt0/= => /negP; apply; apply/eqP.
apply: countable_lebesgue_measure0.
apply: (@sub_countable _ _ _ Z).
  exact: card_image_le.
exact: is_subset1_countable.
Qed.

Let a_ n := fine (contiguous_intervals1 Z n).
Let b_ n := fine (contiguous_intervals2 Z n).

Section construct_x.
Variable (n : nat).
Let ta := [tuple a_ i | i < n].
Let tb := [tuple b_ i | i < n].

Local Definition sort_ta := sort <%R ta.
Local Definition sort_tb := sort <%R tb.
Let merge_tab := (merge <%R sort_ta sort_tb).

(*
fun_of_sort : exists (p : {perm 'I_n}), (sort <%R (ta_ n))
         = [tuple tnth (ta_ n) (p i) | i < n].
    apply/tuple_permP.
    by rewrite perm_sort.
  have sort_bE : sort <%R (tb_ n) = [tuple tnth (tb_ n) i | i < n].
    apply: lt_sorted_eq.
        admit.
      admit.
    admit.
*)

Local Lemma sorted_merge_tab : sorted <%R (c :: merge_tab).
Proof.
Admitted.

(* nth b merge_tab n.*2 = nth b sort_ta n /\
   nth b merge_tab n.*2.+1 = nth b sort_tb n ? *)

Let cd_ := nth b (c :: merge_tab).

Let c_ i := cd_ i.*2.
Let d_ i := cd_ i.*2.+1.

Lemma cd_default k : (n.*2 < k)%N -> cd_ k = b.
Proof.
move=> n2k.
by rewrite /cd_ nth_default//= size_merge size_cat !size_sort !size_tuple addnn.
Qed.

Local Definition lambda : R := \big[maxr/0%R]_(i < n) `|d_ i - c_ i|%R.

(* d @[n --> \oo] --> b ? *)
(* forall i, `]c_ i, d_ i[ `<=` Z ? *)

Lemma itv_partition_max_splitl : forall (s t : seq R) (l : R), sorted <%R s -> sorted <%R t ->
    disj_seq s t ->
    (forall n, (n < size s)%N ->
 itv_partition_max (nth d s n) (nth d s n.+1)
    (rcons [seq x <- t | x \in `[(nth b s n), (nth b s n.+1)[]
                                          (nth d s n.+1)) <= l)->
    itv_partition_max c d (merge <%R s t) <= l.
Proof.
Admitted.

Lemma construct_x :
  exists x : seq R, [/\ itv_partition c d x,
   (itv_partition_max c d x <= lambda),
   (forall i, (i < n.*2)%N -> a_ i \in x),
   (forall i, (i < n.*2)%N -> b_ i \in x) &
   (forall i, nth b x i \notin (interior Z : set R))
            (* \bigcup_(i < n) `]c_ i, d_ i[ ? *)].
Proof.
exists (merge <%R [seq cd_ i | i <- iota 0 n.*2]
   [seq x <- lambda_partition c d lambda |
         x \notin \bigcup_(i < n) `[c_ i, d_ i]%classic]).
split.
- admit.
- (* lemma? *)
  apply: itv_partition_max_splitl.
  + admit.
  + admit.
  + admit.
  + move=> k.
(*    rewrite size_map size_iota => kn.
    have [k12n|] := eqVneq k.+1 n.*2.
      rewrite nth_map_iota//.
        rewrite ![nth _ _ k.+1]nth_default ?size_map ?size_iota -?k12n//.
        rewrite /cd_ (pred_Sn k) k12n.
        have -> : n.*2 = size merge_tab.
          by rewrite /= size_merge size_cat 2!size_tuple addnn.
    rewrite !nth_map_iota//; last first.
      admit.
    * admit.
    * admit.
    apply: (le_trans (itv_partition_max_filter _ _ _ _)).
    apply/ltW/lambda_partition_max.
    apply/bigmax_gtP; right.
    rewrite /=.
    have n0 : (0 < n)%N.
      rewrite -ltn_double double0.
      apply: leq_ltn_trans kn => //.
    exists (Ordinal n0) => //=.
    rewrite normr_gt0 lt0r_neq0// subr_gt0.
    suff : sorted <%R [seq cd_ i | i <- iota 0 n.*2].
      rewrite lt_sorted_pairwise.
      move/(pairwiseP b).
      move/(_ 0 1).
      rewrite !inE size_map size_iota/=.
      rewrite -[X in (X < n.*2)%N]double0 ltn_double.
      rewrite -{1}(add0n 1) addn1 -{2}double0 ltn_Sdouble.
      move/(_ n0 n0 (leqnn 0)).
      rewrite 2?nth_map_iota//.
        by rewrite -(add0n 1) addn1/= -double0 ltn_Sdouble.
      by rewrite double_gt0.
    apply: (@homo_sorted_in _ _ (fun k => (k < n.*2)%N) _ ltn); last 2 first.
    * by apply/allP => p; rewrite mem_iota => /andP[].
    * exact: iota_ltn_sorted.
    move=> m0 m1/=.
    rewrite !unfold_in => m02n m12n m01.
    rewrite /cd_.
    have := sorted_merge_tab.
    rewrite lt_sorted_pairwise => /pairwiseP.
    apply; rewrite ?unfold_in//= size_merge size_cat !size_sort !size_tuple.
    * move: m02n.
      by rewrite -muln2 mulnS muln1; move/leq_trans; apply.
    * move: m12n.
      by rewrite -muln2 mulnS muln1; move/leq_trans; apply.
  *)
  admit.
- move=> k.
  move=> k2n.
  rewrite mem_merge mem_cat; apply/orP; left.
  admit.
- move=> k.
  admit.
- move=> k.
  admit.
Admitted.

End construct_x.

Let lambda_gt0 n : 0 < lambda n.
Proof.
Admitted.

Let cvg_lambda0 : lambda n @[n --> \oo] --> 0.
Proof.
Admitted.

Let x := fun n => sval (cid (@construct_x n)).

Local Notation p n := (size (x n)).

Let pcdx n : itv_partition c d (x n).
Proof. by have [] := proj2_sig (cid (@construct_x n)). Qed.
Let max_x n : itv_partition_max c d (x n) <= (lambda n).
Proof. by have [] := proj2_sig (cid (construct_x n)). Qed.
Let ax n i (_ : (i < n.*2)%N) : a_ i \in (x n).
Proof. by have [_ _ + _ _] := proj2_sig (cid (@construct_x n)); apply. Qed.
Let bx n i (_ : (i < n.*2)%N) : b_ i \in (x n).
Proof. by have [_ _ _ + _] := proj2_sig (cid (@construct_x n)); apply. Qed.
Let xZ n i : nth b (x n) i \notin (interior Z : set R).
Proof. by have [] := proj2_sig (cid (@construct_x n)). Qed.

Let S_ n : R := variation c d f (x n).

Let V_ n : R :=
  

`|f (a_ 0) - c| + \sum_(i < n) `|f (a_ i.+1) - f (b_ i)| + `|f d - f (b_ n)|
    + \sum_(i < n) (fine (total_variation (a_ i) (b_ i) f)).

Local Notation Vcd := (fine (total_variation c d f)).

Lemma SV n : S_ n <= V_ n.
Proof.
Admitted.

Lemma V_tv n : V_ n <= Vcd.
Proof.
Admitted.

Lemma Soo_tv : S_ n @[n --> \oo] --> Vcd.
Proof.
have ac : a <= c.
  apply: lb_le_inf; last by move=> ? /Zab /=; rewrite in_itv/= => /andP[].
  apply/set0P/negP; move/eqP => Z0.
  have := muHZ_gt0; apply/negP.
  rewrite -leNgt le_eqVlt; apply/predU1P; left.
  by rewrite Z0 image_set0 measure0.
have db : d <= b.
  apply: ge_sup; last by move=> ? /Zab /=; rewrite in_itv/= => /andP[].
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
rewrite -{1}(@fineK _ (total_variation c d f)); last first.
  by apply/bounded_variationP => //; exact: ltW.
move/fine_cvgP => [fin_inf].
move/cvg_at_rightP.
move/(_ lambda).
have Hlambda : (forall n : nat, 0 < lambda n) /\ lambda n @[n --> \oo] --> 0.
  split; last exact: cvg_lambda0.
  move=> k.
  exact: lambda_gt0.
move/(_ Hlambda); move{Hlambda} => Hl.
apply: squeeze_cvgr _ Hl (cvg_cst Vcd).
near=> n.
apply/andP; split; last first.
  rewrite /Vcd/total_variation.
  rewrite -lee_fin fineK; last by apply/bounded_variationP => //; exact: ltW.
  apply: le_ereal_sup_tmp.
  exists (S_ n)%:E => //.
  exists (S_ n) => //.
  by exists (x n).
rewrite -lee_fin fineK; last first.
  have := fin_inf.
  move=> [l /= l0].
  apply => //=.
  rewrite sub0r normrN ger0_norm; last first.
    exact/ltW/lambda_gt0.
  move: l l0; near: n.
  admit.
  exact: lambda_gt0.
apply: ge_ereal_inf.
exists (S_ n)%:E => //.
exists (S_ n) => //.
by exists (x n); split.
Unshelve. end_near. Admitted.

Lemma Voo_tv : V_ n @[n --> \oo] --> Vcd.
Proof.
apply: squeeze_cvgr _ Soo_tv (cvg_cst Vcd).
apply: nearW => n.
by rewrite SV V_tv.
Qed.

 (* (3) ~ (8) *)
Let HZ2_gt_osf : \forall n \near \oo, (mu [set H x | x in Z] / 2 <
 \big[+%E/0%E]_(n <= j <oo) oscillation f `[a_ j, b_ j])%E.
Proof.
near=> n.

Admitted.

(* (9) *)
Lemma sum_osf_cvg0 :
  \big[+%E/0%E]_(n <= j <oo) oscillation f `[a_ j, b_ j] @[n --> \oo] --> 0%E.
Proof.
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
apply: nearW => n.
apply: le_ereal_sup_tmp.

have subab_cf k :
   {within `[nth b (sort_ta n) k, nth b (sort_tb n) k], continuous f}.
  admit.
have ltcd k : (nth b (sort_ta n) k) < (nth b (sort_tb n) k).
  admit.
have := fun k => continuous_oscillationE (ltcd k) (subab_cf k).
move/choice => [osc_pts Hosc_pts].
pose osc_seq := \big[cat/[::]]_(i < n) [:: (osc_pts i).1; (osc_pts i).2].
have pab_osc_seq : itv_partition a b (rcons osc_seq b).
  admit.
exists (variation a b f (rcons osc_seq b))%:E.
  exists (variation a b f (rcons osc_seq b)) => //.
  exact: variations_variation.
Admitted.

Lemma contra : False.
Proof.
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
apply/cvg_ex; exists 0%E.
exact: sum_osf_cvg0.
(* ? *) Admitted.

End contra.

(* lemma6 *)
Lemma Lusin_total_variation :
  lusinN `[a, b] (fun x => fine (total_variation a ^~ f x)).
Proof.
apply: contrapT => nl.
exact: (contra nl).
Qed.

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
apply/negP.

Admitted.
*)

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
