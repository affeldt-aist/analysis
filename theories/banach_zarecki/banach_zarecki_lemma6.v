From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import all_boot all_order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean perm finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import reals constructive_ereal topology normedtype.
From mathcomp Require Import ereal sequences.
From mathcomp Require Import measure lebesgue_measure numfun realfun.
From mathcomp Require Import measurable_realfun.
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

Abort.

Lemma itv_partition_max_filter (a b : R) (s : seq R) (P : pred R) :
  itv_partition_max a b [seq x <- s | P x] <= itv_partition_max a b s.
Proof.
Abort.

End lemmas.

Section preliminaries.
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
Abort.

Definition lambda_partition (a b : R) (lambda : R) :=
  let n := (truncn ((b - a) / lambda)).+1 in
  [seq (a + (b - a) * i.+1%:R / n%:R) | i <- iota 0 n].

Local Notation lp := lambda_partition.

Lemma lambda_partition_size0_tmp (a b l : R) :
  (0 < (truncn ((b - a) / l)).+1)%N.
Proof. by []. Qed.

Lemma lambda_partition_size0 (a b l : R) :
  a < b -> 0 < l ->
  (0 < size (lp a b l))%N.
Proof.
move=> ab l0; by rewrite size_map size_iota lambda_partition_size0_tmp.
Qed.

Lemma lambda_partition_div_width (a b l : R) (i : nat) :
  a < b -> 0 < l ->
  `|nth b (a :: (lp a b l)) i.+1 - nth b (a :: (lp a b l)) i| < l.
Proof.
move=> ab l0.
have lpw0 := lambda_partition_size0_tmp.
case: i.
  rewrite /= mulr1 -addrA subrKC.
  rewrite gtr0_norm; last by rewrite divr_gt0// subr_gt0.
  rewrite ltr_pdivrMr// mulrC -ltr_pdivrMr//.
  exact: truncnS_gt.
move=> n.
have [|] := leqP n (truncn ((b - a) / l)).
  rewrite leq_eqVlt => /predU1P[-> |].
    rewrite nth_default; last by rewrite /= size_map size_iota.
    rewrite [lp a b l]lock /=; unlock; rewrite nth_map_iota//.
    by rewrite -mulrA divff// mulr1 subrKC subrr normr0.
  admit.
move=> nsize.
rewrite 2?nth_default ?subrr ?normr0//.

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
  rewrite size_map size_iota mulfK; first by rewrite subrKC.
  rewrite lt0r_neq0//.
- admit.
Admitted.

Lemma lambda_partition_max (a b l : R) :
  a < b -> 0 < l ->
  itv_partition_max a b (lp a b l) < l.
Proof.
move=> ab l0.
rewrite /itv_partition_max -bigmaxr_morph.
apply: bigmax_lt => // n _.
exact: lambda_partition_div_width.
Qed.

End preliminaries.

Section limit_point_closed.
Context {R : realType}.

Lemma not_limit_point_set1 (A : set R) (a : R) : ~ limit_point A a ->
  exists e : {posnum R}, ball a e%:num `&` A `<=` [set a].
Proof.
move=> Ua; apply/not_existsP => aAa.
apply: Ua; rewrite /limit_point => /= V [e /= e0 aeV].
have /nonsubset[/= x [[aex Ax] /eqP xa]] := aAa (PosNum e0).
by exists x; split => //; exact: aeV.
Qed.

Lemma limit_point_closed (A : set R) : closed (limit_point A).
Proof.
rewrite -openC.
set U : set R := ~` _.
rewrite openE/= => a /not_limit_point_set1[e AeAa].
rewrite /interior /nbhs/= /nbhs_ball_; exists e%:num => //= b bae.
suff : b \notin limit_point A by rewrite notin_setE.
have [{}bae aeEa] : nbhs b (ball a e%:num) /\ ball a e%:num `&` A `<=` [set a].
  have [ab|ab] := eqVneq a b.
    split=> [|/= r [aer Ar]].
      by rewrite ab; exact: nbhsx_ballx.
    exact: AeAa.
  split => //.
  rewrite /nbhs/= /nbhs_ball_/=.
  exists (Num.min `|b - a| (e%:num - `|b - a|)) => //=.
    by rewrite lt_min/= normr_gt0 subr_eq0 eq_sym ab/= subr_gt0 distrC.
  move=> x.
  rewrite /ball /ball_ /= lt_min => /andP[bxba bxe].
  by rewrite -(subrKA b) (le_lt_trans (ler_normD _ _))// -ltrBrDl (distrC a).
rewrite notin_setE => /limit_point_infinite_setP/(_ _ bae); apply.
exact: (sub_finite_set aeEa).
Qed.

Section checking.

Lemma isolated_id_set1 (x : R) : isolated [set x] = [set x].
Proof.
rewrite eqEsubset; split; first exact: isolatedS.
rewrite -[isolated _]setU0.
apply: (subset_trans (@subset_closure _ _)).
rewrite closure_isolated_limit_point.
apply: setUS.
move=> z.
move/limit_pointP => [z_ [zx nzx cvgz]]/=.
have := zx z.
have rzx : range z_ x by exists 0 => //; apply: zx.
apply/not_implyP; split => //.
Abort.

Lemma isolated_points_of_limit_points_is_not_empty :
  exists A : set R, isolated (limit_point A) !=set0.
Proof.
exists [set n.+1%:R^-1 | n in [set: nat]].
exists 0%:R; split.
  rewrite inE.
  apply/limit_pointP.
  exists (fun n => n.+1%:R^-1); split.
  - done.
  - move=> n.
    by rewrite lt0r_neq0.
  - have <- : inf [set n.+1%:R^-1 | n in [set: nat]] = 0%:R :> R.
      apply/eqP; rewrite eq_le; apply/andP; split; last first.
        apply: lb_le_inf.
          by exists 1; exists 0 => //; rewrite invr1.
        by move=> _ [n _ <-]; rewrite invr_ge0.
      rewrite -lee_fin.
      rewrite -ereal_inf_EFin; last 2 first.
      - by exists 0 => _ [n _ <-]; rewrite invr_ge0.
      - by exists 1; exists 0 => //; rewrite invr1.
      admit.
    apply: nonincreasing_cvgn.
      apply/nonincreasing_seqP => n.
      by rewrite lef_pV2 ?posrE// ler_nat.
    by exists 0%:R => _ [n _ <-]; rewrite invr_ge0 (_ : 0 = 0%:R)// ler_nat.
exists (ball 0 1).
  exact: nbhsx_ballx.
rewrite eqEsubset; split.
  move=> x/= [] _ l2.
  apply/not_notP => /eqP.
  rewrite eq_le.
  rewrite negb_and => /orP.
  rewrite -2!ltNge => -[]x0;move/limit_point_infinite_setP : l2; apply/existsNP.
    have [x1|x1] := leP 1 x.
      exists (ball x (x - 1 / 2)).
      apply/not_implyP; split.
        apply: nbhsx_ballx.
        rewrite subr_gt0.
        apply: lt_le_trans _ x1.
        rewrite div1r invf_lt1//.
        by rewrite (_ : 1 = 1%:R)// ltr_nat.
      rewrite not_notP.
      apply/finite_set_leP.
      exists 1.
      rewrite -(card_le_eqr (@card_set1 R 1%:R)).
      apply: subset_card_le.
      move=> r/= [+ [n _]];  move/[swap] => <-{r}.
      apply: contraPP.
      case: n => // n _.
(*
      apply/negP; rewrite /ball/= -leNgt.
      rewrite ler_normr; apply/orP; left.
      rewrite lerB//.
      rewrite ler_pdivlMr//.
      rewrite exprSr divfK//.
      apply: exprn_ile1 => //.
      rewrite invf_le1//.
      by rewrite (_ : 1 = 1%:R)// ler_nat.
    exists (ball x (x / 2)).
    apply/not_implyP; split.
      apply: nbhsx_ballx.
      by rewrite divr_gt0.
    rewrite not_notE.
    apply/finite_set_leP.
    exists (truncn (x / 2)).+1.
    apply: (@card_le_trans _ _ _
           [set n%:R | n in `I_((Nat.log2 (truncn (x / 2))).+1)]).
      apply: subset_card_le.
      move=> r/=[+ [n _]] => /[swap] => <-{r}.
      rewrite /ball/=.
      move/ltr_normlW; rewrite ltrBlDr -ltrBlDl {1}(splitr x) addrK => x2n.
      exists (Nat.log2 (truncn (x / 2))) => //.
      rewrite 
      rewrite -{2}(invrK 2) -{2}(expr1 2^-1).
      
      rewrite gtr0_norm; last first.
        rewrite 
  move/limit_pointP => [a_ [a2]].
rewrite subset_set1.
Lemma perfect_set_closedDisolated (A : set R) : closed A ->
  perfect_set (A `\` isolated A).
Proof.
move=> cA.
split.
*)
Abort.

End checking.
 
End limit_point_closed.
Arguments limit_point_closed {R} A.

(* TODO: PR *)
Section interior_lemmas.
Context {R : realType}.

Lemma isolated_interior_set0 (A : set R) :
  isolated (interior A) = set0.
Proof.
apply/eqP.
apply: contrapT.
move/negP.
move/set0P.
move=> [/= x [Ax /=[V]]].
rewrite nbhsE/=.
move=> [U [oU Ux] UV] => VAx.
have {V UV VAx}UAx : U `&` (interior A) = [set x].
  rewrite eqEsubset; split.
    rewrite -VAx.
    exact: setSI.
  rewrite sub1set inE; split => //.
  by rewrite inE in Ax.
have : open (U `&` (interior A)).
  apply: openI => //.
  exact: open_interior.
rewrite UAx.
move/(interior_id _).1.
rewrite interior_set1.
by rewrite eqEsubset => -[_ /(_ x erefl)].
Qed.

Lemma nonempty_open_interval_not_subset1 (A : set R) :
  A !=set0 -> open A -> is_interval A ->
  ~ is_subset1 A.
Proof.
move=> [x Ax] oA itvA.
apply/existsNP.
have /(_ x Ax)[e/= e0] := open_subball oA.
have e20 : 0 < e / 2 by exact: divr_gt0.
move/(_ (e / 2)).
have ballee2 : ball_ [eta normr] 0 e (e / 2).
  rewrite /ball_/= sub0r normrN gtr0_norm//.
by rewrite -subr_gt0 {1}(splitr e) addrK.
move/(_ ballee2 e20).
move/(subset_trans (subset_closure_half e20)).

Admitted.

Lemma limit_point_interior (A : set R) :
  interior A `<=` limit_point (interior A).
Proof.
move=> /= x [e /=e0].
rewrite open_subsetE; last exact: ball_open.
 move=> ballxA.
apply/limit_pointP.
exists (fun n => x - e / n.+2%:R); split.
- move=> _/= [n _ <-].
  apply: ballxA; rewrite /ball_/=.
  rewrite opprB addrCA subrr addr0 ger0_norm; last first.
    by rewrite divr_ge0// ltW.
  rewrite ltr_pdivrMr//.
  rewrite ltr_pMr//.
  by rewrite {1}(_ : 1 = 1%:R)// ltr_nat.
- move=> n.
  rewrite neq_lt; apply/orP; left.
  rewrite gtrBl.
  by rewrite divr_gt0.
- rewrite -{2}(subr0 x).
  apply: cvgB.
    exact: cvg_cst.
  rewrite -(mulr0 e).
  apply: cvgM.
    exact: cvg_cst.
  apply/cvgrVy.
    by apply: nearW.
  under eq_cvg do rewrite /unstable.inv_fun/= invrK.
  apply/cvgrnyP.
  rewrite cvg_shiftS.
  rewrite (cvg_shiftS (fun x => x)).
  exact: cvg_id.
Qed.

Lemma ex_perfect_set (A : set R) :
  closed A ->
  exists B, [/\ B `<=` A, perfect_set B &
   (0 < lebesgue_measure A)%E -> (0 < lebesgue_measure B)%E].
Proof.
move=> cA.
exists (closure (interior A)); split.
- rewrite {2}((closure_id _).1 cA).
  apply: closureS.
  exact: interior_subset.
- apply/perfectP; split; first exact: closed_closure.
  rewrite closure_isolated_limit_point.
  rewrite isolated_interior_set0 set0U.
  rewrite -subset0.
  move=> /= x []/= .
  rewrite inE; move/[dup] => limAx /limit_pointP[a_ [aA anx cvgax]].
  move=> [V].
  rewrite nbhsE/= => -[U [oU Ux] UV VAx].
  have {V UV VAx}UAx : U `&` limit_point (interior A) = [set x].
    rewrite eqEsubset; split.
      rewrite -VAx.
      exact: setSI.
    by rewrite sub1set inE; split.
  pose I_ := open_disjoint_itv oU.
  have := Ux.
  rewrite (open_disjoint_itv_bigcup oU) => -[n _ Inx].
  have In0 : I_ n !=set0 by exists x.
  have := nonempty_open_interval_not_subset1 In0 (@open_disjoint_itv_open _ _ oU n) (@open_disjoint_itv_is_interval _ _ oU n).
  move/existsNP => [x0 /existsNP[x1] /not_implyP[Inx0] /not_implyP[Inx1]].
  move/eqP.
  rewrite eq_le.
  move/nandP.
  rewrite -2!ltNge => -[x10|x01].
Abort.


End interior_lemmas.

Section continuous_interval.
Context {R : realType}.
Variables (D : set R) (f : R -> R).
Hypothesis cf : {within D, continuous f}.

Lemma is_interval_image_cc a b : `[a, b] `<=` D ->
  is_interval (f @` `[a, b]).
Proof.
have [ab abD|ba _] := leP a b; last first.
  rewrite set_itv_ge// ?bnd_simp -?ltNge// image_set0.
  exact/connected_intervalP/connected0.
move=> _ _/= -[x0 x0ab <-] [x1 x1ab <-] z /andP[fx0z zfx1].
have [x01|x10] := leP x0 x1.
  have [x [xx01 fxz]] : exists2 x : R, x \in `[x0, x1] & f x = z.
    apply: IVT => //.
      apply: continuous_subspaceW cf.
      by apply: subset_trans abD; apply: subset_itv;
        rewrite bnd_simp ?(itvP x0ab) ?(itvP x1ab).
    by rewrite ge_min le_max fx0z/= zfx1 orbT.
  exists x => //.
  by apply: subset_itv xx01; rewrite bnd_simp ?(itvP x0ab) ?(itvP x1ab).
have [x [xx01 fxz]] : exists2 x : R, x \in `[x1, x0] & f x = z.
  apply: IVT => //.
  - exact: ltW.
  - apply: continuous_subspaceW cf.
    by apply: subset_trans abD; apply: subset_itv;
      rewrite bnd_simp ?(itvP x0ab) ?(itvP x1ab).
  by rewrite ge_min le_max fx0z/= zfx1 orbT.
exists x => //.
by apply: subset_itv xx01; rewrite bnd_simp ?(itvP x0ab) ?(itvP x1ab).
Qed.

End continuous_interval.

Module lemma6_direct_new.
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

(* https://math.stackexchange.com/questions/1925764/limit-point-of-the-set-of-limit-points-is-in-the-set-of-limit-points *)
Lemma limit_point_redundant (Z : set R) L :
  L = limit_point Z -> limit_point L `<=` L.
(* there is another proof using the fact that limit_point is closed *)
Proof.
move=> LE.
move=> /= p limlimZp.
rewrite LE.
apply/limit_point_open => U pU.
simpl in *.
have [y yp ULy] : exists2 y, y != p & (U `&` L) y.
  have [y [yp Ly Uy]] := limlimZp _ (open_nbhs_nbhs pU).
  by exists y => //.
have [V yV Vp] : exists2 V, nbhs y V & ~ V p.
  have : hausdorff_space R by [].
  rewrite ball_hausdorff => /(_ _ _ yp) -[[r1 r2]/=] => /eqP yr1pr2.
  exists (ball y r1%:num).
    exact: nbhsx_ballx.
  move=> yr1p.
  move: yr1pr2.
  rewrite -subset0.
  move/(_ p).
  by apply; split => //.
have UVy : (U `&` V) y.
  split.
    by case: ULy.
  by apply: nbhs_singleton.
have [z UVZz] : exists z, ((U `&` V) `&` Z) z.
  have : L y by case: ULy.
  rewrite LE.
  rewrite /limit_point/=.
  have : nbhs y (U `&` V).
    apply: filterI => //.
    apply: open_nbhs_nbhs.
    split => //.
      by case: pU.
    by case: UVy.
  move=> /[swap] /[apply] -[z [zy Zz UVz]].
  by exists z; split => //.
have zp : z != p.
  have zV : V z by case: UVZz => -[].
  by apply/eqP => ?; subst z.
exists z; split => //.
by case: UVZz.
by case: UVZz => -[].
Qed.

Definition contiguous_intervals12 (A : set R) : (\bar R * \bar R)^nat :=
  fun n => (contiguous_intervals1 A n, contiguous_intervals2 A n).

(* https://math.stackexchange.com/questions/520209/removing-isolated-points-to-get-a-perfect-set *)
Lemma lemma6_direct : lusinN `[a, b] H.
Proof.
apply: contrapT => nl.
(* use lemma 3 *)
have [Z [Zab cZ isoZ0 Z0 HZ]] : exists Z : set R,
    [/\ Z `<=` `[a, b], compact Z, isolated Z = set0,
        mu Z = 0 & (0%R < mu [set H x | x in Z])%E].
  (* lemma3 *)
  have := image_measure0_Lusin_nondecreasing_new ab cH ndH.
  move/contra_not => /(_ nl).
  move/existsNP=> [Z /not_implyP [Zab /not_implyP[cZ /not_implyP[isoZ0
/not_implyP[muZ0]]]]].
  move/eqP; rewrite neq_lt ltNge measure_ge0/= => muHZ_gt0.
  by exists Z.
have cHZ : compact (H @` Z).
  apply: (@continuous_compact _ _ H Z); last exact: cZ.
  exact: (continuous_subspaceW Zab).
pose c : R := inf Z.
pose d : R := sup Z.
have cd : c < d.
  apply: has_bound_not_subset1_inf_sup.
  - by exists a => ? /Zab/=; rewrite in_itv/= => /andP[].
  - by exists b => ? /Zab/=; rewrite in_itv/= => /andP[].
  move=> Z1.
  move: HZ.
  rewrite measure_gt0/= => /negP; apply; apply/eqP.
  apply: countable_lebesgue_measure0.
  apply: (@sub_countable _ _ _ Z).
    exact: card_image_le.
  exact: is_subset1_countable.
have perfectZ : perfect_set Z.
  apply/perfectP; split => //.
  exact: compact_closed.
pose A_ n := fine (contiguous_intervals1 Z n).
pose B_ n := fine (contiguous_intervals2 Z n).
pose alpha := mu (H @` Z).
have fin_alpha : alpha \is a fin_num.
  rewrite gt0_fin_numE//.
  apply: (@le_lt_trans _ _ (mu (H @` `[a, b]))).
    apply: le_outer_measure.
    exact: image_subset.
  apply: (@le_lt_trans _ _ (mu `[H a, H b])).
    apply: le_outer_measure.
    apply: continuous_nondecreasing_image_itvcc => //.
    exact: ltW.
  have [|] := ltP (H b) (H a).
    rewrite ltNge.
    by rewrite ndH ?boundl_in_itv ?boundr_in_itv ?bnd_simp//= ltW.
  rewrite le_eqVlt => /predU1P[->|HaHb].
    by rewrite set_itv1 completed_lebesgue_measureE lebesgue_measure_set1.
  rewrite completed_lebesgue_measure_itv ifT ?lte_fin//=.
  by rewrite -EFinB ltry.
pose a_ n := sort <%R [tuple A_ i | i < n].
pose b_ n := sort <%R [tuple B_ i | i < n].
pose c_ n i := tnth (c :: b_ n) i.
have tnth_b_ n (i j : 'I_n) : (i < j)%N -> tnth (b_ n) i < tnth (b_ n) j.
  move => ij.
  rewrite /tnth.
  rewrite (set_nth_default (tnth_default (b_ n) j)) ?size_tuple//.
  apply: sorted_ltn_nth => //; rewrite ?inE ?size_tuple//.
  exact: lt_trans.
  (* sorted <%R (b_ n) *)
  admit.
have c_b_ n i : c < tnth (b_ n) i.
  move: n i => [[[]//]|n i].
  suff: c < tnth (b_ n.+1) ord0.
    have [->//|i0] := eqVneq i ord0.
    move=> /lt_le_trans; apply.
    apply/ltW.
    apply: tnth_b_.
    by rewrite lt0n.
  (* c < tnth (b_ n.+1) ord0 *)
  admit.
pose d_ n i := tnth (rcons (a_ n) d) i.
pose lambda n : R :=
  \big[Num.max/0%R]_(i < n.+1) `|d_ n i - c_ n i|.
have lambda_ge0 n : 0 <= lambda n.
  apply: le_trans; last first.
    exact: (le_bigmax _ _ ord0).
  by [].
have lambda0 : lambda @ \oo --> 0.
  apply/cvgrPdist_lt.
  move=> /= e e0.
  near=> n.
  rewrite sub0r normrN ger0_norm; last exact: lambda_ge0.
  rewrite ltNge.
  apply/negP => en.
  admit.
(*
  apply/not_notP.
  suff contra : (forall N, exists n, (N < n)%N /\ e <= lambda n) -> False.
    move=> H.
    apply: contra.
    move=> n.
    move: H.
    rewrite /eventually/filter_from/=.
    move/forallPNP/(_ _ I).
    move/(_ n.+1).
    move/existsNP => [N H].
    have /not_implyP[/= nN] := H.
    move/negP; rewrite -leNgt sub0r normrN gtr0_norm//; last first.
      apply: lambda_gt0.
      exact: leq_ltn_trans nN.
    move=> eN.
    by exists N; split.


    move=> n.
    have -> : Z = [set` Rhull Z] `\` cplt_hull Z.
      rewrite setDD setIidr//.
      exact: sub_Rhull.
    admit.
  admit.
*)
have construct_x n :
  exists x : seq R, [/\ itv_partition c d (behead x),
    (itv_partition_max c d (behead x) <= lambda n),
    (forall i, c_ n i \in x /\ d_ n i \in x),
    (n < size x)%N &
    (forall i j, nth d x j \notin `]c_ n i, d_ n i[) ].
  admit.
pose x := fun n => sval (cid (@construct_x n)).
have pcdx n : itv_partition c d (behead (x n)).
  by have [] := proj2_sig (cid (@construct_x n)).
have max_x n : itv_partition_max c d (behead (x n)) <= lambda n.
  by have [] := proj2_sig (cid (construct_x n)).
pose S_ n : R := variation c d f (behead (x n)).
pose V_ n : R := \sum_(i < n.+1) `|f (d_ n i) - f (c_ n i)| +
     (\sum_(i < n) fine (total_variation (A_ i) (B_ i) f))%R.
pose CD_ n := merge <=%R [tuple c_ n i | i < n.+1] [tuple d_ n i | i < n.+1].
have sub_xcd n : subseq (CD_ n) (x n).
  admit.
have SV n : S_ n <= V_ n.
  rewrite /S_ /V_.
  rewrite /variation.
  rewrite /=.
  admit.
pose Vcd := fine (total_variation c d f).
have V_tv n : V_ n <= Vcd.
  admit.
have Soo_tv : S_ n @[n --> \oo] --> Vcd.
  have ac : a <= c.
    apply: lb_le_inf; last by move=> ? /Zab /=; rewrite in_itv/= => /andP[].
    apply/set0P/negP; move/eqP => Z0'.
    have := HZ; apply/negP.
    rewrite -leNgt le_eqVlt; apply/predU1P; left.
    by rewrite Z0' image_set0 measure0.
  have db : d <= b.
    apply: ge_sup; last by move=> ? /Zab /=; rewrite in_itv/= => /andP[].
    apply/set0P/negP; move/eqP => Z0'.
    have := HZ; apply/negP.
    rewrite -leNgt le_eqVlt; apply/predU1P; left.
    by rewrite Z0' image_set0 measure0.
  have cdcf : {within `[c, d], continuous f}.
    apply: continuous_subspaceW cf.
    by apply: subset_itv; rewrite bnd_simp.
  have cdbvf : bounded_variation c d f.
    apply: (bounded_variationl (ltW cd) db).
    apply: bounded_variationr ac _ bvf.
    by apply: ltW; exact: (lt_le_trans cd).
  have := lemma5 cd cdcf pcdx max_x lambda0.
  rewrite /S_ /Vcd.
  rewrite -[X in _ --> X -> _](@fineK _ (total_variation c d f)); last first.
    admit.
  by move/fine_cvgP => -[_ /=].
have Voo_V : V_ n @[n --> \oo] --> Vcd.
  apply: (squeeze_cvgr _ Soo_tv); last first.
    exact: cvg_cst.
  apply: nearW => n.
  apply/andP; split.
    exact: SV.
  exact: V_tv.
have [n0] : exists2 n0, (0 < n0)%N & forall n, (n >= n0)%N -> V_ n > Vcd - (fine alpha) / 2.
  have alpha20 : 0 < fine alpha / 2.
    rewrite divr_gt0//.
    rewrite -lte_fin fineK//.
  have := Voo_V (ball Vcd (fine alpha / 2)) (nbhsx_ballx _ _ alpha20).
  move=> [n0 _ H].
  exists n0.+1 => //n n0n.
  have := H n (ltnW n0n).
  rewrite /ball/=.
  rewrite ger0_norm; last first.
    rewrite subr_ge0.
    exact: V_tv.
  by rewrite ltrBlDl -ltrBlDr.
move=> n00.
have Z_set0 : Z !=set0.
  apply/set0P/negP; move/eqP => Z_set0.
  have := HZ.
  by rewrite Z_set0 image_set0 measure0; apply/negP; rewrite -leNgt.
have lbZa : lbound Z a.
  move=> r Zr.
  have := Zab r Zr.
  by rewrite /= in_itv/= => /andP[].
have ubZb : ubound Z b.
  move=> r Zr.
  have := Zab r Zr.
  by rewrite /= in_itv/= => /andP[].
near \oo => n.
have n0n : (n0 <= n)%N.
  near: n.
  exact: nbhs_infty_ge.
move/(_ n n0n).
(* (4) *)
rewrite /Vcd/V_.
have -> : fine (total_variation c d f) =
  \sum_(i < n.+1) `|H (d_ n i) - H (c_ n i)| +
   (\sum_(i < n) fine (total_variation (A_ i) (B_ i) f))%R.
  admit.
rewrite addrAC ltrD2r.
(* (5.5) (between (5) and (6)) *)
have alphaH : fine alpha < \sum_(i < n.+1) `|H (d_ n i) - H (c_ n i)|.
  rewrite /alpha.
  have -> : Z = ([set` Rhull Z] `\` cplt_hull Z).
   admit.
  rewrite setDE.
  apply: (@le_lt_trans _ _
    (fine (mu ((H @` [set` Rhull Z]) `&` (H @` (~` cplt_hull Z)))))).
    apply: fine_le.
    - admit.
    - admit.
    apply: le_outer_measure.
    exact: sub_image_setI.
  admit.
move/(@lt_trans _ _ _ (fine alpha / 2)).
rewrite ltrBrDl -splitr; move/(_ alphaH).
(* (6.5) (between (6) and (7)) *)
pose abcd i := [set k | `[A_ k, B_ k] `<=` `[c_ n i, d_ n i]].
have {}n0n : (n0 < n.+1)%N.
  admit.
set on0 := Ordinal n0n.
set Uabcdn := \bigcup_(j in abcd on0) `[A_ j, B_ j]%classic.
have cdi i : c_ n i < d_ n i.
    admit.
(*
have sorted_index_prop : forall n,
   {i_s : seq nat | perm_eq i_s (iota 0 n) &
  sort_ta n = [seq nth d (ta n) i | i <- i_s]}.
  move=> n.
  have := perm_iota_sort <%R _ (ta n).
  by rewrite size_tuple.
pose fun_of_sort_index := fun n => (sval (sorted_index_prop n)).
pose fun_of_sort_indexE := fun n => (svalP (sorted_index_prop n)).1.

pose fun_of_sort_index_ta := fun n => (svalP (sorted_index_prop n)).2.
have fun_of_sort_index_tb : forall n,
  sort_tb n = [seq nth d (tb n) i | i <- sval (sorted_index_prop n)].
have fun_of_sort_prop : forall n, exists (p : {perm 'I_n}), sort_ta n
         = [tuple tnth (ta n) (p i) | i < n].
  move=> n.
  apply/tuple_permP.
  rewrite /sort_ta.
  by rewrite perm_sort.
Print choice.
pose fun_of_sort := fun n => sval (cid (fun_of_sort_prop n)) : {perm 'I_ n}.
pose fun_of_sortE := fun n => svalP (cid (fun_of_sort_prop n)) :
   sort_ta n = [tuple tnth (ta n) (fun_of_sort n i) | i < n].
have fun_of_sort_tb : forall n,
   sort_tb n = [tuple tnth (tb n) (fun_of_sort n i) | i < n].
  move=> n.
  
  admit.
*)
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
have itvfcd i : is_interval (f @` `[c_ n i, d_ n i]).
  apply: (is_interval_image_cc cf).
  apply: subset_itv => //; rewrite bnd_simp.
    rewrite /c_.
    (* a <= c_ n i *)
    admit.
  rewrite /d_.
  (* d_ n i <= b *)
  admit.
have cUabcdn : closed Uabcdn.
    admit.
have hull_Uabcd i : Rhull Uabcdn = `[(c_ n i), (d_ n i)].
    admit.
have prop65 : forall i : 'I_ n.+1, (`|f (d_ n i) - f (c_ n i)|%:E <=
  \sum_(n <= j <oo | `[< `[A_ j, B_ j] `<=` Uabcdn >])
     oscillation f `[A_ j, B_ j])%E.
  move => i.
  apply: lime_ge.
    apply: ereal_nondecreasing_is_cvgn.
    apply: ereal_nondecreasing_series => k _ _.
    exact: oscillation_ge0.
  apply/nearW => k.

  have := @lemma4 _ (c_ n i) (d_ n i) (cdi i) f Uabcdn
                 (itvfcd i) cUabcdn (hull_Uabcd i).
  move/andP => [le1 le2].
  apply: (le_trans (le_trans le1 le2)).
  have -> : (mu^*%mu [set f x | x in Uabcdn] = 0)%E.
    apply/eqP; rewrite eq_le; apply/andP; split; last first.
      exact: outer_measure_ge0.
    have <- : mu^*%mu (f @` Z) = 0.
      rewrite measurable_mu_extE; last first.
        apply: sub_caratheodory.
        apply: compact_measurable.
        apply: continuous_compact => //.
        exact: continuous_subspaceW cf.
      apply: lusinf => //.
      apply: sub_caratheodory.
      exact: compact_measurable.
    apply: le_outer_measure.
    apply: image_subset.
    apply: bigcup_sub => j.
    rewrite /abcd/=.
    move/subset_trans; apply.
    rewrite /a_ /b_.
(*    apply: (subset_trans (contiguous_intervalsS _)).
    rewrite /a_.
*)
    admit.
  admit.
(* (7) *)
have : ((\sum_(i < n.+1) `|f (d_ n i) - f (c_ n i)|)%:E <=
  \sum_(n <= i <oo) oscillation f `[A_ i, B_ i])%E.
  apply: lime_ge.
    apply: ereal_nondecreasing_is_cvgn.
    apply: ereal_nondecreasing_series => m _ _.
    exact: oscillation_ge0.
  near=> m.
  admit.
  (* have := lemma4. *)
have ifcd : is_interval (f @` `[c, d]).
  by apply: (is_interval_image_cc cf); apply: subset_itv; rewrite bnd_simp;
    [exact: lb_le_inf|exact: ge_sup].
have clZ : closed Z by exact: compact_closed.
have hZE : Rhull Z = `[c, d].
  congr Interval.
  - rewrite ifT; last by apply/asboolP; exists a.
    congr BSide.
    apply/asboolP.
    admit.
  - rewrite ifT; last by apply/asboolP; exists b.
    congr BSide.
    apply/asboolPn.
    rewrite not_notE.
    admit.
have := (@lemma4 _ _ _ cd f Z ifcd clZ hZE).
rewrite measurable_mu_extE/=; last first.
  admit.
have -> : mu (f @` Z) = 0.
  apply: lusinf => //=.
  apply: sub_caratheodory.
  exact: compact_measurable.
rewrite add0r.
admit.
Admitted.

End lemma6_direct.

End lemma6_direct_new.

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
pose G_ i := \bigcup_j (open_disjoint_itv (oG i) j).
have H3 i :
  mu (f @` Z1) = mu (f @` (\bigcup_j (Z1 `&` (open_disjoint_itv (oG i) j)))).
  admit.
have H4 i :
    (mu (f @` (\bigcup_j (Z1 `&` (open_disjoint_itv (oG i) j)))) <=
    \sum_(j <oo) (mu^*)%mu (f @` (Z1 `&` (open_disjoint_itv (oG i) j))))%E.
  admit.
have H5 i :
    (\sum_(j <oo) (mu^*)%mu (f @` (Z1 `&` (open_disjoint_itv (oG i) j))) <
    \sum_(j <oo) oscillation f (closure (open_disjoint_itv (oG i) j)))%E.
  admit.
have H6 i :
    (\sum_(j <oo) oscillation f (closure (open_disjoint_itv (oG i) j)) =
    mu (H @` G_ i))%E.
  admit.
apply/eqP; rewrite eq_le measure_ge0 andbT.
Abort.

End lemma6_converse.
