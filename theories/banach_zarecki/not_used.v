From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import boot order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean perm finmap.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions contra cardinality.
From mathcomp Require Import reals topology normedtype ereal sequences derive.
From mathcomp Require Import measure lebesgue_measure numfun realfun.
From mathcomp Require Import measurable_realfun.
From mathcomp Require Import absolute_continuity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma open_itvbb {R : realType} (b0 b1 : bool) (x y : R) :
  open [set` (Interval (BSide b0 x) (BSide b1 y))] =
   (~~ b0 && b1) || (y < x ?<= if ~~ b0 || b1).
Proof.
have e20 (e : R) (e0 : 0 < e) : 0 < e / 2 by rewrite divr_gt0.
have e2e (e : R) (e0 : 0 < e) : e / 2 < e.
  by rewrite {2}(splitr e) ltrDr (e20 _ e0).
have e40 (e : R) (e0 : 0 < e) : 0 < e / 2^+2 by rewrite divr_gt0.
have e42 (e : R) (e0 : 0 < e) : e / 2 ^+ 2 < e / 2.
  rewrite expr2 invfM mulrA.
  rewrite gtr_pMr//; first exact: e20.
  rewrite invf_lt1//.
  by rewrite (_ : 1 = 1%:R)// ltr_nat.
case: b0; case: b1 => //=; rewrite ?orbF ?orbT.
- rewrite propeqE; split; last first.
    move=> yx.
    by rewrite set_itv_ge// bnd_simp -leNgt.
  apply: contraPP.
  move/negP; rewrite -ltNge => xy.
  move/open_itvoo_subset.
  move/(_ x).
  rewrite /= in_itv/= xy lexx/= => /(_ isT).
  move=> [e /= e0].
  move/(_ (e / 2)) => /=.
  rewrite sub0r normrN gtr0_norm ?e20// e2e// => /(_ isT isT).
  move/(_ (x - e / (2^+2))) => /=.
  have sub_itv : x - e / 2 ^+ 2 \in `]x - e / 2, x + e / 2[.
    rewrite in_itv/=; apply/andP; split.
      by rewrite ler_ltB// e42//.
    rewrite ltrD2l.
    apply: (lt_trans _ (e42 _ e0)).
    by rewrite gtrN ?e40.
  move/(_ sub_itv).
  rewrite in_itv/=.
  apply/negP.
  rewrite negb_and; apply/orP; left.
  rewrite -ltNge.
  by rewrite gtrBl e40.
- rewrite propeqE; split; last first.
    by move=> yx; rewrite set_itv_ge// bnd_simp -ltNge.
  apply: contraPP; move/negP; rewrite -leNgt => xy.
  move/open_itvoo_subset.
  move/(_ x).
  rewrite /= in_itv/= xy lexx/= => /(_ isT).
  move=> [e /= e0].
  move/(_ (e / 2)) => /=.
  rewrite sub0r normrN gtr0_norm ?e20// e2e// => /(_ isT isT).
  move/(_ (x - e / (2^+2))) => /=.
  have sub_itv : x - e / 2 ^+ 2 \in `]x - e / 2, x + e / 2[.
    rewrite in_itv/=; apply/andP; split.
      by rewrite ler_ltB//  e42//.
    rewrite ltrD2l.
    apply: (lt_trans _ (e42 _ e0)).
    by rewrite gtrN ?e40.
  move/(_ sub_itv).
  rewrite in_itv/=.
  apply/negP.
  rewrite negb_and; apply/orP; left.
  rewrite -ltNge.
  by rewrite gtrBl e40.
- by rewrite propeqE; split.
- rewrite propeqE; split; last first.
    by move=> yx; rewrite set_itv_ge// bnd_simp -leNgt.
  apply: contraPP; move/negP; rewrite -ltNge => xy.
  move/open_itvoo_subset.
  move/(_ y).
  rewrite /= in_itv/= xy lexx/= => /(_ isT).
  move=> [e /= e0].
  move/(_ (e / 2)) => /=.
  rewrite sub0r normrN gtr0_norm ?e20// e2e// => /(_ isT isT).
  move/(_ (y + e / (2^+2))) => /=.
  have sub_itv : y + e / 2 ^+ 2 \in `]y - e / 2, y + e / 2[.
    rewrite in_itv/=; apply/andP; split.
      rewrite ler_ltD//.
      apply: (lt_trans _ (e40 _ e0)).
      by rewrite ltrNl oppr0 e20.
    by rewrite ltrD2l e42.
  move/(_ sub_itv).
  rewrite in_itv/=.
  apply/negP.
  rewrite negb_and; apply/orP; right.
  rewrite -ltNge.
  by rewrite ltrDl e40.
Qed.

Lemma open_itvby {R : realType} (b0 : bool) (x : R) :
  open [set` (Interval (BSide b0 x) +oo%O)] = ~~ b0.
Proof.
have e20 (e : R) (e0 : 0 < e) : 0 < e / 2 by rewrite divr_gt0.
have e2e (e : R) (e0 : 0 < e) : e / 2 < e.
  by rewrite {2}(splitr e) ltrDr (e20 _ e0).
have e40 (e : R) (e0 : 0 < e) : 0 < e / 2^+2 by rewrite divr_gt0.
have e42 (e : R) (e0 : 0 < e) : e / 2 ^+ 2 < e / 2.
  rewrite expr2 invfM mulrA.
  rewrite gtr_pMr//; first exact: e20.
  rewrite invf_lt1//.
  by rewrite (_ : 1 = 1%:R)// ltr_nat.
case: b0 => /=.
- rewrite propeqE; split => //.
  rewrite falseE.
  move/open_itvoo_subset.
  move/(_ x).
  rewrite /= in_itv/= lexx/= => /(_ isT).
  move=> [e /= e0].
  move/(_ (e / 2)) => /=.
  rewrite sub0r normrN gtr0_norm ?e20// e2e// => /(_ isT isT).
  move/(_ (x - e / (2^+2))) => /=.
  have sub_itv : x - e / 2 ^+ 2 \in `]x - e / 2, x + e / 2[.
    rewrite in_itv/=; apply/andP; split.
      by rewrite ler_ltB// e42//.
    rewrite ltrD2l.
    apply: (lt_trans _ (e42 _ e0)).
    by rewrite gtrN ?e40.
  move/(_ sub_itv).
  rewrite in_itv/=.
  apply/negP.
  rewrite negb_and; apply/orP; left.
  rewrite -ltNge.
  by rewrite gtrBl e40.
by rewrite propeqE; split.
Qed.

Lemma open_itvNyb {R : realType} (b1 : bool) (y : R) :
  open [set` (Interval -oo%O (BSide b1 y))] = b1.
Proof.
have e20 (e : R) (e0 : 0 < e) : 0 < e / 2 by rewrite divr_gt0.
have e2e (e : R) (e0 : 0 < e) : e / 2 < e.
  by rewrite {2}(splitr e) ltrDr (e20 _ e0).
have e40 (e : R) (e0 : 0 < e) : 0 < e / 2^+2 by rewrite divr_gt0.
have e42 (e : R) (e0 : 0 < e) : e / 2 ^+ 2 < e / 2.
  rewrite expr2 invfM mulrA.
  rewrite gtr_pMr//; first exact: e20.
  rewrite invf_lt1//.
  by rewrite (_ : 1 = 1%:R)// ltr_nat.
  case: b1 => //=.
- by rewrite propeqE; split.
rewrite propeqE; split => //.
rewrite falseE.
move/open_itvoo_subset.
move/(_ y).
rewrite /= in_itv/= lexx/= => /(_ isT).
move=> [e /= e0].
move/(_ (e / 2)) => /=.
rewrite sub0r normrN gtr0_norm ?e20// e2e// => /(_ isT isT).
move/(_ (y + e / (2^+2))) => /=.
have sub_itv : y + e / 2 ^+ 2 \in `]y - e / 2, y + e / 2[.
  rewrite in_itv/=; apply/andP; split.
    rewrite ler_ltD//.
    apply: (lt_trans _ (e40 _ e0)).
    by rewrite ltrNl oppr0 e20.
  by rewrite ltrD2l e42.
move/(_ sub_itv).
rewrite in_itv/=.
apply/negP.
rewrite -ltNge.
by rewrite ltrDl e40.
Qed.

Lemma not_bounded_itvby {R : realType} (b0 : bool) (r : R) :
   ~ bounded_set [set` (Interval (BSide b0 r) +oo%O)].
Proof.
suff hubr : ~ has_ubound [set z | r < z].
case: b0; rewrite set_itvE Rbounded_setE; apply/not_andP; right => //.
  apply/forallNP => x.
  have/forallNP/(_ x) := hubr.
  move/existsNP => [z/= /not_implyP[rz /negP]]; rewrite -ltNge => xz.
  apply/existsNP; exists z.
  by apply/not_implyP; split; [|apply/negP]; rewrite /= -?ltNge ?ltW.
apply/forallNP => x.
move/(_ (`|r| + 1 + (`|x| + 1))) => /=.
have rrx : r < `|r| + 1 + (`|x| + 1).
  rewrite -{1}(addr0 r).
  apply: ltrD => //.
  by rewrite (@le_lt_trans _ _ `|r|) ?ltrDl ?ler_norm.
move/(_ rrx).
apply/negP.
rewrite -ltNge -{1}(add0r x).
rewrite ltrD => //.
by rewrite (@le_lt_trans _ _ `|x|) ?ltrDl ?ler_norm.
Qed.

Lemma not_bounded_itvNyb {R : realType} (b0 : bool) (r : R) :
   ~ bounded_set [set` (Interval -oo%O (BSide b0 r))].
Proof.
suff hubr : ~ has_lbound [set z | z < r].
case: b0; rewrite set_itvE Rbounded_setE; apply/not_andP; left => //.
  apply/forallNP => x.
  have/forallNP/(_ x) := hubr.
  move/existsNP => [z/= /not_implyP[rz /negP]]; rewrite -ltNge => xz.
  apply/existsNP; exists z.
  by apply/not_implyP; split; [|apply/negP]; rewrite /= -?ltNge ?ltW.
apply/forallNP => x.
move/(_ (- (`|r| + 1 + (`|x| + 1)))) => /=.
have rxr : - (`|r| + 1 + (`|x| + 1)) < r.
  rewrite -{2}(addr0 r) opprD.
  apply: ltrD => //.
  rewrite (@lt_le_trans _ _ (- `|r|))//.
    by rewrite ltrN2 ltrDl.
  by rewrite lerNl -normrN ler_norm.
move/(_ rxr).
apply/negP.
rewrite -ltNge -{2}(add0r x).
rewrite opprD ltrD => //.
rewrite (@lt_le_trans _ _ (- `|x|))//.
  by rewrite ltrN2 ltrDl.
by rewrite lerNl -normrN ler_norm.
Qed.

Lemma not_bounded_setT {R : realType} : ~ (bounded_set [set: R]).
Proof.
apply/forallNP => x.
rewrite -implypN => _.
move/(_ (`|x| + 1)).
have xx1 : x < `|x| + 1.
  apply: (le_lt_trans (ler_norm _)).
  by rewrite ltrDl.
move/(_ xx1).
apply/existsNP => /=.
exists (`|x| + 1 + 1).
apply/not_implyP; split => //.
apply/negP; rewrite -ltNge.
rewrite [ltRHS]ger0_norm//.
by rewrite ltrDl.
Qed.

Lemma nonempty_open_bounded_itvoo {R : realType} (i : interval R) :
  [set` i] !=set0 -> open [set` i] -> bounded_set [set` i] ->
  exists a b : R, a < b /\ i = `]a, b[.
Proof.
case: i.
move=> [[l|l]|[]][[r|r]|[]];
  rewrite ?open_itvbb ?open_itvby ?open_itvNyb//=; last 10 first.
- move/[swap] => rl.
  by move/set0P; rewrite set_itv_ge ?eqxx// bnd_simp -leNgt.
- by rewrite set_itvE; move/set0P; rewrite eqxx.
- by move=> _ _ /not_bounded_itvby.
- by move=> _ _ /not_bounded_itvNyb.
- by rewrite set_itvE => /set0P/negP.
- by rewrite set_itvE => _ _ /not_bounded_setT.
- by rewrite set_itvE => /set0P/negP.
- by rewrite set_itvE => /set0P/negP.
- by rewrite set_itvE => /set0P/negP.
- by rewrite set_itvE => /set0P/negP.
- move/[swap] => rl; rewrite set_itv_ge; first by rewrite bnd_simp -leNgt.
  by move/set0P/negP.
- move/[swap] => rl; rewrite set_itv_ge; first by rewrite bnd_simp -ltNge.
  by move/set0P/negP.
- by rewrite set_itvE => /set0P/negP.
move=> [x/=]; rewrite in_itv/= => /andP[lx] /(lt_trans lx) {x lx} lr.
by exists l, r; split.
Qed.

Lemma open_nonempty_not_subset1 {R : realType} (i : interval R) :
  open [set` i] -> [set` i] !=set0 ->
  ~ (is_subset1 [set` i]).
Proof.
move=> oi [x ix].
have [e/= e0 He] := open_itvcc_subset oi ix.
have e2e : `|0 - e / 2| < e.
  rewrite sub0r normrN ger0_norm; first by rewrite mulr_ge0// ltW.
  rewrite {2}(splitr e) ltrDl.
  by rewrite mulr_gt0.
move/(_ (x - e / 2) (x + e / 2)).
apply/not_implyP; split.
  apply: (He (e / 2)) => //=.
    by rewrite mulr_gt0.
  by rewrite boundl_in_itv/= bnd_simp lerD2l ge0_cp// mulr_ge0// ltW.
apply/not_implyP; split.
  apply: (He (e / 2)) => //=.
    by rewrite mulr_gt0.
  by rewrite boundr_in_itv/= bnd_simp lerD2l ge0_cp// mulr_ge0// ltW.
apply/eqP; rewrite eq_le negb_and; apply/orP; right; rewrite -ltNge.
by rewrite ltrD2l gt0_cp// mulr_gt0.
Qed.

Lemma not_limit_point_set1 {R : realType} (A : set R) (a : R) :
  ~ limit_point A a ->
  exists e : {posnum R}, ball a e%:num `&` A `<=` [set a].
Proof.
move=> Ua; apply/not_existsP => aAa.
apply: Ua; rewrite /limit_point => /= V [e /= e0 aeV].
have /nonsubset[/= x [[aex Ax] /eqP xa]] := aAa (PosNum e0).
by exists x; split => //; exact: aeV.
Qed.

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

Lemma limit_point_interior (A : set R) :
  interior A `<=` limit_point (interior A).
Proof.
move=> /= x [e /=e0].
rewrite open_subsetE; first exact: ball_open.
 move=> ballxA.
apply/limit_pointP.
exists (fun n => x - e / n.+2%:R); split.
- move=> _/= [n _ <-].
  apply: ballxA; rewrite /ball_/=.
  rewrite opprB addrCA subrr addr0 ger0_norm.
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

End interior_lemmas.

Section limit_point_redundant.

Lemma limit_point_open {R : realType} (U : set R) (p : R) :
  limit_point U p <-> forall V, open_nbhs p V ->
                         exists y : R, [/\ y != p, U y & V y].
Proof.
split.
  move=> Up /= V pV.
  apply: Up.
  by apply: open_nbhs_nbhs.
move=> /= H V.
rewrite nbhsE/= => -[A pA AV].
have [y [yp Uy Ay]] := H _ pA.
exists y; split => //.
by apply: AV.
Qed.

(* https://math.stackexchange.com/questions/1925764/limit-point-of-the-set-of-limit-points-is-in-the-set-of-limit-points *)
Lemma limit_point_redundant {R : realType} (Z : set R) L :
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

End limit_point_redundant.
