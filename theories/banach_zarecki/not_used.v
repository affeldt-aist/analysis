From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import boot order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean perm finmap.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions contra cardinality.
From mathcomp Require Import reals convex topology normedtype ereal sequences.
From mathcomp Require Import derive measure lebesgue_measure numfun realfun.
From mathcomp Require Import measurable_realfun.
From mathcomp Require Import absolute_continuity interleave.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma reshape_index_cons {T} i (x : seq T) (sh : seq (seq T)) :
  (i < size x)%N -> reshape_index (shape (x :: sh)) i = 0%N.
Proof.
move=> ix.
rewrite /reshape_index/= ifT//.
Qed.

Lemma nth_flatten_bounds {R : eqType} (ss : seq (seq R)) i
    (r := reshape_index (shape ss) i)
    (c := reshape_offset (shape ss) i) :
  (i < size (flatten ss))%N ->
  (r < size ss)%N /\ (c < size (nth [::] ss r))%N.
Proof.
rewrite size_flatten => H; split.
  rewrite /r -(size_map size).
  exact: reshape_indexP.
rewrite -nth_shape.
exact: reshape_offsetP.
Qed.

Lemma nth_flatten_interleaveE {R : realType}
    (d : R) (s t : seq (seq R)) i
    (r := reshape_index (shape (interleave s t)) i)
    (c := reshape_offset (shape (interleave s t)) i) :
  size s = size t ->
  nth d (flatten (interleave s t)) i =
    if odd r then
      nth d (nth [::] t r./2) c
    else
      nth d (nth [::] s r./2) c.
Proof.
move=> st.
rewrite nth_flatten (nth_interleaveE [::]) -/r -/c.
case: ifP.
  by case: ifP.
move/negP/negP; rewrite -leqNgt.
rewrite size_interleave => str.
case: ifP; rewrite !nth_default => //; apply: leq_trans (half_leq str).
  by rewrite doubleK st minnn.
by rewrite doubleK st minnn.
Qed.

Section all2_nthP.
Context {S T : eqType}.
Implicit Types (a : S -> T -> bool).
Implicit Types (s : seq S) (t : seq T).

Lemma all2_nthP a s t (ds : S) (dt : T) :
reflect (size s = size t /\
  (forall i : nat, (i < size (zip s t))%N -> a (nth ds s i) (nth dt t i)))
 (all2 a s t).
Proof.
rewrite all2E.
case st : (size s == size t) => /=; last first.
  apply: ReflectF.
  apply/not_andP; left.
  by move/eqP : st.
apply: (@iffP _ _ _ (all_nthP (ds, dt))) => [H|[st' H]].
  split.
    by apply/eqP.
  move=> i /H.
  by rewrite nth_zip => //; apply/eqP.
move=> i /H.
by rewrite nth_zip.
Qed.

Lemma all2_predC a s t :
  all2 (curry (predC (uncurry a))) s t =
      (size s == size t) && ~~ has (uncurry a) (zip s t).
Proof.
elim: s t.
  case => //.
move=> s0 s1 IH.
case => //= t0 t1.
by rewrite IH eqSS negb_or andbCA.
Qed.

End all2_nthP.

Section count2.
Context {S T : Type}.
Implicit Types (a : S -> T -> bool).
Implicit Types (s : seq S) (t : seq T).

Fixpoint count2 a s t : nat :=
  if s is x :: s' then
    if t is y :: t' then
         a x y + count2 a s' t' else 0 else 0.

Lemma eq_count2 a1 a2 : a1 =2 a2 -> count2 a1 =2 count2 a2.
Proof.
move=> a12 s t.
elim: s t => // s0 s1 IH.
by case => //= t0 t1; rewrite a12 IH.
Qed.

Lemma count2_le_minn a s t :
  (count2 a s t <= minn (size s) (size t))%N.
Proof.
elim: s t => [|x s IH] [|y t] //=.
case: (a x y) => /=.
- by rewrite minnSS; exact: IH t.
- rewrite minnSS.
  exact: leq_trans (IH t) (leqnSn _).
Qed.

Lemma all2_count2 a s t :
  all2 a s t =
    (size s == size t) &&
    (count2 a s t == minn (size s) (size t)).
Proof.
elim: s t => [|x s IH] [|y t] //=.
rewrite minnSS.
case: (a x y) => /=.
  by rewrite IH.
case: ((size s).+1 == (size t).+1) => //=; rewrite add0n.
apply: esym; apply: ltn_eqF.
rewrite ltnS.
exact: (count2_le_minn a s t).
Qed.

Lemma eq_all2 a1 a2 :
  a1 =2 a2 -> all2 a1 =2 all2 a2.
Proof.
by move=> Ea s t; rewrite !all2_count2 (eq_count2 Ea).
Qed.

End count2.

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

Section convex.

Lemma Monem {R : realType} (x : R) (t : {i01 R}) : (t%:num).~ *: x = x - t%:num *: x.
Proof. by rewrite /onem [LHS]mulrBl mul1r. Qed.

Lemma convex_interval {R : realType} (i : interval R) : convex_set [set` i].
Proof.
move=> /= x y t /[!inE] ix iy.
wlog : t x y ix iy / x <= y.
  move=> wlg.
  have /orP[xy|yx] := le_total x y; first exact: wlg.
  by rewrite convC/=; exact: wlg.
move=> xy.
apply: (@interval_is_interval _ _ _ _ ix iy).
rewrite /conv/=; apply/andP; split.
  rewrite -subr_ge0 addrAC -(opprB x) -Monem addrC.
  by rewrite -[leRHS]mulrBr mulr_ge0 ?subr_ge0.
rewrite -subr_ge0 opprD addrCA Monem opprB subrKC addrC.
by rewrite -[leRHS]mulrBr mulr_ge0 ?subr_ge0.
Qed.

Lemma closure_seq {R : realType} (A : set R) x : x \in closure A <->
  exists x_ : R^nat, [/\ range x_ `<=` A,
                         forall n, `|x_ n - x| < n.+1%:R^-1 &
                         x_ @ \oo --> x].
Proof.
split.
  rewrite inE => Ax.
  have : forall n, exists un : R, A un /\ `|un - x| < n.+1%:R^-1.
     move=> n.
     move: Ax => /(_ (ball x n.+1%:R^-1) (nbhsx_ballx _ _ _)).
     rewrite invr_gt0 ltr0n => /(_ isT)[un [Aun xn]].
     exists un; split => //.
     by move: xn; rewrite /ball/= distrC.
  move=> /choice[x_ Ax_]; exists x_; split.
  - by move=> r [m _ <-]; apply Ax_.
  - by move=> m; apply Ax_.
  - apply/cvgrPdist_le => /= e e0; near=> n.
    rewrite distrC (le_trans (ltW (Ax_ _).2))// invf_ple ?posrE// -natr1 -lerBlDr.
    by near: n; exact: nbhs_infty_ger.
move=> [x_ [x_A x_x x_oo]].
rewrite inE closureE => B [cloB AB].
move: x_oo.
apply: closed_cvg => //.
apply/nearW => m.
exact/AB/x_A/imageT.
Unshelve. all: end_near. Qed.

Lemma closure_convex_set {R : realType} (A : set R) : convex_set A -> convex_set (closure A).
Proof.
move=> convA x y t xA yA; apply/closure_seq.
have [x_ [x_A x_x x_oo]]:= (closure_seq _ _).1 xA.
have [y_ [y_A y_y y_oo]]:= (closure_seq _ _).1 yA.
pose z_ n := conv t (x_ n : R^o) (y_ n).
exists z_; split.
- move=> r [n _ <-].
  apply/set_mem.
  rewrite convA//; apply/mem_set.
    by apply: x_A; exact/imageT.
  by apply: y_A; exact/imageT.
- move=> n.
  rewrite /z_ convRE /conv/= opprD addrACA -!mulrBr.
  rewrite (le_lt_trans (ler_normD _ _))// !normrM.
  have [->|t0] := eqVneq t%:num 0.
    by rewrite normr0 mul0r add0r onem0 normr1 mul1r.
  have [->|t1] := eqVneq t%:num 1.
    by rewrite onem1 normr0 mul0r addr0 normr1 mul1r.
  rewrite ger0_norm// (@ger0_norm _ _.~) ?onem_ge0//.
  rewrite -[ltRHS]mul1r -[X in _ < X * _](add_onemK t%:num) [in ltRHS]mulrDl.
  rewrite ltrD//.
    by rewrite ltr_pM2l// lt_neqAle eq_sym t0/=.
  by rewrite ltr_pM2l// onem_gt0// lt_neqAle t1/=.
- by apply: cvgD; exact: cvgMl_tmp.
Qed.

Lemma convex_is_inverval {R : realType} (A : set R) : convex_set A -> is_interval A.
Proof.
move=> convA x y Ax Ay z.
have [<-|xy] := eqVneq x y.
  by rewrite -eq_le => /eqP <-.
move=> /andP[xz zy].
have := convA x y.
pose t := (y - z) / (y - x).
have t_ge0 : 0 <= t.
  rewrite divr_ge0 ?subr_ge0//.
  by rewrite (le_trans xz).
have t_le1 : t <= 1.
  rewrite ler_pdivrMr//.
    by rewrite subr_gt0 lt_neqAle xy/= (le_trans xz).
  by rewrite mul1r lerB.
have -> : z = t *: x + t.~ *: y.
  rewrite /t.
  rewrite /onem.
  rewrite -(@divff _ (y - x)) ?subr_eq0 1?eq_sym//.
  rewrite -mulrBl.
  rewrite opprB.
  rewrite (addrC (y - x)) addrA subrK.
  rewrite -[X in _ = _ + X]mulrA mulrCA.
  rewrite -[X in _ = X + _]mulrA [X in _ = X + _]mulrCA.
  rewrite -mulrDr.
  rewrite 2!mulrBl addrACA (addrC (y * x + _)).
  rewrite addrA (mulrC y x) subrK (addrC _ (z * y)) -mulrBr mulrCA mulVf ?mulr1//.
  by rewrite subr_eq0 eq_sym.
pose T := Itv01 t_ge0 t_le1.
by move/(_ T (mem_set Ax) (mem_set Ay)) /set_mem.
Qed.

Lemma smallest_convex_set {R : realType} (A B : set R) : A `<=` B ->
  convex_set B -> [set` Rhull A] `<=` B.
Proof.
move=> AB convB.
rewrite Rhull_smallest => C.
apply; split => //.
exact: convex_is_inverval.
Qed.

End convex.

Section closed_Rhull.

Lemma closed_Rhull {R : realType} (A : set R) : closed A -> closed [set` Rhull A].
Proof.
move=> cloA.
have [->|/set0P A0] := eqVneq A set0.
  by rewrite Rhull0 set_itv_ge ?bnd_simp//=; exact: closed0.
set b := sup A.
have H : has_ubound A -> A b.
  move=> ubA.
  have : forall n, exists un, A un /\ b - n.+1%:R^-1 < un <= b.
    move=> n.
    have : b - n.+1%:R^-1 < b by rewrite gtrDl.
    move=> /(sup_gt A0)[un Aun una]; exists un; split => //.
    by rewrite una/= ub_le_sup.
  move=> /choice[un Aun].
  have : un @ \oo --> b.
    apply/cvgrPdist_le => /= e e0.
    near=> n.
    have [_ /andP[bun unb]] := Aun n.
    rewrite ler_distlC; apply/andP; split.
      rewrite (le_trans _ (ltW bun))// lerB// invf_ple ?posrE// -nat1r -lerBlDl.
      by near: n; exact: nbhs_infty_ger.
    by rewrite (le_trans unb)// lerDl ltW.
  apply: closed_cvg => //; apply/nearW => n.
  by have := (Aun n).1.
rewrite /Rhull.
have [lbA|lbA] := asboolP (has_lbound A).
  set a := inf A.
  have aA : A a.
    have : forall n, exists un, A un /\ a <= un < a + n.+1%:R^-1.
      move=> n.
      have : a < a + n.+1%:R^-1 by rewrite ltrDl.
      move=> /(inf_lt A0)[un Aun una]; exists un; split => //.
      by rewrite una andbT ge_inf.
    move=> /choice[un Aun].
    have : un @ \oo --> a.
      apply/cvgrPdist_le => /= e e0.
      near=> n.
      have [_ /andP[aun una]] := Aun n.
      rewrite ler_distlC; apply/andP; split.
        by rewrite lerBlDr (le_trans aun)// lerDl ltW.
      rewrite (le_trans (ltW una))// lerD2l invf_ple ?posrE// -nat1r -lerBlDl.
      by near: n; exact: nbhs_infty_ger.
    apply: closed_cvg => //; apply/nearW => n.
    by have := (Aun n).1.
  have [ubA|ubA] := asboolP (has_ubound A).
    have Ab := H ubA.
    by rewrite !asboolT//=; exact: itv_closed_ends_closed.
  by case: asboolP => // _; exact: itv_closed_ends_closed.
have [ubA|ubA] := asboolP (has_ubound A); last exact: itv_closed_ends_closed.
by have bA : A b := H ubA; rewrite !asboolT.
Unshelve. all: end_near. Qed.

Lemma closure_Rhull {R : realType} (A : set R) :
  closure [set` Rhull A] = [set` Rhull (closure A)].
Proof.
apply/seteqP; split.
  have AA : [set` Rhull A] `<=` [set` Rhull (closure A)].
    by apply: le_Rhull; exact: subset_closure.
  have closedA : closed [set` Rhull (closure A)].
    by apply: closed_Rhull; exact: closed_closure.
  rewrite closureE => /= r.
  by move/(_ [set` Rhull (closure A)]); apply.
set C := [set` Rhull A].
have convC : convex_set C by exact: convex_interval.
have convclosureC : convex_set (closure C).
  exact: closure_convex_set.
have AcloC : A `<=` closure C.
  apply: subset_trans; last exact: subset_closure.
  exact: sub_Rhull.
have cloAcloC : closure A `<=` closure C.
  rewrite closureE.
  apply: smallest_sub => //.
  exact: closed_closure.
exact: smallest_convex_set.
Qed.

End closed_Rhull.
