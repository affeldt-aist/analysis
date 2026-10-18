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
From mathcomp Require Import absolute_continuity banach_zarecki_lemma2.
From mathcomp Require Import banach_zarecki_lemma3 banach_zarecki_lemma5.
From mathcomp Require Import banach_zarecki_lemma4 (* for contiguous intervals *).
From mathcomp Require Import mesh oscillation interleave variation_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section diam.
Context {R : realType}.

Definition diam (A : set R) :=
  if A == set0 then 0%:E else
  ereal_sup ([set `|a.1 - a.2|%:E | a in setX A A]).

Lemma diam0 : diam set0 = 0%:E.
Proof.
by rewrite /diam eqxx.
Qed.

Lemma diam_ge0 (A : set R) : (0 <= diam A)%E.
Proof.
rewrite /diam; case: ifPn => //.
move/set0P => [x Ax].
apply: le_ereal_sup_tmp.
by exists 0 => //; exists (x, x) => /=; rewrite ?subrr ?normr0//.
Qed.

Lemma diamS (A B : set R) : A `<=` B -> (diam A <= diam B)%E.
Proof.
move=> AB.
rewrite {1}/diam; case : ifPn => [_|].
  exact: diam_ge0.
move/set0P => [a Aa].
rewrite /diam; case: ifPn => [|_].
  move/eqP => B0.
  have := AB a Aa.
  by rewrite B0.
apply: ereal_sup_le => r/= [[x y] [/= Ax Ay] <-].
exists (x, y) => //=.
by split; apply: AB.
Qed.

Section diam_itv.
Implicit Types x y : R.

Let diam_itvcc x y : x < y -> diam [set` `[x, y]] = (y - x)%:E.
Proof.
move=> xy; rewrite /diam ifF.
  by apply/negbTE/set0P; eexists; apply: mid_in_itv => /=; exact: ltW.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: ge_ereal_sup => /= z/= [[z1 z2]]/= [].
  rewrite !in_itv/= => /andP[xz1 z1y] /andP[xz2 z2y] <-.
  rewrite lee_fin.
  have [z12|z12] := leP z1 z2.
    by rewrite ler0_norm ?subr_le0// opprB lerB.
  by rewrite gtr0_norm ?subr_gt0// lerB.
apply: ereal_sup_ubound => /=; exists (y, x) => //=.
  by rewrite !bound_itvE (ltW xy).
by rewrite gtr0_norm// subr_gt0.
Qed.

Let diam_itvoc x y : x < y -> diam [set` `]x, y]] = (y - x)%:E.
Proof.
move=> xy; rewrite /diam ifF.
  by apply/negbTE/set0P; eexists => /=; exact: mid_in_itv.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: ge_ereal_sup => /= z/= [[z1 z2]]/= [].
  rewrite !in_itv/= => /andP[xz1 z1y] /andP[xz2 z2y] <-.
  rewrite lee_fin.
  have [z12|z12] := leP z1 z2.
    by rewrite ler0_norm ?subr_le0// opprB lerB// ltW.
  by rewrite gtr0_norm ?subr_gt0// lerB// ltW.
apply/lee_addgt0Pr => /=e e0.
rewrite -leeBlDr//; apply: le_ereal_sup_tmp.
pose d : R := (Num.min e (y - x)) / 2.
pose a := y.
pose b := x + d.
exists `|a - b|%:E.
  exists (a, b) => //=.
  rewrite !in_itv//= /a xy/= lexx//=; split => //.
  rewrite ltrDl; apply/andP; split.
    by rewrite divr_gt0// lt_min e0/= subr_gt0.
  rewrite /b -lerBrDl /d ler_pdivrMr// ge_min.
  by rewrite ler_pMr ?subr_gt0// ler1n orbT.
rewrite /a /b -EFinB lee_fin ger0_norm.
  rewrite opprD addrA subr_ge0.
  rewrite ler_pdivrMr// ge_min.
  by rewrite ler_pMr ?subr_gt0// ler1n orbT.
rewrite opprD addrA lerB// /d.
rewrite ler_pdivrMr// ge_min.
by rewrite ler_pMr// ler1n.
Qed.

Let diam_itvco x y : x < y -> diam [set` `[x, y[] = (y - x)%:E.
Proof.
move=> xy; rewrite /diam ifF.
  by apply/negbTE/set0P; eexists => /=; exact: mid_in_itv.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: ge_ereal_sup => /= z/= [[z1 z2]]/= [].
  rewrite !in_itv/= => /andP[xz1 z1y] /andP[xz2 z2y] <-.
  rewrite lee_fin.
  have [z12|z12] := leP z1 z2.
    by rewrite ler0_norm ?subr_le0// opprB lerB// ltW.
  by rewrite gtr0_norm ?subr_gt0// lerB// ltW.
apply/lee_addgt0Pr => /=e e0.
rewrite -leeBlDr//.
apply: le_ereal_sup_tmp.
pose d : R := (Num.min e (y - x)) / 2.
pose a := x.
pose b := y - d.
exists `|a - b|%:E.
  exists (a, b) => //=.
  rewrite !in_itv//= /b xy/= lexx//=; split => //.
  apply/andP; split.
    rewrite -lerBlDl -lerN2 opprK opprB.
    rewrite ler_pdivrMr// ge_min.
    by rewrite ler_pMr ?subr_gt0// ler1n orbT.
  by rewrite gtrBl divr_gt0// lt_min e0 subr_gt0.
rewrite /a /b -EFinB lee_fin opprB addrCA.
rewrite ler0_norm.
  rewrite -opprB subr_le0.
  rewrite ler_pdivrMr//.
  rewrite ge_min.
  by rewrite ler_pMr ?subr_gt0// ler1n orbT.
rewrite opprD opprB [leRHS]addrC lerB//.
rewrite ler_pdivrMr// ge_min.
by rewrite ler_pMr// ler1n.
Qed.

Let diam_itvoo (x y : R) : x < y -> diam [set` `]x, y[] = (y - x)%:E.
Proof.
move=> xy; rewrite /diam ifF.
  by apply/negbTE/set0P; eexists => /=; exact: mid_in_itv.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: ge_ereal_sup => /= z/= [[z1 z2]]/= [].
  rewrite !in_itv/= => /andP[xz1 z1y] /andP[xz2 z2y] <-.
  rewrite lee_fin.
  have [z12|z12] := leP z1 z2.
    by rewrite ler0_norm ?subr_le0// opprB lerB// ltW.
  by rewrite gtr0_norm ?subr_gt0// lerB// ltW.
apply/lee_addgt0Pr => /=e e0.
rewrite -leeBlDr//.
apply: le_ereal_sup_tmp.
pose d : R := (Num.min e (y - x)) / 4.
pose a := x + d.
pose b := y - d.
have d0 : 0 < d by rewrite divr_gt0// lt_min e0/= subr_gt0.
exists `|a - b|%:E.
  rewrite /=.
  exists (a, b) => //=.
  rewrite !in_itv//= ltrDl gtrBl d0 andbT/=; split.
    rewrite /a -ltrBrDl ltr_pdivrMr// gt_min.
    by rewrite ltr_pMr ?subr_gt0// ltr1n orbT.
  rewrite /b.
  rewrite -ltrBlDr opprK -ltrBrDl ltr_pdivrMr// gt_min.
  by rewrite ltr_pMr ?subr_gt0// ltr1n orbT.
rewrite /a /b -EFinB lee_fin opprD opprK addrACA -mulr2n.
rewrite ler0_norm.
  rewrite -opprB addrC subr_le0.
  rewrite -mulr_natr /d (_ : 4 = 2 * 2); first by rewrite -natrM.
  rewrite -mulrA invfM -mulrA mulVf// mulr1.
  by rewrite ler_pdivrMr// ge_min ler_pMr ?subr_gt0// ler1n orbT.
rewrite opprD opprB lerB//.
rewrite -mulr_natr /d (_ : 4 = 2 * 2); first by rewrite -natrM.
rewrite -mulrA invfM -mulrA mulVf// mulr1.
by rewrite ler_pdivrMr// ge_min ler_pMr// ler1n.
Qed.

Lemma diam_itv (x y : R) (b0 b1 : bool) : x <= y ->
  diam [set` (Interval (BSide b0 x) (BSide b1 y))] = (y - x)%:E.
Proof.
rewrite le_eqVlt => /predU1P[<-{y}|xy].
  move: b0 b1 => [|] [|]/=.
  by rewrite set_itv_ge ?subrr ?diam0// bnd_simp ltxx.
  rewrite /diam [X in ereal_sup X](_ : _ = [set 0]) ?ereal_sup1//.
    apply/seteqP; split.
      move=> /= z [[z1 z2]/=] => -[/itvxxP -> /itvxxP ->].
      by rewrite subrr normr0.
    rewrite sub1set inE/=; exists (x, x) => //=.
      by rewrite !in_itv/= lexx.
    by rewrite subrr normr0.
  by rewrite if_same subrr.
  by rewrite set_itv_ge ?subrr ?diam0// bnd_simp ltxx.
  by rewrite set_itv_ge ?subrr ?diam0// bnd_simp ltxx.
by move: b0 b1 => [|] [|]; rewrite !(diam_itvoo,diam_itvcc,diam_itvco,diam_itvoc).
Qed.

End diam_itv.

Definition diam_max (s : seq (set R)) := \big[maxe/-oo%E]_(A <- s) (diam A).

Lemma diam_max_ge0 (s : seq (set R)) : s != [::] -> (0 <= diam_max s)%E .
Proof.
case: s => // s0 s1 _.
rewrite /diam_max.
apply: (bigmax_sup_seq _ s0) => //.
  exact: mem_head.
exact: diam_ge0.
Qed.

Lemma diam_max_seq1 (s0 : set R) : diam_max [:: s0] = diam s0.
Proof.
by rewrite /diam_max big_seq1.
Qed.

Lemma diam_max_cons (s0 : set R) (s : seq (set R)) :
  (diam s0 <= diam_max (s0 :: s))%E .
Proof.
apply: (bigmax_sup_seq _ s0) => //.
exact: mem_head.
Qed.

Lemma diam_defaultE (s : seq (set R)) :
  s != [::] ->
diam_max s = \big[maxe/0%E]_(A <- s) (diam A).
Proof.
elim: s => // s0 s1 ih _.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: le_bigmax_seq2 => /=.
    by exists s0; rewrite ?mem_head ?leNye.
  move=> i.
  rewrite in_cons => /predU1P[->|is1].
    by exists s0 => //; rewrite mem_head.
  exists i => //.
  by rewrite in_cons is1 orbT.
rewrite big_seq_cond.
apply: bigmax_le.
  exact: diam_max_ge0.
move=> /= A; rewrite andbT in_cons => /predU1P[->|s1A].
  exact: diam_max_cons.
rewrite /diam_max.
rewrite big_cons le_max; apply/orP; right.
have : s1 != [::].
  by apply/negP; move/eqP=> s10; rewrite s10 in s1A.
move/ih; rewrite /diam_max => ->.
exact: le_bigmax_seq.
Qed.

Lemma diam_max0 : diam_max [::] = -oo%E.
Proof.
by rewrite /diam_max big_nil.
Qed.

Lemma diam_maxS (s t : seq (set R)) :
 (forall A, A \in s -> exists2 B, B \in t & A `<=` B) ->
  (diam_max s <= diam_max t)%E.
Proof.
elim: s => //[_|/= s0 s1 ih h].
  by rewrite /diam_max big_nil leNye.
rewrite /diam_max.
rewrite big_cons.
rewrite ge_max; apply/andP; split.
  have [t0 t0t st0] := h s0 (mem_head _ _).
  apply: (@le_trans _ _ (diam t0)).
    exact: diamS.
  exact: le_bigmax_seq.
rewrite big_seq_cond.
apply: bigmax_le.
  exact: leNye.
move=> X.
rewrite andbT => s1X.
have := h X.
rewrite in_cons s1X orbT; move/(_ isT).
move=> [Y s1Y XY].
apply: (@le_trans _ _ (diam Y)).
  exact: diamS.
exact: le_bigmax_seq.
Qed.

End diam.
