From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import boot order ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import interval_inference archimedean rat.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp contra classical_sets functions.
From mathcomp Require Import cardinality fsbigop interval set_interval.
From mathcomp Require Import reals ereal topology normedtype sequences.
From mathcomp Require Import real_interval esum measure.
From mathcomp Require Import lebesgue_stieltjes_measure lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun.
From mathcomp Require Import realfun exp derive borel_hierarchy.
From mathcomp Require Import absolute_continuity.

Import MeasurableR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section measure_image.
Context {R : realType}.

(* name? *)
(* why "integral" is in name in spite of not using integral *)
(* used in lemma2 *)
(* mk banach_zarecki/lebesgue_measure_extra.v *)
Lemma integral_continuous_nondecreasing_itv (a b : R) (f : R -> R) :
  a <= b ->
  {within `[a, b], continuous f} ->
  {in `]a, b[ &, {homo f : x y / (x <= y)%O}} ->
  lebesgue_measure (f @` `]a, b[) = ((f b)%:E - (f a)%:E)%E.
Proof.
rewrite le_eqVlt => /predU1P[|].
  move=> -> _ _.
  rewrite set_itv_ge.
    by rewrite bnd_simp ltxx.
  by rewrite image_set0 measure0 subee.
move=> ab cf ndf.
have := (continuous_nondecreasing_image_itvoo_itv ab cf ndf).
have ndfcc := (continuous_in_nondecreasing_oo_cc ab cf ndf).
move=> [b0 [b1]] ->.
rewrite lebesgue_measure_itv /=.
have: f a <= f b.
  by rewrite ndfcc ?in_itv/= ?lexx ?ltW.
rewrite le_eqVlt.
move/orP; case; rewrite lte_fin; [move/eqP|]; move=> -> //.
by rewrite ltxx -EFinD subrr.
Qed.

Lemma continuous_image_segment (a b : R) (f : R -> R) :
  a <= b ->
  {within `[a, b], continuous f} ->
  exists c d, [/\ c \in `[a, b]%classic, d \in `[a, b]%classic,
     f @` `[a, b] = `[f c, f d]%classic &
    lebesgue_measure (f @` `[a, b]) = (f d - f c)%:E].
Proof.
move=> ab cf.
have ab0 : `[a, b] !=set0 by exists a => /=; rewrite boundl_in_itv.
have cpt_ab : compact `[a, b] by exact: segment_compact.
have [/= c /[dup]cab + minc] := compact_EVT_min ab0 cpt_ab cf.
rewrite inE/= in_itv/= => /andP[ac cb].
have [/= d /[dup]dab + maxd] := compact_EVT_max ab0 cpt_ab cf.
rewrite inE/= in_itv/= => /andP[ad db].
have fcfd : f c <= f d by exact: minc.
have -> : [set f x | x in `[a, b]] = `[f c, f d]%classic.
  rewrite eqEsubset; split => y.
    move=> [x xab <-]/=; rewrite in_itv/=; apply/andP; split.
      by apply: minc; rewrite inE.
    by apply: maxd; rewrite inE.
  move=> yfcfd.
  have le_y : minr (f c) (f d) <= y <= maxr (f c) (f d).
    by rewrite minEle maxEle !ifT//.
  have /orP[cd|dc] := le_total c d.
    have cfcd : {within `[c, d], continuous f}.
      apply: continuous_subspaceW cf.
      by apply: subset_itv; rewrite bnd_simp.
    have [x xcd <-] := IVT cd cfcd le_y.
    exists x => //=.
    by apply: subset_itv xcd; rewrite bnd_simp.
  have cfdc : {within `[d, c], continuous f}.
    apply: continuous_subspaceW cf.
    by apply: subset_itv; rewrite bnd_simp.
  rewrite minC maxC in le_y.
  have [x xcd <-] := IVT dc cfdc le_y.
  exists x => //=.
  by apply: subset_itv xcd; rewrite bnd_simp.
exists c, d; split => //.
rewrite lebesgue_measure_itv.
move: fcfd; rewrite le_eqVlt => /predU1P[<-|fcfd].
  by rewrite subrr ifF.
by rewrite ifT.
Qed.

End measure_image.


Section measurable_squeeze.
Context {R : realType}.

Lemma measure_squeeze_measurable (B A C : set R) :
  measurable A ->
  measurable C ->
  (*lebesgue_measure A = lebesgue_measure C -> NB: unused *)
  countable (C `\` A) ->
  A `<=` B -> B `<=` C -> measurable B.
Proof.
move=> mA mC cCA AB BC.
rewrite -(setDUK AB).
apply: measurableU => //.
apply: countable_measurable => //.
apply: sub_countable cCA.
apply: subset_card_le.
exact: setSD.
Qed.

End measurable_squeeze.

Section perfect_set_rm.
Context {R : realType}.
Let mu := @lebesgue_measure R.
Local Open Scope ereal_scope.
Local Open Scope classical_set_scope.

Definition oobasis : set (set R) := [set `]ratr x.1, ratr x.2[ | x in setT].

Lemma set0_oobasis : set0 \in oobasis.
Proof.
rewrite inE /oobasis/=.
exists (1, 0)%R => //=.
rewrite -subset0 => x/=; rewrite in_itv/= => /andP[/lt_trans] => /[apply].
by rewrite ltr_rat ltr10.
Qed.

Lemma oobasis_countable : countable oobasis.
Proof.
by rewrite /countable -(card_le_eqr card_rat2); exact: card_image_le.
Qed.

Lemma oobasis_basis : basis oobasis.
Proof.
split; first by move=> A [[a b]] _/= <-; exact: itv_open.
move=> r V; rewrite nbhsE/= => -[U [oU /mem_set Ur] UV].
have [a [b [_ [rB BU]]]] := open_subball_rat oU Ur.
exists (@ball _ R (ratr a) (ratr b)) => /=; last exact: subset_trans UV.
split; last exact/set_mem.
by exists (a - b, a + b)%R => //=; rewrite ball_itv raddfB/= raddfD.
Qed.

Lemma Rsecond_countable : @second_countable R.
Proof. by exists oobasis; [exact: oobasis_countable|exact: oobasis_basis]. Qed.

Definition rat_itv (U : set R) := [set pq : (rat * rat)%type |
  (pq.1 < pq.2)%R /\ `]ratr pq.1, ratr pq.2[ `<=` U].

Lemma open_rat_itv (U : set R) : open U ->
  U = \bigcup_(pq in rat_itv U) `]ratr pq.1, ratr pq.2[.
Proof.
move=> openU.
apply/seteqP; split => [x /mem_set Ux|z [i [i12 + iz]]]; last exact.
suff [[p q] Bpq /=xpq] : exists2 pq : (rat * rat)%type,
    pq \in rat_itv U & x \in `]ratr pq.1, ratr pq.2[.
  by exists (p, q) => //=; [exact: set_mem|by rewrite inE in xpq].
have [a [b [r0 [xB BU]]]] := open_subball_rat openU Ux.
exists (a - b, a + b)%R.
  rewrite inE /rat_itv /=; split => //.
    by rewrite ltrBlDr -addrA ltrDl addr_gt0.
  by rewrite raddfB/= raddfD/= -ball_itv.
rewrite inE/= raddfB/= raddfD/=.
by move: xB; rewrite ball_itv inE.
Qed.

Lemma perfect_set_rm (X : set R) :
  compact X -> mu X < +oo ->
  exists B, [/\ B `<=` X, compact B, isolated B = set0 &
    mu B = mu X].
Proof.
move=> compactX boundedX.
pose G : set R := \bigcup_(U in [set U | open U /\ mu (X `&` U) = 0]) U.
have openG : open G.
  rewrite /G.
  by apply: bigcup_open => ? [].
pose K := X `\` G.
have mG : measurable G by exact: open_measurable.
have mX : measurable X by exact: compact_measurable.
have compactK : compact K.
  rewrite /K.
  rewrite setDE.
  apply: compact_closedI => //.
  by apply: open_closedC.
have G0 : mu (X `&` G) = 0.
  have [F [Fbasis F0] GF] : exists2 F : (set R)^nat,
      (forall i, F i \in oobasis) /\ (forall i, mu (X `&` F i) = 0) &
      G = \bigcup_i F i.
    have GE : G = \bigcup_(U in [set U | oobasis U /\ mu (X `&` U) = 0%R]) U.
      apply/seteqP; split => [r [/= A [oA XA0]]|r].
        rewrite (open_rat_itv oA) => -[pq Apq rpq].
        exists (`]ratr pq.1, ratr pq.2[) => //=.
        split; first by exists pq.
        rewrite /rat_itv /= in Apq.
        apply/eqP; rewrite eq_le measure_ge0 andbT.
        rewrite -XA0 le_measure//= ?inE//=.
          exact: measurableI.
          by apply: measurableI => //; exact: open_measurable.
        by apply: setIS; case: Apq.
      move=> [_/= [[pq _ <-]]] Xpq pqr.
      by exists `]ratr pq.1, ratr pq.2[.
    have /countable_bijP[B] := oobasis_countable.
    (* TODO: write this down in the FAQ *)
    rewrite card_eq_sym => /card_set_bijP[f/=] bijf.
    Check f : nat -> set R.
    pose f1 : set R -> nat := pinv B f.
    exists (fun n => if (n \in B) && (mu (X `&` f n) == 0) then
      f n else set0).
      split.
        move=> n.
        case: ifPn.
          move=> /andP[/set_mem Bn _].
          apply/mem_set.
          case: bijf => + _ _.
          by apply.
        by rewrite set0_oobasis.
      move=> i.
      case: ifPn=> [|_].
        by move=> /andP[_ /eqP].
      by rewrite setI0 [LHS]measure0.
    rewrite GE.
    rewrite bigcup_mkcondr.
    rewrite (reindex_bigcup f B)//.
      by case: bijf.
      by case: bijf.
    rewrite bigcup_mkcond.
    apply: eq_bigcup => //= i _.
    case: ifPn => //= Bi.
    rewrite /mem/= /in_mem/= /in_set/=.
    by case: asboolP => [->|/eqP/negPf ->//]; rewrite eqxx.
  rewrite GF.
  rewrite setI_bigcupr.
  apply/eqP; rewrite eq_le.
  rewrite measure_ge0 andbT.
  apply: (@le_trans _ _ (\sum_(0 <= i <oo) mu (X `&` F i))).
    exact: outer_measure_sigma_subadditive.
  by rewrite eseries0//.
have muKX : mu K = mu X.
  rewrite /K.
  rewrite [LHS]measureD//= -/mu.
    by rewrite G0 sube0.
have isoK : isolated K = set0.
  rewrite -subset0 => /= x.
  move/isolatedP => [xK /= [U xU UKx]].
  have xG : x \notin G by move: xK; rewrite in_setD => /andP[].
  have mXU0 : mu (X `&` U) > 0.
    rewrite lt_neqAle measure_ge0 andbT eq_sym.
    apply/eqP => XU0.
    have UG : U `<=` G.
      rewrite /G.
      apply: bigcup_sup => /=; split => //.
      by case: xU.
    move/negP : xG; apply.
    apply/mem_set/UG.
    by case: xU.
  have : 0 < mu (K `&` U).
    rewrite /K.
    rewrite setDE.
    rewrite setIAC.
    rewrite -setDE.
    have mU : measurable U by apply: open_measurable; case: xU.
    rewrite [ltRHS](@measureD _ _ _ mu (X `&` U) G)//.
      exact: measurableI.
      rewrite (le_lt_trans _ boundedX)// le_measure// ?inE//.
      exact: measurableI.
    have XUG0 : mu (X `&` U `&` G) = 0.
      apply/eqP.
      rewrite eq_le measure_ge0 andbT.
      rewrite -G0.
      rewrite le_measure// ?inE.
      by apply: measurableI => //; apply: measurableI.
      by apply: measurableI => //.
      rewrite setIAC.
      exact: subIsetl.
    by rewrite [X in _ - X]XUG0 sube0.
  by rewrite setIC UKx /mu lebesgue_measure_set1 ltxx.
exists K.
split.
- exact: subDsetl.
- assumption.
- assumption.
- by rewrite muKX.
Qed.

End perfect_set_rm.
