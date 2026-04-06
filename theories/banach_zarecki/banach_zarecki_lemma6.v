From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import all_ssreflect interval_inference ssralg ssrnum.
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

Section ex_perfect_set.
Local Notation mu := (@lebesgue_measure R).

(* enumration of rational numbers in A *)
Let enum_ (A : set R) : nat -> R.
Admitted.

Let elt_prop (A : set R) (x : nat * set R) :=
  [/\ open x.2, is_interval x.2 &
     (forall m : nat, (m < x.1)%nat /\ enum_ A m \notin x.2)].

Let elt_type A := {x : nat * set R * set R | elt_prop A x.1}.

Let p_ A (x : elt_type A) := (proj1_sig x).1.1.
Let U_ A (x : elt_type A) := (proj1_sig x).1.2.
Let E_ A (x : elt_type A) := (proj1_sig x).2.

Let elt_rel A (i j : elt_type A) :=
  [/\ p_ j = (p_ i).+1,
   (forall k : nat, (k <= p_ j)%N -> enum_ A k \notin E_ j)
  & (0 <= mu (U_ j) < (2 ^- (p_ j).+2)%:E * mu A)%E].

Lemma ex_perfect_set (A : set R) :
  (0 < mu A)%E -> compact A ->
  exists B, [/\ B !=set0, B `<=` A, perfect_set B & (0 < mu B)%E].
Proof.
Abort.
(* move=> cA.
pose iA := isolated A : set R.
have : countable iA.
  exact: countable_isolated.
move/countable_bijP => [I].
rewrite card_eq_sym.
move/card_set_bijP => /= [i_ [funi inji surji]].
pose hoge := Record {pU : nat * set R} 
pose dpc_con (pU : nat * set R) (qV : nat * set R) :=
  [/\ compact qV.2, (forall m, qV.1 < m /\ i_ m \in qV.2),
     (forall k, (k < qV.1)%N -> i_ k \notin closure qV.2) &
     closure qV.2 `<=` pU.2].
have : forall X, open X.2 ->  {Y | dpc_con X Y}.
  move=> X.
  have [|] := pselect (exists m, i_ m \in X.2).
    move/cid=> [m imX].

pose dp_con (qX : (nat -> R) * set R)
(abY1 : ((R * R) * set R)) (abY2 : ((R * R) * set R)) :=
  [/\ irrational abY1.1.1, irrational abY1.1.2,
   (forall n, qX.1 n \in `]abY1.1.1, abY1.1.2[) &
  abY2.2 = abY1.2 `\` `]abY1.1.1, abY1.1.2[].
(* enumration of rational numbers in `]b, a[ *)
have : {q_ : nat -> R |
         (forall n, rational (q_ n)) /\ (forall n, q_ n \in `[b, a])}.
  apply: cid.

pose q : nat -> R := 0.


have : forall abY1, { abY2 | dp_con (q, `[b, a]%classic) abY1 abY2}.
  admit.
move/dependent_choice.
move/(_ ((a, b), `[b, a]%classic)).
move=> [abE].
have spabE := fun n => (surjective_pairing (abE n)).
have spab  := fun n => (surjective_pairing (abE n).1).
pose a_ := fun n => (abE n).1.1.
pose b_ := fun n => (abE n).1.2.
pose E_ := fun n => (abE n).2.
move=> [].
rewrite spabE spab => -[a0 b0 E0].
move/all_and4=> [ir_Ebl ir_Ebr qE ES].
exists (\bigcap_n (E_ n)); split.
- have := (@bigcap_inf _ _ 0 [set: nat] E_).
  by rewrite /E_ E0; apply.
- admit.
- 
  [/\ (forall n, irrational (abY.1 n).1), (forall n, irrational (abY.1 n).2),
   (forall n, qX.1 n \in `](abY.1 n).1, (abY.1 n).2[)
 & abY.2 = qX.2 `\` `]abY.1.1, abY.1.2[]}.

End ex_perfect_set.


Lemma perfect_set_compact (A : set R) :
  infinite_set A ->
  compact A -> exists B, B `<=` A /\ perfect_set B.
Proof.
move=> infA cA.
have : forall X : set R, {Y | Y = X `\` (isolated X)}.
  admit.
move/dependent_choice/(_ A) => [B_ [B0A HB]].
exists (\bigcap_n B_ n); split.
  move=> x.
  move/(_ 0 I).
  by rewrite B0A.
apply/perfectP; split.
  apply: closed_bigI => i _.
  elim: i.
    rewrite B0A.
    exact: compact_closed.
  move=> n cBn.
  rewrite HB.
  rewrite {1}((closure_id _).1 cBn).
  rewrite closure_isolated_limit_point.
  rewrite setUKD; last first.
    rewrite subset0; apply/eqP.
    rewrite -disj_set2E.
    exact: disjoint_isolated_limit_point.
  exact: limit_point_closed.

*)
End ex_perfect_set.
 
End limit_point_closed.
Arguments limit_point_closed {R} A.

(* Note: PR in future *)
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
  have [I_ [/all_and2[oI intI] [trivI UUI]]] := open_disjoint oU.
  have := Ux.
  rewrite UUI => -[n _ Inx].
  have In0 : I_ n !=set0 by exists x.
  have := nonempty_open_interval_not_subset1 In0 (oI n) (intI n).
  move/existsNP => [x0 /existsNP[x1] /not_implyP[Inx0] /not_implyP[Inx1]].
  move/eqP.
  rewrite eq_le.
  move/nandP.
  rewrite -2!ltNge => -[x10|x01].
Abort.
(*
    rewrite open_disjoint_i
 /nbhs_singleton Vx VAx].
  rewrite limit_point_interior.
*)

End interior_lemmas.

Section contiguous_interval_partition.
Context {R : realType}.
Implicit Type (A : set R).

(* note: (i <= j :> interval R) means i `<=` j as sets.
         (itv_leEmeet, subitvP, leRhull, etc.) *)
Lemma interval_le_bound (X Y : set R) :
  is_interval X -> is_interval Y ->
  [disjoint X & Y] ->
  (ereal_sup (EFin @` X) <= ereal_inf (EFin @` Y))%E \/
    (ereal_sup (EFin @` Y) <= ereal_inf (EFin @` X))%E.
Proof.
move=> intX intY disjXY.
rewrite 2!leNgt.
apply/nandP/negP => /andP[YX XY].
have X0 : X !=set0.
  apply/set0P.
Admitted.

Definition cgitvs A := contiguous_intervals A.
Definition cgitv_lbs A := fun n => fine (contiguous_intervals1 A n).
Definition cgitv_ubs A := fun n => fine (contiguous_intervals2 A n).

Definition tuple_take {T} (s : T^nat) (n : nat) := [tuple s i | i < n].

Local Notation sort_lbs A := (fun n => (sort <=%R (tuple_take (cgitv_lbs A) n))).

Variable A : set R.
Hypothesis (cA : compact A).

Check (sort_lbs A).

Definition fun_of_sort n : { p : {perm 'I_ n.+1} &
 forall i, forall (iltn : (i < n.+1)%N),
   tnth (sort_lbs A n.+1) (Ordinal iltn) =
           cgitv_lbs A (p (Ordinal iltn))}.
have : perm_eq (sort_lbs A n.+1) (tuple_take (cgitv_lbs A) n.+1).
  by rewrite perm_sort.
move/tuple_permP/cid => [p pH].
exists p.
move=> i iltn.
rewrite pH /=.


Admitted.

Definition sort_fun n := (projT1 (fun_of_sort n)).
(*
Definition sort_ubs (X : set R) := (fun n => (sort <=%R (tuple_take (cgitv_ubs X) n))).

Definition c_ n i := tnth (sort_lbs A n) i.
Definition d_ n i := tnth (sort_fun A n) i.

Definition bound_partition (X : set R) (n : nat) :=
  merge <%R 
*)

End contiguous_interval_partition.


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
pose a_ n := fine (contiguous_intervals1 Z n).
pose b_ n := fine (contiguous_intervals2 Z n).
pose alpha := mu (H @` Z).
pose ta n := [tuple a_ i | i < n].
pose tb n := [tuple b_ i | i < n].
pose sort_ta n := sort <%R (ta n).
pose sort_tb n := sort <%R (tb n).
pose c_ n i := tnth (c :: sort_tb n) i.
pose d_ n i := tnth (rcons (sort_ta n) d) i.

pose lambda n : R := \big[maxr/0%R]_(i < n.+1) `|d_ n i - c_ n i|.
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
have lambda_gt0 n : (0 < n)%N -> 0 < lambda n.
  case: n => // n _.
  rewrite /lambda.
  apply/bigmax_gtP; right.
  exists ord0 => //.
  rewrite /c_/d_.
  rewrite (tnth_nth 0) (tnth_nth 0 (c :: _))/=.
  
  admit.
have lambda0 : lambda @ \oo --> 0.
  apply/cvgrPdist_lt.
  apply/not_notP.
  move/existsNP => /=[e /not_implyP[e0]].
  suff contra : (forall N, exists n, (N < n)%N /\ e <= lambda n) -> False.
    move=> H.
    apply/contra.
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
  move/choice => [N /all_and2[nN eN]].
  have : forall n, (((N n)%:R * e)%:E <= mu Z)%E.
    have dcZ n : \big[setU/set0]_(i < (N n).+1)
          `[c_ (N n) i, d_ (N n) i]%classic `<=` Z.
      admit.
    have mdcZ n : (mu (\big[setU/set0]_(i < (N n).+1)
          `[c_ (N n) i, d_ (N n) i]%classic) <= mu Z)%E.
      exact: le_outer_measure.
    have ecd n : (((N n)%:R * e)%:E <= mu (\big[setU/set0]_(i < (N n).+1)
          `[c_ (N n) i, d_ (N n) i]%classic))%E.
      have -> : (mu (\big[setU/set0]_(i < (N n).+1)
      `[c_ (N n) i, d_ (N n) i]%classic) = \big[+%E/0%E]_(i < (N n).+1)
      mu `[c_ (N n) i, d_ (N n) i])%E.
        admit.
      apply: (@le_trans _ _ (((N n)%:R * lambda (N n))%:E)).
        rewrite lee_fin.
        rewrite ler_pM2l.
          apply: eN.
        admit.
      admit.
    move=> n.
    have -> : Z = [set` Rhull Z] `\` cplt_hull Z.
      rewrite setDD setIidr//.
      exact: sub_Rhull.
    admit.
  admit.
pose merge_tab n := (merge <%R (sort_ta n) (sort_tb n)).
have sorted_merge_tab n : sorted <%R (c :: merge_tab n).
  admit.
(*
pose cd_ n := nth b (c :: merge_tab n).
pose c_ n i := cd_ n i.*2.
pose d_ n i := cd_ n i.*2.+1.
have c2b n i : exists k, c_ n i.+1 = b_ k.
  
  set elt_rel := fun (mp1 mp2 : {m : nat & {perm 'I_ m.+1}}) =>
  (projT1 mp2) = (projT1 mp1).+1 /\
  (sort_ta (projT1 mp2)) = [tuple tnth (ta (projT1 mp2).+1)
     ((projT2 mp2) i) | i < (projT1 mp2).+1].
  have : forall mp1, {mp2 | elt_rel mp1 mp2}.
    move=> mp1; apply/cid.
    have : perm_eq (sort_ta (projT1 mp1).+2) (ta (projT1 mp1).+2).
      by rewrite perm_sort.
    move/tuple_permP => [p pE].
    exists (existT _ (projT1 mp1).+1 p).
    rewrite /elt_rel/=.
    split => //.
    
    admit.
  move/dependent_choice.
  have tinj_ffunid : @injectiveb ('I_ 1) _ [ffun x => x].
    rewrite /injectiveb/dinjectiveb map_inj_uniq.
      exact: enum_uniq.
    by move=> ? ?; rewrite !ffunE.
  move/(_ (@existT nat (fun n => {perm 'I_ n.+1}) 0%N (Perm tinj_ffunid))).
  move=> [mp_ [mp0 mpS]].
  pose m_ n := projT1 (mp_ n).
  pose p_ n := projT2 (mp_ n).
  have mE k : m_ k = k.
    elim: k.
      by have/(f_equal (@projT1 _ _)) := mp0.
    rewrite /m_.
    move=> k.
    have := mpS k.
    rewrite /elt_rel => -[+ _].
    by move=> -> ->.
  exists (p_ i).
  rewrite /c_.
  rewrite /cd_.
  rewrite doubleS/=.
  elim: i.
    rewrite double0/merge_tab.
    admit.
  admit.
*)
have d2a n i : exists k, d_ n i = a_ k.
  admit.

have construct_x n :
  exists x : seq R, [/\ itv_partition c d x,
    (itv_partition_max c d x <= lambda n),
    (forall i, (i < n.*2)%N -> a_ i \in x),
    (forall i, (i < n.*2)%N -> b_ i \in x) &
    (forall i, nth b x i \notin (interior Z : set R))].
    (* \bigcup_(i < n) `]c_ i, d_ i[ ? *)
  admit.
pose x := fun n => sval (cid (@construct_x n)).
have max_x n : itv_partition_max c d (x n) <= lambda n.
  by have [] := proj2_sig (cid (construct_x n)).
have pcdx n : itv_partition c d (x n).
  by have [] := proj2_sig (cid (@construct_x n)).
pose S_ n : R := variation c d f (x n).
pose V_ n : R :=
  `|f (a_ 0) - f c| + \sum_(i < n) `|f (a_ i.+1) - f (b_ i)| + `|f d - f (b_ n)|
    + \sum_(i < n) (fine (total_variation (a_ i) (b_ i) f)).
have SV n : S_ n <= V_ n.
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
  admit. (* squeeze *)
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
    admit.
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
 `|H (a_ 0) - H c|%R + (\sum_(i < n) `|H (a_ i.+1) - H (b_ i)|)%R
    + `|H d - H (b_ n)|%R +
   (\sum_(i < n) fine (total_variation (a_ i) (b_ i) f))%R.
  admit.
rewrite addrC 2!addrA ltrD2r -2!addrA addrC.
(* (5.5) (between (5) and (6)) *)
have alphaH : fine alpha <
  `|H (a_ 0) - H c|%R + (\sum_(i < n) `|H (a_ i.+1) - H (b_ i)|)%R
   + `|H d - H (b_ n)|%R.
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
rewrite addrA.
rewrite ltrBrDl -splitr; move/(_ alphaH).
(* (6.5) (between (6) and (7)) *)
pose abcd i := [set k | `[a_ k, b_ k] `<=` `[c_ n i, d_ n i]].
have {}n0n : (n0 < n.+1)%N.
  admit.
set on0 := Ordinal n0n.
set Uabcdn := \bigcup_(j in abcd on0) `[a_ j, b_ j]%classic.
have prop65 : forall i : 'I_ n.+1, (`|f (d_ n i) - f (c_ n i)|%:E <=
  \sum_(n <= j <oo | `[< `[a_ j, b_ j] `<=` Uabcdn >])
     oscillation f `[a_ j, b_ j])%E.
  move => i.
  apply: lime_ge.
    apply: ereal_nondecreasing_is_cvgn.
    apply: ereal_nondecreasing_series => k _ _.
    exact: oscillation_ge0.
  apply/nearW => k.
  have cdi : c_ n i < d_ n i.
    admit.
  have itvfcd : is_interval [set f x | x in `[(c_ n i), (d_ n i)]].
    admit.
  have cUabcdn : closed Uabcdn.
    admit.
  have hull_Uabcd : Rhull Uabcdn = `[(c_ n i), (d_ n i)].
    admit.
  have := (@lemma4 _ (c_ n i) (d_ n i) cdi f Uabcdn itvfcd cUabcdn hull_Uabcd).
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
have : ((`|f (a_ 0) - f c|%R + \sum_(i < n) `|f (a_ i.+1) - f (b_ i)|
           + `|f d - f (b_ n)|%R)%:E <=
  \sum_(n <= i <oo) oscillation f `[a_ i, b_ i])%E.
  apply: lime_ge.
    apply: ereal_nondecreasing_is_cvgn.
    apply: ereal_nondecreasing_series => m _ _.
    exact: oscillation_ge0.
  near=> m.
  admit.
  (* have := lemma4. *)

have ifcd : is_interval [set f x | x in `[c, d]].
  (* by continuity *)
  admit.
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

(*
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

(* wlog step *)
Lemma lusinN_contra_wlog :
 ~ (lusinN `[a, b] (fun x => fine (total_variation a ^~ f x))) ->
 exists Z : set R,
 [/\ Z `<=` `[a, b], compact Z, mu Z = 0, (0%R < mu [set H x | x in Z])%E &
  perfect_set Z].
Proof.
move=> ababsurdo.
have := image_measure0_Lusin_nondecreasing ab cH ndH.
move/contra_not=> /(_ ababsurdo).
move/existsNP=> [Z' /not_implyP [Z'ab /not_implyP[cZ' /not_implyP[muZ'0]]]].
move/eqP; rewrite neq_lt ltNge measure_ge0/= => muHZ'_gt0.
pose Z := Z' `\` isolated Z'. (* extract lemma to perfect_set_compact *)
  have closedZ : closed Z.
    apply: compact_closed.
  have compactZ' : compact Z'.
    (* rewrite /Z'. *)
    rewrite {1}(_ : Z = closure Z); last exact/closure_id.
    rewrite closure_isolated_limit_point.
    rewrite setUKD; last first.
      rewrite subset0.
      apply/disj_set2P.
      exact: disjoint_isolated_limit_point.
    have clpZ := limit_point_closed Z.
    apply: (subclosed_compact _ cZ) => //.
    apply: subset_trans.
      exact: subset_limit_point.
    by rewrite {2}((closure_id Z).1 closedZ).
  have Z'E : Z' = limit_point Z.
    rewrite /Z'.
    rewrite {1}((closure_id Z).1 closedZ).
    rewrite closure_isolated_limit_point.
    rewrite setUKD//.
    rewrite subset0.
    apply/disj_set2P.
    exact: disjoint_isolated_limit_point.
  have closedZ' : closed Z'.
    rewrite Z'E.
    exact: limit_point_closed.
  apply: (wlg Z').
  - apply: (subset_trans _ Zab).
    exact: subDsetl.
  - exact: compactZ'.
  - apply/eqP.
    rewrite -measure_le0/=.
    rewrite -Z0.
    rewrite le_outer_measure//.
    exact: subDsetl.
  - admit.
  - apply: (@continuous_compact _ _ H Z'); last exact: compactZ'.
    apply: (@continuous_subspaceW _ _ _ Z) => //.
      exact: subDsetl.
    exact: (@continuous_subspaceW _ _ _ _ _ Zab).
  - rewrite /perfect_set; split => //.
    admit.
*)
(*
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
Abort.

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
Abort,

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
Abort.

End construct_x.

Let lambda_gt0 n : (0 < n)%N -> 0 < lambda n.
Proof.
case: n => // n _.
rewrite /lambda.
rewrite (lt_le_trans _ (le_bigmax _ _ ord0))//=.
rewrite double0/=.
rewrite normr_gt0.
rewrite subr_eq0.
Admitted.

Let cvg_lambda0 : lambda n @[n --> \oo] --> 0.
Proof.
apply/cvgrPdist_lt => /= e e0.
near=> n.
rewrite sub0r normrN gtr0_norm; last first.
  apply: lambda_gt0.
  near: n.
  exact: nbhs_infty_gt.
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
have := lemma5 cd cdcf pcdx max_x cvg_lambda0.
rewrite /total_variation ereal_sup_EFin; last 2 first.
- exists (fine (total_variation a b f)).
  move=> _ [s ps <-].
  rewrite -lee_fin fineK; last first.
    apply/bounded_variationP => //.
    exact: ltW.
  apply: (le_trans (variation_le_total_variation _ _)) => //.
  rewrite (total_variationD f ac); last first.
    apply: le_trans db.
    exact: ltW.
  rewrite (total_variationD f _ db); last exact: ltW.
  by rewrite addeCA leeDl ?adde_ge0 ?total_variation_ge0.
- exists (variation c d f [:: d]).
  apply: variations_variation.
  exact: itv_partition1.
move/fine_cvg => /=.
exact.
Qed.

(* prove by lemma5_cvg_style *)
(*
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
have := lemma5_cvg_style cd cdcf.
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
have := fin_inf.
move=> [l /= l0 Hl].
near=> n.
apply/andP; split; last first.
  rewrite /Vcd/total_variation.
  rewrite -lee_fin fineK; last by apply/bounded_variationP => //; exact: ltW.
  apply: le_ereal_sup_tmp.
  exists (S_ n)%:E => //.
  exists (S_ n) => //.
  by exists (x n).
rewrite -lee_fin fineK; last first.
  apply: Hl => //=; last first.
    rewrite /lambda.
    apply/bigmax_gtP.
    right.
    have n0 : (0 < n)%N.
      near: n.
      exact: nbhs_infty_gt.
    exists (Ordinal n0) => //.
    rewrite normr_gt0.
    rewrite lt0r_neq0// subr_gt0.
    have := sorted_merge_tab n.
    move=> /(pathP b).
    apply.
    by rewrite size_merge size_cat !size_tuple/= addnn ltn_double.
  rewrite sub0r normrN ger0_norm; last first.
    exact/ltW/lambda_gt0.
  near: n.
  have := cvg_lambda0.
  move/(_ (ball 0 l)) => /=.
  move/(_ (nbhsx_ballx 0 _ l0)) => H.
  move: H.
  move=> [m _ Hm].
  near=> n.
  have := Hm n.
  have mn : (m <= n)%N.
    near: n.
    exact: nbhs_infty_ge.
  move/(_ mn) => /=.
  rewrite /ball/=.
  rewrite sub0r normrN ger0_norm//.
  exact/ltW/lambda_gt0.
apply: ge_ereal_inf.
exists (S_ n)%:E => //.
exists (S_ n) => //.
by exists (x n); split.
Unshelve. all: end_near. Qed.
*)

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
have aa i : a <= a_ i.
  have : bounded_set Z.
    rewrite Rbounded_setE; split.
    - by exists a => r /Zab/=; rewrite in_itv/= => /andP[].
    - by exists b => r /Zab/=; rewrite in_itv/= => /andP[].
  rewrite Rbounded_setE => -[lbZ ubZ].
  have := @contiguous_intervalsS _ Z i.
  move/(image_subset EFin).
  rewrite (contiguous_ooitv ubZ lbZ i).
  move/closure_subset.
  (* rewrite closure_neitv_oo. *)
  have -> :
   (closure `](contiguous_intervals1 Z i), (contiguous_intervals2 Z i)[ =
   `[(contiguous_intervals1 Z i), (contiguous_intervals2 Z i)])%classic.
    admit.
  (* rewrite contiguous_ooitv. *) admit.
have subab_cf k :
   {within `[nth b (sort_ta n) k, nth b (sort_tb n) k], continuous f}.
  apply: continuous_subspaceW cf.
  apply: subset_itv; rewrite bnd_simp.
    admit.
  admit.
have ltcd k : (nth b (sort_ta n) k) < (nth b (sort_tb n) k).
  admit.
(*
have := fun k => continuous_oscillationE (ltcd k) (subab_cf k).
move/choice => [osc_pts Hosc_pts].
pose osc_seq := \big[cat/[::]]_(i < n) [:: (osc_pts i).1; (osc_pts i).2].
have pab_osc_seq : itv_partition a b (rcons osc_seq b).
  admit.
exists (variation a b f (rcons osc_seq b))%:E.
  exists (variation a b f (rcons osc_seq b)) => //.
  exact: variations_variation.*)
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
  lusinN `[a, b] H.
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

*)

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
