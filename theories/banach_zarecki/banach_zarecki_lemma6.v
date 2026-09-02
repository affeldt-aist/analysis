From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import boot order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean perm finmap.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import cardinality.
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

Section lemmas.
Context {R : realType}.
Local Notation mu := (@completed_lebesgue_measure R).

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

Lemma cl_imf_tentative (a b : R) (f : R -> R) :
  let A := `]a, b[%classic in
  {within (closure A), continuous f} ->
  f @` (closure A) `<=` closure (f @` A).
Proof.
move=> A Af.
pose C := f @^-1` closure (f @` A).
suff closedC : closed C.
  pose B := f @` C.
  apply: (@subset_trans _ B).
    rewrite /B.
    apply: image_subset.
    rewrite closureE.
    apply: smallest_sub => //.
    rewrite /C.
    rewrite -image_sub.
    exact: subset_closure.
  rewrite /B /C.
  exact: image_preimage_subset.
move/continuous_closedP : Af.
move=> /(_ (closure (f @` A)) (@closed_closure _ _)).
move/closed_subspaceP => /=[C'].
rewrite-/C => closedC'.
(* NB: same as above but that fails... keep me, investigate *)
Abort.

Lemma cl_imf (A : set R) (f : R -> R) :
    {within (closure A), continuous f} ->
  f @` (closure A) `<=` closure (f @` A).
Proof.
move=> cf.
rewrite image_sub.
rewrite -(setIid (closure A)).
(* NB: trick here! *)
rewrite -closure_subspaceW; first exact: subset_closure.
rewrite closureE.
apply: smallest_sub.
  apply: ((continuous_closedP _).1 cf).
  exact: closed_closure.
move=> x Ax /=.
apply: subset_closure.
by exists x.
Qed.

Lemma closure_has_ubound (A : set R) (f : R -> R)
  (ubfA : has_ubound [set f x | x in A]) : A !=set0 ->
  has_ubound (closure [set f x | x in A]).
Proof.
move=> A0.
case: ubfA => M fAM.
exists M => y.
move/closure_bigcup.in_mem_closedP => H.
apply/ler_addgt0Pl => /= e e0.
rewrite -lerBlDl.
have [x [yex /= [r Ar frx]]] := H (ball y e) (nbhsx_ballx _ _ e0).
rewrite leNgt; apply/negP => abs.
have : M < x.
  rewrite (lt_le_trans abs)//.
  by move: yex; rewrite /ball/= => /ltr_distlBl/ltW.
apply/negP; rewrite -leNgt -frx.
by apply fAM; by exists r.
Qed.

Lemma closure_has_lbound (A : set R) (f : R -> R)
  (ubfA : has_lbound [set f x | x in A]) : A !=set0 ->
  has_lbound (closure [set f x | x in A]).
Proof.
move=> A0.
move/has_lb_ubN : ubfA.
rewrite image_comp.
move/closure_has_ubound => /(_ A0) H.
rewrite has_lb_ubN.
rewrite -image_comp in H.
apply: subset_has_ubound H => x /= [r fAr <-{x}].
by rewrite -closureN in fAr.
Qed.

Lemma closure_has_sup (A : set R) (f : R -> R)
  (ubfA : has_ubound [set f x | x in A]) : A !=set0 ->
  has_sup (closure [set f x | x in A]).
Proof.
move=> A0.
split.
  have : [set f x | x in A] !=set0.
    by apply: image_nonempty.
  apply: subset_nonempty.
  exact: subset_closure.
exact: closure_has_ubound.
Qed.

Lemma closure_has_inf (A : set R) (f : R -> R)
  (ubfA : has_lbound [set f x | x in A]) : A !=set0 ->
  has_inf (closure [set f x | x in A]).
Proof.
move=> A0.
split.
  have : [set f x | x in A] !=set0.
    by apply: image_nonempty.
  apply: subset_nonempty.
  exact: subset_closure.
exact: closure_has_lbound.
Qed.

Lemma sup_closure (A : set R) (f : R -> R) :
  A !=set0 -> has_ubound [set f x | x in closure A] ->
  sup (closure (f @` A)) = sup (f @` A).
Proof.
move=> A0 ubA.
have ubfA : has_ubound (f @` A).
  apply: subset_has_ubound ubA.
  apply: image_subset.
  exact: subset_closure.
have clfA0 : closure [set f x | x in A] !=set0.
  (* TODO: change order of arguments of subset_nonempty *)
  apply: (@subset_nonempty _ (f @` A)).
    by apply: subset_closure.
  by apply: image_nonempty.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: supS.
  - by apply: image_nonempty.
  - by apply: closure_has_sup.
  - by apply: subset_closure.
set M := sup (f @` A).
apply: ge_sup => // y.
move/closure_bigcup.in_mem_closedP => H.
apply/ler_addgt0Pl => /= e e0.
rewrite -lerBlDl.
have [x [yex /= [r Ar frx]]] := H (ball y e) (nbhsx_ballx _ _ e0).
rewrite leNgt; apply/negP => abs.
have : M < x.
  rewrite (lt_le_trans abs)//.
  move: yex.
  by rewrite /ball/= => /ltr_distlBl/ltW.
apply/negP.
rewrite -leNgt -frx.
by apply: ub_le_sup => //.
Qed.

Lemma inf_closure (A : set R) (f : R -> R) :
  A !=set0 -> has_lbound [set f x | x in closure A] ->
  inf (closure (f @` A)) = inf (f @` A).
Proof.
move=> A0 fA; rewrite /inf; congr (- _).
rewrite [in RHS]image_comp.
rewrite -[RHS]sup_closure//.
  rewrite -(image_comp _ -%R).
  apply/has_ub_lbN.
  rewrite !image_comp compA (_ : _ \o f = f )//.
  by apply/funext => x/=; rewrite opprK.
congr sup.
apply/seteqP; split.
  move=> x/= [r fAr <-{x}].
  by rewrite -image_comp closureN.
move=> x /= fAx; exists (- x); last by rewrite opprK.
by  rewrite -closureN opprK image_comp.
Qed.

Lemma oscillation_closure (A : set R) (f : R -> R) :
  {within (closure A), continuous f} ->
  oscillation f (closure A) = oscillation f A.
Proof.
have [A0 cf|A0 cf] := eqVneq A set0.
  by rewrite A0 closure0.
have imf_cl : f @` A `<=` f @` (closure A).
  apply: image_subset.
  exact: subset_closure.
have cl_imf : f @` (closure A) `<=` closure (f @` A).
  by apply: cl_imf.
have Asub : A `<=` f @^-1` closure (f @` A).
  move=> x Ax /=.
  apply: subset_closure.
  by exists x.
have [hasubfA|hasNubfA] := pselect (has_ubound (f @` A)); last first.
  rewrite !oscillation_hasNub//.
  by move/(subset_has_ubound imf_cl).
have [haslbfA|hasNlbfA] := pselect (has_lbound (f @` A)); last first.
  rewrite !oscillation_hasNlb//.
  by move/(subset_has_lbound imf_cl).
have ubfA : has_ubound [set f x | x in closure A].
  apply: (subset_has_ubound cl_imf).
  apply: closure_has_ubound => //.
  exact/set0P.
have lbfA : has_lbound [set f x | x in closure A].
  apply: (subset_has_lbound cl_imf).
  apply: closure_has_lbound => //.
  exact/set0P.
rewrite /oscillation.
rewrite ifF.
  by apply/negP; move/eqP/closure_eq0/eqP; apply/negP.
rewrite -image_comp.
rewrite -[in RHS]image_comp.
have ? : [set f x | x in closure A] !=set0.
  apply: image_nonempty.
  move/set0P : A0.
  apply: subset_nonempty.
  exact: subset_closure.
have fA0 : [set f x | x in A] !=set0.
  apply: image_nonempty.
  by move/set0P : A0.
rewrite (negbTE A0).
congr (_ - _)%E.
  rewrite !ereal_sup_EFin//; congr EFin.
  apply/eqP; rewrite eq_le.
  apply/andP; split; last exact: supS.
  apply: (@le_trans _ _ (sup (closure (f @` A)))).
    apply: supS => //.
    apply: closure_has_sup => //.
    exact/set0P.
  rewrite -sup_closure//.
  exact/set0P.
rewrite !ereal_inf_EFin//; congr EFin.
apply/eqP; rewrite eq_le.
apply/andP; split; first exact: infS.
apply: (@le_trans _ _ (inf (closure (f @` A)))); last first.
  apply: infS => //.
  apply: closure_has_inf => //.
  exact/set0P.
rewrite -inf_closure//.
exact/set0P.
Qed.

From mathcomp Require Import convex.

Lemma Monem (x : R) (t : {i01 R}) : (t%:num).~ *: x = x - t%:num *: x.
Proof. by rewrite /onem [LHS]mulrBl mul1r. Qed.

Lemma convex_interval (i : interval R) : convex_set [set` i].
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

Lemma closed_Rhull (A : set R) : closed A -> closed [set` Rhull A].
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

Lemma convex_Rhull (A : set R) : convex_set [set` (Rhull A)].
Proof. exact: convex_interval. Qed.

Lemma convex_is_inverval (A : set R) : convex_set A -> is_interval A.
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

Lemma smallest_convex_set (A B : set R) : A `<=` B ->
  convex_set B -> [set` Rhull A] `<=` B.
Proof.
move=> AB convB.
rewrite Rhull_smallest => C.
apply; split => //.
exact: convex_is_inverval.
Qed.

Lemma closure_seq (A : set R) x : x \in closure A <->
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

Lemma closure_convex_set (A : set R) : convex_set A -> convex_set (closure A).
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

Lemma closure_Rhull (A : set R) :
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

Lemma oscillationE (A : set R) (f : R -> R) :
  A !=set0 ->
  let B := [set (EFin \o f) x | x in A] in
  ereal_sup B \is a fin_num ->
  ereal_inf B \is a fin_num ->
  oscillation f A = ereal_sup [set `|f x - f y|%:E | x in A & y in A].
Proof.
move=> A0 B Mfin mfin.
rewrite /oscillation.
move/set0P : (A0) => /negPf ->.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: ge_ereal_sup => /= _ /= [r Ar [s As] <-].
  have [frfs|frfs] := leP (f r) (f s).
    rewrite ler0_norm ?subr_le0// opprB EFinB leeB//.
      apply/le_ereal_sup_tmp.
      by exists ((f s)%:E) => //=; exists s.
    rewrite ge_ereal_inf//.
    by exists ((f r)%:E) => //=; exists r.
  rewrite gtr0_norm ?subr_gt0// EFinB leeB//.
    apply/le_ereal_sup_tmp.
    by exists ((f r)%:E) => //=; exists r.
  rewrite ge_ereal_inf//.
  by exists ((f s)%:E) => //=; exists s.
apply/lee_addgt0Pr => /= e' e'0.
have B0 : B !=set0 by exact: image_nonempty.
set M : \bar R := ereal_sup B.
set m : \bar R := ereal_inf B.
have := ereal_inf_sup B0.
rewrite -/M -/m.
rewrite le_eqVlt => /predU1P[-> {m}|mM].
  rewrite subee//.
  rewrite adde_ge0 ?lee_fin//; last exact: ltW.
  rewrite -(ereal_sup1 0) ereal_sup_le//.
  rewrite sub1set inE/=.
  by case: A0 => x Ax; exists x => //; exists x => //; rewrite subrr normr0.
pose e := minr e' (fine (M - m)).
have e20 : 0 < e / 2.
  rewrite divr_gt0// lt_min e'0/= fine_gt0// sube_gt0 mM/=.
  rewrite -(@gte0_abs _ (_ - _)%E) ?sube_gt0//.
  by rewrite -fin_num_abs fin_numB Mfin mfin.
have [r Ar rMe] : exists2 r, A r & ((f r)%:E > M - (e / 2)%:E)%E.
  have [x [r Ar] rx Bex] := @ub_ereal_sup_adherent _ B _ e20 Mfin.
  exists r => //.
  by rewrite -rx in Bex.
have [s As sme] : exists2 s, A s & ((f s)%:E < m + (e / 2)%:E)%E.
  have [y [s As] sy Bey] := @lb_ereal_inf_adherent _ B _ e20 mfin.
  exists s => //.
  by rewrite -sy in Bey.
rewrite (@le_trans _ _ (`|f r - f s|%:E + e'%:E))//.
  rewrite -leeBlDr//.
  rewrite (@le_trans _ _ ((M - (e' / 2)%:E) - (m + (e' / 2)%:E))%E)//.
    by rewrite oppeD// ?fin_num_adde_defl// addeACA -EFinB -opprD -splitr EFinN.
  rewrite ger0_norm.
    rewrite subr_ge0.
    rewrite -lee_fin (le_trans (ltW sme))// (le_trans _ (ltW rMe))//.
    rewrite leeBrDl// addeCA -EFinD -splitr.
    rewrite -leeBrDl//.
    rewrite -[leRHS]fineK ?fin_numB ?Mfin//.
    rewrite lee_fin.
    by rewrite /e ge_min lexx orbT.
  rewrite EFinB leeB// ltW//.
    rewrite (le_lt_trans _ rMe)//.
    by rewrite leeB// lee_fin ler_wpM2r// /e ge_min lexx.
  rewrite (lt_le_trans sme)//.
  by rewrite leeD2l// lee_fin ler_wpM2r// /e ge_min lexx.
rewrite leeD2r//.
apply/le_ereal_sup_tmp.
exists `|f r - f s|%:E => //=.
by exists r => //; exists s.
Qed.

From mathcomp Require Import contra.

Lemma total_variationP a b (f : R -> R) : a <= b ->
  total_variation a b f = +oo%E <->
  total_variation a b f \isn't a fin_num.
Proof.
move=> ab; split => [->//|].
rewrite fin_numEn => /orP[|/eqP//].
rewrite -leeNy_eq leNgt => /negP abs.
absurd.
apply: abs.
by rewrite (lt_le_trans _ (total_variation_ge0 _ _)).
Qed.

Lemma not_bounded_variationP (a b : R) (f : R -> R) :
  a <= b ->
  ~ bounded_variation a b f <-> total_variation a b f = +oo%E.
Proof.
move=> ab.
split=> [abf|abf].
  apply/total_variationP => //.
  contra: abf.
  by move/bounded_variationP; apply.
move/bounded_variationP => /(_ ab).
apply/negP.
by apply/total_variationP.
Qed.

Lemma total_variation_ge_sub (A : set R) (f : R -> R) :
  bounded_set A ->
  forall x y, A x -> A y ->
  (`|f x - f y|%:E <= total_variation (inf A) (sup A) f)%E.
Proof.
move=> boundA x y.
wlog : x y / x < y.
  move=> wlg Ax Ay.
  have [xy|yx|xy]:= ltgtP x y.
  - exact: wlg.
  - by rewrite distrC wlg.
  - rewrite xy subrr normr0 total_variation_ge0//.
    by rewrite has_bound_inf_sup//; [exact: bounded_has_lbound|
                                     exact: bounded_has_ubound].
move=> xy Ax Ay.
have infAx : inf A <= x by apply: ge_inf => //; exact: bounded_has_lbound.
have ysupA : y <= sup A by apply: ub_le_sup => //; exact: bounded_has_ubound.
apply: le_ereal_sup_tmp.
exists (`|f x - f (inf A)| + `|f y - f x| + `|f (sup A) - f y|)%:E.
  eexists; last reflexivity.
  move: infAx; rewrite le_eqVlt => /predU1P[<-|infA].
  - rewrite subrr normr0 add0r.
    move: ysupA; rewrite le_eqVlt => /predU1P[->|ysupA].
    + rewrite subrr normr0 addr0.
      exists [:: sup A].
        rewrite /itv_partition/=.
        split => //; rewrite andbT.
        rewrite (@le_lt_trans _ _ x)//.
          by rewrite ge_inf//; exact: bounded_has_lbound.
        rewrite (@lt_le_trans _ _ y)//.
        by rewrite ub_le_sup//; exact: bounded_has_ubound.
      by rewrite !variation_recl variation_nil addr0.
    + exists [:: y; sup A].
        rewrite /itv_partition/=.
        split => //; rewrite ysupA !andbT.
        rewrite (@le_lt_trans _ _ x)//.
        by rewrite ge_inf//; exact: bounded_has_lbound.
      by rewrite !variation_recl variation_nil addr0.
  - move: ysupA; rewrite le_eqVlt => /predU1P[->|ysupA].
    + rewrite subrr normr0 addr0.
      exists [:: x; sup A].
        rewrite /itv_partition/=.
        split => //; rewrite infA andbT/=.
        rewrite (@lt_le_trans _ _ y)//.
        by rewrite ub_le_sup//; exact: bounded_has_ubound.
      by rewrite !variation_recl variation_nil addr0.
    + exists [:: x; y; sup A].
        rewrite /itv_partition/=.
        by split => //; rewrite infA andbT xy/= ysupA.
      by rewrite !variation_recl variation_nil addr0 addrA.
rewrite [in leLHS]distrC.
by rewrite !EFinD addeC addeA leeDr// adde_ge0.
Qed.

Lemma sup_not_bounded_variation (A : set R) f :
  bounded_set A ->
  ereal_sup [set (EFin \o f) x | x in A] = +oo%E ->
  ~ bounded_variation (inf A) (sup A) f.
Proof.
move=> boundA.
have [->|/set0P [r Ar] fAy] := eqVneq A set0.
  by rewrite image_set0 ereal_sup0.
move/bounded_variationP.
rewrite has_bound_inf_sup//; [exact: bounded_has_lbound|
                              exact: bounded_has_ubound|].
move=> /(_ isT).
set M := total_variation _ _ _.
move=> Mfin.
suff : (ereal_sup ((EFin \o f) @` A) <= (f r)%:E + (M + 1))%E.
  by rewrite fAy leNgt ltey negbK -(fineK Mfin).
suff: ((EFin \o f) @` A) `<=` `]-oo, (f r)%:E + (M + 1)%E[.
  move/ereal_sup_le => /le_trans; apply.
  apply: ge_ereal_sup => z/=.
  by rewrite in_itv/= => /ltW.
move=> _ /= [s As <-].
rewrite in_itv/= -(fineK Mfin) lte_fin//.
rewrite (@le_lt_trans _ _ (f r + `|f s - f r|))//.
  by rewrite -lerBlDl ler_norm.
rewrite ltrD2l.
rewrite -ltrBlDr.
rewrite -lte_fin fineK//.
rewrite EFinB.
rewrite (@lt_le_trans _ _ `|f s - f r|%:E)//.
   by rewrite lteBlDr// lteDl.
by rewrite total_variation_ge_sub.
Qed.

Lemma inf_not_bounded_variation (A : set R) f :
  bounded_set A ->
  ereal_inf [set (EFin \o f) x | x in A] = -oo%E ->
  ~ bounded_variation (inf A) (sup A) f.
Proof.
move=> boudnA.
rewrite /ereal_inf => /(congr1 (fun x => - x)%E).
rewrite oppeK/=.
rewrite image_comp.
move/sup_not_bounded_variation => fA.
by move/bounded_variationN; exact: fA.
Qed.

Lemma bounded_set_oscillation_le_total_variations (A : set R) f :
  bounded_set A ->
  (oscillation f A <= total_variation (inf A) (sup A) f)%E.
Proof.
move=> boundA.
have [->|/set0P A0] := eqVneq A set0.
  rewrite oscillation0.
  rewrite total_variation_ge0//.
  by rewrite inf0 sup0.
have [supfin|] := boolP (ereal_sup ((EFin \o f) @` A) \is a fin_num); last first.
  move=> /fin_numPn[|].
    move=> /ereal_sup_ninfty/subset_set1[|].
      move/image_set0_set0/eqP.
      by move/set0P : A0 => /negbTE ->.
    rewrite /oscillation => ->.
    rewrite ereal_sup1 ereal_inf1/=.
    by move/set0P : A0 => /negPf ->; rewrite leNye.
  move/sup_not_bounded_variation => /(_ boundA).
  move/not_bounded_variationP => ->.
    by rewrite has_bound_inf_sup//; [exact: bounded_has_lbound|
                                     exact: bounded_has_ubound].
  by rewrite leey.
have [inffin|] := boolP (ereal_inf ((EFin \o f) @` A) \is a fin_num); last first.
  move=> /fin_numPn[|].
    move/inf_not_bounded_variation => /(_ boundA).
    move/not_bounded_variationP => ->.
      by rewrite has_bound_inf_sup//; [exact: bounded_has_lbound|
                                     exact: bounded_has_ubound].
    by rewrite leey.
  move=> /ereal_inf_pinfty/subset_set1[|].
    move/image_set0_set0/eqP.
    by move/set0P : A0 => /negbTE ->.
  rewrite /oscillation => ->.
  rewrite ereal_sup1 ereal_inf1/=.
  by move/set0P : A0 => /negPf ->; rewrite leNye.
rewrite oscillationE//.
apply: ge_ereal_sup => /= _ [r Ar [s As <-]].
wlog : r s Ar As / r < s.
  move=> wlg.
  have [rs|sr|sr] := ltgtP r s.
  + exact: wlg.
  + by rewrite distrC wlg.
  + rewrite sr subrr normr0 total_variation_ge0//.
    by rewrite has_bound_inf_sup//; [exact: bounded_has_lbound|
                                     exact: bounded_has_ubound].
move=> rs; apply: (@le_trans _ _ (total_variation r s f)).
  apply: le_ereal_sup_tmp.
  eexists; last exact: lexx.
  exists `|f r - f s| => //.
  exists [:: s] => /=.
    by rewrite /itv_partition/= andbT.
  by rewrite /variation/= big_nat1/= distrC.
apply: (@le_trans _ _ (total_variation (inf A) s f)).
  rewrite (@total_variationD _ (inf A) s r)//.
    by apply: ge_inf => //; exact: bounded_has_lbound.
    exact: ltW.
  by rewrite leeDr// total_variation_ge0// ge_inf//; exact: bounded_has_lbound.
apply: (@total_variation_nondecreasing _ _ (sup A) f).
- rewrite in_itv/=; apply/andP; split.
    by apply: ge_inf => //; exact: bounded_has_lbound.
  by apply: ub_le_sup => //; exact: bounded_has_ubound.
- rewrite !bound_itvE has_bound_inf_sup//; [exact: bounded_has_lbound|
                                            exact: bounded_has_ubound].
- by apply: ub_le_sup => //; exact: bounded_has_ubound.
(*
rewrite Rbounded_setE/= => -[haslbA hasubA].
apply: (@le_trans _ _ (oscillation f [set` Rhull A])).
  apply: oscillation_sub.
  exact: sub_Rhull.
rewrite -oscillation_closure.
rewrite compact_Rhull.
  rewrite Rcompact_boundE; split => //.*)
Qed.

From mathcomp Require Import derive.

Lemma oscillation_ub (c d : R) (f : R -> R) (e : R) : c < d ->
  {within `[c, d], continuous f} -> 0 < e ->
  exists xy, [/\ `]c, d[%classic xy.1, `]c, d[%classic xy.2, xy.1 <= xy.2 &
    (`|f xy.1 - f xy.2|%:E > oscillation f `]c, d[ - e%:E)%E ].
Proof.
move=> cd cf e0.
have e20 : 0 < e / 2 by rewrite divr_gt0.
pose A := `]c, d[%classic.
have ? : has_ubound [set f x | x in A].
  have [M Mcd Mmax] := EVT_max (ltW cd) cf.
  exists (f M) => _/= [r Ar <-].
  apply: Mmax.
  exact: subset_itv_oo_cc Ar.
have ? : has_lbound [set f x | x in A].
  have [m mcd mmin] := EVT_min (ltW cd) cf.
  exists (f m) => _/= [r Ar <-].
  apply: mmin.
  exact: subset_itv_oo_cc Ar.
have A0 : A !=set0.
  exists ((c + d) / 2).
  rewrite /A/= in_itv/=.
  by rewrite !midf_lt//=.
have : has_sup (f @` A) by split => //; exact: image_nonempty.
move/sup_adherent => /(_ _ e20)[x [r Ar <-{x}] supAer].
have : has_inf (f @` A) by split => //; exact: image_nonempty.
move/inf_adherent => /(_ _ e20)[y [s As <-{y}] infAes].
set D := sup (f @` A) - inf (f @` A).
have /orP[rs|sr] := le_total r s.
  exists (r, s); split => //=.
  rewrite /oscillation -/A.
  move: (A0) => /set0P /negPf ->.
  rewrite (splitr e)/= EFinN.
  rewrite EFinD oppeD//.
  rewrite addeACA.
  rewrite -oppeD.
    by rewrite fin_num_adde_defl.
  rewrite -image_comp.
  rewrite ereal_sup_EFin//.
    exact: image_nonempty.
  rewrite ereal_inf_EFin//.
    exact: image_nonempty.
  rewrite -EFinB lte_fin.
  have [De|eD] := ltP D e.
    rewrite opprD -addrACA -opprD -splitr.
    by rewrite (@lt_le_trans _ _ 0)// subr_lt0.
  have fsfr : f s < f r.
    rewrite (le_lt_trans _ supAer)//.
    rewrite (le_trans (ltW infAes))//.
    rewrite -lerBrDr.
    rewrite -addrA.
    rewrite -opprD.
    rewrite -splitr.
    rewrite lerBrDr.
    by rewrite -lerBrDl.
  rewrite gtr0_norm.
    by rewrite subr_gt0.
  rewrite ltrD//.
  by rewrite ltrN2.
exists (s, r); split => //=.
rewrite /oscillation -/A.
move: (A0) => /set0P /negPf ->.
rewrite (splitr e)/= EFinN.
rewrite EFinD oppeD//.
rewrite addeACA.
rewrite -oppeD.
  by rewrite fin_num_adde_defl.
rewrite -image_comp.
rewrite ereal_sup_EFin//.
  exact: image_nonempty.
rewrite ereal_inf_EFin//.
  exact: image_nonempty.
rewrite -EFinB lte_fin.
have [De|eD] := ltP D e.
  rewrite opprD -addrACA -opprD -splitr.
  by rewrite (@lt_le_trans _ _ 0)// subr_lt0.
have fsfr : f s < f r.
  rewrite (le_lt_trans _ supAer)//.
  rewrite (le_trans (ltW infAes))//.
  rewrite -lerBrDr.
  rewrite -addrA.
  rewrite -opprD.
  rewrite -splitr.
  rewrite lerBrDr.
  by rewrite -lerBrDl.
rewrite ltr0_norm.
  by rewrite subr_lt0.
rewrite opprB.
rewrite ltrD//.
by rewrite ltrN2.
Qed.

Lemma variations_neq0_new (a b : R) (f : R -> R) :
  b < a -> variations a b f = set0.
Proof.
move=> ba.
rewrite -subset0 => /= x [s].
move/itv_partition_le.
by rewrite leNgt ba.
Qed.

Lemma total_variationxx (a b : R) (f : R -> R) : b <= a ->
  total_variation a b f = 0.
Proof.
rewrite le_eqVlt => /predU1P[->|ba].
  by rewrite total_variationxx.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: ge_ereal_sup => z/= [r].
  by rewrite variations_neq0_new.
(*rewrite total_variation_ge0.*)
rewrite /total_variation.
rewrite variations_neq0_new//.
rewrite image_set0 ereal_sup0.
Abort.

(* TODO: move *)
Lemma nth_map_iota {T} (x : T) (n : nat) (f : nat -> T) (i : nat) :
  (i < n)%N ->
  nth x [seq f k | k <- iota 0 n] i = f i.
Proof.
by move=> iltn; rewrite (nth_map 0%N) ?nth_iota; first by rewrite size_iota.
Qed.

(* ordering of interval bounds *)
Section interval_bounds.
Context (A_ B_ : nat -> R).

Definition ABi_ n := [seq ((A_ i, B_ i), i) | i <- iota 0 n].

Definition abi_ n := sort (fun x y => x.1.1 <= y.1.1) (ABi_ n).

Definition seq_a n := unzip1 (unzip1 (abi_ n)).

Definition seq_b n := unzip2 (unzip1 (abi_ n)).

Lemma size_seq_ab {T} (mp : R * R -> T) n :
  size (map mp (unzip1 (abi_ n))) = n.
Proof.
by rewrite !size_map size_sort size_map size_iota.
Qed.

Definition idxs n := unzip2 (abi_ n).

Definition a_ def n := nth def (seq_a n).

Definition b_ def n := nth def (seq_b n).

Definition idx n := nth 0 (idxs n) : nat -> nat.

Lemma sorted_a n : sorted <=%R (seq_a n).
Proof.
rewrite sorted_map ?sort_sorted// sorted_map sort_sorted//=.
by move=> ? ?/=; rewrite le_total.
Qed.

Lemma iota_unzip2 n : iota 0 n = unzip2 (ABi_ n).
Proof.
rewrite /ABi_ /unzip2 -map_comp.
rewrite -[LHS]map_id.
exact: eq_map.
Qed.

Lemma perm_iota_sort1 n : perm_eq (idxs n) (iota 0 (size (ABi_ n))).
Proof.
set d : R := 0.
have [q H1 H2] :=
  perm_iota_sort (fun x y : R * R * nat => x.1.1 <= y.1.1) (d, d, 0) (ABi_ n).
have K1 : forall h, h \in q -> (h < n)%N.
  move=> h.
  rewrite (perm_mem H1) mem_iota leq0n/= add0n.
  by rewrite size_map size_iota.
apply: perm_trans H1.
have idxs_q : idxs n = q.
  rewrite /idxs /abi_.
  move/(congr1 unzip2) : H2 => ->.
  apply/(@eq_from_nth _ 0).
    by rewrite !size_map.
  move=> i.
  rewrite !size_map => iq.
  rewrite (nth_map 0) ?size_map//.
  rewrite (nth_map 0) ?size_map//.
  rewrite snd_map ?size_map ?size_iota//.
    rewrite K1//.
    by apply/mem_nth.
  rewrite (nth_map 0) ?size_map ?size_iota//.
    rewrite K1//.
    by apply/mem_nth.
  rewrite (nth_map 0) ?size_map ?size_iota//.
    rewrite K1//.
    by apply/mem_nth.
  rewrite nth_iota//.
  rewrite K1//.
  exact/mem_nth.
by rewrite idxs_q.
Qed.

Lemma qin n i : i \in idxs n -> (i < n)%N.
Proof.
rewrite (perm_mem (perm_iota_sort1 n)).
rewrite mem_iota leq0n/= add0n.
by rewrite size_map size_iota.
Qed.

Lemma perm_iota_sort2 d n : sort (fun x y : R * R * nat => x.1.1 <= y.1.1) (ABi_ n) =
    [seq nth (d, d, 0) (ABi_ n) i | i <- idxs n].
Proof.
have [q H1 H2] :=
  perm_iota_sort (fun x y : R * R * nat => x.1.1 <= y.1.1) (d, d, 0) (ABi_ n).
have K1 : forall h, h \in q -> (h < n)%N.
  move=> h.
  rewrite (perm_mem H1) mem_iota leq0n/= add0n.
  by rewrite size_map size_iota.
have idxs_q : idxs n = q.
  (* copy paste *)
  rewrite /idxs /abi_.
  move/(congr1 unzip2) : H2 => ->.
  apply/(@eq_from_nth _ 0).
    by rewrite !size_map.
  move=> i.
  rewrite !size_map => iq.
  rewrite (nth_map 0) ?size_map//.
  rewrite (nth_map 0) ?size_map//.
  rewrite snd_map ?size_map ?size_iota//.
    rewrite K1//.
    by apply/mem_nth.
  rewrite (nth_map 0) ?size_map ?size_iota//.
    rewrite K1//.
    by apply/mem_nth.
  rewrite (nth_map 0) ?size_map ?size_iota//.
    rewrite K1//.
    by apply/mem_nth.
  rewrite nth_iota// K1//.
  exact/mem_nth.
by rewrite H2 idxs_q.
Qed.

Lemma idx_bij n :
  exists idxn_ord_with_inv : ('I_n -> 'I_n) * ('I_n -> 'I_n),
  [/\ (forall (i : nat) (iltn1 : (i < n)%N),
         idx n i = idxn_ord_with_inv.1 (Ordinal iltn1)),
  @cancel _ _ idxn_ord_with_inv.1 idxn_ord_with_inv.2 &
  @cancel _ _ idxn_ord_with_inv.2 idxn_ord_with_inv.1].
Proof.
have abE : (abi_ n) =i (ABi_ n).
  apply: perm_mem.
  by rewrite perm_sort; exact: perm_refl.
pose d : R := 0.
have idx_lt (i : 'I_ n) : (idx n i < n)%N.
  rewrite /idx /idxs.
  have isize : (i < size (abi_ n))%N by rewrite size_sort size_map size_iota.
  rewrite /idx.
  rewrite (nth_map (d, d, 0))//.
  have : nth (d, d, 0%N) (abi_ n) i  \in (ABi_ n).
    by rewrite -(abE _); exact: mem_nth.
  by move/mapP => [m]; rewrite mem_iota add0n => /andP[_ mn] ->.
pose idx_ord (i : 'I_n) := Ordinal (idx_lt i).
pose idx_inv (j : nat) := index j (idxs n).
have idx_inv_lt (j : 'I_n) : (idx_inv j < n)%N.
  rewrite /idx_inv.
(* rewrite (_: n.+1 = soze (idxs n) is error (why?) *)
  have : (size (idxs n) <= n)%N.
    by rewrite size_map size_sort size_map size_iota.
  move/ltn_leq_trans; apply.
  rewrite index_mem.
  rewrite (@perm_mem _ _ (iota 0 n)).
    rewrite iota_unzip2.
    apply: perm_map.
    by rewrite perm_sort.
  by rewrite mem_iota leq0n/=.
pose idx_ord_inv j := Ordinal (idx_inv_lt j).
have idxE (i : 'I_n) : idx n i = idx_ord i by [].
exists (idx_ord, idx_ord_inv); split => //.
- move=> x/=.
  destruct n; first by case: x.
  rewrite -(inord_val (idx_ord x)) -(inord_val (idx_ord_inv _))/=.
  rewrite -[RHS](inord_val x); congr inord; rewrite /idx_inv inordK//.
  rewrite nthK//; last by rewrite inE size_map size_sort size_map size_iota.
  rewrite (@perm_uniq _ _ (iota 0 n.+1)).
    have : perm_eq (abi_ n.+1) (ABi_ n.+1) by rewrite perm_sort.
    move/(perm_map snd)/perm_trans; apply.
    by rewrite -map_comp map_id.
  exact: iota_uniq.
- move=> x/=.
  destruct n; first by case: x.
  rewrite -(inord_val (idx_ord_inv x)) -(inord_val (idx_ord _))/=.
  rewrite -[RHS](inord_val x) ; congr inord; rewrite /idx_inv inordK//.
    exact: idx_inv_lt.
  apply: nth_index.
  suff -> : idxs n.+1 =i iota 0 n.+1.
    rewrite mem_iota leq0n//=.
  rewrite iota_unzip2.
  exact: eq_mem_map.
Qed.

Let abidE def n i : (a_ def n i, b_ def n i, idx n i) = nth (def, def, 0) (abi_ n) i.
Proof.
rewrite -(zip_unzip (abi_ n)) -(zip_unzip (unzip1 _)).
by rewrite !nth_zip ?size_zip ?size_map ?minnn.
Qed.

Lemma anth def n i : a_ def n i = (nth (def, def, 0) (abi_ n) i).1.1.
Proof. by rewrite -abidE. Qed.

Lemma bnth def n i : b_ def n i = (nth (def, def, 0) (abi_ n) i).1.2.
Proof. by rewrite -abidE. Qed.

Lemma idxE def n i : idx n i = (nth (def, def, 0) (abi_ n) i).2.
Proof. by rewrite -abidE. Qed.

Lemma nth_abE def n i : (i < n)%N ->
  let p := nth (def, def, 0%N) (abi_ n) i in
  [/\ p.1.1 = A_ p.2, p.1.2 = B_ p.2 & (p.2 < n)%N].
Proof.
have abE : abi_ n =i ABi_ n.
  apply: perm_mem.
  by rewrite perm_sort; exact: perm_refl.
move=> ilen p.
have isize : (i < size (abi_ n))%N by rewrite size_sort size_map size_iota.
have : p \in (ABi_ n) by rewrite -(abE p); exact: mem_nth.
move/mapP => [m]; rewrite mem_iota add0n => /andP[_ mn] ->.
by split.
Qed.

Lemma altb def n i : (forall i, A_ i < B_ i) ->
  (i < n)%N -> a_ def n i < b_ def n i.
Proof.
move=> AB ni.
rewrite anth bnth.
have [-> -> idxn] := nth_abE def ni.
exact/AB.
Qed.

Lemma aleb def n i : (forall i, A_ i < B_ i) ->
  a_ def n i <= b_ def n i.
Proof.
move=> AB.
have [ni|ni ] := leqP n i.
  rewrite /a_ /b_.
  by rewrite !nth_default ?size_seq_ab.
exact/ltW/altb.
Qed.

Lemma perm_eqA_B_ def n : perm_eq
  [seq `]A_ i, B_ i[%classic | i <- iota 0 n]
  [seq `]a_ def n i, b_ def n i[%classic | i <- iota 0 n].
Proof.
rewrite perm_sym; apply/(perm_iotaP set0).
exists (idxs n).
  rewrite size_map size_iota.
  rewrite /idxs.
  apply: (perm_trans (@perm_map _ _ snd (abi_ n) (ABi_ n) _)).
    by rewrite perm_sort.
  by rewrite -map_comp map_id perm_refl.
apply: (@eq_from_nth _ set0); first by rewrite !size_map size_sort size_map.
move=> j; rewrite size_map size_iota => jn.
rewrite nth_map_iota// -map_comp.
rewrite (nth_map (def, def, 0)); first by rewrite size_sort size_map size_iota.
rewrite anth bnth.
by have [-> -> idn] := nth_abE def jn; rewrite /comp nth_map_iota.
Qed.

Definition cd_ c d n := zip (c :: seq_b n) (rcons (seq_a n) d).

Lemma size_seq_cd {T} (mp : R * R -> T) c d n : size (map mp (cd_ c d n)) = n.+1.
Proof.
rewrite size_map size_zip size_rcons/= !size_map minnn.
by rewrite size_sort size_map size_iota.
Qed.

Definition seq_c c d n := unzip1 (cd_ c d n).

Definition seq_d c d n := unzip2 (cd_ c d n).

Definition c_ c d n j := nth d (seq_c c d n) j.

Lemma cbE c d n j : c_ c d n j = if j == 0 then c else b_ d n j.-1.
Proof.
case: j => [|j/=].
  rewrite eqxx.
  rewrite /c_ /seq_c unzip1_zip//=.
  by rewrite size_rcons !size_map.
have [nj|jn] := leqP n.+1 j.+1.
  rewrite /c_ /seq_c.
  rewrite bnth !nth_default ?size_seq_cd//.
  by rewrite size_sort size_map size_iota -ltnS.
rewrite /c_ /seq_c.
by rewrite unzip1_zip/=; first by rewrite size_rcons/= !size_map.
Qed.

Definition d_ c d n j := nth d (seq_d c d n) j.

Lemma daE c d n j : d_ c d n j = a_ d n j.
Proof.
rewrite /d_ /seq_d.
rewrite unzip2_zip; first by rewrite size_rcons/= !size_map.
rewrite nth_rcons !size_map size_sort size_map size_iota.
case: ifPn => [//|].
rewrite if_same /a_ -leqNgt => nj.
rewrite /a_.
by rewrite nth_default// size_seq_ab.
Qed.

Lemma seq_b_nth_iota_idxs d n :
  seq_b n = [seq nth d [seq B_ i | i <- iota 0 n] i | i <- idxs n].
Proof.
rewrite /seq_b.
rewrite /unzip2.
rewrite -2!map_comp.
apply/eq_in_map => i iq.
rewrite -compA [in LHS]/=.
move: iq.
rewrite /abi_ mem_sort => /mapP[j].
rewrite mem_iota leq0n add0n => jn ->.
rewrite [n]lock /= -lock.
by rewrite nth_map_iota.
Qed.

Lemma seq_b_idxs n : seq_b n = [seq B_ i | i <- idxs n].
Proof.
rewrite (seq_b_nth_iota_idxs 0).
apply/eq_in_map => i iq.
rewrite nth_map_iota//.
exact: qin iq.
Qed.

End interval_bounds.

Lemma subspace_setCS (X A B : set R) : A `<=` X -> B `<=` X ->
  A `<=` B = (X `\` B `<=` X `\` A).
Proof.
move=> AX BX.
apply/propeqP; split => [|H x Ax]; first exact: setDS.
have [Xx|nBx] := pselect (X x).
  apply/not_notP => nBx.
  have /H[_] := conj Xx nBx.
  exact.
exfalso.
apply: nBx.
exact: AX.
Qed.

Lemma contiguous_intervals_Rhull (A : set R) (cA : closed A) :
  \bigcup_k contiguous_intervals A k `|` A = [set` Rhull A].
Proof.
rewrite -bigcup_contiguous_intervals//.
by rewrite /cplt_hull setDKU//; exact: sub_Rhull.
Qed.

Lemma ordinal_val (n : nat) (i : 'I_ n.+1) :
  i = Ordinal (ltn_ord i).
Proof. by rewrite -(inord_val (Ordinal _))/= inord_val. Qed.

(*
Z : set R
contiguous_intervals Z :
[c   = c_0, d_0 = a_0]  ]a_0, b_0[
[c_1 = b_0, d_1 = a_1]  ]a_1, b_1[
[c_2 = b_1, d_2 = a_2]  ]a_2, b_2[
...
[c_n.-1 = b_n.-2, d_n.-1 = a_n.-1] ]a_n.-1, b_n.-1[
[c_n    = b_n.-1, d_n = a_n]       ]a_n, b_n[
[c_n.+1 = b_n, d_n.+1 = d]
*)
Section contiguous_intervals.
Context (Z : set R) (a b : R) (lbZ : has_lbound Z) (ubZ : has_ubound Z).
Let supp := contiguous_intervals_support Z.
Variable h1 : {splitbij [set: nat] >-> supp}.
Let A_ n := contiguous_intervals1 Z (h1 n).
Let B_ n := contiguous_intervals2 Z (h1 n).

Let seq_b := seq_b A_ B_.

Lemma sorted_B_idxs n : sorted <=%R [seq B_ i | i <- idxs A_ B_ n].
Proof.
rewrite /B_.
rewrite map_comp.
apply: contiguous_intervals_sort => //.
  move=> i/=.
  move/mapP => /= [j jq ->].
  by have [+ _ _] := @bij _ _ _ _ h1; exact.
rewrite -map_comp/=.
rewrite [X in sorted _ X](_ : _ = [seq A_ i | i <- idxs A_ B_ n])//.
pose d : R := 0.
suff: sorted (fun x y : R * R * nat => x.1.1 <= y.1.1) (abi_ A_ B_ n).
  rewrite /abi_.
  rewrite (perm_iota_sort2 A_ B_ d).
  evar (l : seq (R * R * nat)).
  rewrite (_ : [seq nth (d, d, 0) (ABi_ A_ B_ n) i | i <- idxs A_ B_ n] = l).
    by apply: eq_map.
  rewrite {}/l.
  have -> : [seq A_ i | i <- idxs A_ B_ n] =
             [seq nth d (unzip1 (unzip1 (ABi_ A_ B_ n))) i | i <- idxs A_ B_ n].
    apply/eq_in_map => i iq.
    have ? : (i < n)%N.
      move: iq.
      by rewrite (perm_mem (perm_iota_sort1 A_ B_ n)) mem_iota leq0n/= add0n size_map size_iota.
    by rewrite /ABi_ /unzip1 -2!map_comp nth_map_iota.
  rewrite -sorted_map.
  rewrite -map_comp.
  under eq_map => i/=.
  have -> : (nth (d, d, 0) (ABi_ A_ B_ n) i).1.1 = nth d (unzip1 (unzip1 (ABi_ A_ B_ n))) i.
    have [iltSn|ni] := ltnP i n.
      rewrite (nth_map (d, d)); first by rewrite !size_map size_iota.
      by rewrite (nth_map (d, d, 0))// !size_map size_iota.
    by rewrite !nth_default// !size_map size_iota.
  over.
  by [].
rewrite /abi_.
apply: sort_sorted.
by move=> ? ?/=; rewrite le_total.
Qed.

Lemma sorted_b (d : R) n : sorted <=%R (seq_b n).
Proof.
rewrite /seq_b.
rewrite (seq_b_nth_iota_idxs A_ B_ d).
rewrite [X in sorted _ X](_ : _ = [seq B_ i | i <- idxs A_ B_ n]).
  rewrite -seq_b_idxs.
  by rewrite (seq_b_nth_iota_idxs A_ B_ d).
exact: sorted_B_idxs.
Qed.

Let c := inf Z.
Let d := sup Z.
Let a_ := a_ A_ B_ d.
Let b_ := b_ A_ B_ d.

Lemma clea_bled : Z !=set0 -> (forall i, A_ i < B_ i) ->
  (forall n i, c <= a_ n i) /\ (forall n i, b_ n i <= d).
Proof.
move=> Z0 AB.
apply/all_and2 => n; apply/all_and2 => i.
have [ni|] := leqP n i.
  rewrite /a_ /b_ /lemmas.a_ /lemmas.b_.
  rewrite !nth_default ?size_seq_ab//; split => //; exact: has_bound_inf_sup.
move/(nth_abE A_ B_ d) => [+ + _].
rewrite -/abi_.
rewrite -anth -bnth -idxE -/a_ -/b_ => -> ->.
have ABcd : `]A_ (idx A_ B_ n i), B_ (idx A_ B_ n i)[ `<=` `[c, d].
  rewrite -contiguous_ooitv//.
  apply: (@subset_trans  _ [set` Rhull Z]).
    apply: (subset_trans (@contiguous_intervalsS _ _ _)).
    exact: cplt_hull_subset_Rhull.
  apply: subset_itv.
    rewrite ifT.
      exact/asboolP.
    by have [_|_] := boolP `[< (Z (inf Z)) >]; rewrite bnd_simp.
  rewrite ifT.
    exact/asboolP.
  by have [_|_] := boolP `[< (Z (sup Z)) >]; rewrite bnd_simp.
split.
  rewrite leNgt; apply/negP => Ac.
  set x := ((A_ (idx A_ B_ n i)) + minr (B_ (idx A_ B_ n i)) c) / 2.
  have : x < c.
    rewrite /x [in ltRHS](splitr c) mulrDl ltr_leD// ?ltr_pM2r ?ler_pM2r//.
    by rewrite ge_min lexx orbT.
  apply/negP; rewrite -leNgt.
  have : x \in `]A_ (idx A_ B_ n i), B_ (idx A_ B_ n i)[.
    rewrite in_itv/=; apply/andP; split.
      by rewrite midf_lt// lt_min AB Ac.
    rewrite (splitr (B_ _)) /x mulrDl ltr_leD// ?ltr_pM2r ?ler_pM2r//.
    by rewrite ge_min lexx.
  move/(ABcd x) => /=.
  by rewrite in_itv/= => /andP[].
rewrite leNgt; apply/negP => Bd.
  set y := (maxr (A_ (idx A_ B_ n i)) d + B_ (idx A_ B_ n i)) / 2.
  have : d < y.
    rewrite /y [in ltLHS](splitr d) mulrDl ler_ltD// ?ltr_pM2r ?ler_pM2r//.
    by rewrite le_max lexx orbT.
  apply/negP; rewrite -leNgt.
  have : y \in `]A_ (idx A_ B_ n i), B_ (idx A_ B_ n i)[.
    rewrite in_itv/=; apply/andP; split.
      rewrite (splitr (A_ _)) /y mulrDl ler_ltD// ?ltr_pM2r ?ler_pM2r//.
      by rewrite le_max lexx.
    by rewrite midf_lt// gt_max Bd AB.
  by move/(ABcd y) => /= /itvP ->.
Qed.

Lemma blea : c < d -> compact Z -> Z !=set0 -> (forall i, A_ i < B_ i) ->
  forall n i, b_ n i <= a_ n i.+1.
Proof.
(* disjoint_contiguous_intervals *)
move=> cd compactZ Z0 AB.
move=> n i.
have [ni|iltn] := leqP n.-1 i.
  rewrite /a_ /lemmas.a_.
  rewrite nth_default//.
    rewrite !size_map size_sort size_map size_iota.
    by destruct n => //.
  exact: (clea_bled Z0 AB).2.
rewrite leNgt; apply/negP => aibi.
(* TODO: take out, seems to depend only on sorted_b *)
have : `]a_ n i, b_ n i[ `&` `]a_ n i.+1, b_ n i.+1[ !=set0.
  rewrite [X in X !=set0](_ : _ = [set` `]a_ n i.+1, b_ n i[]).
    rewrite -set_itvI/=.
    rewrite /Order.meet/=.
    apply/set_itvP => r/=.
    congr (_ \in _).
    rewrite join_r.
      rewrite bnd_simp /a_.
      rewrite sorted_leq_nth ?inE//.
          exact: le_trans.
          exact: sorted_a.
        rewrite !size_map size_sort size_map size_iota.
        by rewrite (leq_trans iltn)// leq_pred.
      rewrite !size_map size_sort size_map size_iota.
      by destruct n => //.
    rewrite meet_l//.
    rewrite bnd_simp.
    rewrite sorted_leq_nth ?inE//.
        exact: le_trans.
        exact: sorted_b.
      rewrite !size_map size_sort size_map size_iota.
      by rewrite (leq_trans iltn)// leq_pred.
    rewrite !size_map size_sort size_map size_iota.
    by destruct n.
  exists ((a_ n i.+1 + b_ n i) / 2) => /=.
  by rewrite in_itv/= midf_lt//= midf_lt.
rewrite /a_ /b_ /seq_a /seq_b.
have /(@perm_eq_trivIset _ _ _ setT (subsetT _)) := perm_eqA_B_ A_ B_ d n.
have triv_cgitv : trivIset [set: nat]
   [eta nth set0 [seq `]A_ i1, B_ i1[%classic | i1 <- iota 0 n]].
  apply/trivIsetP.
  move=> j1 j2 _ _ => j12.
  have [nj1|j1n] := ltnP n.-1 j1.
    rewrite nth_default ?size_map ?size_iota ?set0I//.
    by destruct n.
  have [nj2|j2n] := ltnP n.-1 j2.
    rewrite [X in _ `&` X]nth_default ?size_map ?size_iota ?setI0//.
    by destruct n.
  rewrite !nth_map_iota//.
    by destruct n.
    by destruct n.
  rewrite -!contiguous_ooitv//.
  have /trivIsetP := @disjoint_contiguous_intervals _ Z.
  apply => //.
  apply/negP; move/eqP.
  have [_ injh1 _] := @bij _ _ _ _ h1; move/injh1.
  by rewrite inE/= => /(_ I I); exact/eqP.
move/(_ triv_cgitv).
move/trivIsetP.
move/(_ _ _ I I (negbT (ltn_eqF (ltnSn i)))).
rewrite !nth_map_iota//; last first.
  move=> H /set0P/negP.
  exact/negP/eqP.
by destruct n.
by rewrite (leq_trans iltn)// leq_pred.
Qed.

Lemma cled : c < d -> compact Z -> Z !=set0 -> (forall i, A_ i < B_ i) ->
  forall n i, c_ A_ B_ c d n i <= d_ A_ B_ c d n i.
Proof.
move=> ? ? ? ? n i.
rewrite cbE daE.
case: i => /=[|i].
  by apply clea_bled.
by rewrite blea.
Qed.

Lemma Zcd n : c < d -> compact Z -> Z !=set0 -> (forall i, A_ i < B_ i) ->
  Z `<=` \bigcup_(i < n.+1) `[c_ A_ B_ c d n i, d_ A_ B_ c d n i]%classic.
Proof.
move=> cd cZ Z0 AB.
suff : [set` Rhull Z] `\` \bigcup_(i < n.+1) `[c_ A_ B_ c d n i, d_ A_ B_ c d n i]%classic
  `<=` cplt_hull Z.
  rewrite -subspace_setCS//.
    exact: sub_Rhull.
  move=> x [i iltn2]/=.
  rewrite compact_Rhull// !in_itv/= -/c -/d.
  move=> /andP[cx xd]; apply/andP; split.
    apply: le_trans cx.
    rewrite cbE; case: i iltn2 xd => //= i.
    rewrite ltnS => iltn1 _.
    apply: le_trans.
      by apply clea_bled.
    exact: aleb.
  apply: (le_trans xd).
  rewrite daE.
  apply: le_trans; first exact: aleb.
  by apply clea_bled.
apply: (@subset_trans _ (\bigcup_(i < n) `]a_ n i, b_ n i[%classic)).
  destruct n.
    rewrite 2!bigcup_mkord big_ord0 big_ord_recl/= big_ord0 setU0.
    rewrite cbE/= daE/= anth/=.
    by rewrite compact_Rhull// setDv.
  move=> x [hZx].
  rewrite {1}/bigcup/= exists2E; move/forallNP => ncdx.
  have has_b : has (> x) (seq_b n.+1).
    apply/(has_nthP d).
    exists n => //.
      by rewrite size_seq_ab.
  have := ncdx n.+1.
     rewrite ltnSn => /andP; rewrite andTb.
     rewrite in_itv/= negb_andb -!ltNge => /orP[|].
     by rewrite cbE.
   rewrite daE.
   rewrite /lemmas.a_.
   rewrite nth_default ?size_seq_ab// ltNge => /negP.
   by have := hZx; rewrite compact_Rhull//= in_itv/= => /andP[].
  (* x < b_ n k となる最小のk (remark: sorted <=%R (seq_b n)) *)
  pose k := find (> x) (seq_b n.+1).
  have kn1 : (k < n.+1)%N.
    by move: has_b; rewrite has_find size_seq_ab.
  exists k => //=.
  rewrite in_itv/=; apply/andP; split; last by rewrite nth_find.
  have [k0|] := eqVneq k 0.
    rewrite k0 ltNge; apply/negP => xan0.
    apply: (ncdx 0); split => //; rewrite in_itv cbE daE/=.
    apply/andP; split => //.
    by move: hZx; rewrite compact_Rhull//= in_itv/= => /andP[].
  rewrite -leqn0 -ltnNge => k0.
  rewrite ltNge; apply/negP => xank.
  apply: (ncdx k); split; first by rewrite ltnS ltnW.
  rewrite in_itv/= cbE daE ifF.
    by apply/negP/negP; rewrite -leqn0 -ltnNge.
  apply/andP; split => //.
  rewrite leNgt; apply/negP/negP; apply: negbT.
  apply: before_find; rewrite -/k.
  by rewrite ltn_predL.
rewrite bigcup_contiguous_intervals//.
  by apply: compact_closed.
rewrite bigcup_contiguous_intervals_support.
rewrite (_: \bigcup_(k in supp) contiguous_intervals Z k =
            \bigcup_k contiguous_intervals Z (h1 k)).
  have [funh1 injh1 surjh1] := @bij _ _ _ _ h1.
  by rewrite (reindex_bigcup _ _ _ _ funh1 surjh1).
move=> x [i /= iltn].
rewrite /a_ /b_ anth bnth.
have [-> -> _] := nth_abE A_ B_ d iltn.
rewrite -!idxE => xAB.
exists (idx A_ B_ n i) => //.
by rewrite contiguous_ooitv.
Qed.

Lemma citvScd n x : compact Z -> Z !=set0 -> (forall i, A_ i < B_ i) ->
  contiguous_intervals Z (h1 n) x ->
  forall m, (m <= n)%N ->
  exists2 p, (p < m.+1)%N & x \in `[c_ A_ B_ c d m p, d_ A_ B_ c d m p].
Proof.
move=> cZ X0 AB xn m nm.
have hasxd : has (> x) (seq_d A_ B_ c d m).
  apply/hasP.
  exists d.
    have {1}<- : d_ A_ B_ c d m m = d.
    rewrite daE /lemmas.a_ nth_default//.
      by rewrite size_seq_ab.
    rewrite mem_nth//.
    by rewrite size_seq_cd.
  have := xn.
  move/contiguous_intervalsS.
  by move/cplt_hull_lt_sup => /(_ ubZ).
set p := find (> x) (seq_d A_ B_ c d m).
have pE : p = find (> x) (seq_d A_ B_ c d m) by [].
have pltm2 : (p < m.+1)%N.
  rewrite -(size_seq_cd A_ B_ snd c d m).
  by rewrite -has_find.
exists p => //.
rewrite in_itv/=; apply/andP; split; last first.
  exact/ltW/nth_find.
case: p pE pltm2.
  rewrite cbE/=.
  have := xn.
  move/contiguous_intervalsS.
  move/cplt_hull_subset_Rhull.
  by rewrite compact_Rhull//= in_itv/= => /andP[].
move=> p pE p1ltm2.
rewrite leNgt; apply/negP.
rewrite cbE/= bnth.
have pltm1 : (p < m)%N.
  by rewrite ltnS in p1ltm2.
have : d_ A_ B_ c d m p < x.
  rewrite ltNge le_eqVlt; apply/negP => /predU1P.
  apply/not_orP; split.
    rewrite daE.
    move=> xamp.
    move: (xn).
    rewrite xamp.
    rewrite contiguous_ooitv//= in_itv/= => /andP[_ ].
    rewrite -/(B_ _).
    rewrite /a_.
    rewrite anth.
    have [-> _] := nth_abE A_ B_ d pltm1.
    rewrite -idxE => idxmpm1 AmpBn.
    have := @disjoint_contiguous_intervals _ Z.
    move/trivIsetP/(_ (h1 (idx A_ B_ m p)) (h1 n)).
    move/(_ I I).
    (* lemma *)
    have pn : h1 (idx A_ B_ m p) != h1 n.
      have [_ injh1 _] := @bij _ _ _ _ h1.
      apply/eqP.
      move/injh1; rewrite inE/= => /(_ I I).
      apply/eqP.
      rewrite neq_ltn; apply/orP; left.
      by rewrite (ltn_leq_trans idxmpm1)// ltnW.
    move/(_ pn).
    move/eqP; apply/negP/set0P.
    have : A_ n < B_ (idx A_ B_ m p).
      apply: (@lt_trans _ _ x).
        move: xn.
        by rewrite contiguous_ooitv//= in_itv/= => /andP[].
      rewrite xamp /a_ anth.
      have [-> _ _] := nth_abE A_ B_ d pltm1.
      rewrite -idxE.
      exact: AB.
    exists ((A_ (idx A_ B_ m p) + B_ n) / 2); split.
      rewrite contiguous_ooitv//= in_itv/=.
      apply/andP; split.
        by rewrite midf_lt.
      rewrite -/(B_ (idx A_ B_ m p)) mulrDl.
      rewrite (splitr (B_ (idx A_ B_ m p))).
      apply: ltr_leD.
        by rewrite ltr_pM2r.
      rewrite ler_pM2r//.
      rewrite leNgt; apply/negP => mpn.
      have := @disjoint_contiguous_intervals _ Z.
      move/trivIsetP/(_ (h1 (idx A_ B_ m p)) (h1 n)) => /=.
      move/(_ I I pn)/eqP.
      apply/negP/set0P.
      exists ((A_ (idx A_ B_ m p) + B_ (idx A_ B_ m p)) / 2); split.
        rewrite contiguous_ooitv//= in_itv/=; rewrite !midf_lt//.
        exact: AB.
      rewrite contiguous_ooitv//= in_itv/=; apply/andP; split.
        rewrite -/(A_ n) (splitr (A_ n)) mulrDl ltrD//.
          rewrite ltr_pM2r//.
          move: xn.
          rewrite contiguous_ooitv//= in_itv/= => /andP[+ _].
          rewrite xamp /a_ anth.
          by have [-> _ _] := nth_abE A_ B_ d pltm1; rewrite -idxE.
        by rewrite ltr_pM2r.
      rewrite -/(B_ n) (splitr (B_ n)) mulrDl.
      by apply: ltrD; rewrite ltr_pM2r.
    rewrite contiguous_ooitv//= in_itv/=; apply/andP; split.
      rewrite -/(A_ n) (splitr (A_ n)) mulrDl.
      apply: ltrD.
        rewrite ltr_pM2r//.
        move: xn.
        rewrite contiguous_ooitv//= in_itv/= => /andP[+ _].
        rewrite xamp /a_ anth.
        by have [-> _ _] := nth_abE A_ B_ d pltm1; rewrite -idxE.
      by rewrite ltr_pM2r.
    rewrite -/(B_ n) [in ltRHS](splitr (B_ n)) mulrDl.
    rewrite ltrD2r.
    by rewrite ltr_pM2r.
  apply/negP/negPf.
  apply: before_find.
  by rewrite pE.
rewrite daE anth.
have [-> -> +] := nth_abE A_ B_ d pltm1.
rewrite -idxE => idxltm1 Apx xBp.
have np : h1 n != h1 (idx A_ B_ m p).
  (* lt_le_trans pltm1 nm *)
  have [_ injh1 _] := @bij _ _ _ _ h1.
  apply/eqP; move/injh1; rewrite inE/= => /(_ I I).
  move/eqP.
  rewrite gtn_eqF//.
  by rewrite (ltn_leq_trans idxltm1)// ltnW.
have := @disjoint_contiguous_intervals _ Z.
move/trivIsetP/(_ (h1 n) (h1 (idx A_ B_ m p))).
move/(_ I I np).
apply/eqP/set0P; exists x; split => //.
by rewrite contiguous_ooitv//= in_itv/=; apply/andP; split.
Qed.

Lemma hullZ_abcd n : c < d -> compact Z -> Z !=set0 -> (forall i, A_ i < B_ i) ->
  [set` Rhull Z] =
  \bigcup_(i < n.+1) `[c_ A_ B_ c d n i, d_ A_ B_ c d n i]%classic `|`
  \bigcup_(i < n) `]a_ n i, b_ n i[%classic.
Proof.
move=> cd cZ Z_nonempty AB.
have clZ : closed Z by apply: compact_closed.
rewrite -(contiguous_intervals_Rhull clZ).
pose h := h1^-1%FUN.
have h1h : {in supp, cancel h h1} by exact: funK.
apply/seteqP; split => [r|r].
- move=> [|].
  + move=> [i _ Zir].
    have [hin|hin] := boolP (i \in map h1 (iota 0 n)).
      right.
      have [[idx_ord idx_ord_inv] /= [idx_ordE can_ord_inv can_inv_ord]]
        := idx_bij A_ B_ n.
      rewrite -/idx in idx_ordE.
      have hi_lt : (h i < n)%N.
        move: hin.
        rewrite -{1}(h1h i).
         by rewrite inE; exists r.
       rewrite mem_map.
         move=> t0 t1.
         have [_ + _]:= @bij _ _ _ _ h1.
         by apply => //; rewrite inE.
       by rewrite mem_iota add0n => /andP[].
      exists (idx_ord_inv (Ordinal hi_lt)).
        by rewrite /=.
      rewrite /a_ anth /b_ bnth.
      have []// := @nth_abE A_ B_ d n (idx_ord_inv (Ordinal hi_lt)).
      move=> -> ->; rewrite -idxE.
      rewrite -/idx.
      rewrite !idx_ordE.
      rewrite [X in (idx_ord X < _)%N](_ : _ = idx_ord_inv (Ordinal hi_lt)).
        exact: val_inj.
      rewrite [X in A_ (idx_ord X)] (_ : _ = idx_ord_inv (Ordinal hi_lt)).
        exact: val_inj.
      rewrite [X in B_ (idx_ord X)] (_ : _ = idx_ord_inv (Ordinal hi_lt)).
        exact: val_inj.
      rewrite can_inv_ord/=.
      move=> _.
      move: (Zir).
      rewrite (contiguous_ooitv ubZ lbZ).
      rewrite /A_ /B_.
      rewrite !h1h//.
      by rewrite inE; exists r.
    left.
    have ih1hi : i = h1 (h i) by rewrite h1h// inE; exists r.
    have nhi : (n <= h i)%N.
      move: hin.
      rewrite {1}ih1hi mem_map.
        move=> x y.
        have/set_bij_inj := (@bij _ _ _ _ h1).
        by apply; rewrite !inE.
      by rewrite mem_iota add0n leq0n/= -ltnNge ltnS.
    rewrite ih1hi in Zir.
    have [k kn2 rcd] := citvScd cZ Z_nonempty AB Zir nhi.
    by exists k.
  + move=> Zr.
    left.
    exact: Zcd.
- move=> [[i _]|[i _]]; rewrite (contiguous_intervals_Rhull clZ).
  + rewrite /= in_itv/= => /andP[cir rdi].
    rewrite compact_Rhull// in_itv/=; apply/andP; split.
      apply: le_trans cir.
      rewrite cbE; case: i rdi => //= i _.
      apply: le_trans; last exact: aleb.
      by apply clea_bled.
    apply: (le_trans rdi).
    rewrite daE.
    apply: le_trans; first exact: aleb.
    by apply clea_bled.
  + rewrite /= in_itv/= => /andP[/ltW air /ltW rbi].
    rewrite compact_Rhull// in_itv/=; apply/andP; split.
      apply: (le_trans _ air).
      by apply clea_bled.
    apply: (le_trans rbi).
    by apply clea_bled.
Qed.

Lemma disj_abcd n :
  \bigcup_(i < n.+1) `[c_ A_ B_ c d n i, d_ A_ B_ c d n i]%classic `&`
  \bigcup_(i < n) contiguous_intervals Z (h1 i) = set0.
Proof.
rewrite eqEsubset; split => x//=.
move=> [[i/= iltn2 xcidi] [j/= jltn1]].
rewrite contiguous_ooitv//= -/(A_ j) -/(B_ j).
have [[idx_ord idx_inv] /= [idx_ordE inv_ord ord_inv]] := idx_bij A_ B_ n.
rewrite -/idx in idx_ordE.
destruct n => //.
set j' : 'I_ n.+1 := Ordinal jltn1.
have -> : j = nat_of_ord j' by [].
rewrite -(ord_inv j').
rewrite (ordinal_val (idx_inv j')) -idx_ordE.
rewrite (idxE A_ B_ d)//.
have [] := @nth_abE A_ B_ d n.+1 (idx_inv j'); first by [].
move=> <- <- _.
rewrite -anth -bnth.
rewrite in_itv/= => /andP[aj'x bxj'].
move : xcidi.
rewrite cbE daE.
rewrite in_itv/=; apply/negP; rewrite negb_and -!ltNge; apply/orP.
case: i iltn2 => /=.
  move=> _; right.
  apply: le_lt_trans aj'x.
  by rewrite le_sorted_leq_nth// ?sorted_a// inE size_seq_ab.
move=> i.
rewrite ltnS => iltn1.
have [ji|ij] := leqP (idx_inv j') i.
  left.
  rewrite (lt_le_trans bxj')//.
  by rewrite le_sorted_leq_nth// ?sorted_b// inE size_seq_ab.
right.
apply: le_lt_trans aj'x.
move: iltn1.
rewrite leq_eqVlt => /predU1P[|].
  move/eq_add_S => eqin.
  rewrite /lemmas.a_ !nth_default// size_seq_ab.
    by rewrite eqin.
  by rewrite -[ltnLHS]eqin.
rewrite ltnS => iltn.
by rewrite le_sorted_leq_nth// ?sorted_a// inE size_seq_ab.
Qed.

End contiguous_intervals.

(* need *)
Lemma sum_oscillation_le_total_variation (a b : R) (f : R -> R) (A B : R^nat) :
  a < b ->
  {within `[a, b], continuous f} ->
  (forall i0 : nat, A i0 < B i0) ->
  let I i := `]A i, B i[%classic in
  trivIset [set: nat] I ->
  (forall n, `[A n, B n]%classic `<=` `[a, b]) ->
  (\sum_(i <oo) oscillation f (I i) <= total_variation a b f)%E.
Proof.
move=> ab cf AB I tI Iab.
apply: lime_le.
  apply: ereal_nondecreasing_is_cvgn => m n mn.
  apply: ereal_nondecreasing_series => // k _ _.
  by rewrite oscillation_ge0.
near=> n.
(* define the same functions as in lemma 6 *)
pose ABi_ := ABi_ A B.
pose abi_ := abi_ A B.
pose seq_a := seq_a A B.
pose seq_b := seq_b A B.
pose idxs := idxs A B.
pose a_ := a_ A B b.
pose b_ := b_ A B b.
pose idx n := idx A B.
pose i_ i : set R := `](a_ n i), (b_ n i)[%classic.
(* *)
apply/lee_addgt0Pr => /= e e0.
have ? : has_ubound (f @` `]a, b[).
  have [M Mcd Mmax] := EVT_max (ltW ab) cf.
  exists (f M) => _/= [r Ar <-].
  apply: Mmax.
  exact: subset_itv_oo_cc Ar.
have ? : has_lbound (f @` `]a, b[).
  have [m mcd mmin] := EVT_min (ltW ab) cf.
  exists (f m) => _/= [r Ar <-].
  apply: mmin.
  exact: subset_itv_oo_cc Ar.
have : forall i : 'I_n, exists xy, [/\ i_ i xy.1, i_ i xy.2, xy.1 <= xy.2 &
    (`|f xy.1 - f xy.2|%:E > oscillation f (i_ i) - (e / n%:R)%:E)%E].
  move=> i.
  apply: oscillation_ub => //.
  - exact/altb.
  - apply: continuous_subspaceW cf.
    rewrite /a_.
    rewrite anth.
    rewrite /b_.
    rewrite bnth.
    have [H1 H2 H3] := nth_abE A B b (ltn_ord i).
    rewrite H1 H2.
    exact: Iab.
  - rewrite divr_gt0//.
    by near: n; exact: nbhs_infty_gtr.
move/choice => [xy Hxy].
(*have [idx1 [idx_idx1 idx12K idx21K]] := idx_bij A B n.
rewrite (_ : (\sum_(0 <= i < n) oscillation f (I i))%R =
             (\sum_(0 <= i < n) oscillation f (i_ (idx1.1 i)))%R).*)
pose s := map (fun k =>
  if k == 0 then a else
  if k == n then b else
  if odd k then (a_ n (k.+1./2)) else
                (b_ n (k./2))) (iota 0 n).
rewrite -leeBlDr//.
rewrite (@le_trans _ _ (\sum_(i < n) `|f (xy i).1 - f (xy i).2|%:E))//.
  rewrite [leLHS](_ : _ =
      (\sum_(i < n) (oscillation f (I i) - (e / n%:R)%:E)))%E.
    rewrite big_mkord.
    rewrite big_split/=.
    admit.
  apply: lee_sum => /= k _.
  have [_ _ /=] := Hxy k.
  (*by move/ltW.*) admit.
(*pose s0 (i : nat) : R := if ~~ odd i then (xy i).1 else (xy i).2.
pose d := a :: rcons s0 b.*)
rewrite /total_variation.
rewrite (@le_trans _ _ (variation a b f s)%:E)//.
  rewrite /variation/= size_map size_iota !sumEFin lee_fin.
  rewrite big_mkord.
(*  apply: ler_sum => /= i _.*)
  admit.
apply: variation_le_total_variation.
rewrite /itv_partition; split.
  rewrite /s.
  admit.
admit.
Admitted.

Lemma mesh_mem_filter (a b c d : R) (s : seq R) :
  a <= c -> d <= b ->
  mesh c d [seq x <- s | x \in `[c, d]] <= mesh a b s.
Proof.
Abort.

Lemma mesh_filter (a b : R) (s : seq R) (P : pred R) :
  mesh a b [seq x <- s | P x] <= mesh a b s.
Proof.
Abort.

(* deprecating sorted_map *)
Lemma sort_sorted_fst {T1 T2 : eqType} (le1 : rel T1)
  (p : seq (T1 * T2)) :
  transitive le1 ->
  let le12 := (fun x y : T1 * T2 => le1 x.1 y.1) in
  sorted le12 p <-> sorted le1 [seq i.1 | i <- p].
Proof.
Abort.

(* map_rcons *)
Lemma rcons_fst {T : Type} (s : seq (T * T)) (x : T * T) :
  unzip1 (rcons s x) = rcons (unzip1 s) x.1.
Proof.
by move: s x; elim => // s1 s2 + s3/= => ->.
Abort.

(* duplicate map_rcons *)
Lemma rcons_snd {T : Type} (s : seq (T * T)) (x : T * T) :
  unzip2 (rcons s x) = rcons (unzip2 s) x.2.
Proof.
by move: s x; elim => // s1 s2 + s3/= => ->.
Abort.

(* duplicate map_rcons *)
Lemma rcons_snd_iota {T : nzSemiRingType} (s : seq (T * T)) (x : T * T) m :
  [seq ((rcons s x)`_i).2 | i <- iota 0 m.+1] =
  rcons [seq (s`_i).2 | i <- iota 0 m] (x.2).
Proof.
Abort.

(* duplicate map_rcons *)
Lemma sort_sorted_snd' (p : seq (R * R)) n :
  let le1 := (fun x y : R * R => x.1 <= y.1) in
  size p = n.+1 ->
  sorted le1 p ->
  (forall i, (p`_i).1 < (p`_i).2) ->
  ((forall i j, `](p`_i).1, (p`_i).2[ `&` `](p`_j).1, (p`_j).2[ = set0) ->
    sorted <=%R [seq (p`_i).2 | i <- iota 0 n.+1] /\
      (forall i, (i < n)%N -> (p`_i).2 <= (p`_i.+1).1)).
Proof.
move=> le1.
move: p; elim: n => // m IHn.
apply: last_ind => // p1 p2 _.
rewrite size_rcons; move/eq_add_S.
move=> pn sp ltp disjp.
have p21m : ((rcons p1 p2)`_m).2 <= ((rcons p1 p2)`_m.+1).1.
  admit.
split.
Abort.

(* duplicate get_subset1? *)
Lemma is_subset1_set1 (A : set R) :
  A !=set0 -> is_subset1 A -> exists x, A = [set x].
Proof.
move=> [x Ax] A1; exists x; apply/seteqP; split => [|y ->//].
by move=> y Ay; exact: A1.
Abort.

(* duplicate nth_map? *)
Lemma snd_map {T1 T2} (l : seq (T1 * T2)) d1 d2 i :
 (i < size l)%N ->
  (nth (d1, d2) l i).2 = nth d2 (map snd l) i.
Proof. by move=> ?; rewrite (nth_map (d1, d2)). Qed.

(* *)
Lemma nth_set (P : set R) (l : seq R) i : (i < size l)%N ->
  [set` l] `<=` P -> P (nth 0 l i).
Proof.
move=> li lA.
by have /lA := mem_nth 0 li.
Abort.

Lemma subset_neitvE (a b c d : R) : a < b ->
  `]a, b[ `<=` `[c, d] ->
c <= a /\ b <= d.
Proof.
(*
have [clea bled]: (forall n i, c <= a_ n i) /\ (forall n i, b_ n i <= d).
  apply/all_and2 => n; apply/all_and2 => i.
  have [ni|] := leqP n.+1 i.
    by rewrite /a_ /b_ !nth_default ?size_seq//; split => //; apply: ltW.
  move/(nth_abE n i) => [+ + _].
  rewrite -anth -bnth -idxE => -> ->.
  have ABcd : `]A_ (idx n i), B_ (idx n i)[ `<=` `[c, d].
    rewrite -compact_Rhull// -contiguous_ooitv//.
    apply: (subset_trans (@contiguous_intervalsS _ _ _)).
    exact: cplt_hull_subset_Rhull.
  split.
    rewrite leNgt; apply/negP => Ac.
    set x := ((A_ (idx n i)) + minr (B_ (idx n i)) c) / 2.
    have : x < c.
      rewrite /x [in ltRHS](splitr c) mulrDl ltr_leD// ?ltr_pM2r ?ler_pM2r//.
      by rewrite /minr; case: ifP => //; apply: ltW.
    apply/negP; rewrite -leNgt.
    have : x \in `]A_ (idx n i), B_ (idx n i)[.
      rewrite in_itv/=; apply/andP; split.
        by rewrite midf_lt// /minr; case: ifP.
      rewrite (splitr (B_ _)) /x mulrDl ltr_leD// ?ltr_pM2r ?ler_pM2r//.
      by rewrite /minr; case: ifPn => //; rewrite -leNgt.
    move/(ABcd x) => /=.
    by rewrite in_itv/= => /andP[].
  rewrite leNgt; apply/negP => Bd.
    set y := (maxr (A_ (idx n i)) d + B_ (idx n i)) / 2.
    have : d < y.
      rewrite /y [in ltLHS](splitr d) mulrDl ler_ltD// ?ltr_pM2r ?ler_pM2r//.
      by rewrite /maxr; case: ifPn => //; rewrite -leNgt.
    apply/negP; rewrite -leNgt.
    have : y \in `]A_ (idx n i), B_ (idx n i)[.
      rewrite in_itv/=; apply/andP; split.
        rewrite (splitr (A_ _)) /y mulrDl ler_ltD// ?ltr_pM2r ?ler_pM2r//.
        by rewrite /maxr; case: ifPn => //; apply: ltW.
      by rewrite midf_lt// /maxr; case: ifP.
    move/(ABcd y) => /=.
    by rewrite in_itv/= => /andP[].
*)
Abort.

End lemmas.

Section mesh_lemmas.
Context {R : realType}.
Implicit Types (a b : R) (f : R -> R).
Implicit Types (s : seq R) (x : R).

Lemma mesh_eq_merge_subseq a b s t :
  path <=%R a s -> path <=%R a t ->
  subseq t s ->
  mesh a b (merge <=%R s t) = mesh a b s.
Proof.
elim: t s => //=.
  move=> pas _ _.
  by rewrite merge0r.
move=> h t IH s pas /andP[ah pht] subhts.
rewrite merge_cons_mergel.
- exact: le_trans.
- exact: le_path_min.
rewrite IH.
- apply: merge_path => //.
  by rewrite /= ah.
- apply: (path_le _ ah) => //; exact: le_trans.
- apply: (@subseq_trans _ s); last exact: subseq_mergel.
  apply: subseq_trans subhts.
  exact: subseq_cons.
rewrite /mesh.
rewrite size_merge.
have hs : h \in s.
  have /mem_subseq/subsetP := subhts.
(*  move/(_ h); rewrite 2!inE; apply.
  exact: mem_head.
set n := index h (s ++ [:: h]).
have : (n <= size (s ++ [:: h]))%N.
  by rewrite index_size.
rewrite size_cat/= addn1 => ns.*)
(* needs Monoid instance! *)
(* have : (\big[@Num.max {nonneg R}/_]_(0 <= n0 < (size s).+1)
      widen_itv `|nth b (merge <=%R s [:: h]) n0 - nth b (a :: merge <=%R s [:: h]) n0|%:itv)%:num = a.
rewrite big_cat_nat.
have := (@big_cat_nat {nonneg R} (0%:nng) (@maxr {nonneg R})). (leq0n n) ns).
*)
Abort.

Lemma path_merge_ltW a b (s t : seq R) :
  path <=%R a s -> subseq t s ->
  mesh a b s = mesh a b (merge <=%R s t).
Proof.
Abort.

Lemma mesh_merge1_le a b s x :
  path <%R a s -> a <= x <= b -> last a s == b ->
  mesh a b (merge <%R s [:: x]) <= mesh a b s.
Proof.
move=> ps /eqP sb.
have [xs|xs] := boolP (x \in s).
  (* rewrite itv_partition_max_merge_subseq. *)
  admit.
(*
apply: subseq_itv_partition_max.
have itv_partition_max_merge :
*)
Abort.

Lemma mesh_merge1' a b l s x :
  path <=%R a s -> last a s == b ->
  mesh a b s <= l ->
  mesh a b (merge <=%R s [:: x]) <= l.
Proof.
elim: s => //.
  move=> ? /=.
  rewrite /mesh/=.
  rewrite big_nat_recl// big_nil/=.
rewrite /mesh /=.
Abort.

Lemma mesh_merge a b l s t :
  mesh a b s <= l ->
  mesh a b (merge <=%R s t) <= l.
Proof.
Abort.

End mesh_lemmas.

Section adjacent_pairs.
Context {T : Type}.
Implicit Types (s : seq T).

Definition adjacent_pairs (s : seq T) := zip s (behead s).

Lemma adjacent_pairs_nil : adjacent_pairs [::] = [::].
Proof. by []. Qed.

Lemma adjacent_pairs_seq1 (x : T) : adjacent_pairs [:: x] = [::].
Proof. by []. Qed.

Lemma adjacent_pairs_cons (x y : T) s :
  adjacent_pairs (x :: y :: s) = (x, y) :: adjacent_pairs (y :: s).
Proof. by []. Qed.

Lemma adjacent_pairs_rcons (x y : T) s :
  adjacent_pairs (rcons (rcons s x) y) =
    rcons (adjacent_pairs (rcons s x)) (x, y).
Proof.
elim/last_ind : s x y => //= s0 s1 IH x y.
rewrite IH.
Abort.

End adjacent_pairs.

(* generalize *)
Lemma filter_ocitv_cat {R : realType}
    (b a c : R) (t : seq R) :
  (a <= b)%O ->
  (b <= c)%O ->
  sorted <=%O t ->
  [seq x <- t | (a < x <= c)%O]
  =
  [seq x <- t | (a < x <= b)%O] ++
  [seq x <- t | (b < x <= c)%O].
Proof.
elim: t b => // t0 t1 IH b ab bc st/=.
case: ifP; last first.
  move/negP/negP; rewrite negb_and -!leNgt => /orP[at0|t0c].
    rewrite !ifF//.
    - admit.
    - admit.
    apply: IH => //.
    admit.
  rewrite !ifF//.
  - admit.
  - admit.
  apply: IH => //.
  admit.
move=> /andP[at0 t0c].
have [t0b|bt0]/= := leP t0 b.
  rewrite at0 (IH b)//.
  admit.
rewrite andbF t0c (IH b)//.
  admit.
suff -> : [seq x <- t1 | a < x & x <= b] = [::] by rewrite cat0s.
apply: size0nil.
apply/eqP; rewrite -leqn0 leqNgt size_filter_gt0.
apply/hasPn => x xt1.
rewrite negb_and -ltNge; apply/orP; right.
apply: (lt_le_trans bt0).
by have/le_path_min/allP := st; apply.
Admitted.

Section split_seq.

Definition split_seq d {T : porderType d} (s t : seq T) : seq (seq T) :=
  [seq [seq x <- t | (p.1 < x <= p.2)%O]
   | p <- adjacent_pairs s].

Lemma split_0seq d {T : porderType d} (t : seq T) :
  split_seq [::] t = [::].
Proof. by []. Qed.

Lemma split_1seq d {T : porderType d} x (t : seq T) :
  split_seq [:: x] t = [::].
Proof. by []. Qed.

Lemma split_seq0 d {T : porderType d} (s : seq T) :
  split_seq s [::] = [::].
Proof.
rewrite /split_seq.
Abort.

Lemma split_seq_cons d {T : porderType d}
    (x y : T) (s t : seq T) :
  split_seq (x :: y :: s) t =
    [seq z <- t | (x < z <= y)%O] ::
    split_seq (y :: s) t.
Proof.
Admitted.

(* generalize *)
Lemma flatten_split_seq {R : realType}
    (x : R) (s t : seq R) :
  sorted <=%O (x :: s) ->
  sorted <=%O t ->
  flatten (split_seq (x :: s) t) =
    [seq y <- t | (x < y <= last x s)%O].
Proof.
elim: s x.
  move=> x _ st.
  rewrite /=; apply/esym.
  apply: size0nil.
  apply/eqP; rewrite -leqn0 leqNgt size_filter_gt0.
  apply/hasPn => y ty.
  by rewrite negb_and -ltNge orb_negb_l.
move=> s0; elim.
  by move=> ?//= ? ? _; rewrite cats0.
move=> s1 s2 IH0 IH1 x sorted_s sorted_t.
rewrite split_seq_cons -cat1s flatten_cat.
rewrite IH1//.
  by have/andP[] := sorted_s.
rewrite /= cats0.
rewrite -filter_ocitv_cat//.
  by have/andP[] := sorted_s.
have := sorted_s.
rewrite (lock (s1 :: s2))/= le_path_sortedE; unlock.
move/and3P => [_ /allP + _]; apply.
exact: mem_last.
Qed.

(* generalize *)
Lemma split_seqK {R : realType} (s t : seq R) (d0 d1 : R) :
  s != [::] ->
  sorted <=%O s ->
  sorted <=%O t ->
  (head d0 s < head d0 t)%O ->
  (last d1 t <= last d1 s)%O ->
  t = flatten (split_seq s t).
Proof.
case: s => // s0 s1 _.
elim/last_ind : s1 => //=.
  move=> _.
  elim: t => // t0 t1 IH/=.
  rewrite le_path_sortedE => /andP[/allP t0t1 _].
  move/lt_le_trans => H.
  have : (t0 <= last t0 t1)%O.
    elim/last_ind : t1 IH t0t1 => // t1 t2 IH0 IH1; apply.
    by rewrite last_rcons mem_rcons mem_head.
  by move/le_trans => H' /H' /H; rewrite ltxx.
move=> s1 s2 _.

  rewrite last_nil.
Lemma split_seqK d {T : orderType d} (s t : seq T) (d0 d1 : T) :
  s != [::] ->
  sorted <=%O s ->
  sorted <=%O t ->
  (head d0 s < head d0 t)%O ->
  (last d1 t <= last d1 s)%O ->
  t = flatten (split_seq s t).
Proof.
Abort.

End split_seq.


Section subdivision_of_itv_partition.
Context {R : realType}.
Implicit Types (a b : R) (s : seq R).
Implicit Type (f : R -> R).

Definition split_seq d {T : porderType d} (s t : seq T) :
  [seq [seq t0 <- t | (s0 < t <= s1)%O] | s1 = next s s0].

Lemma subseq_variationE a b f (s t : seq R) :
  itv_partition a b t ->
  subseq s t ->
let nths := nth b (a :: s ++ [:: b]) in
  variation a b f t =
    \sum_(i < (size s).+1)
       variation a b f [seq y <- t | nths i < y <= nths i.+1].
Proof.

Admitted.

Definition itvs_of_seq (df : R) s :=
let nths := nth df s in
  [seq (nths n.+1, nths n) | n <- iota 0 (size s).+1].

Lemma variation_seq1 (c : R) a b f :
  variation a b f [:: c] = `|f c - f a|.
Proof. by rewrite /variation/= big_nat1/=. Qed.

Lemma variation_subdivition a b f s (ps : itv_partition a b s) :
  variation a b f s =
    \sum_(sdiv <- subdivition_of_itv_partition a b s ps)
   variation sdiv.1 sdiv.2 f [:: sdiv.2].

End subdivision_of_itv_partition.
*)

Section preliminaries.
Context {R : realType}.

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

Lemma size_lambda_partition0 (a b l : R) :
  a < b -> 0 < l ->
  (0 < size (lp a b l))%N.
Proof.
move=> ab l0; by rewrite size_map size_iota lambda_partition_size0_tmp.
Qed.

Lemma lambda_partition_mesh (a b l : R) :
  a < b -> 0 < l ->
   mesh a b (lp a b l) < l.
Proof.
move=> ab l0.
rewrite /mesh.

have : forall n : nat, (0 <= n < (truncn ((b - a) / l)).+1)%N ->
 `|nth b (a :: lp a b l) n.+1 - nth b (a :: lp a b l) n|%:nng < NngNum (ltW l0).
  move=> n /andP[_ nl]; rewrite -num_lt/=.
  rewrite /lp nth_map_iota//.
  case: n nl.
    move=> _ /=.
    rewrite mulr1 addrAC subrr add0r ger0_norm.
      by rewrite mulr_ge0// subr_ge0 ltW.
    rewrite ltr_pdivrMr// mulrC -ltr_pdivrMr//.
    exact: truncnS_gt.
  move=> n.
  rewrite ltnS => nbal.
  rewrite [X in _ - X]
      (_: _ = a + (b - a) * n.+1%:R / (truncn ((b - a) / l)).+1%:R).
    transitivity (nth b
    ([seq a + (b - a) * i.+1%:R /
     (truncn ((b - a) / l)).+1%:R | i <- iota 0 (truncn ((b - a) / l)).+1])
    n).
      done.
    rewrite nth_map_iota//.
    by rewrite ltnW// ltnS.
  rewrite opprD addrACA subrr add0r.
  rewrite -nat1r mulrDr mulrDl addrK mulr1.
  rewrite ger0_norm.
    by rewrite mulr_ge0// subr_ge0 ltW.
  rewrite ltr_pdivrMr// mulrC -ltr_pdivrMr//.
  exact: truncnS_gt.
have l0_nng : 0%:nng < NngNum (ltW l0).
  by rewrite -num_lt.
move/(bigmax_lt (iota 0 (size (lp a b l))) l0_nng).
rewrite -num_lt//.
apply: le_lt_trans.
rewrite num_le.
rewrite big_nat_cond.
apply: sub_bigmax.
move=> n; rewrite andbT => /andP[-> ]/leq_trans; apply.
by rewrite size_map size_iota.
Qed.

Lemma last_lambda (a b l x : R) :
  a < b -> 0 < l ->
  last x (lp a b l) = b.
Proof.
move=> ab l0.
rewrite (last_nth b).
rewrite -(@prednK (size _))//.
rewrite /lp (lock (iota 0))/=; unlock; rewrite nth_map_iota.
  by rewrite size_map size_iota.
by rewrite size_map size_iota/= -mulrA divff// mulr1 addrCA subrr addr0.
Qed.

Lemma lambda_partition_partition (a b l : R) :
  a < b -> 0 < l ->
  itv_partition a b (lp a b l).
Proof.
move=> ab l0.
split; last by rewrite last_lambda.

Admitted.


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
      rewrite -ereal_inf_EFin.
      - by exists 0 => _ [n _ <-]; rewrite invr_ge0.
      - by exists 1; exists 0 => //; rewrite invr1.
        have : {homo (fun n : nat => (n.+1%:R^-1)%:E : \bar R) :
                                     n m / (n <= m)%N >-> (m <= n)%E}.
          apply/nonincreasing_seqP => n.
          rewrite lee_fin.
          rewrite lef_pV2 ?posrE//.
          by rewrite ler_nat.
        rewrite image_comp.
        move/ereal_nonincreasing_cvgn/cvg_lim <- => //.
        rewrite le_eqVlt; apply/predU1P; left.
        apply: cvg_lim => //.
        apply/cvg_EFin.
          by apply: nearW => n.
        exact: cvg_harmonic.
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
      case: n => // n _; first by rewrite invr1 in n.
      apply/negP; rewrite /ball/= -leNgt.
      rewrite ler_normr; apply/orP; left.
      rewrite lerB//.
      rewrite ler_pdivlMr//.
(*      rewrite exprSr divfK//.
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
*)
Abort.

End checking.

End limit_point_closed.

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
Abort.

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
(*  have := nonempty_open_interval_not_subset1 In0 (@open_disjoint_itv_open _ _ oU n) (@open_disjoint_itv_is_interval _ _ oU n).
  move/existsNP => [x0 /existsNP[x1] /not_implyP[Inx0] /not_implyP[Inx1]].
  move/eqP.
  rewrite eq_le.
  move/nandP.
  rewrite -2!ltNge => -[x10|x01].*)
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
  have [x xx01 fxz] : exists2 x : R, x \in `[x0, x1] & f x = z.
    apply: IVT => //.
      apply: continuous_subspaceW cf.
      by apply: subset_trans abD; apply: subset_itv;
        rewrite bnd_simp ?(itvP x0ab) ?(itvP x1ab).
    by rewrite ge_min le_max fx0z/= zfx1 orbT.
  exists x => //.
  by apply: subset_itv xx01; rewrite bnd_simp ?(itvP x0ab) ?(itvP x1ab).
have [x xx01 fxz] : exists2 x : R, x \in `[x1, x0] & f x = z.
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

Lemma diam_Rhull (A : set R) : diam [set` Rhull A] = diam A.
Proof.
rewrite /diam.
Admitted.

Lemma diam_closure (A : set R) : diam (closure A) = diam A.
Proof.
have [->|A0] := eqVneq A set0.
  by rewrite closure0.
rewrite -diam_Rhull -(diam_Rhull A).
Abort.

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

(* unnecessary? *)
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

Lemma diam_s t : seq (set R)) :
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

(*
Section oscillation_measure.
Context {R : realType}.

Variable (f : R -> R).
Definition osc_mu (g : R -> R) := (oscillation g).

Lemma osc_mu0 : osc_mu f set0 = 0.
Proof. by rewrite /osc_mu oscillation0. Qed.

Lemma osc_mu_ge0 A : (0 <= osc_mu f A)%E.
Proof. by rewrite oscillation_ge0. Qed.

Lemma le_osc_mu A B : A `<=` B -> (osc_mu f A <= osc_mu f B)%E.
Proof. exact: oscillation_sub. Qed.

(* oscillation_subadditive2? *)
Lemma osc_mu_subadditive2 A B :
   {within A `|` B, continuous f} -> 
   (osc_mu f (A `|` B) <= osc_mu f A + osc_mu f B)%E.
Proof.
move=> cf.
have := derive.EVT_max cf.

Lemma osc_mu_sigma_subadditive : sigma_subadditive (osc_mu f).
Proof.
move=> A.
rewrite seqDU_bigcup_eq.
Admitted.
*)

Section interleave.

(*
Definition interleave {R : realType} (a b : R) (s t : seq R)
  (ps : itv_partition a b s) (pt : itv_partition a b t)
  (st : forall n, nth b s n <= nth b t n <= nth b s n.+1)
:=
  merge <=%R s t.
*)

Definition seq_of_pair {T} (s : seq (T * T)) : seq (seq T) :=
  [seq [:: ab.1; ab.2] | ab <- s].

Definition intlv {T} (s t : seq T) :=
    flatten (seq_of_pair (zip s t)).

Lemma shape_pairs {T} (s : seq (T * T)) :
  shape (seq_of_pair s) = nseq (size s) 2.
Proof. by elim: s => [|[x y] s IH] //=; rewrite IH. Abort.

Lemma size_intlv {T} (s t : seq T) :
   size (intlv s t) = 2 * size (zip s t).
Proof.
(*
by rewrite size_flatten shape_pairs sumn_nseq.
*)Abort.

Lemma intlv_cons {T} (x y : T) (s t : seq T) :
  intlv (x :: s) (y :: t) = x :: y :: intlv s t.
Proof. by elim: s t. Abort.

Lemma subseq_intlvr {T : eqType} (s t : seq T) :
  (size s <= size t)%N ->
   subseq s (intlv s t).
Proof.
elim: s t.
  by move=> ? _; apply: sub0seq.
move=> s0 s1 IHs.
case => // t0 t1.
rewrite [X in X -> _]/= ltnS => st.
(* rewrite intlv_cons. *)
Abort.

Lemma interleave_merge {R : realType} (s t : seq R) :
  size s = size t ->
  sorted <=%R (intlv s t) ->
  intlv s t = merge <=%R s t.
Proof.
move=> st sintlv.
Abort.

End interleave.

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

Definition contiguous_intervals12 (A : set R) :
  nat -> (R * R) :=
  fun n => (contiguous_intervals1 A n, contiguous_intervals2 A n).


Lemma Ritv_open_bounded (b0 b1 : bool) (x y : R) :
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

Lemma Ritv_open_lray (b0 : bool) (x : R) :
  open [set` (Interval (BSide b0 x) (BInfty _ false))] = ~~ b0.
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

Lemma Ritv_open_rray (b1 : bool) (y : R) :
  open [set` (Interval (BInfty _ true) (BSide b1 y))] = b1.
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

Lemma not_bounded_set_lray (b0 : bool) (r : R) :
   ~ bounded_set [set` (Interval (BSide b0 r) (BInfty _ false))].
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

Lemma not_bounded_set_rray (b0 : bool) (r : R) :
   ~ bounded_set [set` (Interval (BInfty _ true) (BSide b0 r))].
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

Lemma not_bounded_setT : ~ (bounded_set (@setT R)).
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

Lemma nonempty_bounded_Rooitv (i : interval R) :
  [set` i] !=set0 -> open [set` i] -> bounded_set [set` i] ->
  exists a b : R, a < b /\ i = `]a, b[.
Proof.
case: i.
move=> [[l|l]|[]][[r|r]|[]];
  rewrite ?Ritv_open_bounded ?Ritv_open_lray ?Ritv_open_rray//=; last 10 first.
- move/[swap] => rl.
  by move/set0P; rewrite set_itv_ge ?eqxx// bnd_simp -leNgt.
- by rewrite set_itvE; move/set0P; rewrite eqxx.
- by move=> _ _ /not_bounded_set_lray.
- by move=> _ _ /not_bounded_set_rray.
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

Lemma nonempty_open_Rinterval_is_not_subset1 (i : interval R) :
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
(*
move=> oi.
have [bi|] := pselect (bounded_set [set` i]).
  move/nonempty_bounded_Rooitv /(_ oi bi) => [il [ir [ilr ->]]].
  move/(_ ((il *+ 2 + ir) / 3) ((il + ir *+ 2) / 3)).
  apply/not_implyP; split; [|apply/not_implyP; split].
  - admit.
  - admit.
  admit.
*)
Qed.

Lemma compact_mem_sup (A : set R) : compact A -> A (sup A).
Proof.
rewrite Rcompact_boundE => -[cA ubA _].
Abort.

Lemma compact_mem_inf (A : set R) : compact A -> A (inf A).
Proof.
Abort.

(*
Lemma lebesgue_measure_eq_itv_bnd (A : set R) (x y : R)
 (b0 b1 : bool) :
  (x <= y) ->
  A = [set` Interval (BSide b0 x) (BSide b1 y)] ->
  (lebesgue_measure A = (y - x)%:E)%E.
Proof.
rewrite le_eqVlt => /predU1P[->|].
  move=> ->; rewrite subrr.
  case: b0; case: b1; rewrite ?set_itvoo0 ?set_itvoc0 ?set_itvco0 ?measure0//.
  by rewrite set_itv1 lebesgue_measure_set1.
move=> xy ->.
by case: b0; case: b1; rewrite lebesgue_measure_itv lte_fin xy.
Qed.
*)

From mathcomp Require Import esum.

Lemma completed_lebesgue_measure_eq_itv (A : set R) (x y : itv_bound R) :
  (x < y)%E ->
  A = [set` Interval x y] ->
  (mu A = ereal_of_itv_bound y - ereal_of_itv_bound x)%E.
Proof.
by move=> xy ->; rewrite completed_lebesgue_measure_itv xy.
Qed.

Lemma zip_nthE {A B : Type} (dx : A) (dy : B)
    (xs : seq A) (ys : seq B) :
  size xs = size ys ->
  [seq (nth dx xs i, nth dy ys i) | i <- iota 0 (size xs)] = zip xs ys.
Proof.
move=> xy.
apply: (@eq_from_nth _ (dx, dy)).
  by rewrite size_map size_iota size_zip xy minnn.
move=> j; rewrite size_map size_iota => Hj.
rewrite (nth_map 0%N); first by rewrite size_iota.
by rewrite nth_iota // add0n nth_zip.
Qed.

Lemma map_unzip_nth {A B C : Type} (da : A) (db : B)
    (F : A -> B -> C) (s : seq (A * B)) :
  [seq F (nth da (unzip1 s) i) (nth db (unzip2 s) i)
     | i <- iota 0 (size s)]
  = [seq F p.1 p.2 | p <- s].
Proof.
rewrite -[in RHS](zip_unzip s) -(zip_nthE da db); first by rewrite !size_map.
by rewrite -map_comp size_map.
Qed.

Import MeasurableR.

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
move: (cZ); rewrite Rcompact_boundE => -[clZ ubZ lbZ].
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
  by apply/perfectP; split.
have Z_nonempty : Z !=set0.
  apply/set0P; apply/negP => /eqP Z0'.
  by move: HZ; rewrite Z0' image_set0 measure0 ltxx.
have closedZ : closed Z by exact: compact_closed cZ.
pose supp := contiguous_intervals_support Z.
have infsupp := contiguous_infinite Zab cZ Z_nonempty Z0 perfectZ.
have countsupp : countable supp by exact: subset_card_le.
have /ppcard_eqP[/= h] := eq_card_nat countsupp infsupp.
pose h1 : {splitbij [set: nat] >-> supp} := h^-1%FUN.
have h1h : {in supp, cancel h h1} by exact: funK.
have hh1 : cancel h1 h by move=> x; apply: invK; rewrite inE.
have ne_cgitvs n : contiguous_intervals Z (h1 n) !=set0.
  have : supp (h1 n).
    have := @bij _ _ _ _ h1.
    by move=> [+ _ _]; exact.
  by rewrite /supp/contiguous_intervals_support/=.
pose A_ n := contiguous_intervals1 Z (h1 n).
pose B_ n := contiguous_intervals2 Z (h1 n).
have AB n : A_ n < B_ n.
  have : contiguous_intervals_support Z (h1 n).
  have := @bij _ _ _ _ h1.
  move=> [].
  by move/(_ n I).
  move=> [x].
  rewrite contiguous_ooitv//= in_itv/= => /andP[Ax xB].
  exact: lt_trans Ax xB.
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
pose ABi_ := ABi_ A_ B_.
pose abi_ := abi_ A_ B_.
pose seq_a := seq_a A_ B_.
pose seq_b := seq_b A_ B_.
pose idxs := idxs A_ B_.
pose a_ := a_ A_ B_ d.
pose b_ := b_ A_ B_ d.
pose idx := idx A_ B_.
have lbZa : lbound Z a by move=> r /Zab /itvP ->.
have ubZb : ubound Z b by move=> r /Zab /itvP ->.
pose cd_ := cd_ A_ B_ c d.
pose seq_c := seq_c A_ B_ c d.
pose seq_d := seq_d A_ B_ c d.
pose c_ := c_ A_ B_ c d.
pose d_ := d_ A_ B_ c d.
(* for non-increasingness of lambda
have cdS_split n j : exists k, [/\ (k < n.+1)%N,
  c_ n.+1 k \in `[B_ (idx n k), (A_ (idx n k.+1))],
  d_ n.+1 k \in `[B_ (idx n k), (A_ (idx n k.+1))] &
  cd_ n.+1 = take k (cd_ n) ++
   [:: (B_ n.+1, A_ n.+1)] ++
   drop k (cd_ n)].
  admit.
*)
pose lambda n := diam_max [seq `[c_ n i, d_ n i]%classic | i <- iota 0 n.+1].
have lambda_fin n : lambda n \is a fin_num.
  rewrite ge0_fin_numE; first exact: diam_max_ge0.
  rewrite /lambda /diam_max big_seq_cond; apply: bigmax_lt; first by [].
  move=> s; rewrite andbT.
  move/mapP => [i].
  rewrite mem_iota add0n => /andP[_ iltn2 ->].
  by rewrite diam_itv ?ltry ?cled.
have lambda_ge0 n : (0 <= lambda n)%E.
  exact: diam_max_ge0.
have mcgitv i : mu.-cara.-measurable (contiguous_intervals Z i).
  move=> k; apply: sub_caratheodory.
  rewrite RGenOpenSets.measurableE.
  apply: open_measurable.
  exact: open_contiguous_intervals.
have lambda0 : (fine \o lambda) @ \oo --> 0%R.
  apply: fine_cvg.
  apply (@squeeze_cvge _ _ _ R (cst 0) _
    (fun n => \sum_(i < n.+1) mu `[c_ n i, d_ n i])).
  - near=> n; apply/andP; split; first exact: lambda_ge0.
      rewrite /lambda /diam_max big_tuple.
      apply: bigmax_le.
      exact: leNye.
    move=> /= i _.
    rewrite tnth_map (tnth_nth 0) nth_iota// add0n.
    rewrite diam_itv; first exact: cled.
    rewrite (bigD1 i)//=.
    have -> : mu `[c_ n i, d_ n i] = (d_ n i - c_ n i)%:E.
      rewrite completed_lebesgue_measure_itv lte_fin.
      have [_|] := ltP (c_ n i) (d_ n i).
        by rewrite /= -EFinB.
      rewrite le_eqVlt; move/predU1P => [->|].
        by rewrite subrr.
      by rewrite ltNge cled.
    apply: leeDl.
    by rewrite sume_ge0.
  - exact: cvg_cst.
  - apply: (@cvg_trans _
      (mu (\bigcap_(i < n) ([set` Rhull Z] `\` (contiguous_intervals Z (h1 i))))
        @[n --> \oo])).
    apply: near_eq_cvg.
    near=> n.
    have n0 : (0 < n)%N.
      by near: n; exact: nbhs_infty_gt.
    destruct n => //.
    transitivity (mu (\bigcup_(i < n.+2) `[c_ n.+1 i, d_ n.+1 i]%classic)).
      congr mu.
      rewrite -setD_bigcupr; first by exists 0.
      rewrite (hullZ_abcd lbZ ubZ n.+1 cd cZ Z_nonempty AB)//.
      rewrite setDUD.
      have -> : \bigcup_(i < n.+1) `]a_ n.+1 i, b_ n.+1 i[%classic
        `\` \bigcup_(i < n.+1) contiguous_intervals Z (h1 i) = set0.
        rewrite eqEsubset; split => // x/=.
        apply/not_implyP; apply.
        move=> [i/= iltn1].
        rewrite /a_ anth /b_ bnth.
        have [-> -> idxltn1] := nth_abE A_ B_ d iltn1.
        rewrite -!idxE => xAB.
        exists (idx n.+1 i) => //=.
          rewrite /idx (idxE A_ B_ d).
          by rewrite (leq_trans idxltn1)//.
        by rewrite contiguous_ooitv.
      rewrite setU0.
      apply: setDidl.
      by apply: disj_abcd.
    rewrite bigcup_mkord.
    rewrite completed_lebesgue_measureE.
    rewrite measure_semi_additive_ord//=.
      (* lemma? *)
      case => i iltn2.
      case => j jltn2 _ _/=.
      move=> [x/= [xi xj]]/=.
      rewrite -(inord_val (Ordinal _))/=.
      rewrite -(inord_val (Ordinal _))/=.
      apply: ord_inj; rewrite !inordK//.
      apply/eqP/not_notP => /negP => ij.
      wlog : i j iltn2 jltn2 x xi xj ij / (i < j)%N.
        move=> H.
        move: (ij); rewrite neq_ltn => /orP[iltj|jlti].
          exact: (H i j _ _ x).
        apply: (H j i _ _ x) => //.
        by rewrite eq_sym.
      move=> {}ij.
      move: xi xj.
      rewrite !in_itv/= => /andP[_ +] /andP[+ _].
      move/[swap]/le_trans => H /H {H}.
      apply/negP; rewrite -ltNge.
      rewrite /d_ daE /c_ cbE.
      case: j jltn2 ij => //=j.
      rewrite !ltnS => jn ij.
      apply: (@le_lt_trans _ _ (a_ n.+1 j)).
        rewrite le_sorted_leq_nth// ?sorted_a// inE size_seq_ab//.
        by rewrite (leq_ltn_trans ij).
      rewrite /a_ anth /b_ bnth.
      have [] := @nth_abE R A_ B_ d n.+1 j; first by [].
      by move=> -> ->.
    exact: bigsetU_measurable.
  have <- : mu (\bigcap_n ([set` Rhull Z] `\` (contiguous_intervals Z (h1 n)))) = 0%:E.
    rewrite -setD_bigcupr//.
    have [funh1 injh1 surjh1] := @bij _ _ _ _ h1.
    rewrite -(reindex_bigcup _ _ _ _ funh1 surjh1).
    rewrite -bigcup_contiguous_intervals_support.
    rewrite -bigcup_contiguous_intervals//.
    rewrite setDD.
    rewrite setIidr; first exact: sub_Rhull.
    exact: Z0.
  apply: cvg_measure_bigcap_new_new => /=; last 2 first.
      by move=> ?; apply: measurableD => //; exact: sub_caratheodory.
    apply: bigcap_measurable => // ? _; apply: measurableD => //.
    exact: sub_caratheodory.
  apply: (@le_lt_trans _ _ (mu [set` Rhull Z])).
    apply: le_outer_measure.
    exact: subDsetl.
  rewrite compact_Rhull//.
  rewrite completed_lebesgue_measure_itv//= lte_fin.
  rewrite cd.
  by rewrite -EFinB ltry.
have construct_x n :
  exists x : seq R, [/\ itv_partition c d (behead x),
    ((mesh c d (behead x))%:E <= lambda n)%E,
    (forall i : 'I_ n.+1, c_ n i \in x /\ d_ n i \in x),
    (n <= size x)%N &
    (forall (i j : 'I_ n.+1), nth d x j \notin `]c_ n i, d_ n i[) ].
  (* use lambda_partition *)
  admit.
pose xs := fun n => sval (cid (@construct_x n)).
have pcdx n : itv_partition c d (behead (xs n)).
  by have [] := proj2_sig (cid (@construct_x n)).
have max_xs n : mesh c d (behead (xs n)) <= fine (lambda n).
  have [_ +] := proj2_sig (cid (construct_x n)).
  rewrite -[X in (_ <= X)%E](@fineK _ (lambda n)); last first.
    admit.
  admit.
pose S_ n : R := variation c d f (behead (xs n)).
(* (2) *)
pose V_ n : \bar R := \sum_(i < n.+1) `|f (d_ n i) - f (c_ n i)|%:E +
     (\sum_(i < n) total_variation (A_ i) (B_ i) f).
pose CD_ n := merge <=%R [tuple c_ n i | i < n.+1] [tuple d_ n i | i < n.+1].
have sub_xcd n : subseq (CD_ n) (xs n).
  admit.
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
have SV n : ((S_ n)%:E <= V_ n)%E.
  rewrite /S_ /V_.
  rewrite variation_subdivition
  apply: (le_trans (lee_tofin
   (@variation_subseq _ c d f (behead (xs n)) (behead (CD_ n)) _ _ _))).
  - admit.
  - admit.
  - admit.

(*
  apply: (@le_trans _ _ (\sum_(i < n.+2) `|f (d_ n i) - f (c_ n i)|%:E +
               \sum_(i < n.+1)
                    variation (A_ i) (B_ i) [seq x <- xs | x \in `]A_ i, B_ i[].
    admit.
  apply: lee_sum.
  exact: variation_le_total_variation.
*)
  admit.
(*

                    \sum_(i < n.+1) `|f (c_ n i.+1) - f (d_ n i)|%:E )%E).
    admit.
  apply: leeD2l.
  rewrite (_ : (\sum_(i < n.+1) `|f (c_ n i.+1) - f (d_ n i)|%:E)%R =
     (\sum_(i < n.+1) `|f (B_ i) - f (A_ i)|%:E)%R)%E.
    rewrite (_ : (\sum_(i < n.+1) `|f (c_ n i.+1) - f (d_ n i)|%:E)%R =
       (\sum_(i < n.+1) `|f (b_ n i) - f (a_ n i)|%:E)%R)%E.
      apply: eq_bigr => i _.
      by rewrite cbE daE/=.
    transitivity (\sum_(i0 < n.+1) `|f (B_ (idx n i0)) - f (A_ (idx n i0))|%:E).
      apply: eq_bigr => i _.
      rewrite /a_ /b_ anth bnth.
      have [-> ->] := nth_abE A_ B_ d (ltn_ord i).
      by rewrite -idxE => idxn1.
    (* idx is bijection *)
    have [[idx_ord idx_inv] /= [idx_ordE inv_ord ord_inv]] := idx_bij A_ B_ n.
    rewrite -/idx in idx_ordE.
    transitivity (\sum_(i0 < n.+1) `|f (B_ (idx_ord i0)) - f (A_ (idx_ord i0))|%:E).
      apply: eq_bigr => i _.
      by rewrite !idx_ordE -!ordinal_val.
    rewrite -(@reindex_inj _ _ _ _ idx_ord xpredT
       (fun k => `|f (B_ k) - f (A_ k)|%:E))//=.
    by move=> i j; move/(f_equal idx_inv); rewrite !inv_ord.
  apply: (@le_trans _ _ ((\sum_(i < n.+1) oscillation f `[A_ i, B_ i]))).
    apply: lee_sum => i _.
    apply: variation_oscillation.
    - apply: continuous_subspaceW cdcf.
      apply: subset_neitv_oocc => //.
      rewrite /A_ /B_ -contiguous_ooitv//.
      rewrite -compact_Rhull//.
      apply: (subset_trans (@contiguous_intervalsS _ _ _)).
      exact: cplt_hull_subset_Rhull.
    - by rewrite boundr_in_itv/= bnd_simp ltW.
    - by rewrite boundl_in_itv/= bnd_simp ltW.
  apply: lee_sum => i _.
  rewrite -[X in total_variation X _](inf_itvcc (ltW (AB i))).
  rewrite -[X in total_variation _ X](sup_itvcc (ltW (AB i))).
  apply: bounded_set_oscillation_le_total_variations.
  apply: compact_bounded.
  exact: segment_compact.
*)
set Vcd : \bar R := total_variation c d f.
have V_tv n : (V_ n <= Vcd)%E.
  admit.
have cdbvf : bounded_variation c d f.
  apply: (bounded_variationl (ltW cd) db).
  apply: bounded_variationr ac _ bvf.
  by apply: ltW; exact: (lt_le_trans cd).
have Soo_tv : (S_ n)%:E @[n --> \oo] --> Vcd.
  have := lemma5 cd cdcf pcdx max_xs lambda0.
  by rewrite /S_ /Vcd.
have Voo_V : V_ n @[n --> \oo] --> Vcd.
  apply: (squeeze_cvge _ Soo_tv); last first.
    exact: cvg_cst.
  apply: nearW => n.
  apply/andP; split.
    exact: SV.
  exact: V_tv.
(* (3) *)
have eq3 : \forall n \near \oo, (Vcd - alpha / 2 < V_ n)%E.
  have alpha20 : 0 < fine (alpha / 2).
    apply: fine_gt0; rewrite mule_gt0//=.
      by rewrite inver ifF; exact/negP/negP.
    rewrite inver ifF; first exact/negP/negP.
    by rewrite lte_mul_pinfty ?measure_ge0 ?ltry.
  move: Voo_V.
  rewrite -{1}(@fineK _ Vcd).
    by apply/bounded_variationP => //; exact: ltW.
  move/fine_cvg.
  move/(_ (ball (fine Vcd) (fine (alpha / 2))) (nbhsx_ballx _ _ alpha20)).
  move=> [n0 _ H].
  exists n0.+1 => //n n0n.
  have := H n (ltnW n0n).
  rewrite /ball/=.
  rewrite /ereal_ball/=.
  have Vcdoo : (Vcd < +oo)%E.
    rewrite -ge0_fin_numE; last by apply/bounded_variationP => //; exact: ltW.
    by apply: total_variation_ge0; exact: ltW.
  have Vn_fin : V_ n \is a fin_num.
    rewrite ge0_fin_numE.
      apply: adde_ge0.
        exact: sume_ge0.
      apply: sume_ge0 => ? _.
      apply: total_variation_ge0.
      exact: ltW.
    exact: (le_lt_trans (V_tv n)).
  have al2fin : (alpha / 2)%E \is a fin_num.
    rewrite inver ifF; first exact/negP/negP.
    rewrite ge0_fin_numE.
      by rewrite mule_ge0 ?ltW.
    rewrite lte_mul_pinfty ?ltW//.
    exact: ltry.
  rewrite ger0_norm.
    rewrite subr_ge0.
    rewrite fine_le//.
      apply/bounded_variationP => //.
      exact: ltW.
  rewrite ltrBlDl -ltrBlDr.
  rewrite -fineB//.
    by apply/bounded_variationP => //; exact: ltW.
  rewrite -lte_fin !fineK//.
  rewrite fin_numB; apply/andP; split => //.
  by apply/bounded_variationP => //; exact: ltW.
(* (4) *)
(* total_variationD? *)
have eq4 n : total_variation c d f =
  \sum_(i < n.+1) (H (d_ n i) - H (c_ n i))%:E +
   \sum_(i < n) (total_variation (A_ i) (B_ i) f).
  admit.

have ABsubcd i : `[A_ i, B_ i] `<=` `[c, d].
  rewrite -[in X in X `<=` _]setU_1itvob ?bnd_simp//.
    by apply/ltW.
  rewrite -[in X in X `<=` _]setU_itvob1 ?bnd_simp//.
  rewrite 2!subUset; split.
    rewrite sub1set inE/= in_itv/=; apply/andP; split.
      by apply: inf_contiguous_intervals1 => //; rewrite inE/=; exact: ne_cgitvs.
    by apply: sup_contiguous_intervals1 => //; rewrite inE/=; exact: ne_cgitvs.
  split; last first.
    rewrite sub1set inE/= in_itv/=; apply/andP; split.
      by apply: inf_contiguous_intervals2 => //; rewrite inE/=; exact: ne_cgitvs.
      by apply: sup_contiguous_intervals2 => //; rewrite inE/=; exact: ne_cgitvs.
  rewrite -contiguous_ooitv//.
  rewrite -compact_Rhull//.
  apply: (subset_trans (@contiguous_intervalsS _ Z (h1 i))).
  exact: cplt_hull_subset_Rhull.

have ABbvf n : \sum_(i < n) total_variation (A_ i) (B_ i) f \is a fin_num.
  apply/sum_fin_numP => /=.
  case => i iltn _ _.
  destruct n => //.
  rewrite -(inord_val (Ordinal _))/= !inordK//.
  apply/bounded_variationP.
    exact: ltW.
  apply: (@bounded_variationr _ c).
  - (* generalize incl_itv_lb? *)
    (* a < b -> `]a, b[ `<=` `[c, d] -> a < c *)
    rewrite leNgt; apply/negP => cA.
    move: (ABsubcd i).
    move/disj_setPCl/disj_set2P.
    apply/eqP/set0P.
    have [Bc|cB] := leP (B_ i) c.
      exists (((A_ i) + (B_ i)) / 2) => /=; split.
        by rewrite in_itv/= !midf_le -/(A_ i)//; exact/ltW.
      apply/negP; rewrite in_itv/= negb_and -ltNge; apply/orP; left.
      rewrite -/c (@splitr _ c).
      rewrite mulrDl.
      by rewrite ltr_leD ?ltr_pM2r ?ler_pM2r.
      exists ((A_ i + c) / 2) => /=; split; rewrite in_itv/=.
      by rewrite !midf_le// -/(B_ i) ?ltW// (@splitr _ (B_ i)) mulrDl ltrD ?ltr_pM2r.
    apply/negP; rewrite negb_and -ltNge; apply/orP; left.
    by rewrite -/c midf_lt.
  - exact: ltW.
    apply: bounded_variationl cdbvf.
    rewrite leNgt; apply/negP => Bc.
    move: (ABsubcd i).
    move/disj_setPCl/disj_set2P.
    apply/eqP/set0P.
    exists (((A_ i) + (B_ i)) / 2) => /=; split.
      by rewrite in_itv/= !midf_le -/(A_ i)// ltW.
    apply/negP; rewrite in_itv/= negb_and -ltNge; apply/orP; left.
    rewrite -/c (@splitr _ c) mulrDl ltrD ?ltr_pM2r//.
    exact: (lt_trans (AB i)).
  (* generalize incl_itv_ub? *)
  (* a < b -> `]a, b[ `<=` `[c, d] -> b < d *)
  rewrite leNgt; apply/negP => dB.
  move: (ABsubcd i).
  move/disj_setPCl/disj_set2P.
  apply/eqP/set0P.
  have [Ad|dA] := leP d (A_ i).
    exists (((A_ i) + (B_ i)) / 2) => /=; split.
      by rewrite in_itv/= !midf_le -/(A_ i)// ltW.
    apply/negP; rewrite in_itv/= negb_and -!ltNge; apply/orP; right.
    rewrite (@splitr _ d).
    rewrite mulrDl.
    by rewrite ler_ltD ?ltr_pM2r ?ler_pM2r.
  exists ((d + B_ i) / 2) => /=; split; rewrite in_itv/=.
    by rewrite !midf_le// ?ltW// (@splitr _ (A_ i)) mulrDl ltrD ?ltr_pM2r.
  apply/negP; rewrite negb_and -!ltNge; apply/orP; right.
  by rewrite midf_lt.

(* (5) *)
have eq5 : \forall n \near \oo,
  (\sum_(i < n.+1) (H (d_ n i) - H (c_ n i))%:E - (alpha / 2) <
  \sum_(i < n.+1) `|f (d_ n i) - f (c_ n i)|%:E)%E.
  move: eq3 => [n0 _/= hyp].
  exists n0 => // n/= n0n.
  move: (hyp n n0n) => {hyp}.
  rewrite /V_ -lteBlDr.
    by case: n n0n.
  rewrite /Vcd (eq4 n).
  apply: le_lt_trans.
  by rewrite addeAC leeB// -addeA leeDl// subre_ge0.

(* (5.5) (between (5) and (6)) *)
have alphaH n : (alpha < \sum_(i < n.+1) (H (d_ n i) - H (c_ n i))%:E)%E.
  rewrite /alpha.
  apply: (@le_lt_trans _ _ (\sum_(i < n.+2) (H (d_ n.+1 i) - H (c_ n.+1 i))%:E)).
    admit.
  admit.
(*
rewrite addrAC ltrD2r.
move/(@lt_trans _ _ _ (fine alpha / 2)).
rewrite addrA.
rewrite ltrBrDl -splitr; move/(_ alphaH).
*)
(* (6) *)
have ineq6 : \forall n \near \oo,
    (alpha / 2 < \sum_(i < n.+1) `|f (d_ n i) - f (c_ n i)|%:E)%E.
  have [n0 _ /= H5] := eq5.
  exists n0 => // n/= n0n.
  apply: lt_trans (H5 n n0n).
  rewrite lteBrDl.
    apply: fin_numM => //.
    exact: fin_numV.
  rewrite -mule2n -mule_natr.
  rewrite muleAC -muleA divee// mule1.
  exact: alphaH.

have cdIcplt_hull (S : set R) : measurable S -> S `<=` `[c, d] ->
                                mu S = mu (S `&` cplt_hull Z).
  move=> mS Scd.
  rewrite -[in LHS](setIidl Scd).
  rewrite -compact_Rhull//.
  have -> : [set` Rhull Z] = Z `|` cplt_hull Z.
    rewrite -(setUIDK [set` Rhull Z] Z); congr setU.
    apply: setIidr.
    exact: sub_Rhull.
  rewrite setIUr.
  rewrite measureU/=.
  - apply: sub_caratheodory.
    rewrite RGenOpenSets.measurableE.
    apply: measurableI => //.
    exact: compact_measurable.
  - apply: sub_caratheodory.
    rewrite RGenOpenSets.measurableE.
    apply: measurableI => //.
    apply: measurableD => //.
    exact: compact_measurable.
  - by rewrite setIACA setDIK setI0.
    rewrite -[RHS]add0e; congr +%E.
    apply/eqP; rewrite -measure_le0/=.
    rewrite -Z0.
    apply: le_outer_measure.
    exact: subIsetr.
(* (6.5) (between (6) and (7)) *)
pose ABcd n (i : 'I_ n.+1) := [set k | `]A_ k, B_ k[ `<=` `[c_ n i, d_ n i]].
(* have UABcdE n : \bigcup_(i < n.+1) (ABcd _ i) = [set k | n < k]. *)
set Zsub := fun n (i : 'I_ n.+1) => Z `&` `[c_ n i, d_ n i].
have hull_Zsub n (i : 'I_ n.+1) :
  [set` Rhull (Zsub n i)] `<=` `[c_ n i, d_ n i]%classic.
  rewrite Rhull_smallest.
  apply: smallest_sub; first exact: interval_is_interval.
  exact: subIsetr.
have cf_cd n i : {within `[c_ n i, d_ n i], continuous f}.
  apply: continuous_subspaceW cf.
  apply: subset_itv; rewrite bnd_simp.
    apply: (le_trans ac).
    rewrite /c_ cbE; case: i => //= i.
    apply: le_trans; last exact: aleb.
    exact: (proj1 (@clea_bled _ _ _ _ _ _ _)).
  apply: (le_trans _ db).
  rewrite /d_ daE.
  apply: le_trans; first exact: aleb.
  rewrite /A_ /B_ /d.
  exact: (proj2 (@clea_bled _ _ _ _ _ _ _)).
have itvfcd n (i : 'I_ n.+1) : is_interval (f @` `[c_ n i, d_ n i]).
  apply: (is_interval_image_cc cf).
  apply: subset_itv => //; rewrite bnd_simp.
    apply: (le_trans ac).
    rewrite [leRHS]cbE; case: i; case => //= i _.
    apply: le_trans; last exact: aleb.
    by apply clea_bled.
  apply: le_trans db.
  rewrite /d_ daE.
  apply: le_trans; first exact: aleb.
  by apply clea_bled.

have Zsub_cover n (i : 'I_ n.+1) :
    `[c_ n i, d_ n i]%classic `<=` Zsub n i `|` \bigcup_(i0 in
    (fun k : nat => `[A_ (n + k)%N, B_ (n + k)%N] `<=` `[c_ n i, d_ n i]))
  `](A_ (n + i0)%N, B_ (n + i0)%N).1,
         (A_ (n + i0)%N, B_ (n + i0)%N).2[%classic.
    move=> x/= cdx.
    have : [set` Rhull Z] x.
      rewrite (hullZ_abcd lbZ ubZ n cd cZ Z_nonempty AB); left.
      by exists i => /=.
    rewrite -(setUIDK [set` Rhull Z] Z).
    rewrite setIidr -/(cplt_hull Z); first exact: sub_Rhull.
    move=> [Zx|].
      by left.
    rewrite bigcup_contiguous_intervals//.
    rewrite bigcup_contiguous_intervals_support.
    have [funh1 injh1 surjh1] := @bij _ _ _ _ h1.
    rewrite (reindex_bigcup h1 _ _ _ funh1 surjh1).
    move=> [k _ kx]; right.
    have nk : (n <= k)%N.
      rewrite leqNgt; apply/negP => kn1.
      move: (disj_abcd d lbZ ubZ h1 n).
      apply/eqP/set0P; exists x; split.
        by exists i => /=.
      by exists k => /=.
    exists (k - n)%N.
    rewrite subnKC//.
    apply: subset_neitv_oocc => //.
    move=> z /[dup] ABkz.
    rewrite /A_ /B_ -contiguous_ooitv// => kz.
    have [k' k'n2 cdk'z/=] := citvScd lbZ ubZ cZ Z_nonempty AB kz nk.

    suff -> : i = k' :> nat by [].

    apply/not_notP => /eqP ik'.
    have [|zx] := leP x z.
      admit.
    have zxk : `]z, x[%classic `<=` contiguous_intervals Z (h1 k).
      admit.
    have : d_ n k' < c_ n i.
      admit.
    rewrite /d_ daE /c_ cbE.
    case: i cdx ik'.
    case.
      admit.
    move=> /= i iltn2 cdx ik'.
    move=> ak'bi.
    have {k'n2}k'n1 : (k' < n)%N.
      admit.
    have zai : z <= a_ n i.
      move : ik'.
      rewrite neq_ltn => /orP[i1k'|k'i1].
        admit.
      have := @le_sorted_leq_nth _ _ d _ (sorted_a A_ B_ n) k' i.
      rewrite !inE size_seq_ab.
      move/(_ k'n1 iltn2 k'i1); rewrite -/(a_ n k') -/(a_ n i).
      apply: le_trans.
      move: cdk'z.
      by rewrite /d_ daE in_itv/= => /andP[_].
    have bix : b_ n i <= x.
      move: cdx.
      rewrite /c_ cbE /=.
      by rewrite in_itv/= => /andP[].
    have : `]a_ n i, b_ n i[ `<=` contiguous_intervals Z (h1 k).
      apply: (@subset_trans _ `]z, x[%classic).
      (* by zai and bix *)
        admit.
      (* because contiguous_intervals is interval *)
      admit.
    rewrite /a_ anth /b_ bnth.
    have [-> ->] := @nth_abE R A_ B_ d n i iltn2.
    rewrite -idxE.
    move=> idxin1.
    rewrite /A_ /B_.
    rewrite -contiguous_ooitv// => citvik.
    have ik : idx n i = k.
      admit.
    (* same for k' *)
    have k'k : idx n k' = k.
      admit.
    move: ik'.
    admit.
  admit.
have disj_cd n : trivIset (`I_ n.+1) (fun i => `[c_ n i, d_ n i]%classic).
  apply/trivIsetP => i j /= iltn2 jltn2 ij.
  admit.
(* (7) *)
have ineq7 n : ((\sum_(i < n.+1) `|f (d_ n i) - f (c_ n i)|)%:E <=
  \sum_(n <= i <oo) oscillation f `[A_ i, B_ i])%E.
  have prop65 : forall i : 'I_ n.+1, (`|f (d_ n i) - f (c_ n i)|%:E <=
    \sum_(n <= j <oo | `[< `[A_ j, B_ j] `<=` `[c_ n i, d_ n i] >])
     oscillation f `[A_ j, B_ j])%E.
    move => i.
(* change to lemma4_cover *)
    have /andP[le1 le2] := @lemma4_cover _ _ _ (cled a lbZ ubZ cd cZ Z_nonempty AB n i) f _
    (fun k : nat => (A_ (n + k)%N, B_ (n + k)%N)) (cf_cd n i)
    (itvfcd n i) (hull_Zsub n i)
    (fun k => (ltW (AB (n + k)%N))) (Zsub_cover n i).
    rewrite /=.
    apply: (le_trans le1); apply: (le_trans le2).
    have -> : mu^*%mu [set f x | x in Zsub n i] = 0.
      rewrite measurable_mu_extE/=.
        apply: sub_caratheodory.
        rewrite RGenOpenSets.measurableE.
        apply: compact_measurable.
        apply: continuous_compact.
          apply: continuous_subspaceW cf.
          by apply: subIset; left.
        apply: compact_closedI => //.
        exact: itv_closed.
      apply: lusinf.
      - admit.
      - admit.
      apply/eqP; rewrite -measure_le0/=.
      by rewrite -Z0; apply: le_outer_measure; apply: subIsetl.
    rewrite add0r/=.
    rewrite [leLHS](_: _ =
      \big[+%E/0%R]_(n <= i0 <oo | `[< `[A_ i0, B_ i0] `<=` `[c_ n i, d_ n i] >])
      oscillation f `[A_ i0, B_ i0]).
    (* rewrite cvg_shiftn. *)
      rewrite eseries_mkcond [RHS]eseries_mkcond.
      rewrite -(nneseries_addn n).
        by move=> k; case: ifP => // _; apply: oscillation_ge0.
      apply: eq_eseriesr => k _; case: ifP => /asboolP Hk.
        by rewrite addnC ifT//; apply/asboolP; rewrite addnC.
      by rewrite ifF//; apply/asboolP; rewrite addnC.
  
  by apply: lee_nneseries => // j _ _; exact: oscillation_ge0.
  apply: (@le_trans _ _
    (\sum_(i < n.+1)
      \big[+%E/0%R]_(n <= i0 <oo | `[< `[A_ i0, B_ i0] `<=` `[c_ n i, d_ n i] >])
          oscillation f `[A_ i0, B_ i0])%E).
  by rewrite -sumEFin; apply: lee_sum => /= i _.
  (* interchange *)
  have : (\sum_(i < n.+1)
       \big[+%E/0]_(n <= i0 <oo | `[< `[A_ i0, B_ i0] `<=` `[c_ n i, d_ n i] >])
         oscillation f `[A_ i0, B_ i0] <=
           \sum_(n <= i0 <oo)
              (\sum_(i < n.+1 | `[< `[A_ i0, B_ i0] `<=` `[c_ n i, d_ n i] >])
       oscillation f `[A_ i0, B_ i0]))%E.
  under eq_bigr do rewrite eseries_mkcond.
  rewrite -nneseries_sum.
    move=> i j _.
    by case: ifP => // _; exact: oscillation_ge0.
  apply: lee_nneseries.
  - move=> i ni _.
    apply: sume_ge0 => j _.
    by case: ifP => // _; exact: oscillation_ge0.
  - by move=> i _; rewrite -big_mkcond; apply: lee_sum.
  move/le_trans; apply.
  rewrite eseries_cond [leRHS]eseries_cond/=.
  apply: lee_nneseries.
    by move=> i ni _; apply: sume_ge0 => j _; exact: oscillation_ge0.
  move=> j nj.
  have : supp (h1 j).
    have [+ _ _] := @bij _ _ _ _ h1.
    exact.
  move=> [z jz].
  have [k kn2 kz] := citvScd lbZ ubZ cZ Z_nonempty AB jz nj.
  rewrite (bigD1_ord (Ordinal kn2))/=.
    apply/asboolP.
    admit.
  rewrite big1; last by rewrite adde0.
  move=> i /asboolP ji.
  exfalso.
  move: ji.
  apply/existsNP; exists z.
  apply/not_implyP; split.
    admit.
  rewrite /=.
  have kj := neq_bump k i.
  move=> zbump.
  have/trivIsetP/(_ k (bump k i))/= := disj_cd n.
  move/(_ kn2).
  have bumpn2 : (bump k i < n.+1)%N.
    rewrite /bump -[ltnRHS]add1n -addnS leq_add//.
    by case: (k <= i)%N.
  move/(_ bumpn2 kj).
  by move/eqP; apply/negP/set0P; exists z.

(* (8), used in the last step *)
have ineq8 : \forall n \near \oo,
  (alpha / 2 <= \sum_(n <= j <oo) oscillation f `[A_ j, B_ j])%E.
  have [n _ H6] := ineq6.
  exists n => // n0 /= n0n.
  apply: (le_trans _ (ineq7 n0)).
  apply: ltW.
  apply: (lt_le_trans (H6 n0 n0n)).
  by rewrite sumEFin.
(* (9), used in the last step *)
have eq9 :
   (\sum_(n <= j <oo) oscillation f `[A_ j, B_ j])%E @[n --> \oo] --> 0%:E.
(*  rewrite (cvg_shiftS (fun k => \big[+%E/0]_(k <= j <oo) _)).*)
  apply: nneseries_tail_cvg.
    apply: (@le_lt_trans _ _ Vcd).
      (* oscillation_closure *)
      rewrite [leLHS](_ : _ = (\big[+%E/0%R]_(0 <= k <oo) oscillation f `]A_ k, B_ k[)).
        apply: eq_eseriesr => i _.
        rewrite -[in RHS]oscillation_closure.
          rewrite closure_neitv_oo//.
          apply: (continuous_subspaceW _ cf).
          apply: (subset_trans (ABsubcd i)).
          rewrite -compact_Rhull// -(@RhullK _ `[a, b]%classic).
            rewrite inE.
            exact: interval_is_interval.
          exact: le_Rhull.
        by rewrite closure_neitv_oo.
      apply: sum_oscillation_le_total_variation.
        exact: cd.
        exact: cdcf.
        exact: AB.
        rewrite /A_ /B_.
        rewrite [X in _ _ X](_: _ = (contiguous_intervals Z) \o h1).
          by apply/funext => i; rewrite -contiguous_ooitv.
        rewrite trivIset_comp.
          by apply: set_bij_inj; apply: bij.
        apply: (@sub_trivIset _ _ _ setT) => //.
        exact: disjoint_contiguous_intervals.
        exact: ABsubcd.
    have/(bounded_variationP _ (ltW cd)) := cdbvf.
    by rewrite ge0_fin_numE// total_variation_ge0// ltW.
  move=> n _.
  exact: oscillation_ge0.
(* the last step *)
have : (alpha / 2 <= 0%:E)%E.
  have/cvg_lim <- := eq9.
    exact: ereal_hausdorff.
  apply: (lime_ge _ ineq8).
  by apply/cvg_ex; exists 0%:E.
rewrite pmule_lle0 ?inve_gt0//.
apply/negP.
by rewrite -ltNge.
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
    \sum_(j <oo) (mu^* )%mu (f @` (Z1 `&` (open_disjoint_itv (oG i) j))))%E.
  admit.
have H5 i :
    (\sum_(j <oo) (mu^* )%mu (f @` (Z1 `&` (open_disjoint_itv (oG i) j))) <
    \sum_(j <oo) oscillation f (closure (open_disjoint_itv (oG i) j)))%E.
  admit.
have H6 i :
    (\sum_(j <oo) oscillation f (closure (open_disjoint_itv (oG i) j)) =
    mu (H @` G_ i))%E.
  admit.
apply/eqP; rewrite eq_le measure_ge0 andbT.

Abort.

End lemma6_converse.
