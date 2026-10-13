From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum interval.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp contra classical_sets.
From mathcomp Require Import reals ereal topology normedtype numfun derive.
From mathcomp Require Import realfun. (*NB: for total_variation*)
From mathcomp Require Import absolute_continuity. (*TODO: for closure_bigcup only*)
From mathcomp Require Import variation_extra.

(**md**************************************************************************)
(* # Oscillation                                                              *)
(*                                                                            *)
(* `oscillation f A`                                                          *)
(* : oscillation of function `f : R -> R` on `A : set R`                      *)
(* : This is an extended real number.                                         *)
(*                                                                            *)
(* `omega_max a s f`                                                          *)
(* : max of oscillation over the intervals $[(a::s)_i, (a::s)_{i+1}]$         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma closure_has_ubound {R : realType} (A : set R) (f : R -> R)
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

Lemma closure_has_lbound {R : realType} (A : set R) (f : R -> R)
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

Lemma is_subset1P (T : Type) (A : set T) : is_subset1 A ->
  A = set0 \/ exists a, A = [set a].
Proof.
move=> A1.
have [|/set0P[x Ax]] := eqVneq A set0; first by left.
right; exists x.
apply/seteqP; split => [y|y ->//].
by move/A1; exact.
Qed.

(* TODO: PR? *)
Lemma setNEFin {R : realType} (f : R -> R) (A : set R) :
  [set (- x)%E | x in ((EFin \o f) @` A)] = (EFin \o (\- f)%R) @` A.
Proof.
apply/seteqP; split => [_ [_/= [r Ar] <- <-]|_/= [r Ar] <-].
  by exists r.
by exists (f r)%:E => //; exists r.
Qed.

(* TODO: PR? *)
Lemma ereal_inf_sup {R : realType} (A : set (\bar R)) : A !=set0 ->
  (ereal_inf A <= ereal_sup A)%E.
Proof.
move=> [a Aa].
by rewrite (@le_trans _ _ a)//;
  [exact: ereal_inf_lbound|exact: ereal_sup_ubound].
Qed.

Definition oscillation {R : realType} (f : R -> R) (A : set R) : \bar R :=
  (if A == set0 then
     0
   else
     ereal_sup ((EFin \o f) @` A) - ereal_inf ((EFin \o f) @` A))%E.

Section oscillation_lemmas.
Context (R : realType).
Local Open Scope ereal_scope.
Implicit Types (f : R -> R) (A : set R).

Lemma oscillation0 f : oscillation f set0 = 0.
Proof. by rewrite /oscillation eqxx. Qed.

Lemma oscillation_set1 (a : R) f : oscillation f [set a] = 0.
Proof.
rewrite /oscillation ifF.
  by apply/negP/negP/set0P; exists a.
by rewrite !image_set1 ereal_sup1 ereal_inf1 subee.
Qed.

Lemma is_subset1_oscillation0 f A : is_subset1 A -> oscillation f A = 0.
Proof.
move=> /is_subset1P[->|[x ->]]; first by rewrite oscillation0.
by rewrite oscillation_set1.
Qed.

Lemma oscillationN f A : oscillation (\- f)%R A = oscillation f A.
Proof.
rewrite /oscillation; case: ifPn => // A0.
rewrite [X in _ = X - _]ereal_supEN [in X in _ = _ - X]ereal_infEN.
by rewrite [RHS]addeC [in RHS]oppeK setNEFin.
Qed.

Lemma oscillation_hasNub f A : ~ has_ubound (f @` A) -> oscillation f A = +oo.
Proof.
move=> hasNubA.
rewrite /oscillation; case: ifPn => [/eqP A0|A0].
  absurd: hasNubA; rewrite A0 image_set0 /has_ubound ubound0.
  by apply/set0P; exact: setT0.
rewrite -image_comp (@hasNub_ereal_sup _ (f @` A))//.
  by apply/set0P; contra: A0; exact: image_set0_set0.
rewrite addye//.
apply/eqP; rewrite eqe_oppLRP/= => /ereal_inf_pinfty fA.
move/set0P : A0 => [x Ax].
have := ltry (f x).
by apply/negP; rewrite -leNgt leye_eq; apply/eqP/fA; exists (f x).
Qed.

Lemma oscillation_hasNlb f A : ~ has_lbound (f @` A) -> oscillation f A = +oo.
Proof.
move=> hasNlbA; have /oscillation_hasNub : ~ has_ubound ((\- f)%R @` A).
  move/has_ub_lbN.
  rewrite [X in has_lbound X](_ : _ = f @` A)//.
  rewrite image_comp//= (_ : _ \o _ = f)//=.
  by apply/funext => r/=; rewrite opprK.
by rewrite oscillationN.
Qed.

Lemma oscillation_ge0 f A : (0 <= oscillation f A)%E.
Proof.
rewrite /oscillation; case: ifPn => // /set0P[r Ar].
set s : \bar R := ereal_sup _; set i : \bar R := ereal_inf _.
have frsup : ((f r)%:E <= s)%E by rewrite ereal_sup_ubound//=; exists r.
have inffr : (i <= (f r)%:E)%E by rewrite ereal_inf_lbound//=; exists r.
have [sfin|] := boolP (s \is a fin_num).
  have [ifin|] := boolP (i \is a fin_num).
    by rewrite sube_ge0 ?sfin ?ifin// ereal_inf_sup//; exists (f r)%:E, r.
  rewrite fin_numE negb_and !negbK => /predU1P[iy|/eqP iy].
    by rewrite iy addey//; move: sfin; rewrite fin_numE => /andP[].
  by move: inffr; rewrite iy.
rewrite fin_numE negb_and !negbK => /predU1P[sy|/eqP sy].
  by absurd; move/ereal_sup_ninfty : (sy) => /(_ _ (ex_intro2 _ _ _ Ar erefl)).
have [iy|iy] := eqVneq i +oo%E.
  by move: inffr; rewrite iy leye_eq.
by rewrite sy addye// eqe_oppLR.
Qed.

Lemma oscillation_sub f i j :
  i `<=` j -> (oscillation f i <= oscillation f j)%E.
Proof.
move=> ij; have [->|i0] := eqVneq i set0.
  by rewrite oscillation0 oscillation_ge0.
have [j0|j0] := eqVneq j set0.
  by move: ij; rewrite j0 subset0 => /eqP; rewrite (negbTE i0).
rewrite /oscillation (negbTE i0) (negbTE j0) leeB//.
- by apply: ereal_sup_le; exact: image_subset.
- by apply: ereal_inf_le_tmp; exact: image_subset.
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
have : (M < x)%R.
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
move=> A0 fA; rewrite /inf; congr (- _)%R.
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
move=> x /= fAx; exists (- x)%R; last by rewrite opprK.
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
have e20 : (0 < e / 2)%R.
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
wlog : r s Ar As / (r < s)%R.
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
  exists `|f r - f s|%R => //.
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

Lemma oscillation_ub (c d : R) (f : R -> R) (e : R) : (c < d)%R ->
  {within `[c, d], continuous f} (* shouldn't be necessary *) ->
  (0 < e)%R ->
  exists xy, [/\ `]c, d[%classic xy.1, `]c, d[%classic xy.2, (xy.1 < xy.2)%R &
    (`|f xy.1 - f xy.2|%:E > oscillation f `]c, d[ - e%:E)%E ].
Proof.
move=> cd cf e0.
pose w := oscillation f `]c, d[.
pose A := `]c, d[%classic.
have has_ubfA : has_ubound [set f x | x in A].
  have [M Mcd Mmax] := EVT_max (ltW cd) cf.
  exists (f M) => _/= [r Ar <-].
  apply: Mmax.
  exact: subset_itv_oo_cc Ar.
have has_lbfA : has_lbound [set f x | x in A].
  have [m mcd mmin] := EVT_min (ltW cd) cf.
  exists (f m) => _/= [r Ar <-].
  apply: mmin.
  exact: subset_itv_oo_cc Ar.
have A0 : A !=set0.
  exists ((c + d) / 2)%R.
  by rewrite /A/= in_itv/= !midf_lt.
have supfA : has_sup (f @` A) by split => //; exact: image_nonempty.
have inffA : has_inf (f @` A) by split => //; exact: image_nonempty.
pose S : set (\bar R):= [set `|f x - f y|%:E | x in A & y in A].
have wS : w = ereal_sup S.
  rewrite /w oscillationE//.
  - rewrite -(image_comp _ EFin) ereal_sup_EFin//; exact: image_nonempty.
  - rewrite -(image_comp _ EFin) ereal_inf_EFin//; exact: image_nonempty.
have [u [v [Au Av uve]]] : exists u v, [/\ A u, A v & (`|f u - f v|%:E > w - e%:E)%E].
  have : ereal_sup S \is a fin_num.
    rewrite /S.
    rewrite [X in ereal_sup X](_ : _ = [set x%:E | x in [set `|f x - f y|%R | x in A & y in A]]).
      (* TODO: lemma *)
      rewrite eqEsubset; split => [_/= [r Ar] [y Ay <-]|].
        eexists; last reflexivity.
        exists r => //.
        by exists y.
      move=> x /= [r [s As] [y Ay <-{r}] <-{x}].
      exists s => //.
      by exists y => //.
    rewrite ereal_sup_EFin//.
    have : has_ubound [set `|f x|%R | x in A].
      (* TODO: lemma *)
      case: has_ubfA => M HM.
      case: has_lbfA => m Hm.
      exists (maxr `|M| `|m|)%R => /= x/= [r Ar] <-.
      have [fr0|fr0] := lerP (f r) 0.
        rewrite ler0_norm// le_max.
        apply/orP; right.
        rewrite lerNl.
        rewrite (@le_trans _ _ m)//.
          by rewrite lerNl -normrN ler_norm.
        by apply: Hm; by exists r.
      rewrite gtr0_norm// le_max.
      apply/orP; left.
      rewrite (@le_trans _ _ M)//.
        by apply: HM; by exists r.
      by rewrite ler_norm.
    case => m Hm.
    exists (m + m)%R => y/= [r Ar [s As <-]].
    rewrite (le_trans (ler_normB _ _))// lerD//.
      apply: Hm; by exists r.
    apply: Hm; by exists s.
    (* TODO: lemma *)
    case: A0 => r Ar.
    exists `|f r - f r|%R, r => //.
    by exists r.
  move/ub_ereal_sup_adherent => /(_ _ e0)[_ [r rx] [r' Ar'] <- Hr].
  exists r, r'; split => //=.
  rewrite EFinN lteBlDr//.
  rewrite wS.
  move: Hr.
  by rewrite lteBlDr.
have [u_lt_v|v_lt_u|u_eq_v] := ltgtP u v.
- set x := u; set y := v.
  have [cx xy yd] : [/\ c < x, x < y & y < d]%R.
    split => //.
    by move/mem_set : Au; rewrite inE => /itvP ->.
    by move/mem_set : Av; rewrite inE => /itvP ->.
  by exists (x, y); split => //=.
- set y := u; set x := v.
  have [cx xy yd] : [/\ c < x, x < y & y < d]%R.
    split => //.
    by move/mem_set : Av; rewrite inE => /itvP ->.
    by move/mem_set : Au; rewrite inE => /itvP ->.
  exists (x, y); split => //=.
  by rewrite distrC.
- have [we|ew] := ltP w e%:E.
    have [x [y [Ax Ay xy]]] : exists x y : R, [/\ A x, A y & (x < y)%R].
      set x := ((c + d) / 2)%R.
      set y := ((x + d) / 2)%R.
      have Ax : A x by rewrite /A /= in_itv/= !midf_lt.
      have Ay : A y.
        rewrite /A /= in_itv/= !midf_lt// andbT.
        by rewrite (@lt_trans _ _ x) ?midf_lt.
      exists x, y; split => //.
      rewrite midf_lt//.
      by move/mem_set : Ax; rewrite inE => /itvP ->.
    exists (x, y); split => //=.
    rewrite -/w EFinN.
    rewrite (@lt_le_trans _ _ 0%E)// ?sube_lt0//.
    by apply/orP; right.
  have : (w - e%:E < 0)%E.
    by rewrite (lt_le_trans uve)// u_eq_v subrr normr0.
  rewrite sube_lt0.
    by apply/orP; right.
  by rewrite ltNge ew.
Qed.

End oscillation_lemmas.

Section omega_max.
Context {R : realType}.
Implicit Types (a : R) (f : R -> R) (s : seq R) (x : R).

(* NB: we can take 0 as a default element since the list is never addressed
   out of bounds in the definition *)
Definition omega_max a s f : \bar R :=
   \big[maxe/-oo%E]_(0 <= i < size s) oscillation f
    `[(a :: s)`_i, (a :: s)`_i.+1].

Lemma omega_max0 (a b : R) f : omega_max a [:: b] f = oscillation f `[a, b].
Proof. by rewrite/omega_max/= big_nat1. Qed.

(*
Lemma bigmaxE T Q FH :
forall (F : T -> R) (HF : forall x, 0 <= F x),
  (\big[max/0%:nng]_(i in Q) (FH i)%:nng)%:num = (\big[max/0]_(i in Q) (F i)).

   reflect (\big[maxr/0%:nng]_(0 <= k < n) (P k)%:nng)%:num)
   (\big[maxr/0%R]_(0 <= k < n) P k).
*)

Lemma omega_max_nil a f : omega_max a [::] f = -oo%E.
Proof. by rewrite /omega_max /= big_nil. Qed.

Lemma omega_max_ge0 a f s : s != [::] -> (0 <= omega_max a s f)%E.
Proof.
case: s => [//|h t s0].
by rewrite /omega_max/= big_nat_recl//= le_max oscillation_ge0.
Qed.

(* TODO: PR *)
Lemma itv_partition_nth_ge_new def a b s m : (m < (size s).+1)%N ->
  itv_partition a b s -> (a <= nth def (a :: s) m)%O.
Proof.
elim: m def s a b => [def s a b _//|n ih def [//|h t] a b].
rewrite ltnS => nh [/= /andP[ah ht] lb].
by rewrite (le_trans (ltW ah))// (ih _ _ _ b).
Qed.

Lemma omega_max_le_oscillation a b f s :
  itv_partition a b s ->
  (omega_max a s f <= oscillation f `[a, b])%E.
Proof.
move=> ps.
rewrite /omega_max big_seq bigmax_le//.
  by rewrite leNye.
move=> /= n.
rewrite mem_iota add0n subn0 leq0n/= => ns.
apply: oscillation_sub.
apply: subset_itvScc; rewrite bnd_simp//.
  apply: itv_partition_nth_ge_new ps => //.
  by rewrite (leq_trans ns).
exact: (itv_partition_le_ub _ ps).
Qed.

Lemma omega_max_cons a f s x :
  a <= x <= head a s ->
  s != [::] ->
  (omega_max a (x :: s) f <= omega_max a s f)%E.
Proof.
elim: s => // h s' IH /=/andP[ax xh] _.
rewrite /omega_max/=.
rewrite 3?big_nat_recl//=.
rewrite maxA.
apply: le_max2 => //.
rewrite maxEge; case: ifPn => _; apply: oscillation_sub.
  by apply: subset_itvl; rewrite bnd_simp.
by apply: subset_itvr; rewrite bnd_simp.
Qed.

Lemma le_omega_max a f s t :
  s != [::] ->
  path <=%R a s ->
  sorted <=%R t ->
  subseq s t ->
  (omega_max a t f <= omega_max a s f)%E.
Proof.
elim: t a s.
  by move=> ? ?; rewrite omega_max_nil leNye.
move=> ht t IHt a s s0.
elim: s t s0 IHt => // hs s IHs t _ IHt /= /andP[ahs phss] phtt.
case: ifPn.
  move/eqP => hsht qst.
  case: s IHs phss qst => [|h s IHs phss qst].
(*
    rewrite hsht.
    rewrite /omega_max/=.
    rewrite big_nat1/= big_nat_recl/=.
    apply: bigmax_le.
*)
  admit.
  rewrite /omega_max/=.
  rewrite 2?big_nat_recl//= hsht.
  rewrite le_max2 => //.
  (* apply: IHt => //. *)
    admit.
  (* rewrite le_max; apply/orP. *)
    admit.
Abort.
(*
rewrite /=; case: ifPn => hshht /andP[ahs] phss.
  move=> /andP[hhtht phtt] sub_stt.
  apply: (@le_trans _ _ (omega_max a b f [:: ht & t])).
    apply: omega_max_cons => //=.
    rewrite hhtht andbT.
    by have /eqP <- := hshht.
  have := (IHs s).
  have := @omega_max_cons a b f s hs.
  have /eqP <- := hshht; rewrite ahs/=.
  have := (IHs s).
  by rewrite /= eqxx IH.

rewrite /=; case: ifPn => [/eqP|] at0.
  move: rat0; rewrite -{}at0 {t0} => raa.
  rewrite [X in subseq _ X](_ : _ = merge r (a :: s) t1)//.
  exact: (subseq_trans (subseq_cons _ _) (ih s IH)).
rewrite [X in subseq _ X](_ : _ = merge r (a :: s) t1)//.
exact: ih.

  rewrite /=; case: ifPn => hsht phss.
  move=> sub_stt.
  have := @omega_max_cons a b f t ht.
  have := (IHs s).
  by rewrite /= eqxx IH.
rewrite /=; case: ifPn => [/eqP|] at0.
  move: rat0; rewrite -{}at0 {t0} => raa.
  rewrite [X in subseq _ X](_ : _ = merge r (a :: s) t1)//.
  exact: (subseq_trans (subseq_cons _ _) (ih s IH)).
rewrite [X in subseq _ X](_ : _ = merge r (a :: s) t1)//.
exact: ih.

elim: t s.
  by move => ? /negP.
move=> x t' IHs s; move/IHs => IHs'.
elim: s IHs' => //.
Admitted.
*)

Import Order.Def.

Lemma omega_max_merge1 a b f s x :
  s != [::] -> path <=%R a s -> last a s == b ->
  a <= x <= b ->
(omega_max a (merge <%R s [:: x]) f <= omega_max a s f)%E.
Proof.
move: s a.
elim => // h s IH a _ pahs lsb.
case: s IH pahs lsb => [_|].
  rewrite /= andbT => /[swap]/eqP -> ab.
  move=> /andP[ax xb].
  rewrite ifN; first by rewrite -leNgt.
  rewrite /omega_max/=.
  rewrite !big_nat_recl//= !big_nil/=.
  rewrite 2!maxeNy.
  rewrite ge_max; apply/andP; split; apply: oscillation_sub.
  - exact: subset_itvl.
  - exact: subset_itvr.
move=> s0 s1 IH.
rewrite [s0 :: s1]lock => /=/andP[ah phs] ls1b /andP[ax xb].
case: ifPn => [hx|].
  rewrite /omega_max/=.
  rewrite !big_nat_recl//=.
  rewrite le_max2//.
  rewrite -lock IH//=.
  - by move: phs; rewrite -lock.
  - by move: ls1b; rewrite -lock.
  - by rewrite xb ltW.
rewrite -leNgt => xh.
rewrite /omega_max/=.
rewrite !big_nat_recl//=.
rewrite maxA le_max2// ge_max; apply/andP; split; apply: oscillation_sub.
- exact: subset_itvl.
- exact: subset_itvr.
Qed.

End omega_max.
