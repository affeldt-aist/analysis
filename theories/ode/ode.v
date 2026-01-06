(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix interval poly.
From mathcomp Require Import generic_quotient ring_quotient.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import constructive_ereal.
From mathcomp Require Import functions reals interval_inference topology.
From mathcomp Require Import prodnormedzmodule tvs normedtype landau.
From mathcomp Require Import ereal sequences derive numfun measure realfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral ftc common.
From mathcomp Require Import contfun.

(**md**************************************************************************)
(* # ODE                                                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Open Scope ring_scope.
Open Scope classical_set_scope.

(* why is this defined here? *)
Section VectorIntegral.
Variable (R : realType).
Variable (d : measure_display).
Variable (T : measurableType d).
Variable (mu : measure T R).
Variable (D : set T).
Variable (n : nat).
Definition vRintegral (f : T -> 'rV[R]_n) : 'rV[R]_n :=
  \row_i (Rintegral mu D (fun x => (f x) ord0 i)).

Lemma vRintegralE (f : T -> 'rV[R]_n) i :
  (vRintegral f) ord0 i = Rintegral mu D (fun x => (f x) ord0 i).
Proof. by rewrite /vRintegral mxE. Qed.
End VectorIntegral.
Notation "\vint [ mu ]_ ( x 'in' D ) F" :=
  (vRintegral mu D (fun x => F))
  (at level 36).

(* first, we define picard_from_cont
   that takes a function continuous over a closed ball *)

(* Definition picard_from_cont' {R : realType} {n : nat} (U := 'rV[R]_n) *)
(*   (u0 : U) (r : R) *)
(*   (B := closed_ball u0 r) *)
(*   (f : R -> U -> U) (g : R -> U) *)
(*     (t0 t1 : R) *)
(*     (imageg : g @` `[t0, t1] `<=` B) : R -> U := *)
(*   fun t => u0 + (\vint[lebesgue_measure]_(x in `[t0, t]) f x (g x))%R. *)
Definition picard_from_cont' {R : realType} (U := R)
  (u0 : U) (r : R)
  (B := closed_ball u0 r)
  (f : R -> U -> U) (g : R -> U)
    (t0 t1 : R)
    (imageg : g @` `[t0, t1] `<=` B) : R -> U :=
  fun t => u0 + (\int[lebesgue_measure]_(x in `[t0, t]) f x (g x))%R.

Section vector_continuous.
Context {R : realType}.

Context {n : nat}.
Let U := 'rV[R]_n.
Lemma within_continuous_vec (h : R -> U) D :
  {within D, continuous h} <-> forall i, {within D, continuous (fun x => (h x) ord0 i)}.
Proof.
split.
- move=> hcont i.

  (* apply/subspace_continuousP => /= x Dx. *)
  (* have /subspace_continuousP/(_ x Dx) := hcont. *)
  (* move => h'. *)
  (* have := (proj1 (cvg_mx_entourageP R 1 n)). *)
  (* apply. *)
Abort.
End vector_continuous.
Section picard_from_cont'.
Context {R : realType}.
(*Variable U : normedModType R.*)
Local Notation mu := lebesgue_measure.
Context {n : nat}.
(* Let U := 'rV[R]_n. *)

Let U := R.
Variables (f : R -> U -> U) (a b : R).
Hypothesis ab : a <= b.
Variables (u0 : U) (r : {posnum R}).

Let B : set U := closed_ball u0 r%:num.

Variable k : R.
Hypothesis k0 : k > 0.
(* properties of the function f defining the differential equation: *)
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (f x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous f ^~ y}}.

Variable g : R -> U (*contFunBallType d0*).
Variable cg : {within `[a, b], continuous g}.
Hypothesis imageg : g @` `[a, b] `<=` B.

Lemma set_fun_picard_from_cont' :
  {homo picard_from_cont' f imageg : x / `[a, b] x >-> [set: U] x}.
Proof. by []. Qed.

HB.instance Definition _ :=
  @isFun.Build (subspace `[a, b]) _ `[a, b] [set: U] (picard_from_cont' f imageg)
    (set_fun_picard_from_cont').

Lemma within_continuous_picard_from_cont' :
  {within `[a, b], continuous (picard_from_cont' f imageg)}.
Proof.
rewrite /picard_from_cont'.
suff: {within `[a, b], continuous (fun t => \int[mu]_(x0 in `[a, t]) f x0 (g x0))}.
  move=> abf x.
  apply: cvgD.
    exact: cvg_cst.
  exact: abf.
move=> /= x.
apply: parameterized_integral_continuous => //.
apply: continuous_compact_integrable; first exact: segment_compact.
move=> {x}.
exact: (within_continuous_lipschitz _ k0 lip2 cont1).
Qed.

(* Lemma within_continuous_picard_from_cont' : *)
(*   {within `[a, b], continuous (picard_from_cont' f imageg)}. *)
(* Proof. *)
(* rewrite /picard_from_cont'. *)
(* suff: {within `[a, b], continuous (fun t => \vint[mu]_(x0 in `[a, t]) f x0 (g x0))}. *)
(*   move=> abf x. *)
(*   apply: cvgD. *)
(*     exact: cvg_cst. *)
(*   exact: abf. *)
(* apply/within_continuous_vec => i. *)
(* have -> : *)
(*   (fun x0 : R => *)
(*      (\vint[mu]_(x1 in `[a, x0]) f x1 (g x1)) ord0 i) *)
(*   = *)
(*   (fun x0 : R => *)
(*      Rintegral mu `[a, x0] (fun x1 => (f x1 (g x1)) ord0 i)). *)
(*   by apply/funext => x0;rewrite vRintegralE.  *)
(* move=> /= x. *)
(* apply: parameterized_integral_continuous => //. *)
(* apply: continuous_compact_integrable; first exact: segment_compact. *)
(* move=> {x}. *)
(* apply within_continuous_vec. *)
(* exact: (within_continuous_tmp ab k0 lip2 cont1). *)
(* Qed. *)

HB.instance Definition _ := isContinuous.Build (subspace `[a, b]) U
  (picard_from_cont' f imageg : subspace _ -> _)
  within_continuous_picard_from_cont'.

HB.about picard_from_cont'.

(*HB.instance Definition _ (g : contFunBallType d)
    (imageg : g @` `[- d, d] `<=` `[- d, d]) :=
  picard_from_cont'_isContinuousFunBuild imageg.*)

(*Local Lemma continuous_picard_from_cont' (g : contFunBallType d)
    (imageg : g @` `[- d, d] `<=` `[- d, d]) :
  {within `[- d, d], continuous picard_from_cont' imageg}.*)
Local Lemma continuous_picard_from_cont' :
  {within `[a, b], continuous picard_from_cont' f imageg}.
Proof. exact: cts_fun. Abort.

End picard_from_cont'.

Section picard_from_cont.
Context {R : realType}.
Context {n : nat}.
(* Let U := 'rV[R]_n. *)

Let U := R.
Variables (f : R -> U -> U) (a b : R).
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.

Definition picard_from_cont
  (k : R) (lcf_x : {in `[a, b]%R, forall x, k.-lipschitz_B (f x)})
  (cf_y : {in B, forall y, {within `[a, b], continuous f ^~ y}})
  (g : R -> U) : R -> U :=
match pselect (g @` `[a, b] `<=` B) with
| left imageg => @picard_from_cont' R u0 r%:num f g a b imageg
| _ => cst 0
end.

End picard_from_cont.

(* second, we define picard_to_cont
   that takes a function continuous over a closed ball
   and returns a function continuous over a closed ball *)
Section picard_to_cont.
Context {R : realType} {n : nat}.

(* Let U := 'rV[R]_n. *)
Let U := R.

Local Notation mu := lebesgue_measure.
Variables (f : R -> U -> U) (a b : R) (k : R).
Hypothesis ab : a < b.
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.
Hypothesis k0 : 0 < k.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (f x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous f ^~ y}}.

Definition hmax : R := sup [set `|f t u0| | t in `[a, b]].

Lemma hmax_ge0 : 0 <= hmax.
Proof. by rewrite /hmax sup_ge0//= => x [y _ <-]. Qed.

(*Variable rho : {nonneg R}. (* rho < 1 *)*)
Variable rho : {posnum R}. (* rho < 1 *)

Definition Delta := Num.min (b - a) (Num.min (r%:num / (k * r%:num + hmax)) (rho%:num / k)).

Lemma lip2_Delta : {in `[a, a + Delta]%R, forall x, k.-lipschitz_B (f x)}.
Proof.
(* TODO: generalize to the subset relation *)
move /in_switch: lip2 => lip2'.
apply /in_switch.
apply: lipschitzW lip2'.
apply: subset_itvl.
by rewrite bnd_simp /Delta -lerBrDl ge_min lexx.
Qed.

Lemma cont1_Delta : {in B, forall y, {within `[a, a + Delta], continuous f ^~ y}}.
Proof.
move=> /= x xB.
apply: continuous_subspaceW; last exact: cont1.
apply: subset_itvl.
by rewrite bnd_simp /Delta -lerBrDl ge_min lexx.
Qed.

Local Notation picard_from_cont_not := (@picard_from_cont _ f a (a + Delta) u0 r k lip2_Delta cont1_Delta).

Lemma Delta_gt0 : 0 < Delta.
Proof.
rewrite lt_min subr_gt0 ab/=.
rewrite lt_min mulr_gt0//=.
  by rewrite divr_gt0//.
rewrite invr_gt0//.
rewrite ltr_wpDr//.
  exact: hmax_ge0.
by rewrite mulr_gt0//.
Qed.

Let aaDelta : a < a + Delta.
Proof. by rewrite ltrDl Delta_gt0. Qed.

Import Cont_on_seg_quot.

Local Notation V := (quot_continuousFunType (ltW aaDelta)).
(* Local Notation Vn := 'rV[V]_n. *)
(* Definition to_fun (g : Vn) : _ -> _ := fun t => (\row_i (g ord0 i t)). *)
Lemma set_fun_picard_from_cont (g : V) :
  set_fun `[a, a + Delta] setT (picard_from_cont_not g).
Proof. by []. Qed.

Definition restrictedV := [set f : V | f @` `[a, a + Delta] `<=` B ].

HB.instance Definition _ (g : V) := @isFun.Build
  (subspace `[a, a + Delta]) _
  `[a, a + Delta] setT (picard_from_cont_not g) (set_fun_picard_from_cont g).

Lemma continuous_picard_from_cont (g : V) :
  {within `[a, a + Delta], continuous (picard_from_cont_not  g)}.
Proof.
have := @cts_fun _ _ g.
rewrite /picard_from_cont; case: pselect => //=.
  move => z cg.
  apply: (@cts_fun (subspace `[a, (a + Delta)])).
  + exact: (ltW aaDelta).
  + exact: k0.
  + exact : lip2_Delta.
  + exact : cont1_Delta.
  + exact : cg.
move => _ _.
apply: continuous_subspaceT => z;apply: cvg_cst.
Qed.

HB.instance Definition _ (g : V) :=
  @isContinuous.Build _ _
     (picard_from_cont_not g : subspace _ -> _)
     (@continuous_picard_from_cont g).

Check fun g : V => picard_from_cont_not g : continuousFunType _ _.

Check fun g : V => (\pi_(V)%qT (picard_from_cont_not g )) : V.

Definition picard_to_cont (x : V) : V := \pi_V%qT (picard_from_cont_not x).

Lemma integrable_comp (F : V) y : y \in `[a, (a + Delta)]%R ->
  [set F x | x in `[a, y]] `<=` closed_ball u0 r%:num ->
  mu.-integrable `[a, y] (EFin \o (fun t : R => f t (F t))).
Proof.
move => yaaDelta ab0r.
apply: continuous_compact_integrable; first exact: segment_compact.
move: (yaaDelta); rewrite  in_itv/= => /andP[ay yaDelta].
apply: (within_continuous_lipschitz _ k0).
- have := @cts_fun _ _ F.
  by apply/continuous_subspaceW/subset_itvl; rewrite bnd_simp.
- apply/in_switch.
  move/in_switch : lip2_Delta.
  by apply/lipschitzW/subset_itvl; rewrite bnd_simp.
- rewrite -/B => x xB.
  have := cont1_Delta xB.
  by apply/continuous_subspaceW/subset_itvl; rewrite bnd_simp.
- exact: ab0r.
Qed.

Lemma set_fun_picard_to_cont : set_fun restrictedV restrictedV picard_to_cont.
Proof.
move=> F.
rewrite /restrictedV/= => invariant _/= [y yaaDelta <-].
rewrite /picard_to_cont.
rewrite /B.
rewrite closed_ball_itv//=.
rewrite in_itv//=.
rewrite [X in _ <= X <= _](_ : _ = (picard_from_cont_not F) y); last first.
  have /eqmod_on_itv : (repr (\pi_(V)%qT (picard_from_cont_not F)) =
       picard_from_cont_not F %[mod V])%qT.
    by rewrite reprK.
  move=> <-//.
  have aDeltab : (a + Delta) <= b.
    by rewrite -lerBrDl ge_min lexx.
  by rewrite inE/=.
rewrite /picard_from_cont/=.
case: pselect => /= abu0r; last first.
  done.
rewrite /picard_from_cont'.
rewrite -ler_distl.
rewrite -addrA subrKC.
rewrite (le_trans (le_normr_Rintegral _ _))//=.
  apply integrable_comp; first by [].
  apply: subset_trans abu0r.
  apply/image_subset/subset_itvl; rewrite bnd_simp.
  by move : yaaDelta; rewrite in_itv /= => /andP[].
have integrable2 : mu.-integrable `[a, y] (EFin \o (fun x => f x (F x))).
  apply integrable_comp => //=.
  apply: subset_trans abu0r.
  apply/image_subset/subset_itvl; rewrite bnd_simp.
  by move : yaaDelta;rewrite in_itv /= => /andP[].
have integrable1 : mu.-integrable `[a, y]
    (fun x : g_sigma_algebraType (R.-ocitv).-measurable =>
     (`|f x (F x) - f x u0|%:E + `|f x u0|%:E)).
  rewrite integrableD//=.
    apply integrable_norm => /=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinD.
    rewrite integrableD //=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinN.
    rewrite integrableN //=.
    apply continuous_compact_integrable => //=; first exact: segment_compact.
    apply /continuous_subspaceW/cont1_Delta.
      apply: subset_itvl; rewrite bnd_simp.
      by move : yaaDelta;rewrite in_itv /= => /andP[].
    rewrite /B inE.
    exact: closed_ballxx.
  apply integrable_norm => /=.
  apply continuous_compact_integrable => //=; first exact: segment_compact.
  apply/continuous_subspaceW/cont1_Delta.
    apply: subset_itvl; rewrite bnd_simp.
    by move : yaaDelta;rewrite in_itv /= => /andP[].
  rewrite /B inE.
  exact: closed_ballxx.
rewrite (@le_trans _ _ (\int[mu]_(x in `[a, y]) (`|f x (F x) - f x u0| + `|f x u0|)))//.
  apply: le_Rintegral => //=.
  - exact: integrable_norm.
  - move=> x xay.
    by rewrite (le_trans _ (ler_normD _ _))// subrK.
rewrite (@le_trans _ _ (\int[mu]_(x in `[a, y]) (k * `|F x - u0| + hmax)))//.
  apply: le_Rintegral => //=.
  - under [x in integrable _ _  x]eq_fun do rewrite EFinD.
    rewrite integrableD //=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinM.
    rewrite integrableMr //=.
    exact: bounded_cst.
    apply integrable_norm => //=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinB.
    rewrite integrableB //=.
    apply continuous_compact_integrable => //; first exact: segment_compact.
    apply /continuous_subspaceW/cts_fun.
    apply: subset_itvl;  rewrite bnd_simp.
    by move : yaaDelta; rewrite in_itv /= => /andP[].
    apply measurable_bounded_integrable => //=.
    rewrite lebesgue_measure_itv //=.
    case: ifPn => //=.
    by rewrite -EFinD ltry.
    exact: bounded_cst.
    apply measurable_bounded_integrable => //=.
    rewrite lebesgue_measure_itv //=.
    case: ifPn => //=.
    by rewrite -EFinD ltry.
    exact: bounded_cst.
  - move=> x xay.
    rewrite lerD//.
      have xaaDelta : x \in `[a, (a + Delta)]%R.
      move : x xay.
      apply: subset_itvl.
      rewrite bnd_simp.
      by rewrite (itvP yaaDelta).
      move/lip2_Delta :  xaaDelta.
      move/(_ (F x, u0)).
      apply.
      split => /=.
        apply: invariant => /=.
        exists x => //.
        move : xay.
        apply: subset_itvl.
        rewrite bnd_simp.
        by rewrite (itvP yaaDelta).
      by apply: closed_ballxx.
    rewrite /hmax.
    rewrite ub_le_sup//.
      have [M [Mb1 Mb2]] : bounded_set [set `|f t u0| | t in `[a,b]].
        apply/compact_bounded/continuous_compact; last exact: segment_compact.
        apply within_continuous_comp_norm.
          by rewrite ltW.
        by apply cont1;rewrite inE;apply: closed_ballxx.
      exists (M + 1) => _ [x0 x0ab] <- /=.
      rewrite -normr_id.
      apply Mb2.
        by rewrite ltrDl.
      by exists x0.
    exists x => //.
    move: xay; rewrite in_itv/= in_itv/= => /andP[] -> /=.
    move/le_trans; apply.
    move : yaaDelta; rewrite in_itv /= => /andP[].
    move => _ /le_trans;apply.
    by rewrite -lerBrDl /Delta ge_min lexx.
rewrite (@le_trans _ _ (\int[mu]_(x in `[a, y]) ((k * r%:num + hmax))))//.
  apply: le_Rintegral => //=.
  - under [x in integrable _ _  x]eq_fun do rewrite EFinD.
    rewrite integrableD //=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinM.
    rewrite integrableMr //=.
    exact: bounded_cst.
    apply integrable_norm => //=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinB.
    rewrite integrableB //=.
    apply continuous_compact_integrable => //.
    exact: segment_compact.
    apply /continuous_subspaceW/cts_fun.
    apply: subset_itvl; rewrite bnd_simp.
    by move : yaaDelta; rewrite in_itv /= => /andP[].
    apply measurable_bounded_integrable => //=.
    rewrite lebesgue_measure_itv //=.
    case: ifPn => //=.
      by rewrite -EFinD ltry.
    exact: bounded_cst.
    apply measurable_bounded_integrable => //=.
    rewrite lebesgue_measure_itv //=.
    case: ifPn => //=.
    by rewrite -EFinD ltry.
    exact: bounded_cst.
  - apply measurable_bounded_integrable => //=.
    rewrite lebesgue_measure_itv //=.
    case: ifPn => //=.
    by rewrite -EFinD ltry.
    exact: bounded_cst.
  - move=> x xay.
    rewrite lerD2r.
    rewrite ler_pM2l//.
    have : B (F x).
      apply: invariant => /=.
      exists x => //.
      move: xay; rewrite !in_itv/= => /andP[] -> /=.
      move /le_trans.
      apply.
      move : yaaDelta.
      rewrite in_itv /= => /andP[].
      by move => _ /le_trans;apply.
      rewrite /B.
      rewrite closed_ball_itv//= in_itv/=.
      by rewrite ler_distl.
rewrite Rintegral_cst//.
rewrite /= (* to remove a reverse_coercion *).
rewrite lebesgue_measure_itv/=.
rewrite lte_fin.
move: (yaaDelta); rewrite in_itv/= => /andP[ya yaDelta].
move: ya.
rewrite le_eqVlt => /predU1P[->| ay].
  by rewrite ltxx/= mulr0//.
rewrite (@le_trans _ _ (((k * r%:num)%R + hmax)%E * Delta))//.
  rewrite ler_wpM2l//.
    by rewrite addr_ge0 ?mulr_ge0 ?(ltW k0)// hmax_ge0.
  rewrite ay//=.
  move: yaaDelta.
  rewrite in_itv/= => /andP[_].
  by rewrite -lerBlDl.
rewrite -ler_pdivlMl//; last first.
  rewrite ltr_pwDl//.
    by rewrite mulr_gt0.
  exact: hmax_ge0.
rewrite 2!ge_min.
by rewrite mulrC lexx/= orbT.
Qed.

Lemma picard_from_cont_simpl g t :
  [set g x | x in `[a, (a + Delta)%E]] `<=` closed_ball u0 r%:num ->
  picard_from_cont_not g t = u0 + (\int[mu]_(x in `[a, t]) f x (g x))%R.
Proof.
rewrite /picard_from_cont_not; case: pselect => [| // ] .
by rewrite /picard_from_cont'.
Qed.

Lemma picard_to_cont_init g :
  [set g x | x in `[a, (a + Delta)%E]] `<=` closed_ball u0 r%:num ->
  picard_from_cont_not g a = u0.
Proof.
move => h.
rewrite picard_from_cont_simpl => //.
by rewrite set_itv1 Rintegral_set1 addr0.
Qed.

Fail Check picard_to_cont : {fun [set: V] >-> [set: V]}.

HB.instance Definition _ :=
    @isFun.Build _ _ _ _ picard_to_cont set_fun_picard_to_cont.

Check picard_to_cont : {fun restrictedV >-> restrictedV}.
(* still, we can't state that it is a contraction for typing reasons *)
Fail Lemma tmp : is_contraction (picard_to_cont
  : {fun [set: W] >-> [set: W]}).
About is_contraction.
End picard_to_cont.

Section picard_to_cont_normedtype4.
Context {R : realType}.
Let U := R.

Variable f : R -> U -> R.
Variable (a b : R).
Hypothesis ab : a < b.
Variable k : R.
Hypothesis k0 : 0 < k.
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (f x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous f ^~ y}}.

Variable rho : {posnum R}. (* rho < 1 *)
Hypothesis rho1 : (rho%:num < 1).

Import Cont_on_seg_quot.

Notation V := (quot_continuousFunType (ltW (aaDelta_subproof f ab u0 r k0 rho))).
Notation Vr := (@restrictedV _ f a b k ab u0 r k0 rho).

HB.about cst.

Check @cst (subspace `[a, a + Delta f a b k u0 r rho]) R u0 : {fun `[a, a + Delta f a b k u0 r rho] >-> [set: R]}.

Check @cst (subspace `[a, a + Delta f a b k u0 r rho]) R u0 : continuousType (subspace `[a, a + Delta f a b k u0 r rho]) R.

(* Check @cst (subspace `[a, a + Delta f a b k u0 r rho]) R u0 : continuousFunType `[a, a + Delta f a b k u0 r rho] [set: R]. *)
Lemma restrictedVball : Vr = @closed_ball R V
  (pi V (@cst (subspace `[a, a + Delta f a b k u0 r rho]) R u0)) r%:num.
Proof.
rewrite closed_ballE => //.
rewrite /Vr.
apply eq_set => /= f' ;apply propext;split => h.
- rewrite -(@reprK _ V f').
  rewrite /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
  rewrite norm_piE.
  apply: infty_norm0_le => /=.
  apply (ltW (aaDelta_subproof f ab u0 r k0 rho)).
  move => x adx.
  move /(_ (f' x)) : h.
  rewrite closed_ballE => //.
  apply.
  exists x => //.
  by rewrite inE in adx.
  move => _ [x xad] <-.
  rewrite closed_ballE => //.
  rewrite /closed_ball_ /=.
  have -> :  (u0 - f' x) = ((pi V (cst u0)) - f' : V) x.
  by rewrite -(@reprK _ V f')  /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add !eval_mod_on_itv => //;rewrite inE.
  rewrite -(@reprK _ V f').
  rewrite /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
  rewrite eval_mod_on_itv;last by rewrite inE.
  rewrite -inE in xad.
  apply: (le_trans (infty_norm0_ge (ltW (aaDelta_subproof f ab u0 r k0 rho)) _ xad)).
  rewrite -(norm_piE (ltW (aaDelta_subproof f ab u0 r k0 rho))).
  by rewrite Quotient.pi_add Quotient.pi_opp reprK.
Qed.

Definition contrac : {fun Vr >-> Vr} :=
  @picard_to_cont R f a b k ab u0 r k0 lip2 cont1 rho.

Lemma set_fun_picard : set_fun Vr Vr contrac.
Proof. by []. Qed.

HB.instance Definition _ := @isFun.Build _ _ Vr Vr contrac set_fun_picard.

(*Hypothesis dtwok : d0%:num < (2 * k)^-1.

Let twodk := (d0%:num * k) *+ 2.

Let twodk_ge0 : 0 <= twodk.
Proof. by rewrite /twodk mulrn_wge0// mulr_ge0// ltW. Qed.*)

Local Notation mu := (@lebesgue_measure _).

(* Lemma reprE (h : V) x : *)
(*   (*x \in `[a, b] ->*) repr h x = h x. *)
(* Proof. *)
(* by []. *)
(* Qed. *)

(* Local Lemma in_itv_cases (x  : R) : x \in `[a, b] ->  x \in `]a, b[ \/ (x = a \/ x = b). *)
(* Proof. *)
(*   rewrite -setUitv1/=; last by rewrite bnd_simp ltW. *)
(*   rewrite -setU1itv/=; last by rewrite bnd_simp . *)
(*   rewrite inE/= in_itv/= => -[[?|?]|?]. *)
(* Qed. *)
Lemma is_contraction_picard_to_cont : is_contraction contrac.
Proof.
rewrite /is_contraction.
rewrite /contraction.
rewrite /contrac.
rewrite /picard_to_cont.
rewrite /picard_from_cont.
rewrite /picard_from_cont'.
exists (NngNum (ge0 rho)); split => //=.
move=> /= [/= x y] [Vrx Vry].
rewrite /picard_to_cont/=.
rewrite !piE/=.
rewrite norm_piE/=.
rewrite /infty_norm0/=.
have aad :   a <= (a + Delta f a b k u0 r rho) by rewrite lerDl ltW// Delta_gt0.
apply: ge_sup => //=.
  set u := _ \o _; exists (u a) => /=; exists a => //.
  by rewrite in_itv/= lexx.
move=> _ /= [t tNdd <-].
have tb : t <= b.
  move: tNdd.
  rewrite in_itv/= => /andP[Ndt].
  move=> /le_trans; apply.
  rewrite -lerBrDl /Delta.
  by rewrite ge_min lexx.
rewrite /picard_from_cont/=.
case: pselect => //= Hg.
case: pselect => [|//].
move=> Hg2.
rewrite /picard_from_cont'/=.
rewrite !fctE.
rewrite (addrC u0).
rewrite addrKA.
have integrable1 :  mu.-integrable `[a, t] (EFin \o(fun x0 => f x0 (x x0))).
  apply integrable_comp => //=.
  move => _ [x0 h] <-.
  apply: Hg => /=.
  exists x0 => //.
  apply /subset_itvl/h.
  rewrite bnd_simp.
  by move: tNdd; rewrite !in_itv/= => /andP[] .

have integrable2 :  mu.-integrable `[a, t] (EFin \o(fun x0 => f x0 (y x0))).
  apply integrable_comp => //=.
  move => _ [x0 h] <-.
  apply: Hg2 => /=.
  exists x0 => //.
  apply /subset_itvl/h.
  rewrite bnd_simp.
  by move: tNdd; rewrite !in_itv/= => /andP[] .
rewrite -RintegralB//=.
rewrite (le_trans (le_normr_Rintegral _ _))//=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinB.
    rewrite integrableB //=.
have integrable3 :   mu.-integrable `[a, t] (fun x0 => `|x x0 - y x0|%:E).
    apply integrable_norm => //=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinB.
    rewrite integrableB //=.
    apply continuous_compact_integrable => //=.
    exact: segment_compact.
    apply /continuous_subspaceW/cts_fun.
    apply: subset_itvl.
    rewrite bnd_simp.
    by move : tNdd;rewrite in_itv /= => /andP[].
    apply continuous_compact_integrable => //=.
    exact: segment_compact.
    apply /continuous_subspaceW/cts_fun.
    apply: subset_itvl.
    rewrite bnd_simp.
    by move : tNdd;rewrite in_itv /= => /andP[].
rewrite (@le_trans _ _ (k * \int[mu]_(t0 in `[a, t]) `| x t0 - y t0|))//.
  rewrite (@le_trans _ _ (\int[mu]_(t0 in `[a, t]) (k * `|x t0 - y t0|)))//.
    apply: le_Rintegral => //=.
      apply integrable_norm => //=.
      under [x in integrable _ _  x]eq_fun do rewrite EFinB.
      rewrite integrableB //=.
      under [x in integrable _ _  x]eq_fun do rewrite EFinM.
      rewrite integrableMr //=.
      exact: bounded_cst.
    move=> x0 x0at.
    have : x0 \in `[a, b]%R by apply /subset_itvl/x0at.
    move/lip2.
    rewrite /dominated_by/= => /(_ (x x0, y x0)) /=.
    apply; split.
      apply: Vrx => /=.
      exists x0 => //.
      apply /subset_itvl/x0at.
      move: tNdd.
      by rewrite in_itv/= => /andP[Ndt].
    apply: Hg2 => /=.
    exists x0 => //.
    apply /subset_itvl/x0at.
    move: tNdd.
    by rewrite in_itv/= => /andP[Ndt].
  rewrite RintegralZl//=.
rewrite (@le_trans _ _ (k * \int[mu]_(t0 in `[a, t]) `|x - y| ))//.
  rewrite ler_pM2l//.
  apply: le_Rintegral => //=.
  apply measurable_bounded_integrable => //=.
  rewrite lebesgue_measure_itv //=.
  case: ifPn => //=.
  by rewrite -EFinD ltry.
  exact: bounded_cst.
  move => x0 x0at .
  have x0ad :   x0 \in `[a, (a + Delta f a b k u0 r rho)%E].
    rewrite inE.
    rewrite inE in x0at.
    apply /subset_itvl/x0at.
    move: tNdd.
    by rewrite in_itv/= => /andP[Ndt].
  have -> : x x0 - y x0 = (x - y : V) x0.
    apply (@eqmod_on_itv _ _ _ _ (ltW (aaDelta_subproof f ab u0 r k0 rho)) (repr x - repr y)) => //.
    by rewrite Quotient.pi_add Quotient.pi_opp !reprK //.
  exact: infty_norm0_ge.
rewrite (@le_trans _ _ (k * `|x - y| * (t - a)))//.
rewrite -mulrA ler_wpM2l//; first exact: ltW.
  rewrite Rintegral_cst//.
  rewrite ler_pM => //.
  move: tNdd.
  rewrite in_itv/= => /andP[+ _].
  rewrite le_eqVlt => /predU1P[-> | ].
  by rewrite set_itv1 lebesgue_measure_set1 subrr lexx.
  rewrite /= (lebesgue_measure_itv `[a,t]%R) /= lte_fin => -> //.
rewrite [leLHS]mulrAC.
rewrite ler_wpM2r//.
move: tNdd.
rewrite in_itv/= => /andP[Ndt].
rewrite -lerBlDl.
rewrite /Delta !le_min => /andP[_ /andP[_]].
by rewrite ler_pdivlMr// mulrC.
Qed.

End picard_to_cont_normedtype4.

Section picard.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
Let U := R.

Variables (f : R -> U -> R) (a b : R) (k : R) (u0 : U) (r : {posnum R}).
Hypothesis ab : a < b.
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (f x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous f ^~ y}}.
Variable rho : {posnum R}.
Hypothesis rho1 : (rho%:num < 1).
(*Variable y_ : R -> R.
Hypothesis y_init_t : y_ 0 = 0.*)

(*Hypothesis dtwok : d0%:num < (2 * k)^-1.*)

Definition tmp : is_contraction (contrac ab k0 lip2 cont1 rho) :=
  (@is_contraction_picard_to_cont R f a b ab k k0 u0 r lip2 cont1 rho rho1).

Import Cont_on_seg_quot.

Notation V := (quot_continuousFunType (ltW (aaDelta_subproof f ab u0 r k0 rho))).

Lemma Vr0 : (@restrictedV _ f a _ k _ u0 r k0 rho : set V) !=set0.
Proof.
exists (pi V (cst u0)).
move => _ [y x0] <-.
suff -> : quot_continuousFunType_to_fun  (\pi_(V)%qT (cst u0)) y = u0.
  exact: closed_ballxx.
rewrite /quot_continuousFunType_to_fun/=.
have /eqmod_on_itv : (repr (\pi_(V)%qT (cst u0)) = cst u0 %[mod V])%qT by rewrite reprK.
apply.
by rewrite inE.
Qed.

Notation Vr := (@restrictedV _ f a b k ab u0 r k0 rho).
Lemma closed_Vr : closed Vr.
Proof. by rewrite restrictedVball; exact: closed_ball_closed. Qed.

Let phioo : V :=
  sval (cid2 (@banach_fixed_point R V Vr
  (@contrac _ f a b ab _ k0 u0 r lip2 cont1 rho)
  (@is_contraction_picard_to_cont _ f _ _ ab _ k0 u0 r lip2 cont1 rho rho1)
  closed_Vr
  Vr0)).

Let phiooE : phioo = (@contrac _ f a b ab _ k0 u0 r lip2 cont1 rho) phioo.
Proof. by rewrite {}/phioo; case: cid2. Qed.

Lemma contrac_simpl g t : Vr g ->  t \in `[a, (a + Delta f a b k u0 r rho)%E] ->
  (@contrac _ f a b ab _ k0 u0 r lip2 cont1 rho) g t =
  u0 + (\int[mu]_(x in `[a, t]) f x (g x))%R.
Proof.
by move=> Vrg taad; rewrite /contrac eval_mod_on_itv //; exact: picard_from_cont_simpl.
Qed.

Theorem picard_lindelof_existence : phioo a = u0 /\
  {in `]a, a + Delta f a b k u0 r rho[, forall x, phioo^`() x = f x (phioo x)}.
Proof.
have Vrphioo : Vr phioo.
  by apply (svalP (cid2 (banach_fixed_point (is_contraction_picard_to_cont ab k0 lip2 cont1 rho1) closed_Vr Vr0))).
split.
- rewrite phiooE.
  rewrite /contrac.
  rewrite eval_mod_on_itv; last by rewrite inE/= in_itv/= lexx (ltW (aaDelta_subproof f ab u0 r k0 rho)).
  rewrite /picard_from_cont /= picard_to_cont_init //.
  move => t tad.
  rewrite {1}phiooE.
  have altd:  a < (a + Delta f a b k u0 r rho)%E by rewrite ltrDl Delta_gt0.
  suff -> :  (contrac ab k0 lip2 cont1 rho phioo)^`() t =  (fun x0 => (u0 + (\int[mu]_(x in `[a, x0]) f x (phioo x))%R))^`()  t.
    move : (tad).
    rewrite inE /= in_itv /= => /andP[ta taDelta].
    have Fint :  (mu.-integrable `[a, (a + Delta f a b k u0 r rho)%E] (EFin \o (fun x : R => f x (phioo x)))).
      apply integrable_comp => //.
      by rewrite   in_itv /= lexx ltW.
    have Fcont :  {for t, continuous (fun x0 : R => f x0 (phioo x0))}.
      rewrite inE in tad.
      apply: (within_continuous_continuous _ _ tad) => //.
      apply: (within_continuous_lipschitz _ k0 _ (u0 := u0) (r := r)).
      exact: cts_fun.
      exact: lip2_Delta.
      exact: cont1_Delta.
      exact: Vrphioo.
    have [H1 H2] := @continuous_FTC1_closed _ (fun x => f x (phioo x)) a t _ taDelta Fint ta Fcont.
    rewrite derive1E deriveD /=;last 2 first.
    exact: derivable_cst.
    exact: H1.
    rewrite -!derive1E.
    rewrite H2.
    by rewrite derive1_cst add0r.
rewrite /contrac/picard_to_cont/picard_from_cont.
move : t tad.
apply : eq_on_itv_deriv.
move => t tad /=.
rewrite -(@picard_from_cont_simpl _ _ a  b k _ r lip2 cont1 rho) //=.
rewrite eval_mod_on_itv => //.
by rewrite inE;apply: subset_itv_oo_cc;rewrite -inE.
Qed.

End picard.
