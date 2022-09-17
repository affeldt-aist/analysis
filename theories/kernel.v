(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral.

(******************************************************************************)
(*                                  Kernels                                   *)
(*                                                                            *)
(* This file provides a formation of kernels and extends the theory of        *)
(* measures with, e.g., Tonelli-Fubini's theorem for s-finite measures.       *)
(*                                                                            *)
(*   finite_measure mu == the measure mu is finite                            *)
(*  sfinite_measure mu == the measure mu is s-finite                          *)
(*       R.-ker X ~> Y == kernel                                              *)
(*             kseries == countable sum of kernels                            *)
(*     R.-sfker X ~> Y == s-finite kernel                                     *)
(*      R.-fker X ~> Y == finite kernel                                       *)
(*     R.-spker X ~> Y == subprobability kernel                               *)
(*      R.-pker X ~> Y == probability kernel                                  *)
(*      kprobability m == kernel defined by a probability measure             *)
(*           kdirac mf == kernel defined by a measurable function             *)
(*          kadd k1 k2 == lifting of the addition of measures to kernels      *)
(*        mnormalize f == normalization of a kernel to a probability          *)
(*              l \; k == composition of kernels                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(* PR 516 in progress *)
HB.mixin Record isProbability (d : measure_display) (T : measurableType d)
  (R : realType) (P : set T -> \bar R) of isMeasure d R T P :=
  { probability_setT : P setT = 1%E }.

#[short(type=probability)]
HB.structure Definition Probability (d : measure_display) (T : measurableType d)
    (R : realType) :=
  {P of isProbability d T R P & isMeasure d R T P }.

Section probability_lemmas.
Variables (d : _) (T : measurableType d) (R : realType) (P : probability T R).

Lemma probability_le1 (A : set T) : measurable A -> (P A <= 1)%E.
Proof.
move=> mA; rewrite -(@probability_setT _ _ _ P).
by apply: le_measure => //; rewrite ?in_setE.
Qed.

End probability_lemmas.
(* /PR 516 in progress *)

(* TODO: PR *)
Lemma setT0 (T : pointedType) : setT != set0 :> set T.
Proof. by apply/eqP => /seteqP[] /(_ point) /(_ Logic.I). Qed.

Lemma set_unit (A : set unit) : A = set0 \/ A = setT.
Proof.
have [->|/set0P[[] Att]] := eqVneq A set0; [by left|right].
by apply/seteqP; split => [|] [].
Qed.

Lemma set_boolE (B : set bool) : [\/ B == [set true], B == [set false], B == set0 | B == setT].
Proof.
have [Bt|Bt] := boolP (true \in B).
  have [Bf|Bf] := boolP (false \in B).
    have -> : B = setT.
      by apply/seteqP; split => // -[] _; [rewrite inE in Bt| rewrite inE in Bf].
    by apply/or4P; rewrite eqxx/= !orbT.
  have -> : B = [set true].
      apply/seteqP; split => -[]//=.
        by rewrite notin_set in Bf.
      by rewrite inE in Bt.
  by apply/or4P; rewrite eqxx.
have [Bf|Bf] := boolP (false \in B).
  have -> : B = [set false].
    apply/seteqP; split => -[]//=.
      by rewrite notin_set in Bt.
    by rewrite inE in Bf.
  by apply/or4P; rewrite eqxx/= orbT.
have -> : B = set0.
  apply/seteqP; split => -[]//=.
    by rewrite notin_set in Bt.
  by rewrite notin_set in Bf.
by apply/or4P; rewrite eqxx/= !orbT.
Qed.

Canonical unit_pointedType := PointedType unit tt.

Section discrete_measurable_unit.

Definition discrete_measurable_unit : set (set unit) := [set: set unit].

Let discrete_measurable0 : discrete_measurable_unit set0. Proof. by []. Qed.

Let discrete_measurableC X :
  discrete_measurable_unit X -> discrete_measurable_unit (~` X).
Proof. by []. Qed.

Let discrete_measurableU (F : (set unit)^nat) :
  (forall i, discrete_measurable_unit (F i)) ->
  discrete_measurable_unit (\bigcup_i F i).
Proof. by []. Qed.

HB.instance Definition _ := @isMeasurable.Build default_measure_display unit
  (Pointed.class _) discrete_measurable_unit discrete_measurable0
  discrete_measurableC discrete_measurableU.

End discrete_measurable_unit.

Section discrete_measurable_bool.

Definition discrete_measurable_bool : set (set bool) := [set: set bool].

Let discrete_measurable0 : discrete_measurable_bool set0. Proof. by []. Qed.

Let discrete_measurableC X :
  discrete_measurable_bool X -> discrete_measurable_bool (~` X).
Proof. by []. Qed.

Let discrete_measurableU (F : (set bool)^nat) :
  (forall i, discrete_measurable_bool (F i)) ->
  discrete_measurable_bool (\bigcup_i F i).
Proof. by []. Qed.

HB.instance Definition _ := @isMeasurable.Build default_measure_display bool
  (Pointed.class _) discrete_measurable_bool discrete_measurable0
  discrete_measurableC discrete_measurableU.

End discrete_measurable_bool.

Lemma measurable_curry (T1 T2 : Type) (d : _) (T : semiRingOfSetsType d)
    (G : T1 * T2 -> set T) (x : T1 * T2) :
  measurable (G x) <-> measurable (curry G x.1 x.2).
Proof. by case: x. Qed.

Lemma emeasurable_itv (R : realType) (i : nat) :
  measurable (`[(i%:R)%:E, (i.+1%:R)%:E[%classic : set \bar R).
Proof.
rewrite -[X in measurable X]setCK.
apply: measurableC.
rewrite set_interval.setCitv /=.
apply: measurableU.
  exact: emeasurable_itv_ninfty_bnd.
exact: emeasurable_itv_bnd_pinfty.
Qed.

Lemma measurable_fun_fst (d1 d2 : _) (T1 : measurableType d1)
  (T2 : measurableType d2) : measurable_fun setT (@fst T1 T2).
Proof.
have := @measurable_fun_id _ [the measurableType _ of (T1 * T2)%type] setT.
by move=> /prod_measurable_funP[].
Qed.

Lemma measurable_fun_snd (d1 d2 : _) (T1 : measurableType d1)
  (T2 : measurableType d2) : measurable_fun setT (@snd T1 T2).
Proof.
have := @measurable_fun_id _ [the measurableType _ of (T1 * T2)%type] setT.
by move=> /prod_measurable_funP[].
Qed.

Definition swap (T1 T2 : Type) (x : T1 * T2) := (x.2, x.1).

Lemma measurable_fun_swap d d' (X : measurableType d) (Y : measurableType d') :
  measurable_fun [set: X * Y] (@swap X Y).
Proof.
by apply/prod_measurable_funP => /=; split;
  [exact: measurable_fun_snd|exact: measurable_fun_fst].
Qed.

Section measurable_fun_pair.
Variables (d d2 d3 : _) (X : measurableType d) (Y : measurableType d2)
  (Z : measurableType d3).

Lemma measurable_fun_pair (f : X -> Y) (g : X -> Z) :
  measurable_fun setT f -> measurable_fun setT g ->
  measurable_fun setT (fun x => (f x, g x)).
Proof. by move=> mf mg; apply/prod_measurable_funP. Qed.

End measurable_fun_pair.

Section measurable_fun_comp.
Variables (d1 d2 d3 : measure_display).
Variables (T1 : measurableType d1).
Variables (T2 : measurableType d2).
Variables (T3 : measurableType d3).

(* NB: this generalizes MathComp-Analysis' measurable_fun_comp *)
Lemma measurable_fun_comp' F (f : T2 -> T3) E (g : T1 -> T2) :
  measurable F ->
  g @` E `<=` F ->
  measurable_fun F f -> measurable_fun E g -> measurable_fun E (f \o g).
Proof.
move=> mF FgE mf mg /= mE A mA.
rewrite comp_preimage.
rewrite [X in measurable X](_ : _ = E `&` g @^-1` (F `&` f @^-1` A)); last first.
  apply/seteqP; split=> [|? [?] []//].
  by move=> x/= [Ex Afgx]; split => //; split => //; exact: FgE.
by apply/mg => //; exact: mf.
Qed.

End measurable_fun_comp.

Lemma measurable_fun_if (d d' : _) (X : measurableType d)
    (Y : measurableType d') (x y : X -> Y) D (md : measurable D)
    (f : X -> bool) (mf : measurable_fun setT f) :
  measurable_fun (D `&` (f @^-1` [set true])) x ->
  measurable_fun (D `&` (f @^-1` [set false])) y ->
  measurable_fun D (fun t => if f t then x t else y t).
Proof.
move=> mx my /= _ B mB.
have mDf : measurable (D `&` [set b | f b]).
  apply: measurableI => //.
  rewrite [X in measurable X](_ : _ = f @^-1` [set true])//.
  by have := mf measurableT [set true]; rewrite setTI; exact.
have := mx mDf _ mB.
have mDNf : measurable (D `&` f @^-1` [set false]).
  apply: measurableI => //.
  by have := mf measurableT [set false]; rewrite setTI; exact.
have := my mDNf _ mB.
move=> yB xB.
rewrite (_ : _ @^-1` B =
    ((f @^-1` [set true]) `&` (x @^-1` B) `&` (f @^-1` [set true])) `|`
    ((f @^-1` [set false]) `&` (y @^-1` B) `&` (f @^-1` [set false]))); last first.
  apply/seteqP; split=> [t /=| t].
    by case: ifPn => ft; [left|right].
  by move=> /= [|]; case: ifPn => ft; case=> -[].
rewrite setIUr; apply: measurableU.
- rewrite -(setIid D) -(setIA D) setICA setIA.
  by apply: measurableI => //; rewrite setIA.
- rewrite -(setIid D) -(setIA D) setICA setIA.
  by apply: measurableI => //; rewrite setIA.
Qed.

Lemma measurable_fun_ifT (d d' : _) (X : measurableType d)
    (Y : measurableType d') (x y : X -> Y) (f : X -> bool)
    (mf : measurable_fun setT f) :
  measurable_fun setT x -> measurable_fun setT y ->
  measurable_fun setT (fun t => if f t then x t else y t).
Proof.
by move=> mx my; apply: measurable_fun_if => //;
  [exact: measurable_funS mx|exact: measurable_funS my].
Qed.

Lemma measurable_fun_if_pair (d d' : _) (X : measurableType d)
    (Y : measurableType d') (x y : X -> Y) :
  measurable_fun setT x -> measurable_fun setT y ->
  measurable_fun setT (fun tb => if tb.2 then x tb.1 else y tb.1).
Proof.
move=> mx my.
have {}mx : measurable_fun [set: X * bool] (x \o fst).
  by apply: measurable_fun_comp => //; exact: measurable_fun_fst.
have {}my : measurable_fun [set: X * bool] (y \o fst).
  by apply: measurable_fun_comp => //; exact: measurable_fun_fst.
by apply: measurable_fun_ifT => //=; exact: measurable_fun_snd.
Qed.

Lemma measurable_fun_opp (R : realType) : measurable_fun [set: R] -%R.
Proof.
apply: continuous_measurable_fun.
by have := (@opp_continuous R [the normedModType R of R^o]).
Qed.

Section integralM_0ifneg.
Local Open Scope ereal_scope.
Variables (d : _) (T : measurableType d) (R : realType).
Variables (m : {measure set T -> \bar R}) (D : set T) (mD : measurable D).

Lemma integralM_0ifneg (f : R -> T -> \bar R) (k : R)
  (f0 : forall r t, D t -> 0 <= f r t) :
  ((k < 0)%R -> f k = cst 0%E) -> measurable_fun setT (f k) ->
  \int[m]_(x in D) (k%:E * (f k) x) = k%:E * \int[m]_(x in D) ((f k) x).
Proof.
move=> fk0 mfk; have [k0|k0] := ltP k 0%R.
  rewrite (eq_integral (cst 0%E)) ?integral0 ?mule0; last first.
    by move=> x _; rewrite fk0// mule0.
  rewrite (eq_integral (cst 0%E)) ?integral0 ?mule0// => x _.
  by rewrite fk0// indic0.
rewrite ge0_integralM//.
- by apply/(@measurable_funS _ _ _ _ setT) => //.
- by move=> y Dy; rewrite f0.
Qed.

End integralM_0ifneg.
Arguments integralM_0ifneg {d T R} m {D} mD f.

Section fubini_tonelli.
Local Open Scope ereal_scope.
Variables (d1 d2 : measure_display).
Variables (T1 : measurableType d1) (T2 : measurableType d2) (R : realType).
Variables (m1 : {measure set T1 -> \bar R}) (m2 : {measure set T2 -> \bar R}).
Hypotheses (sm1 : sigma_finite setT m1) (sm2 : sigma_finite setT m2).
Variables (f : T1 * T2 -> \bar R) (f0 : forall xy, 0 <= f xy).
Variables (mf : measurable_fun setT f).

Lemma fubini_tonelli :
  \int[m1]_x \int[m2]_y f (x, y) = \int[m2]_y \int[m1]_x f (x, y).
Proof. by rewrite -fubini_tonelli1// fubini_tonelli2. Qed.

End fubini_tonelli.
(* /TODO: PR *)

Definition finite_measure d (T : measurableType d) (R : realType)
    (mu : set T -> \bar R) :=
  mu setT < +oo.

Definition sfinite_measure d (T : measurableType d) (R : realType)
    (mu : set T -> \bar R) :=
  exists2 mu_ : {measure set T -> \bar R}^nat,
    forall n, finite_measure (mu_ n) & forall U, measurable U -> mu U = mseries mu_ 0 U.

Lemma finite_measure_sigma_finite d (T : measurableType d) (R : realType)
  (mu : {measure set T -> \bar R}) :
  finite_measure mu -> sigma_finite setT mu.
Proof.
exists (fun i => if i \in [set 0%N] then setT else set0).
  by rewrite -bigcup_mkcondr setTI bigcup_const//; exists 0%N.
move=> n; split; first by case: ifPn.
by case: ifPn => // _; rewrite ?measure0//; exact: finite_measure.
Qed.

Section sfinite_fubini.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d') (R : realType).
Variables (m1 : {measure set X -> \bar R}) (sfm1 : sfinite_measure m1).
Variables (m2 : {measure set Y -> \bar R}) (sfm2 : sfinite_measure m2).
Variables (f : X * Y -> \bar R) (f0 : forall xy, 0 <= f xy).
Variable (mf : measurable_fun setT f).

Lemma sfinite_fubini :
  \int[m1]_x \int[m2]_y f (x, y) = \int[m2]_y \int[m1]_x f (x, y).
Proof.
have [m1_ fm1 m1E] := sfm1.
have [m2_ fm2 m2E] := sfm2.
rewrite [LHS](eq_measure_integral [the measure _ _ of mseries m1_ 0]); last first.
  by move=> A mA _; rewrite m1E.
transitivity (\int[[the measure _ _ of mseries m1_ 0]]_x
    \int[[the measure _ _ of mseries m2_ 0]]_y f (x, y)).
  by apply eq_integral => x _; apply: eq_measure_integral => U mA _; rewrite m2E.
transitivity (\sum_(n <oo) \int[m1_ n]_x \sum_(m <oo) \int[m2_ m]_y f (x, y)).
  rewrite ge0_integral_measure_series; [|by []| |]; last 2 first.
    by move=> t _; exact: integral_ge0.
    rewrite [X in measurable_fun _ X](_ : _ =
        fun x => \sum_(n <oo) \int[m2_ n]_y f (x, y)); last first.
      apply/funext => x.
      by rewrite ge0_integral_measure_series//; exact/measurable_fun_prod1.
    apply: ge0_emeasurable_fun_sum; first by move=> k x; exact: integral_ge0.
    move=> k; apply: measurable_fun_fubini_tonelli_F => //=.
    exact: finite_measure_sigma_finite.
  apply: eq_nneseries => n _; apply eq_integral => x _.
  by rewrite ge0_integral_measure_series//; exact/measurable_fun_prod1.
transitivity (\sum_(n <oo) \sum_(m <oo) \int[m1_ n]_x \int[m2_ m]_y f (x, y)).
  apply eq_nneseries => n _.
  rewrite integral_sum//.
    move=> m; apply: measurable_fun_fubini_tonelli_F => //=.
    exact: finite_measure_sigma_finite.
  by move=> m x _; exact: integral_ge0.
transitivity (\sum_(n <oo) \sum_(m <oo) \int[m2_ m]_y \int[m1_ n]_x f (x, y)).
  apply eq_nneseries => n _; apply eq_nneseries => m _.
  by rewrite fubini_tonelli//; exact: finite_measure_sigma_finite.
transitivity (\sum_(n <oo) \int[[the measure _ _ of mseries m2_ 0]]_y \int[m1_ n]_x f (x, y)).
  apply eq_nneseries => n _ /=.  rewrite ge0_integral_measure_series//.
    by move=> y _; exact: integral_ge0.
  apply: measurable_fun_fubini_tonelli_G => //=.
  by apply: finite_measure_sigma_finite; exact: fm1.
transitivity (\int[[the measure _ _ of mseries m2_ 0]]_y \sum_(n <oo) \int[m1_ n]_x f (x, y)).
  rewrite integral_sum//.
    move=> n; apply: measurable_fun_fubini_tonelli_G => //=.
    by apply: finite_measure_sigma_finite; exact: fm1.
  by move=> n y _; exact: integral_ge0.
transitivity (\int[[the measure _ _ of mseries m2_ 0]]_y
              \int[[the measure _ _ of mseries m1_ 0]]_x f (x, y)).
  apply eq_integral => y _.
  by rewrite ge0_integral_measure_series//; exact/measurable_fun_prod2.
transitivity (\int[m2]_y \int[mseries m1_ 0]_x f (x, y)).
  by apply eq_measure_integral => A mA _ /=; rewrite m2E.
by apply eq_integral => y _; apply eq_measure_integral => A mA _ /=; rewrite m1E.
Qed.

End sfinite_fubini.
Arguments sfinite_fubini {d d' X Y R m1} _ {m2} _ f.

Reserved Notation "R .-ker X ~> Y" (at level 42, format "R .-ker  X  ~>  Y").
Reserved Notation "R .-sfker X ~> Y" (at level 42, format "R .-sfker  X  ~>  Y").
Reserved Notation "R .-fker X ~> Y" (at level 42, format "R .-fker  X  ~>  Y").
Reserved Notation "R .-spker X ~> Y" (at level 42, format "R .-spker  X  ~>  Y").
Reserved Notation "R .-pker X ~> Y" (at level 42, format "R .-pker  X  ~>  Y").

HB.mixin Record isKernel d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) :=
  { measurable_kernel : forall U, measurable U -> measurable_fun setT (k ^~ U) }.

#[short(type=kernel)]
HB.structure Definition Kernel
    d d' (X : measurableType d) (Y : measurableType d') (R : realType) :=
  { k & isKernel _ _ X Y R k }.
Notation "R .-ker X ~> Y" := (kernel X Y R).

Arguments measurable_kernel {_ _ _ _ _} _.

Section kseries.
Variables (d d' : measure_display) (R : realType).
Variables (X : measurableType d) (Y : measurableType d').
Variable k : (R.-ker X ~> Y)^nat.

Definition kseries : X -> {measure set Y -> \bar R} :=
  fun x => [the measure _ _ of mseries (k ^~ x) 0].

Lemma measurable_fun_kseries (U : set Y) :
  measurable U ->
  measurable_fun setT (kseries ^~ U).
Proof.
move=> mU.
by apply: ge0_emeasurable_fun_sum => // n; exact/measurable_kernel.
Qed.

HB.instance Definition _ :=
  isKernel.Build _ _ _ _ _ kseries measurable_fun_kseries.

End kseries.

Lemma integral_kseries
  (d d' : _) (X : measurableType d) (Y : measurableType d')
  (R : realType) (k : (R.-ker X ~> Y)^nat) (f : Y -> \bar R) x :
  (forall y, 0 <= f y) ->
  measurable_fun setT f ->
  \int[kseries k x]_y (f y) = \sum_(i <oo) \int[k i x]_y (f y).
Proof.
by move=> f0 mf; rewrite /kseries/= ge0_integral_measure_series.
Qed.

Section measure_fam_uub.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variables (R : numFieldType) (k : X -> {measure set Y -> \bar R}).

Definition measure_fam_uub := exists r, forall x, k x [set: Y] < r%:E.

Lemma measure_fam_uubP : measure_fam_uub <->
  exists r : {posnum R}, forall x, k x [set: Y] < r%:num%:E.
Proof.
split => [|] [r kr]; last by exists r%:num.
suff r_gt0 : (0 < r)%R by exists (PosNum r_gt0).
by rewrite -lte_fin; apply: (le_lt_trans _ (kr point)).
Qed.

End measure_fam_uub.

HB.mixin Record Kernel_isSFinite_subdef
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) := {
  sfinite_subdef : exists2 s : (R.-ker X ~> Y)^nat,
    forall n, measure_fam_uub (s n) &
    forall x U, measurable U -> k x U = kseries s x U }.

#[short(type=sfinite_kernel)]
HB.structure Definition SFiniteKernel
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) :=
  {k of Kernel_isSFinite_subdef _ _ X Y R k & isKernel d d' X Y R k }.
Notation "R .-sfker X ~> Y" := (sfinite_kernel X Y R).

Arguments sfinite_subdef {_ _ _ _ _} _.

HB.mixin Record SFiniteKernel_isFinite
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) :=
  { measure_uub : measure_fam_uub k }.

#[short(type=finite_kernel)]
HB.structure Definition FiniteKernel
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) :=
  {k of SFiniteKernel_isFinite _ _ X Y R k & @SFiniteKernel _ _ X Y R k }.
Notation "R .-fker X ~> Y" := (finite_kernel X Y R).

Arguments measure_uub {_ _ _ _ _} _.

HB.factory Record Kernel_isFinite d d' (X : measurableType d)
    (Y : measurableType d') (R : realType) (k : X -> {measure set Y -> \bar R}) of isKernel _ _ _ _ _ k := {
  measure_uub : measure_fam_uub k }.

Section kzero.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variable R : realType.

Definition kzero : X -> {measure set Y -> \bar R} :=
  fun _ : X => [the measure _ _ of mzero].

Let measurable_fun_kzero U : measurable U ->
  measurable_fun setT (kzero ^~ U).
Proof. by move=> ?/=; exact: measurable_fun_cst. Qed.

HB.instance Definition _ :=
  @isKernel.Build _ _ X Y R kzero measurable_fun_kzero.

(*Let kernel_from_mzero_sfinite0 : exists2 s : (R.-ker T' ~> T)^nat, forall n, measure_fam_uub (s n) &
    forall x U, measurable U -> kernel_from_mzero x U = kseries s x U.
Proof.
exists (fun=> [the _.-ker _ ~> _ of kernel_from_mzero]).
  move=> _.
  by exists 1%R => y; rewrite /= /mzero.
by move=> t U mU/=; rewrite /mseries nneseries0.
Qed.

HB.instance Definition _ :=
  @isSFinite0.Build _ _ _ T R kernel_from_mzero
  kernel_from_mzero_sfinite0.*)

Lemma kzero_uub : measure_fam_uub kzero.
Proof. by exists 1%R => /= t; rewrite /mzero/=. Qed.

(*HB.instance Definition _ :=
  @SFiniteKernel_isFinite.Build _ _ _ T R kernel_from_mzero
  kernel_from_mzero_uub.*)

End kzero.

HB.builders Context d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) k of Kernel_isFinite d d' X Y R k.

Lemma sfinite_finite :
  exists2 k_ : (R.-ker _ ~> _)^nat, forall n, measure_fam_uub (k_ n) &
    forall x U, measurable U -> k x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof.
exists (fun n => if n is O then [the _.-ker _ ~> _ of k] else
  [the _.-ker _ ~> _ of @kzero _ _ X Y R]).
  by case => [|_]; [exact: measure_uub|exact: kzero_uub].
move=> t U mU/=; rewrite /mseries.
rewrite (nneseries_split 1%N)// big_ord_recl/= big_ord0 adde0.
rewrite ereal_series (@eq_nneseries _ _ (fun=> 0%E)); last by case.
by rewrite nneseries0// adde0.
Qed.

HB.instance Definition _ := @Kernel_isSFinite_subdef.Build d d' X Y R k sfinite_finite.

HB.instance Definition _ := @SFiniteKernel_isFinite.Build  d d' X Y R k measure_uub.

HB.end.

Section sfinite.
Variables (d d' :  _) (X : measurableType d) (Y : measurableType d').
Variables (R : realType) (k : R.-sfker X ~> Y).

Let s : (X -> {measure set Y -> \bar R})^nat :=
  let: exist2 x _ _ := cid2 (sfinite_subdef k) in x.

Let ms n : @isKernel d d' X Y R (s n).
Proof.
split; rewrite /s; case: cid2 => /= s' s'_uub kE.
exact: measurable_kernel.
Qed.

HB.instance Definition _ n := ms n.

Let s_uub n : measure_fam_uub (s n).
Proof. by rewrite /s; case: cid2. Qed.

HB.instance Definition _ n :=
  @Kernel_isFinite.Build d d' X Y R (s n) (s_uub n).

Lemma sfinite : exists s : (R.-fker X ~> Y)^nat,
  forall x U, measurable U -> k x U = kseries s x U.
Proof.
exists (fun n => [the _.-fker _ ~> _ of s n]) => x U mU.
by rewrite /s /= /s; by case: cid2 => ? ? ->.
Qed.

End sfinite.

HB.instance Definition _ (d d' : _) (X : measurableType d)
    (Y : measurableType d') (R : realType) :=
  @Kernel_isFinite.Build _ _ _ _ R (@kzero _ _ X Y R)
                                   (@kzero_uub _ _ X Y R).

HB.factory Record Kernel_isSFinite d d' (X : measurableType d)
    (Y : measurableType d') (R : realType) (k : X -> {measure set Y -> \bar R})
    of isKernel _ _ _ _ _ k := {
  sfinite : exists s : (R.-fker X ~> Y)^nat,
    forall x U, measurable U -> k x U = kseries s x U }.

HB.builders Context d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) k of Kernel_isSFinite d d' X Y R k.

Lemma sfinite_subdef : Kernel_isSFinite_subdef d d' X Y R k.
Proof.
split; have [s sE] := sfinite; exists s => //.
by move=> n; exact: measure_uub.
Qed.

HB.instance Definition _ := (*@isSFinite0.Build d d' X Y R k*) sfinite_subdef.

HB.end.

HB.mixin Record FiniteKernel_isSubProbability
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) :=
  { sprob_kernel : ereal_sup [set k x [set: Y] | x in setT] <= 1}.

#[short(type=sprobability_kernel)]
HB.structure Definition SubProbabilityKernel
    (d d' : _) (X : measurableType d) (Y : measurableType d')
    (R : realType) :=
  {k of FiniteKernel_isSubProbability _ _ X Y R k &
        @FiniteKernel _ _ X Y R k}.
Notation "R .-spker X ~> Y" := (sprobability_kernel X Y R).

HB.factory Record Kernel_isSubProbability
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) of isKernel _ _ X Y R k :=
  { sprob_kernel : ereal_sup [set k x [set: Y] | x in setT] <= 1}.

HB.builders Context d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) k of Kernel_isSubProbability d d' X Y R k.

Let finite : @Kernel_isFinite d d' X Y R k.
Proof.
split; exists 2%R => /= ?; rewrite (@le_lt_trans _ _ 1%:E) ?lte_fin ?ltr1n//.
by rewrite (le_trans _ sprob_kernel)//; exact: ereal_sup_ub.
Qed.

HB.instance Definition _ := finite.

HB.instance Definition _ := @FiniteKernel_isSubProbability.Build _ _ _ _ _ k sprob_kernel.

HB.end.

HB.mixin Record SubProbability_isProbability
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) :=
  { prob_kernel : forall x, k x [set: Y] = 1}.

#[short(type=probability_kernel)]
HB.structure Definition ProbabilityKernel
    (d d' : _) (X : measurableType d) (Y : measurableType d')
    (R : realType) :=
  {k of SubProbability_isProbability _ _ X Y R k &
        @SubProbabilityKernel _ _ X Y R k}.
Notation "R .-pker X ~> Y" := (probability_kernel X Y R).

HB.factory Record Kernel_isProbability
    d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) (k : X -> {measure set Y -> \bar R}) of isKernel _ _ X Y R k :=
  { prob_kernel : forall x, k x setT = 1 }.

HB.builders Context d d' (X : measurableType d) (Y : measurableType d')
    (R : realType) k of Kernel_isProbability d d' X Y R k.

Let sprob_kernel : @Kernel_isSubProbability d d' X Y R k.
Proof.
by split; apply: ub_ereal_sup => x [y _ <-{x}]; rewrite prob_kernel.
Qed.

HB.instance Definition _ := sprob_kernel.

HB.instance Definition _ := @SubProbability_isProbability.Build _ _ _ _ _ k prob_kernel.

HB.end.

Lemma finite_kernel_measure (d d' : _) (X : measurableType d)
    (Y : measurableType d') (R : realType) (k : R.-fker X ~> Y) (x : X) :
  finite_measure (k x).
Proof.
have [r k_r] := measure_uub k.
by rewrite /finite_measure (@lt_trans _ _ r%:E) ?ltey.
Qed.

Lemma sfinite_kernel_measure (d d' : _) (X : measurableType d)
    (Y : measurableType d') (R : realType) (k : R.-sfker X ~> Y) (x : X) :
  sfinite_measure (k x).
Proof.
have [k_ k_E] := sfinite k.
exists (fun n => k_ n x); last by move=> A mA; rewrite k_E.
move=> n; rewrite /finite_measure.
exact: finite_kernel_measure.
Qed.

(* see measurable_prod_subset in lebesgue_integral.v;
   the differences between the two are:
   - m2 is a kernel instead of a measure (the proof uses the
     measurability of each measure of the family)
   - as a consequence, m2D_bounded holds for all x *)
Section measurable_prod_subset_kernel.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d')
          (R : realType).
Implicit Types A : set (X * Y).

Section xsection_kernel.
Variable (k : R.-ker X ~> Y) (D : set Y) (mD : measurable D).
Let kD x := mrestr (k x) mD.
HB.instance Definition _ x := Measure.on (kD x).
Let phi A := fun x => kD x (xsection A x).
Let XY := [set A | measurable A /\ measurable_fun setT (phi A)].

Let phiM (A : set X) B : phi (A `*` B) = (fun x => kD x B * (\1_A x)%:E).
Proof.
rewrite funeqE => x; rewrite indicE /phi/=.
have [xA|xA] := boolP (x \in A); first by rewrite mule1 in_xsectionM.
by rewrite mule0 notin_xsectionM// set0I measure0.
Qed.

Lemma measurable_prod_subset_xsection_kernel :
    (forall x, exists M, forall X, measurable X -> kD x X < M%:E) ->
  measurable `<=` XY.
Proof.
move=> kD_ub; rewrite measurable_prod_measurableType.
set C := [set A `*` B | A in measurable & B in measurable].
have CI : setI_closed C.
  move=> _ _ [X1 mX1 [X2 mX2 <-]] [Y1 mY1 [Y2 mY2 <-]].
  exists (X1 `&` Y1); first exact: measurableI.
  by exists (X2 `&` Y2); [exact: measurableI|rewrite setMI].
have CT : C setT by exists setT => //; exists setT => //; rewrite setMTT.
have CXY : C `<=` XY.
  move=> _ [A mA [B mB <-]]; split; first exact: measurableM.
  rewrite phiM.
  apply: emeasurable_funM => //; first exact/measurable_kernel/measurableI.
  by apply/EFin_measurable_fun; rewrite (_ : \1_ _ = mindic R mA).
suff monoB : monotone_class setT XY by exact: monotone_class_subset.
split => //; [exact: CXY| |exact: xsection_ndseq_closed].
move=> A B BA [mA mphiA] [mB mphiB]; split; first exact: measurableD.
suff : phi (A `\` B) = (fun x => phi A x - phi B x).
  by move=> ->; exact: emeasurable_funB.
rewrite funeqE => x; rewrite /phi/= xsectionD// measureD.
- by rewrite setIidr//; exact: le_xsection.
- exact: measurable_xsection.
- exact: measurable_xsection.
- have [M kM] := kD_ub x.
  rewrite (lt_le_trans (kM (xsection A x) _)) ?leey//.
  exact: measurable_xsection.
Qed.

End xsection_kernel.

End measurable_prod_subset_kernel.

(* see measurable_fun_xsection in lebesgue_integral.v
   the difference is that this section uses a finite kernel m2
   instead of a sigma-finite measure m2 *)
Section measurable_fun_xsection_finite_kernel.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d')
          (R : realType).
Variables (k : R.-fker X ~> Y).
Implicit Types A : set (X * Y).

Let phi A := fun x => k x (xsection A x).
Let XY := [set A | measurable A /\ measurable_fun setT (phi A)].

Lemma measurable_fun_xsection_finite_kernel A :
  A \in measurable -> measurable_fun setT (phi A).
Proof.
move: A; suff : measurable `<=` XY by move=> + A; rewrite inE => /[apply] -[].
move=> /= A mA; rewrite /XY/=; split => //; rewrite (_ : phi _ =
    (fun x => mrestr (k x) measurableT (xsection A x))); last first.
  by apply/funext => x//=; rewrite /mrestr setIT.
apply measurable_prod_subset_xsection_kernel => // x.
have [r hr] := measure_uub k; exists r => B mB.
by rewrite (le_lt_trans _ (hr x)) // /mrestr /= setIT le_measure// inE.
Qed.

End measurable_fun_xsection_finite_kernel.

(* pollard? *)
Section measurable_fun_integral_finite_sfinite.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d')
  (R : realType).

Lemma measurable_fun_xsection_integral
    (l : X -> {measure set Y -> \bar R})
    (k : X * Y -> \bar R)
    (k_ : ({nnsfun [the measurableType _ of (X * Y)%type] >-> R})^nat)
    (ndk_ : nondecreasing_seq (k_ : (X * Y -> R)^nat))
    (k_k : forall z, EFin \o (k_ ^~ z) --> k z) :
  (forall n r, measurable_fun setT (fun x => l x (xsection (k_ n @^-1` [set r]) x))) ->
  measurable_fun setT (fun x => \int[l x]_y k (x, y)).
Proof.
move=> h.
rewrite (_ : (fun x => _) =
    (fun x => elim_sup (fun n => \int[l x]_y (k_ n (x, y))%:E))); last first.
  apply/funext => x.
  transitivity (lim (fun n => \int[l x]_y (k_ n (x, y))%:E)); last first.
    rewrite is_cvg_elim_supE//.
    apply: ereal_nondecreasing_is_cvg => m n mn.
    apply: ge0_le_integral => //.
    - by move=> y _; rewrite lee_fin.
    - exact/EFin_measurable_fun/measurable_fun_prod1.
    - by move=> y _; rewrite lee_fin.
    - exact/EFin_measurable_fun/measurable_fun_prod1.
    - by move=> y _; rewrite lee_fin; exact/lefP/ndk_.
  rewrite -monotone_convergence//.
  - by apply: eq_integral => y _; apply/esym/cvg_lim => //; exact: k_k.
  - by move=> n; exact/EFin_measurable_fun/measurable_fun_prod1.
  - by move=> n y _; rewrite lee_fin.
  - by move=> y _ m n mn; rewrite lee_fin; exact/lefP/ndk_.
apply: measurable_fun_elim_sup => n.
rewrite [X in measurable_fun _ X](_ : _ = (fun x => \int[l x]_y
  (\sum_(r <- fset_set (range (k_ n)))(*TODO: upd when the PR 743 is merged*)
     r * \1_(k_ n @^-1` [set r]) (x, y))%:E)); last first.
  by apply/funext => x; apply: eq_integral => y _; rewrite fimfunE.
rewrite [X in measurable_fun _ X](_ : _ = (fun x =>
  \sum_(r <- fset_set (range (k_ n)))(*TODO: upd when the PR 743 is merged*)
    (\int[l x]_y (r * \1_(k_ n @^-1` [set r]) (x, y))%:E))); last first.
  apply/funext => x; rewrite -ge0_integral_sum//.
  - by apply: eq_integral => y _; rewrite sumEFin.
  - move=> r.
    apply/EFin_measurable_fun/measurable_funrM/measurable_fun_prod1 => /=.
    rewrite (_ : \1_ _ = mindic R (measurable_sfunP (k_ n) r))//.
    exact/measurable_funP.
  - by move=> m y _; rewrite nnfun_muleindic_ge0.
apply emeasurable_fun_sum => r.
rewrite [X in measurable_fun _ X](_ : _ = (fun x => r%:E *
    \int[l x]_y (\1_(k_ n @^-1` [set r]) (x, y))%:E)); last first.
  apply/funext => x.
  under eq_integral do rewrite EFinM.
  rewrite (integralM_0ifneg _ _ (fun k y => (\1_(k_ n @^-1` [set r]) (x, y))%:E))//.
  - by move=> _ y _; rewrite lee_fin.
  - by move=> r0; apply/funext => y; rewrite preimage_nnfun0// indicE in_set0.
  - apply/EFin_measurable_fun/measurable_fun_prod1 => /=.
    rewrite (_ : \1_ _ = mindic R (measurable_sfunP (k_ n) r))//.
    exact/measurable_funP.
apply/measurable_funeM.
rewrite (_ : (fun x => _) = (fun x => l x (xsection (k_ n @^-1` [set r]) x))).
  exact/h.
apply/funext => x; rewrite integral_indic//; last first.
  rewrite (_ : (fun x => _) = xsection (k_ n @^-1` [set r]) x).
    exact: measurable_xsection.
  by rewrite /xsection; apply/seteqP; split=> y/= /[!inE].
congr (l x _); apply/funext => y1/=; rewrite /xsection/= inE.
by apply/propext; tauto.
Qed.

Lemma measurable_fun_integral_finite_kernel
    (l : R.-fker X ~> Y)
    (k : X * Y -> \bar R) (k0 : forall z, 0 <= k z) (mk : measurable_fun setT k) :
  measurable_fun setT (fun x => \int[l x]_y k (x, y)).
Proof.
have [k_ [ndk_ k_k]] := approximation measurableT mk (fun x _ => k0 x).
apply: (measurable_fun_xsection_integral ndk_ (k_k ^~ Logic.I)) => n r.
have [l_ hl_] := measure_uub l.
by apply: measurable_fun_xsection_finite_kernel => // /[!inE].
Qed.

Lemma measurable_fun_integral_sfinite_kernel
    (l : R.-sfker X ~> Y)
    (k : X * Y -> \bar R) (k0 : forall t, 0 <= k t) (mk : measurable_fun setT k) :
  measurable_fun setT (fun x => \int[l x]_y k (x, y)).
Proof.
have [k_ [ndk_ k_k]] := approximation measurableT mk (fun xy _ => k0 xy).
apply: (measurable_fun_xsection_integral ndk_ (k_k ^~ Logic.I)) => n r.
have [l_ hl_] := sfinite l.
rewrite (_ : (fun x => _) =
    (fun x => mseries (l_ ^~ x) 0 (xsection (k_ n @^-1` [set r]) x))); last first.
  by apply/funext => x; rewrite hl_//; exact/measurable_xsection.
apply: ge0_emeasurable_fun_sum => // m.
by apply: measurable_fun_xsection_finite_kernel => // /[!inE].
Qed.

End measurable_fun_integral_finite_sfinite.
Arguments measurable_fun_xsection_integral {_ _ _ _ _} l k.
Arguments measurable_fun_integral_finite_kernel {_ _ _ _ _} l k.
Arguments measurable_fun_integral_sfinite_kernel {_ _ _ _ _} l k.

Section kprobability.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variables (R : realType) (P : probability Y R).

Definition kprobability : X -> {measure set Y -> \bar R} := fun=> P.

Let measurable_fun_kprobability U : measurable U ->
  measurable_fun setT (kprobability ^~ U).
Proof. by move=> mU; exact: measurable_fun_cst. Qed.

HB.instance Definition _ :=
  @isKernel.Build _ _ X Y R kprobability measurable_fun_kprobability.

Let kprobability_prob x : kprobability x setT = 1.
Proof. by rewrite /kprobability/= probability_setT. Qed.

HB.instance Definition _ :=
  @Kernel_isProbability.Build _ _ X Y R kprobability kprobability_prob.

End kprobability.

Section kdirac.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variables (R : realType) (f : X -> Y).

Definition kdirac (mf : measurable_fun setT f)
    : X -> {measure set Y -> \bar R} :=
  fun x : X => [the measure _ _ of dirac (f x)].

Hypothesis mf : measurable_fun setT f.

Let measurable_fun_kdirac U : measurable U ->
  measurable_fun setT (kdirac mf ^~ U).
Proof.
move=> mU; apply/EFin_measurable_fun.
by rewrite (_ : (fun x => _) = mindic R mU \o f)//; exact/measurable_fun_comp.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ _ (kdirac mf)
  measurable_fun_kdirac.

Let kdirac_prob x : kdirac mf x setT = 1.
Proof. by rewrite /kdirac/= diracE in_setT. Qed.

HB.instance Definition _ := Kernel_isProbability.Build _ _ _ _ _
  (kdirac mf) kdirac_prob.

End kdirac.
Arguments kdirac {d d' X Y R f}.

Section kadd.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variables (R : realType) (k1 k2 : R.-ker X ~> Y).

Definition kadd : X -> {measure set Y -> \bar R} :=
  fun x => [the measure _ _ of measure_add (k1 x) (k2 x)].

Let measurable_fun_kadd U : measurable U ->
  measurable_fun setT (kadd ^~ U).
Proof.
move=> mU; rewrite /kadd.
rewrite (_ : (fun _ => _) = (fun x => k1 x U + k2 x U)); last first.
  by apply/funext => x; rewrite -measure_addE.
by apply: emeasurable_funD; exact/measurable_kernel.
Qed.

HB.instance Definition _ :=
  @isKernel.Build _ _ _ _ _ kadd measurable_fun_kadd.
End kadd.

Section sfkadd.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variables (R : realType) (k1 k2 : R.-sfker X ~> Y).

Let sfinite_kadd : exists2 k_ : (R.-ker _ ~> _)^nat, forall n, measure_fam_uub (k_ n) &
  forall x U, measurable U ->
    kadd k1 k2 x U = [the measure _ _ of mseries (k_ ^~ x) 0] U.
Proof.
have [f1 hk1] := sfinite k1.
have [f2 hk2] := sfinite k2.
exists (fun n => [the _.-ker _ ~> _ of kadd (f1 n) (f2 n)]).
  move=> n.
  have [r1 f1r1] := measure_uub (f1 n).
  have [r2 f2r2] := measure_uub (f2 n).
  exists (r1 + r2)%R => x/=.
  by rewrite /msum !big_ord_recr/= big_ord0 add0e EFinD lte_add.
move=> x U mU.
rewrite /kadd/=.
rewrite -/(measure_add (k1 x) (k2 x)) measure_addE.
rewrite /mseries.
rewrite hk1//= hk2//= /mseries.
rewrite -nneseriesD//.
apply: eq_nneseries => n _.
by rewrite -/(measure_add (f1 n x) (f2 n x)) measure_addE.
Qed.

HB.instance Definition _ t :=
  Kernel_isSFinite_subdef.Build _ _ _ _ R (kadd k1 k2) sfinite_kadd.
End sfkadd.

Section fkadd.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variables (R : realType) (k1 k2 : R.-fker X ~> Y).

Let kadd_finite_uub : measure_fam_uub (kadd k1 k2).
Proof.
have [f1 hk1] := measure_uub k1; have [f2 hk2] := measure_uub k2.
exists (f1 + f2)%R => x; rewrite /kadd /=.
rewrite -/(measure_add (k1 x) (k2 x)).
by rewrite measure_addE EFinD; exact: lte_add.
Qed.

HB.instance Definition _ t :=
  Kernel_isFinite.Build _ _ _ _ R (kadd k1 k2) kadd_finite_uub.
End fkadd.

Section kernel_measurable_preimage.
Variables (d d' : _) (T : measurableType d) (T' : measurableType d').
Variable R : realType.

Lemma measurable_eq_cst (f : R.-ker T ~> T') k :
  measurable [set t | f t setT == k].
Proof.
rewrite [X in measurable X](_ : _ = (f ^~ setT) @^-1` [set k]); last first.
  by apply/seteqP; split => t/= /eqP.
have /(_ measurableT [set k]) := measurable_kernel f setT measurableT.
by rewrite setTI; exact.
Qed.

Lemma measurable_neq_cst (f : R.-ker T ~> T') k :
  measurable [set t | f t setT != k].
Proof.
rewrite [X in measurable X](_ : _ = (f ^~ setT) @^-1` [set~ k]); last first.
  by apply/seteqP; split => t /eqP.
have /(_ measurableT [set~ k]) := measurable_kernel f setT measurableT.
by rewrite setTI; apply => //; exact: measurableC.
Qed.

End kernel_measurable_preimage.

Lemma measurable_fun_eq_cst (d d' : _) (T : measurableType d)
    (T' : measurableType d') (R : realType) (f : R.-ker T ~> T') k :
  measurable_fun setT (fun t => f t setT == k).
Proof.
move=> _ /= B mB; rewrite setTI.
have [/eqP->|/eqP->|/eqP->|/eqP->] := set_boolE B.
- exact: measurable_eq_cst.
- rewrite (_ : _ @^-1` _ = [set b | f b setT != k]); last first.
    by apply/seteqP; split => [t /negbT//|t /negbTE].
  exact: measurable_neq_cst.
- by rewrite preimage_set0.
- by rewrite preimage_setT.
Qed.

Section mnormalize.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variables (R : realType) (f : X -> {measure set Y -> \bar R}).
Variable P : probability Y R.

Definition mnormalize x U :=
  let evidence := f x [set: Y] in
  if (evidence == 0) || (evidence == +oo) then P U
  else f x U * (fine evidence)^-1%:E.

Let mnormalize0 x : mnormalize x set0 = 0.
Proof.
by rewrite /mnormalize; case: ifPn => // _; rewrite measure0 mul0e.
Qed.

Let mnormalize_ge0 x U : 0 <= mnormalize x U.
Proof. by rewrite /mnormalize; case: ifPn => //; case: ifPn. Qed.

Lemma mnormalize_sigma_additive x : semi_sigma_additive (mnormalize x).
Proof.
move=> F mF tF mUF; rewrite /mnormalize/=.
case: ifPn => [_|_].
  exact: measure_semi_sigma_additive.
rewrite (_ : (fun n => _) = ((fun n => \sum_(0 <= i < n) f x (F i)) \*
                          cst ((fine (f x setT))^-1)%:E)); last first.
  by apply/funext => n; rewrite -ge0_sume_distrl.
by apply: ereal_cvgMr => //; exact: measure_semi_sigma_additive.
Qed.

HB.instance Definition _ x := isMeasure.Build _ _ _ (mnormalize x)
  (mnormalize0 x) (mnormalize_ge0 x) (@mnormalize_sigma_additive x).

Lemma mnormalize1 x : mnormalize x setT = 1.
Proof.
rewrite /mnormalize; case: ifPn; first by rewrite probability_setT.
rewrite negb_or => /andP[ft0 ftoo].
have ? : f x setT \is a fin_num.
  by rewrite ge0_fin_numE// lt_neqAle ftoo/= leey.
by rewrite -{1}(@fineK _ (f x setT))// -EFinM divrr// ?unitfE fine_eq0.
Qed.

HB.instance Definition _ x :=
  isProbability.Build _ _ _ (mnormalize x) (mnormalize1 x).

End mnormalize.

Section knormalize.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d').
Variables (R : realType) (f : R.-ker X ~> Y).

Definition knormalize (P : probability Y R) :=
  fun t => [the measure _ _ of mnormalize f P t].

Variable P : probability Y R.

Let measurable_fun_knormalize U :
  measurable U -> measurable_fun setT (knormalize P ^~ U).
Proof.
move=> mU; rewrite /knormalize/= /mnormalize /=.
rewrite (_ : (fun _ => _) = (fun x =>
     if f x setT == 0 then P U else if f x setT == +oo then P U
     else f x U * ((fine (f x setT))^-1)%:E)); last first.
  apply/funext => x; case: ifPn => [/orP[->//|->]|].
    by case: ifPn.
  by rewrite negb_or=> /andP[/negbTE -> /negbTE ->].
apply: measurable_fun_if => //.
- exact: measurable_fun_eq_cst.
- exact: measurable_fun_cst.
- apply: measurable_fun_if => //.
  + rewrite setTI [X in measurable X](_ : _ = [set t | f t setT != 0]); last first.
      by apply/seteqP; split => [x /negbT//|x /negbTE].
    exact: measurable_neq_cst.
  + exact: measurable_fun_eq_cst.
  + exact: measurable_fun_cst.
  + apply: emeasurable_funM.
      by have := measurable_kernel f U mU; exact: measurable_funS.
    apply/EFin_measurable_fun.
    apply: (measurable_fun_comp' (F := [set r : R | r != 0%R])) => //.
    * exact: open_measurable.
    * move=> /= r [t] [] [_ H1] H2 H3.
      apply/eqP => H4; subst r.
      move/eqP : H4.
      rewrite fine_eq0 ?H1//.
      rewrite ge0_fin_numE//.
      by rewrite lt_neqAle leey H2.
    * apply: open_continuous_measurable_fun => //.
      apply/in_setP => x /= x0.
      by apply: inv_continuous.
    * apply: measurable_fun_comp => /=.
        exact: measurable_fun_fine.
      by have := measurable_kernel f _ measurableT; exact: measurable_funS.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ R (knormalize P)
  measurable_fun_knormalize.

Let knormalize1 x : knormalize P x setT = 1.
Proof.
rewrite /knormalize/= /mnormalize.
case: ifPn => [_|]; first by rewrite probability_setT.
rewrite negb_or => /andP[fx0 fxoo].
have ? : f x setT \is a fin_num by rewrite ge0_fin_numE// lt_neqAle fxoo/= leey.
rewrite -{1}(@fineK _ (f x setT))//=.
by rewrite -EFinM divrr// ?lte_fin ?ltr1n// ?unitfE fine_eq0.
Qed.

HB.instance Definition _ :=
  @Kernel_isProbability.Build _ _ _ _ _ (knormalize P) knormalize1.

End knormalize.

Section kcomp_def.
Variables (d1 d2 d3 : _) (X : measurableType d1) (Y : measurableType d2)
          (Z : measurableType d3) (R : realType).
Variable l : X -> {measure set Y -> \bar R}.
Variable k : (X * Y)%type -> {measure set Z -> \bar R}.

Definition kcomp x U := \int[l x]_y k (x, y) U.

End kcomp_def.

Section kcomp_is_measure.
Variables (d1 d2 d3 : _) (X : measurableType d1) (Y : measurableType d2)
          (Z : measurableType d3) (R : realType).
Variable l : R.-ker X ~> Y.
Variable k : R.-ker [the measurableType _ of (X * Y)%type] ~> Z.

Local Notation "l \; k" := (kcomp l k).

Let kcomp0 x : (l \; k) x set0 = 0.
Proof.
by rewrite /kcomp (eq_integral (cst 0)) ?integral0// => y _; rewrite measure0.
Qed.

Let kcomp_ge0 x U : 0 <= (l \; k) x U. Proof. exact: integral_ge0. Qed.

Let kcomp_sigma_additive x : semi_sigma_additive ((l \; k) x).
Proof.
move=> U mU tU mUU; rewrite [X in _ --> X](_ : _ =
  \int[l x]_y (\sum_(n <oo) k (x, y) (U n)))%E; last first.
  apply: eq_integral => V _.
  by apply/esym/cvg_lim => //; exact/measure_semi_sigma_additive.
apply/cvg_closeP; split.
  by apply: is_cvg_nneseries => n _; exact: integral_ge0.
rewrite closeE// integral_sum// => n.
by have /measurable_fun_prod1 := measurable_kernel k (U n) (mU n).
Qed.

HB.instance Definition _ x := isMeasure.Build _ R _
  ((l \; k) x) (kcomp0 x) (kcomp_ge0 x) (@kcomp_sigma_additive x).

Definition mkcomp : X -> {measure set Z -> \bar R} :=
  fun x => [the measure _ _ of (l \; k) x].

End kcomp_is_measure.

Notation "l \; k" := (mkcomp l k).

Module KCOMP_FINITE_KERNEL.

Section kcomp_finite_kernel_kernel.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType) (l : R.-fker X ~> Y)
          (k : R.-ker [the measurableType _ of (X * Y)%type] ~> Z).

Lemma measurable_fun_kcomp_finite U :
  measurable U -> measurable_fun setT ((l \; k) ^~ U).
Proof.
move=> mU; apply: (measurable_fun_integral_finite_kernel _ (k ^~ U)) => //=.
exact/measurable_kernel.
Qed.

HB.instance Definition _ :=
  isKernel.Build _ _ X Z R (l \; k) measurable_fun_kcomp_finite.

End kcomp_finite_kernel_kernel.

Section kcomp_finite_kernel_finite.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType).
Variable l : R.-fker X ~> Y.
Variable k : R.-fker [the measurableType _ of (X * Y)%type] ~> Z.

Let mkcomp_finite : measure_fam_uub (l \; k).
Proof.
have /measure_fam_uubP[r hr] := measure_uub k.
have /measure_fam_uubP[s hs] := measure_uub l.
apply/measure_fam_uubP; exists (PosNum [gt0 of (r%:num * s%:num)%R]) => x /=.
apply: (@le_lt_trans _ _ (\int[l x]__ r%:num%:E)).
  apply: ge0_le_integral => //.
  - have /measurable_fun_prod1 := measurable_kernel k setT measurableT.
    exact.
  - exact/measurable_fun_cst.
  - by move=> y _; exact/ltW/hr.
by rewrite integral_cst//= EFinM lte_pmul2l.
Qed.

HB.instance Definition _ :=
  Kernel_isFinite.Build _ _ X Z R (l \; k) mkcomp_finite.

End kcomp_finite_kernel_finite.
End KCOMP_FINITE_KERNEL.

Section kcomp_sfinite_kernel.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType).
Variable l : R.-sfker X ~> Y.
Variable k : R.-sfker [the measurableType _ of (X * Y)%type] ~> Z.

Import KCOMP_FINITE_KERNEL.

Lemma mkcomp_sfinite : exists k_ : (R.-fker X ~> Z)^nat, forall x U, measurable U ->
  (l \; k) x U = kseries k_ x U.
Proof.
have [k_ hk_] := sfinite k; have [l_ hl_] := sfinite l.
have [kl hkl] : exists kl : (R.-fker X ~> Z) ^nat, forall x U,
    \esum_(i in setT) (l_ i.2 \; k_ i.1) x U = \sum_(i <oo) kl i x U.
  have /ppcard_eqP[f] : ([set: nat] #= [set: nat * nat])%card.
    by rewrite card_eq_sym; exact: card_nat2.
  exists (fun i => [the _.-fker _ ~> _ of l_ (f i).2 \; k_ (f i).1]) => x U.
  by rewrite (reindex_esum [set: nat] _ f)// nneseries_esum// fun_true.
exists kl => x U mU.
transitivity (([the _.-ker _ ~> _ of kseries l_] \;
               [the _.-ker _ ~> _ of kseries k_]) x U).
  rewrite /= /kcomp [in RHS](eq_measure_integral (l x)); last first.
    by move=> *; rewrite hl_.
  by apply: eq_integral => y _; rewrite hk_.
rewrite /= /kcomp/= integral_sum//=; last first.
  by move=> n; have /measurable_fun_prod1 := measurable_kernel (k_ n) _ mU; exact.
transitivity (\sum_(i <oo) \sum_(j <oo) (l_ j \; k_ i) x U).
  apply: eq_nneseries => i _; rewrite integral_kseries//.
  by have /measurable_fun_prod1 := measurable_kernel (k_ i) _ mU; exact.
rewrite /mseries -hkl/=.
rewrite (_ : setT = setT `*`` (fun=> setT)); last by apply/seteqP; split.
rewrite -(@esum_esum _ _ _ _ _ (fun i j => (l_ j \; k_ i) x U))//.
rewrite nneseries_esum; last by move=> n _; exact: nneseries_ge0.
by rewrite fun_true; apply: eq_esum => /= i _; rewrite nneseries_esum// fun_true.
Qed.

Lemma measurable_fun_mkcomp_sfinite U : measurable U ->
  measurable_fun setT ((l \; k) ^~ U).
Proof.
move=> mU; apply: (measurable_fun_integral_sfinite_kernel _ (k ^~ U)) => //.
exact/measurable_kernel.
Qed.

End kcomp_sfinite_kernel.

Module KCOMP_SFINITE_KERNEL.
Section kcomp_sfinite_kernel.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType).
Variable l : R.-sfker X ~> Y.
Variable k : R.-sfker [the measurableType _ of (X * Y)%type] ~> Z.

HB.instance Definition _ :=
  isKernel.Build _ _ X Z R (l \; k) (measurable_fun_mkcomp_sfinite l k).

#[export]
HB.instance Definition _ :=
  Kernel_isSFinite.Build _ _ X Z R (l \; k) (mkcomp_sfinite l k).

End kcomp_sfinite_kernel.
End KCOMP_SFINITE_KERNEL.
HB.export KCOMP_SFINITE_KERNEL.

(* pollard? *)
Section measurable_fun_integral_kernel'.
Variables (d d' : _) (X : measurableType d) (Y : measurableType d')
  (R : realType).
Variables (l : X -> {measure set Y -> \bar R})
  (k : Y -> \bar R)
  (k_ : ({nnsfun Y >-> R}) ^nat)
  (ndk_ : nondecreasing_seq (k_ : (Y -> R)^nat))
  (k_k : forall z, setT z -> EFin \o (k_ ^~ z) --> k z).

Let p : (X * Y -> R)^nat := fun n xy => k_ n xy.2.

Let p_ge0 n x : (0 <= p n x)%R. Proof. by []. Qed.

HB.instance Definition _ n := @IsNonNegFun.Build _ R (p n) (p_ge0 n).

Let mp n : measurable_fun setT (p n).
Proof.
rewrite /p => _ /= B mB; rewrite setTI.
have mk_n : measurable_fun setT (k_ n) by [].
rewrite (_ : _ @^-1` _ = setT `*` (k_ n @^-1` B)); last first.
  by apply/seteqP; split => xy /=; tauto.
apply: measurableM => //.
have := mk_n measurableT _ mB.
by rewrite setTI.
Qed.

HB.instance Definition _ n := @IsMeasurableFun.Build _ _ R (p n) (mp n).

Let fp n : finite_set (range (p n)).
Proof.
have := @fimfunP _ _ (k_ n).
suff : range (k_ n) = range (p n) by move=> <-.
by apply/seteqP; split => r [y ?] <-; [exists (point, y)|exists y.2].
Qed.

HB.instance Definition _ n := @FiniteImage.Build _ _ (p n) (fp n).

Lemma measurable_fun_preimage_integral :
  (forall n r, measurable_fun setT (fun x => l x (k_ n @^-1` [set r]))) ->
  measurable_fun setT (fun x => \int[l x]_z k z).
Proof.
move=> h.
apply: (measurable_fun_xsection_integral l (fun xy => k xy.2)
  (fun n => [the {nnsfun _ >-> _} of p n])) => /=.
- by rewrite /p => m n mn; apply/lefP => -[x y] /=; exact/lefP/ndk_.
- by move=> [x y]; exact: k_k.
- move=> n r _ /= B mB.
  have := h n r measurableT B mB.
  rewrite !setTI.
  suff : ((fun x => l x (k_ n @^-1` [set r])) @^-1` B) =
         ((fun x => l x (xsection (p n @^-1` [set r]) x)) @^-1` B) by move=> ->.
  apply/seteqP; split => x/=.
    suff : (k_ n @^-1` [set r]) = (xsection (p n @^-1` [set r]) x) by move=> ->.
    by apply/seteqP; split; move=> y/=;
      rewrite /xsection/= /p /preimage/= inE/=.
  suff : (k_ n @^-1` [set r]) = (xsection (p n @^-1` [set r]) x) by move=> ->.
  by apply/seteqP; split; move=> y/=; rewrite /xsection/= /p /preimage/= inE/=.
Qed.

End measurable_fun_integral_kernel'.

Lemma measurable_fun_integral_kernel
    (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
    (Z : measurableType d3) (R : realType)
    (l : R.-ker [the measurableType _ of (X * Y)%type] ~> Z) c
    (k : Z -> \bar R) (k0 : forall z, True -> 0 <= k z) (mk : measurable_fun setT k) :
  measurable_fun setT (fun y => \int[l (c, y)]_z k z).
Proof.
have [k_ [ndk_ k_k]] := approximation measurableT mk k0.
apply: (measurable_fun_preimage_integral ndk_ k_k) => n r.
have := measurable_kernel l (k_ n @^-1` [set r]) (measurable_sfunP (k_ n) r).
by move=> /measurable_fun_prod1; exact.
Qed.

Section integral_kcomp.

Let integral_kcomp_indic d d' d3 (X : measurableType d) (Y : measurableType d')
    (Z : measurableType d3) (R : realType) (l : R.-sfker X ~> Y)
    (k : R.-sfker [the measurableType _ of (X * Y)%type] ~> Z)
    x (E : set _) (mE : measurable E) :
  \int[(l \; k) x]_z (\1_E z)%:E = \int[l x]_y (\int[k (x, y)]_z (\1_E z)%:E).
Proof.
rewrite integral_indic//= /kcomp.
by apply eq_integral => y _; rewrite integral_indic.
Qed.

Let integral_kcomp_nnsfun d d' d3 (X : measurableType d) (Y : measurableType d')
    (Z : measurableType d3) (R : realType) (l : R.-sfker X ~> Y)
    (k : R.-sfker [the measurableType _ of (X * Y)%type] ~> Z)
    x (f : {nnsfun Z >-> R}) :
  \int[(l \; k) x]_z (f z)%:E = \int[l x]_y (\int[k (x, y)]_z (f z)%:E).
Proof.
under [in LHS]eq_integral do rewrite fimfunE -sumEFin.
rewrite ge0_integral_sum//; last 2 first.
  move=> r; apply/EFin_measurable_fun/measurable_funrM.
  have fr : measurable (f @^-1` [set r]) by exact/measurable_sfunP.
  by rewrite (_ : \1__ = mindic R fr).
  by move=> r z _; rewrite EFinM nnfun_muleindic_ge0.
under [in RHS]eq_integral.
  move=> y _.
  under eq_integral.
    move=> z _.
    rewrite fimfunE -sumEFin.
    over.
  rewrite /= ge0_integral_sum//; last 2 first.
    move=> r; apply/EFin_measurable_fun/measurable_funrM.
    have fr : measurable (f @^-1` [set r]) by exact/measurable_sfunP.
    by rewrite (_ : \1__ = mindic R fr).
    by move=> r z _; rewrite EFinM nnfun_muleindic_ge0.
  under eq_bigr.
    move=> r _.
    rewrite (@integralM_indic _ _ _ _ _ _ (fun r => f @^-1` [set r]))//; last first.
      by move=> r0; rewrite preimage_nnfun0.
    rewrite integral_indic// setIT.
    over.
  over.
rewrite /= ge0_integral_sum//; last 2 first.
  - move=> r; apply: measurable_funeM.
    have := measurable_kernel k (f @^-1` [set r]) (measurable_sfunP f r).
    by move=> /measurable_fun_prod1; exact.
  - move=> n y _.
    have := @mulemu_ge0 _ _ _ (k (x, y)) n (fun n => f @^-1` [set n]).
    by apply; exact: preimage_nnfun0.
apply eq_bigr => r _.
rewrite (@integralM_indic _ _ _ _ _ _ (fun r => f @^-1` [set r]))//; last first.
  exact: preimage_nnfun0.
rewrite /= integral_kcomp_indic; last exact/measurable_sfunP.
rewrite (@integralM_0ifneg _ _ _ _ _ _ (fun r t => k (x, t) (f @^-1` [set r])))//; last 2 first.
  move=> r0.
  apply/funext => y.
  by rewrite preimage_nnfun0// measure0.
  have := measurable_kernel k (f @^-1` [set r]) (measurable_sfunP f r).
  by move/measurable_fun_prod1; exact.
congr (_ * _); apply eq_integral => y _.
by rewrite integral_indic// setIT.
Qed.

Lemma integral_kcomp d d' d3 (X : measurableType d) (Y : measurableType d')
    (Z : measurableType d3) (R : realType) (l : R.-sfker X ~> Y)
    (k : R.-sfker [the measurableType _ of (X * Y)%type] ~> Z)
    x f : (forall z, 0 <= f z) -> measurable_fun setT f ->
  \int[(l \; k) x]_z f z = \int[l x]_y (\int[k (x, y)]_z f z).
Proof.
move=> f0 mf.
have [f_ [ndf_ f_f]] := approximation measurableT mf (fun z _ => f0 z).
transitivity (\int[(l \; k) x]_z (lim (EFin \o (f_^~ z)))).
  apply/eq_integral => z _.
  apply/esym/cvg_lim => //=.
  exact: f_f.
rewrite monotone_convergence//; last 3 first.
  by move=> n; apply/EFin_measurable_fun.
  by move=> n z _; rewrite lee_fin.
  by move=> z _ a b /ndf_ /lefP ab; rewrite lee_fin.
rewrite (_ : (fun _ => _) = (fun n => \int[l x]_y (\int[k (x, y)]_z (f_ n z)%:E)))//; last first.
  by apply/funext => n; rewrite integral_kcomp_nnsfun.
transitivity (\int[l x]_y lim (fun n => \int[k (x, y)]_z (f_ n z)%:E)).
  rewrite -monotone_convergence//; last 3 first.
  move=> n.
  apply: measurable_fun_integral_kernel => //.
  - by move=> z; rewrite lee_fin.
  - by apply/EFin_measurable_fun.
  - move=> n y _.
    by apply integral_ge0 => // z _; rewrite lee_fin.
  - move=> y _ a b ab.
    apply: ge0_le_integral => //.
    + by move=> z _; rewrite lee_fin.
    + exact/EFin_measurable_fun.
    + by move=> z _; rewrite lee_fin.
    + exact/EFin_measurable_fun.
    + move: ab => /ndf_ /lefP ab z _.
      by rewrite lee_fin.
apply eq_integral => y _.
rewrite -monotone_convergence//; last 3 first.
  move=> n; exact/EFin_measurable_fun.
  by move=> n z _; rewrite lee_fin.
  by move=> z _ a b /ndf_ /lefP; rewrite lee_fin.
apply eq_integral => z _.
apply/cvg_lim => //.
exact: f_f.
Qed.

End integral_kcomp.
