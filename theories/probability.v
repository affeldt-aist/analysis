(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg poly ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop.
From HB Require Import structures.
Require Import exp numfun lebesgue_measure lebesgue_integral.
Require Import reals ereal signed topology normedtype sequences esum measure.
Require Import exp numfun lebesgue_measure lebesgue_integral kernel.

(**md**************************************************************************)
(* # Probability                                                              *)
(*                                                                            *)
(* This file provides basic notions of probability theory. See measure.v for  *)
(* the type probability T R (a measure that sums to 1).                       *)
(*                                                                            *)
(* ```                                                                        *)
(*          {RV P >-> R} == real random variable: a measurable function from  *)
(*                          the measurableType of the probability P to R      *)
(*      distribution P X == measure image of the probability measure P by the *)
(*                          random variable X : {RV P -> R}                   *)
(*                          P as type probability T R with T of type          *)
(*                          measurableType.                                   *)
(*                          Declared as an instance of probability measure.   *)
(*               'E_P[X] == expectation of the real measurable function X     *)
(*        covariance X Y == covariance between real random variable X and Y   *)
(*               'V_P[X] == variance of the real random variable X            *)
(*         mmt_gen_fun X == moment generating function of the random variable *)
(*                          X *)
(*       {dmfun T >-> R} == type of discrete real-valued measurable functions *)
(*         {dRV P >-> R} == real-valued discrete random variable              *)
(*             dRV_dom X == domain of the discrete random variable X          *)
(*            dRV_enum X == bijection between the domain and the range of X   *)
(*               pmf X r := fine (P (X @^-1` [set r]))                        *)
(*         enum_prob X k == probability of the kth value in the range of X    *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "'{' 'RV' P >-> R '}'"
  (at level 0, format "'{' 'RV'  P  '>->'  R '}'").
Reserved Notation "''E_' P [ X ]" (format "''E_' P [ X ]", at level 5).
Reserved Notation "''V_' P [ X ]" (format "''V_' P [ X ]", at level 5).
Reserved Notation "{ 'dmfun' aT >-> T }"
  (at level 0, format "{ 'dmfun'  aT  >->  T }").
Reserved Notation "'{' 'dRV' P >-> R '}'"
  (at level 0, format "'{' 'dRV'  P  '>->'  R '}'").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition random_variable (d : _) (T : measurableType d) (R : realType)
  (P : probability T R) := {mfun T >-> R}.

Notation "{ 'RV' P >-> R }" := (@random_variable _ _ R P) : form_scope.

Lemma notin_range_measure d (T : measurableType d) (R : realType)
    (P : {measure set T -> \bar R}) (X : T -> R) r :
  r \notin range X -> P (X @^-1` [set r]) = 0%E.
Proof. by rewrite notin_setE => hr; rewrite preimage10. Qed.

Lemma probability_range d (T : measurableType d) (R : realType)
  (P : probability T R) (X : {RV P >-> R}) : P (X @^-1` range X) = 1%E.
Proof. by rewrite preimage_range probability_setT. Qed.

Definition distribution d (T : measurableType d) (R : realType)
    (P : probability T R) (X : {mfun T >-> R}) :=
  pushforward P (@measurable_funP _ _ _ X).

Section distribution_is_probability.
Context d (T : measurableType d) (R : realType) (P : probability T R)
        (X : {mfun T >-> R}).

Let distribution0 : distribution P X set0 = 0%E.
Proof. exact: measure0. Qed.

Let distribution_ge0 A : (0 <= distribution P X A)%E.
Proof. exact: measure_ge0. Qed.

Let distribution_sigma_additive : semi_sigma_additive (distribution P X).
Proof. exact: measure_semi_sigma_additive. Qed.

HB.instance Definition _ := isMeasure.Build _ _ R (distribution P X)
  distribution0 distribution_ge0 distribution_sigma_additive.

Let distribution_is_probability : distribution P X [set: _] = 1%:E.
Proof.
by rewrite /distribution /= /pushforward /= preimage_setT probability_setT.
Qed.

HB.instance Definition _ := Measure_isProbability.Build _ _ R
  (distribution P X) distribution_is_probability.

End distribution_is_probability.

Section transfer_probability.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma probability_distribution (X : {RV P >-> R}) r :
  P [set x | X x = r] = distribution P X [set r].
Proof. by []. Qed.

Lemma integral_distribution (X : {RV P >-> R}) (f : R -> \bar R) :
    measurable_fun [set: R] f -> (forall y, 0 <= f y) ->
  \int[distribution P X]_y f y = \int[P]_x (f \o X) x.
Proof. by move=> mf f0; rewrite integral_pushforward. Qed.

End transfer_probability.

HB.lock Definition expectation {d} {T : measurableType d} {R : realType}
  (P : probability T R) (X : T -> R) := (\int[P]_w (X w)%:E)%E.
Canonical expectation_unlockable := Unlockable expectation.unlock.
Arguments expectation {d T R} P _%R.
Notation "''E_' P [ X ]" := (@expectation _ _ _ P X) : ereal_scope.

Section expectation_lemmas.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma expectation_fin_num (X : {RV P >-> R}) : P.-integrable setT (EFin \o X) ->
  'E_P[X] \is a fin_num.
Proof. by move=> ?; rewrite unlock integral_fune_fin_num. Qed.

Lemma expectation_cst r : 'E_P[cst r] = r%:E.
Proof. by rewrite unlock/= integral_cst//= probability_setT mule1. Qed.

Lemma expectation_indic (A : set T) (mA : measurable A) : 'E_P[\1_A] = P A.
Proof. by rewrite unlock integral_indic// setIT. Qed.

Lemma integrable_expectation (X : {RV P >-> R})
  (iX : P.-integrable [set: T] (EFin \o X)) : `| 'E_P[X] | < +oo.
Proof.
move: iX => /integrableP[? Xoo]; rewrite (le_lt_trans _ Xoo)// unlock.
exact: le_trans (le_abse_integral _ _ _).
Qed.

Lemma expectationM (X : {RV P >-> R}) (iX : P.-integrable [set: T] (EFin \o X))
  (k : R) : 'E_P[k \o* X] = k%:E * 'E_P [X].
Proof.
rewrite unlock; under eq_integral do rewrite EFinM.
by rewrite -integralZl//; under eq_integral do rewrite muleC.
Qed.

Lemma expectation_ge0 (X : {RV P >-> R}) :
  (forall x, 0 <= X x)%R -> 0 <= 'E_P[X].
Proof.
by move=> ?; rewrite unlock integral_ge0// => x _; rewrite lee_fin.
Qed.

Lemma expectation_le (X Y : T -> R) :
    measurable_fun [set: T] X -> measurable_fun [set: T] Y ->
    (forall x, 0 <= X x)%R -> (forall x, 0 <= Y x)%R ->
  {ae P, (forall x, X x <= Y x)%R} -> 'E_P[X] <= 'E_P[Y].
Proof.
move=> mX mY X0 Y0 XY; rewrite unlock ae_ge0_le_integral => //.
- by move=> t _; apply: X0.
- exact/EFin_measurable_fun.
- by move=> t _; apply: Y0.
- exact/EFin_measurable_fun.
- move: XY => [N [mN PN XYN]]; exists N; split => // t /= h.
  by apply: XYN => /=; apply: contra_not h; rewrite lee_fin.
Qed.

Lemma expectationD (X Y : {RV P >-> R}) :
    P.-integrable [set: T] (EFin \o X) -> P.-integrable [set: T] (EFin \o Y) ->
  'E_P[X \+ Y] = 'E_P[X] + 'E_P[Y].
Proof. by move=> ? ?; rewrite unlock integralD_EFin. Qed.

Lemma expectationB (X Y : {RV P >-> R}) :
    P.-integrable [set: T] (EFin \o X) -> P.-integrable [set: T] (EFin \o Y) ->
  'E_P[X \- Y] = 'E_P[X] - 'E_P[Y].
Proof. by move=> ? ?; rewrite unlock integralB_EFin. Qed.

Lemma expectation_sum (X : seq {RV P >-> R}) :
    (forall Xi, Xi \in X -> P.-integrable [set: T] (EFin \o Xi)) ->
  'E_P[\sum_(Xi <- X) Xi] = \sum_(Xi <- X) 'E_P[Xi].
Proof.
elim: X => [|X0 X IHX] intX; first by rewrite !big_nil expectation_cst.
have intX0 : P.-integrable [set: T] (EFin \o X0).
  by apply: intX; rewrite in_cons eqxx.
have {}intX Xi : Xi \in X -> P.-integrable [set: T] (EFin \o Xi).
  by move=> XiX; apply: intX; rewrite in_cons XiX orbT.
rewrite !big_cons expectationD ?IHX// (_ : _ \o _ = fun x =>
    \sum_(f <- map (fun x : {RV P >-> R} => EFin \o x) X) f x).
  by apply: integrable_sum => // _ /mapP[h hX ->]; exact: intX.
by apply/funext => t/=; rewrite big_map sumEFin mfun_sum.
Qed.

End expectation_lemmas.

HB.lock Definition covariance {d} {T : measurableType d} {R : realType}
    (P : probability T R) (X Y : T -> R) :=
  'E_P[(X \- cst (fine 'E_P[X])) * (Y \- cst (fine 'E_P[Y]))]%E.
Canonical covariance_unlockable := Unlockable covariance.unlock.
Arguments covariance {d T R} P _%R _%R.

Section covariance_lemmas.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma covarianceE (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) ->
    P.-integrable setT (EFin \o Y) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  covariance P X Y = 'E_P[X * Y] - 'E_P[X] * 'E_P[Y].
Proof.
move=> X1 Y1 XY1.
have ? : 'E_P[X] \is a fin_num by rewrite fin_num_abs// integrable_expectation.
have ? : 'E_P[Y] \is a fin_num by rewrite fin_num_abs// integrable_expectation.
rewrite unlock [X in 'E_P[X]](_ : _ = (X \* Y \- fine 'E_P[X] \o* Y
    \- fine 'E_P[Y] \o* X \+ fine ('E_P[X] * 'E_P[Y]) \o* cst 1)%R); last first.
  apply/funeqP => x /=; rewrite mulrDr !mulrDl/= mul1r fineM// mulrNN addrA.
  by rewrite mulrN mulNr [Z in (X x * Y x - Z)%R]mulrC.
have ? : P.-integrable [set: T] (EFin \o (X \* Y \- fine 'E_P[X] \o* Y)%R).
  by rewrite compreBr ?integrableB// compre_scale ?integrableZl.
rewrite expectationD/=; last 2 first.
  - by rewrite compreBr// integrableB// compre_scale ?integrableZl.
  - by rewrite compre_scale// integrableZl// finite_measure_integrable_cst.
rewrite 2?expectationB//= ?compre_scale// ?integrableZl//.
rewrite 3?expectationM//= ?finite_measure_integrable_cst//.
by rewrite expectation_cst mule1 fineM// EFinM !fineK// muleC subeK ?fin_numM.
Qed.

Lemma covarianceC (X Y : T -> R) : covariance P X Y = covariance P Y X.
Proof.
by rewrite unlock; congr expectation; apply/funeqP => x /=; rewrite mulrC.
Qed.

Lemma covariance_fin_num (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) ->
    P.-integrable setT (EFin \o Y) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  covariance P X Y \is a fin_num.
Proof.
by move=> X1 Y1 XY1; rewrite covarianceE// fin_numB fin_numM expectation_fin_num.
Qed.

Lemma covariance_cst_l c (X : {RV P >-> R}) : covariance P (cst c) X = 0.
Proof.
rewrite unlock expectation_cst/=.
rewrite [X in 'E_P[X]](_ : _ = cst 0%R) ?expectation_cst//.
by apply/funeqP => x; rewrite /GRing.mul/= subrr mul0r.
Qed.

Lemma covariance_cst_r (X : {RV P >-> R}) c : covariance P X (cst c) = 0.
Proof. by rewrite covarianceC covariance_cst_l. Qed.

Lemma covarianceZl a (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) ->
    P.-integrable setT (EFin \o Y) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  covariance P (a \o* X)%R Y = a%:E * covariance P X Y.
Proof.
move=> X1 Y1 XY1.
have aXY : (a \o* X * Y = a \o* (X * Y))%R.
  by apply/funeqP => x; rewrite mulrAC.
rewrite [LHS]covarianceE => [||//|] /=; last 2 first.
- by rewrite compre_scale ?integrableZl.
- by rewrite aXY compre_scale ?integrableZl.
rewrite covarianceE// aXY !expectationM//.
by rewrite -muleA -muleBr// fin_num_adde_defr// expectation_fin_num.
Qed.

Lemma covarianceZr a (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) ->
    P.-integrable setT (EFin \o Y) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  covariance P X (a \o* Y)%R = a%:E * covariance P X Y.
Proof.
move=> X1 Y1 XY1.
by rewrite [in RHS]covarianceC covarianceC covarianceZl; last rewrite mulrC.
Qed.

Lemma covarianceNl (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) ->
    P.-integrable setT (EFin \o Y) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  covariance P (\- X)%R Y = - covariance P X Y.
Proof.
move=> X1 Y1 XY1.
have -> : (\- X = -1 \o* X)%R by apply/funeqP => x /=; rewrite mulrN mulr1.
by rewrite covarianceZl// EFinN mulNe mul1e.
Qed.

Lemma covarianceNr (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) ->
    P.-integrable setT (EFin \o Y) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  covariance P X (\- Y)%R = - covariance P X Y.
Proof. by move=> X1 Y1 XY1; rewrite !(covarianceC X) covarianceNl 1?mulrC. Qed.

Lemma covarianceNN (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) ->
    P.-integrable setT (EFin \o Y) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  covariance P (\- X)%R (\- Y)%R = covariance P X Y.
Proof.
move=> X1 Y1 XY1.
have NY : P.-integrable setT (EFin \o (\- Y)%R) by rewrite compreN ?integrableN.
by rewrite covarianceNl ?covarianceNr ?oppeK//= mulrN compreN ?integrableN.
Qed.

Lemma covarianceDl (X Y Z : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
    P.-integrable setT (EFin \o Y) -> P.-integrable setT (EFin \o (Y ^+ 2)%R) ->
    P.-integrable setT (EFin \o Z) -> P.-integrable setT (EFin \o (Z ^+ 2)%R) ->
    P.-integrable setT (EFin \o (X * Z)%R) ->
    P.-integrable setT (EFin \o (Y * Z)%R) ->
  covariance P (X \+ Y)%R Z = covariance P X Z + covariance P Y Z.
Proof.
move=> X1 X2 Y1 Y2 Z1 Z2 XZ1 YZ1.
rewrite [LHS]covarianceE//= ?mulrDl ?compreDr// ?integrableD//.
rewrite 2?expectationD//=.
rewrite muleDl ?fin_num_adde_defr ?expectation_fin_num//.
rewrite oppeD ?fin_num_adde_defr ?fin_numM ?expectation_fin_num//.
by rewrite addeACA 2?covarianceE.
Qed.

Lemma covarianceDr (X Y Z : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
    P.-integrable setT (EFin \o Y) -> P.-integrable setT (EFin \o (Y ^+ 2)%R) ->
    P.-integrable setT (EFin \o Z) -> P.-integrable setT (EFin \o (Z ^+ 2)%R) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
    P.-integrable setT (EFin \o (X * Z)%R) ->
  covariance P X (Y \+ Z)%R = covariance P X Y + covariance P X Z.
Proof.
move=> X1 X2 Y1 Y2 Z1 Z2 XY1 XZ1.
by rewrite covarianceC covarianceDl ?(covarianceC X) 1?mulrC.
Qed.

Lemma covarianceBl (X Y Z : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
    P.-integrable setT (EFin \o Y) -> P.-integrable setT (EFin \o (Y ^+ 2)%R) ->
    P.-integrable setT (EFin \o Z) -> P.-integrable setT (EFin \o (Z ^+ 2)%R) ->
    P.-integrable setT (EFin \o (X * Z)%R) ->
    P.-integrable setT (EFin \o (Y * Z)%R) ->
  covariance P (X \- Y)%R Z = covariance P X Z - covariance P Y Z.
Proof.
move=> X1 X2 Y1 Y2 Z1 Z2 XZ1 YZ1.
rewrite -[(X \- Y)%R]/(X \+ (\- Y))%R covarianceDl ?covarianceNl//=.
- by rewrite compreN// integrableN.
- by rewrite mulrNN.
- by rewrite mulNr compreN// integrableN.
Qed.

Lemma covarianceBr (X Y Z : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
    P.-integrable setT (EFin \o Y) -> P.-integrable setT (EFin \o (Y ^+ 2)%R) ->
    P.-integrable setT (EFin \o Z) -> P.-integrable setT (EFin \o (Z ^+ 2)%R) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
    P.-integrable setT (EFin \o (X * Z)%R) ->
  covariance P X (Y \- Z)%R = covariance P X Y - covariance P X Z.
Proof.
move=> X1 X2 Y1 Y2 Z1 Z2 XY1 XZ1.
by rewrite !(covarianceC X) covarianceBl 1?(mulrC _ X).
Qed.

End covariance_lemmas.

Section variance.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Definition variance (X : T -> R) := covariance P X X.
Local Notation "''V_' P [ X ]" := (variance X).

Lemma varianceE (X : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
  'V_P[X] = 'E_P[X ^+ 2] - ('E_P[X]) ^+ 2.
Proof. by move=> X1 X2; rewrite /variance covarianceE. Qed.

Lemma variance_fin_num (X : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o X ^+ 2)%R ->
  'V_P[X] \is a fin_num.
Proof. by move=> /[dup]; apply: covariance_fin_num. Qed.

Lemma variance_ge0 (X : {RV P >-> R}) : (0 <= 'V_P[X])%E.
Proof.
by rewrite /variance unlock; apply: expectation_ge0 => x; apply: sqr_ge0.
Qed.

Lemma variance_cst r : 'V_P[cst r] = 0%E.
Proof.
rewrite /variance unlock expectation_cst/=.
rewrite [X in 'E_P[X]](_ : _ = cst 0%R) ?expectation_cst//.
by apply/funext => x; rewrite /GRing.exp/GRing.mul/= subrr mulr0.
Qed.

Lemma varianceZ a (X : {RV P >-> R}) :
  P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
  'V_P[(a \o* X)%R] = (a ^+ 2)%:E * 'V_P[X].
Proof.
move=> X1 X2; rewrite /variance covarianceZl//=.
- by rewrite covarianceZr// muleA.
- by rewrite compre_scale// integrableZl.
- rewrite [X in EFin \o X](_ : _ = (a \o* X ^+ 2)%R); last first.
    by apply/funeqP => x; rewrite mulrA.
  by rewrite compre_scale// integrableZl.
Qed.

Lemma varianceN (X : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
  'V_P[(\- X)%R] = 'V_P[X].
Proof. by move=> X1 X2; rewrite /variance covarianceNN. Qed.

Lemma varianceD (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
    P.-integrable setT (EFin \o Y) -> P.-integrable setT (EFin \o (Y ^+ 2)%R) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  'V_P[X \+ Y]%R = 'V_P[X] + 'V_P[Y] + 2%:E * covariance P X Y.
Proof.
move=> X1 X2 Y1 Y2 XY1.
rewrite -['V_P[_]]/(covariance P (X \+ Y)%R (X \+ Y)%R).
have XY : P.-integrable [set: T] (EFin \o (X \+ Y)%R).
  by rewrite compreDr// integrableD.
rewrite covarianceDl//=; last 3 first.
- rewrite -expr2 sqrrD compreDr ?integrableD// compreDr// integrableD//.
  rewrite -mulr_natr -[(_ * 2)%R]/(2 \o* (X * Y))%R compre_scale//.
  exact: integrableZl.
- by rewrite mulrDr compreDr ?integrableD.
- by rewrite mulrDr mulrC compreDr ?integrableD.
rewrite covarianceDr// covarianceDr; [|by []..|by rewrite mulrC |exact: Y2].
rewrite (covarianceC P Y X) [LHS]addeA [LHS](ACl (1*4*(2*3)))/=.
by rewrite -[2%R]/(1 + 1)%R EFinD muleDl ?mul1e// covariance_fin_num.
Qed.

Lemma varianceB (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
    P.-integrable setT (EFin \o Y) -> P.-integrable setT (EFin \o (Y ^+ 2)%R) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  'V_P[(X \- Y)%R] = 'V_P[X] + 'V_P[Y] - 2%:E * covariance P X Y.
Proof.
move=> X1 X2 Y1 Y2 XY1.
rewrite -[(X \- Y)%R]/(X \+ (\- Y))%R.
rewrite varianceD/= ?varianceN ?covarianceNr ?muleN//.
- by rewrite compreN ?integrableN.
- by rewrite mulrNN.
- by rewrite mulrN compreN ?integrableN.
Qed.

Lemma varianceD_cst_l c (X : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
  'V_P[(cst c \+ X)%R] = 'V_P[X].
Proof.
move=> X1 X2.
rewrite varianceD//=; last 3 first.
- exact: finite_measure_integrable_cst.
- by rewrite compre_scale// integrableZl// finite_measure_integrable_cst.
- by rewrite mulrC compre_scale ?integrableZl.
by rewrite variance_cst add0e covariance_cst_l mule0 adde0.
Qed.

Lemma varianceD_cst_r (X : {RV P >-> R}) c :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
  'V_P[(X \+ cst c)%R] = 'V_P[X].
Proof.
move=> X1 X2.
have -> : (X \+ cst c = cst c \+ X)%R by apply/funeqP => x /=; rewrite addrC.
exact: varianceD_cst_l.
Qed.

Lemma varianceB_cst_l c (X : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
  'V_P[(cst c \- X)%R] = 'V_P[X].
Proof.
move=> X1 X2.
rewrite -[(cst c \- X)%R]/(cst c \+ (\- X))%R varianceD_cst_l/=; last 2 first.
- by rewrite compreN ?integrableN.
- by rewrite mulrNN; apply: X2.
by rewrite varianceN.
Qed.

Lemma varianceB_cst_r (X : {RV P >-> R}) c :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
  'V_P[(X \- cst c)%R] = 'V_P[X].
Proof.
by move=> X1 X2; rewrite -[(X \- cst c)%R]/(X \+ (cst (- c)))%R varianceD_cst_r.
Qed.

Lemma covariance_le (X Y : {RV P >-> R}) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
    P.-integrable setT (EFin \o Y) -> P.-integrable setT (EFin \o (Y ^+ 2)%R) ->
    P.-integrable setT (EFin \o (X * Y)%R) ->
  covariance P X Y <= sqrte 'V_P[X] * sqrte 'V_P[Y].
Proof.
move=> X1 X2 Y1 Y2 XY1.
rewrite -sqrteM ?variance_ge0//.
rewrite lee_sqrE ?sqrte_ge0// sqr_sqrte ?mule_ge0 ?variance_ge0//.
rewrite -(fineK (variance_fin_num X1 X2)) -(fineK (variance_fin_num Y1 Y2)).
rewrite -(fineK (covariance_fin_num X1 Y1 XY1)).
rewrite -EFin_expe -EFinM lee_fin -(@ler_pM2l _ 4) ?ltr0n// [leRHS]mulrA.
rewrite [in leLHS](_ : 4 = 2 * 2)%R -natrM// [in leLHS]natrM mulrACA -expr2.
rewrite -subr_le0; apply: deg_le2_ge0 => r; rewrite -lee_fin !EFinD.
rewrite EFinM fineK ?variance_fin_num// muleC -varianceZ//.
rewrite 2!EFinM ?fineK ?variance_fin_num// ?covariance_fin_num//.
rewrite -muleA [_ * r%:E]muleC -covarianceZl//.
rewrite addeAC -varianceD ?variance_ge0//=.
- by rewrite compre_scale ?integrableZl.
- rewrite [X in EFin \o X](_ : _ = r ^+2 \o* X ^+ 2)%R 1?mulrACA//.
  by rewrite compre_scale ?integrableZl.
- by rewrite -mulrAC compre_scale// integrableZl.
Qed.

End variance.
Notation "'V_ P [ X ]" := (variance P X).

Section markov_chebyshev_cantelli.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma markov (X : {RV P >-> R}) (f : R -> R) (eps : R) :
    (0 < eps)%R ->
    measurable_fun [set: R] f -> (forall r, 0 <= f r)%R ->
    {in Num.nneg &, {homo f : x y / x <= y}}%R ->
  (f eps)%:E * P [set x | eps%:E <= `| (X x)%:E | ] <=
    'E_P[f \o (fun x => `| x |%R) \o X].
Proof.
move=> e0 mf f0 f_nd; rewrite -(setTI [set _ | _]).
apply: (le_trans (@le_integral_comp_abse _ _ _ P _ measurableT (EFin \o X)
  eps (er_map f) _ _ _ _ e0)) => //=.
- exact: measurable_er_map.
- by case => //= r _; exact: f0.
- move=> [x| |] [y| |]; rewrite !inE/= !in_itv/= ?andbT ?lee_fin ?leey//.
  by move=> ? ? ?; rewrite f_nd.
- exact/EFin_measurable_fun.
- by rewrite unlock.
Qed.

Definition mmt_gen_fun (X : {RV P >-> R}) (t : R) := 'E_P[expR \o t \o* X].

Lemma chernoff (X : {RV P >-> R}) (r a : R) : (0 < r)%R ->
  P [set x | X x >= a]%R <= mmt_gen_fun X r * (expR (- (r * a)))%:E.
Proof.
move=> t0.
rewrite /mmt_gen_fun; have -> : expR \o r \o* X =
    (normr \o normr) \o [the {mfun T >-> R} of expR \o r \o* X].
  by apply: funext => t /=; rewrite normr_id ger0_norm ?expR_ge0.
rewrite expRN lee_pdivl_mulr ?expR_gt0//.
rewrite (le_trans _ (markov _ (expR_gt0 (r * a)) _ _ _))//; last first.
  exact: (monoW_in (@ger0_le_norm _)).
rewrite ger0_norm ?expR_ge0// muleC lee_pmul2l// ?lte_fin ?expR_gt0//.
rewrite [X in _ <= P X](_ : _ = [set x | a <= X x]%R)//; apply: eq_set => t/=.
by rewrite ger0_norm ?expR_ge0// lee_fin ler_expR  mulrC ler_pM2r.
Qed.

Lemma chebyshev (X : {RV P >-> R}) (eps : R) : (0 < eps)%R ->
  P [set x | (eps <= `| X x - fine ('E_P[X])|)%R ] <= (eps ^- 2)%:E * 'V_P[X].
Proof.
move => heps; have [->|hv] := eqVneq 'V_P[X] +oo.
  by rewrite mulr_infty gtr0_sg ?mul1e// ?leey// invr_gt0// exprn_gt0.
have h (Y : {RV P >-> R}) :
    P [set x | (eps <= `|Y x|)%R] <= (eps ^- 2)%:E * 'E_P[Y ^+ 2].
  rewrite -lee_pdivr_mull; last by rewrite invr_gt0// exprn_gt0.
  rewrite exprnN expfV exprz_inv opprK -exprnP.
  apply: (@le_trans _ _ ('E_P[(@GRing.exp R ^~ 2%N \o normr) \o Y])).
    apply: (@markov Y (@GRing.exp R ^~ 2%N)) => //.
    - by move=> r; apply: sqr_ge0.
    - move=> x y; rewrite !nnegrE => x0 y0.
      by rewrite ler_sqr.
  apply: expectation_le => //.
    - by apply: measurableT_comp => //; exact: measurableT_comp.
  - by move=> x /=; apply: sqr_ge0.
  - by move=> x /=; apply: sqr_ge0.
  - by apply/aeW => t /=; rewrite real_normK// num_real.
have := h [the {mfun T >-> R} of (X \- cst (fine ('E_P[X])))%R].
by move=> /le_trans; apply; rewrite /variance [in leRHS]unlock.
Qed.

Lemma cantelli (X : {RV P >-> R}) (lambda : R) :
    P.-integrable setT (EFin \o X) -> P.-integrable setT (EFin \o (X ^+ 2)%R) ->
    (0 < lambda)%R ->
  P [set x | lambda%:E <= (X x)%:E - 'E_P[X]]
  <= (fine 'V_P[X] / (fine 'V_P[X] + lambda^2))%:E.
Proof.
move=> X1 X2 lambda_gt0.
have finEK : (fine 'E_P[X])%:E = 'E_P[X].
  by rewrite fineK ?unlock ?integral_fune_fin_num.
have finVK : (fine 'V_P[X])%:E = 'V_P[X] by rewrite fineK ?variance_fin_num.
pose Y := (X \- cst (fine 'E_P[X]))%R.
have Y1 : P.-integrable [set: T] (EFin \o Y).
  rewrite compreBr => [|//]; apply: integrableB X1 _ => [//|].
  exact: finite_measure_integrable_cst.
have Y2 : P.-integrable [set: T] (EFin \o (Y ^+ 2)%R).
  rewrite sqrrD/= compreDr => [|//].
  apply: integrableD => [//||]; last first.
    rewrite -[(_ ^+ 2)%R]/(cst ((- fine 'E_P[X]) ^+ 2)%R).
    exact: finite_measure_integrable_cst.
  rewrite compreDr => [|//]; apply: integrableD X2 _ => [//|].
  rewrite [X in EFin \o X](_ : _ = (- fine 'E_P[X] * 2) \o* X)%R; last first.
    by apply/funeqP => x /=; rewrite -mulr_natl mulrC mulrA.
  by rewrite compre_scale => [|//]; apply: integrableZl X1.
have EY : 'E_P[Y] = 0.
  rewrite expectationB/= ?finite_measure_integrable_cst//.
  rewrite expectation_cst finEK subee//.
  by rewrite unlock; apply: integral_fune_fin_num X1.
have VY : 'V_P[Y] = 'V_P[X] by rewrite varianceB_cst_r.
have le (u : R) : (0 <= u)%R ->
    P [set x | lambda%:E <= (X x)%:E - 'E_P[X]]
    <= ((fine 'V_P[X] + u^2) / (lambda + u)^2)%:E.
  move=> uge0; rewrite EFinM.
  have YU1 : P.-integrable [set: T] (EFin \o (Y \+ cst u)%R).
    rewrite compreDr => [|//]; apply: integrableD Y1 _ => [//|].
    exact: finite_measure_integrable_cst.
  have YU2 : P.-integrable [set: T] (EFin \o ((Y \+ cst u) ^+ 2)%R).
    rewrite sqrrD/= compreDr => [|//].
    apply: integrableD => [//||]; last first.
      rewrite -[(_ ^+ 2)%R]/(cst (u ^+ 2))%R.
      exact: finite_measure_integrable_cst.
    rewrite compreDr => [|//]; apply: integrableD Y2 _ => [//|].
    rewrite [X in EFin \o X](_ : _ = (2 * u) \o* Y)%R; last first.
      by apply/funeqP => x /=; rewrite -mulr_natl mulrCA.
    by rewrite compre_scale => [|//]; apply: integrableZl Y1.
  have -> : (fine 'V_P[X] + u^2)%:E = 'E_P[(Y \+ cst u)^+2]%R.
    rewrite -VY -[RHS](@subeK _ _ (('E_P[(Y \+ cst u)%R])^+2)); last first.
      by rewrite fin_numX ?unlock ?integral_fune_fin_num.
    rewrite -varianceE/= -/Y -?expe2//.
    rewrite expectationD/= ?EY ?add0e ?expectation_cst -?EFinM; last 2 first.
    - rewrite compreBr => [|//]; apply: integrableB X1 _ => [//|].
      exact: finite_measure_integrable_cst.
    - exact: finite_measure_integrable_cst.
    by rewrite (varianceD_cst_r _ Y1 Y2) EFinD fineK ?(variance_fin_num Y1 Y2).
  have le : [set x | lambda%:E <= (X x)%:E - 'E_P[X]]
      `<=` [set x | ((lambda + u)^2)%:E <= ((Y x + u)^+2)%:E].
    move=> x /= le; rewrite lee_fin; apply: lerXn2r.
    - exact: addr_ge0 (ltW lambda_gt0) _.
    - apply/(addr_ge0 _ uge0)/(le_trans (ltW lambda_gt0) _).
      by rewrite -lee_fin EFinB finEK.
    - by rewrite lerD2r -lee_fin EFinB finEK.
  apply: (le_trans (le_measure _ _ _ le)).
  - rewrite -[[set _ | _]]setTI inE; apply: emeasurable_fun_c_infty => [//|].
    by apply: emeasurable_funB => //; exact: measurable_int X1.
  - rewrite -[[set _ | _]]setTI inE; apply: emeasurable_fun_c_infty => [//|].
    rewrite EFin_measurable_fun [X in measurable_fun _ X](_ : _ =
      (fun x => x ^+ 2) \o (fun x => Y x + u))%R//.
    apply/measurableT_comp => //; apply/measurable_funD => //.
    by rewrite -EFin_measurable_fun; apply: measurable_int Y1.
  set eps := ((lambda + u) ^ 2)%R.
  have peps : (0 < eps)%R by rewrite exprz_gt0 ?ltr_wpDr.
  rewrite (lee_pdivl_mulr _ _ peps) muleC.
  under eq_set => x.
    rewrite -[leRHS]gee0_abs ?lee_fin ?sqr_ge0 -?lee_fin => [|//].
    rewrite -[(_ ^+ 2)%R]/(((Y \+ cst u) ^+ 2) x)%R; over.
  rewrite -[X in X%:E * _]gtr0_norm => [|//].
  apply: (le_trans (markov _ peps _ _ _)) => //=.
    by move=> x y /[!nnegrE] /ger0_norm-> /ger0_norm->.
  rewrite -/Y le_eqVlt; apply/orP; left; apply/eqP; congr expectation.
  by apply/funeqP => x /=; rewrite -expr2 normr_id ger0_norm ?sqr_ge0.
pose u0 := (fine 'V_P[X] / lambda)%R.
have u0ge0 : (0 <= u0)%R.
  by apply: divr_ge0 (ltW lambda_gt0); rewrite -lee_fin finVK variance_ge0.
apply: le_trans (le _ u0ge0) _; rewrite lee_fin le_eqVlt; apply/orP; left.
rewrite eqr_div; [|apply: lt0r_neq0..]; last 2 first.
- by rewrite exprz_gt0 -1?[ltLHS]addr0 ?ltr_leD.
- by rewrite ltr_wpDl ?fine_ge0 ?variance_ge0 ?exprz_gt0.
apply/eqP; have -> : fine 'V_P[X] = (u0 * lambda)%R.
  by rewrite /u0 -mulrA mulVr ?mulr1 ?unitfE ?gt_eqF.
by rewrite -mulrDl -mulrDr (addrC u0) [in RHS](mulrAC u0) -exprnP expr2 !mulrA.
Qed.

End markov_chebyshev_cantelli.

HB.mixin Record MeasurableFun_isDiscrete d (T : measurableType d) (R : realType)
    (X : T -> R) of @MeasurableFun d T R X := {
  countable_range : countable (range X)
}.

HB.structure Definition discreteMeasurableFun d (T : measurableType d)
    (R : realType) := {
  X of isMeasurableFun d T R X & MeasurableFun_isDiscrete d T R X
}.

Notation "{ 'dmfun' aT >-> T }" :=
  (@discreteMeasurableFun.type _ aT T) : form_scope.

Definition discrete_random_variable (d : _) (T : measurableType d)
  (R : realType) (P : probability T R) := {dmfun T >-> R}.

Notation "{ 'dRV' P >-> R }" :=
  (@discrete_random_variable _ _ R P) : form_scope.

Section dRV_definitions.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Definition dRV_dom_enum (X : {dRV P >-> R}) :
  { B : set nat & {splitbij B >-> range X}}.
Proof.
have /countable_bijP/cid[B] := @countable_range _ _ _ X.
move/card_esym/ppcard_eqP/unsquash => f.
exists B; exact: f.
Qed.

Definition dRV_dom (X : {dRV P >-> R}) : set nat := projT1 (dRV_dom_enum X).

Definition dRV_enum (X : {dRV P >-> R}) : {splitbij (dRV_dom X) >-> range X} :=
  projT2 (dRV_dom_enum X).

Definition enum_prob (X : {dRV P >-> R}) :=
  (fun k => P (X @^-1` [set dRV_enum X k])) \_ (dRV_dom X).

End dRV_definitions.

Section distribution_dRV.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).
Variable X : {dRV P >-> R}.

Lemma distribution_dRV_enum (n : nat) : n \in dRV_dom X ->
  distribution P X [set dRV_enum X n] = enum_prob X n.
Proof.
by move=> nX; rewrite /distribution/= /enum_prob/= patchE nX.
Qed.

Lemma distribution_dRV A : measurable A ->
  distribution P X A = \sum_(k <oo) enum_prob X k * \d_ (dRV_enum X k) A.
Proof.
move=> mA; rewrite /distribution /pushforward.
have mAX i : dRV_dom X i -> measurable (X @^-1` (A `&` [set dRV_enum X i])).
  move=> _; rewrite preimage_setI; apply: measurableI => //.
  exact/measurable_sfunP.
have tAX : trivIset (dRV_dom X) (fun k => X @^-1` (A `&` [set dRV_enum X k])).
  under eq_fun do rewrite preimage_setI; rewrite -/(trivIset _ _).
  apply: trivIset_setIl; apply/trivIsetP => i j iX jX /eqP ij.
  rewrite -preimage_setI (_ : _ `&` _ = set0)//.
  by apply/seteqP; split => //= x [] -> {x} /inj; rewrite inE inE => /(_ iX jX).
have := measure_bigcup P _ (fun k => X @^-1` (A `&` [set dRV_enum X k])) mAX tAX.
rewrite -preimage_bigcup => {mAX tAX}PXU.
rewrite -{1}(setIT A) -(setUv (\bigcup_(i in dRV_dom X) [set dRV_enum X i])).
rewrite setIUr preimage_setU measureU; last 3 first.
  - rewrite preimage_setI; apply: measurableI => //.
      exact: measurable_sfunP.
    by apply: measurable_sfunP; exact: bigcup_measurable.
  - apply: measurable_sfunP; apply: measurableI => //.
    by apply: measurableC; exact: bigcup_measurable.
  - rewrite 2!preimage_setI setIACA -!setIA -preimage_setI.
    by rewrite setICr preimage_set0 2!setI0.
rewrite [X in _ + X = _](_ : _ = 0) ?adde0; last first.
  rewrite (_ : _ @^-1` _ = set0) ?measure0//; apply/disjoints_subset => x AXx.
  rewrite setCK /bigcup /=; exists ((dRV_enum X)^-1 (X x))%function.
    exact: funS.
  by rewrite invK// inE.
rewrite setI_bigcupr; etransitivity; first exact: PXU.
rewrite eseries_mkcond; apply: eq_eseriesr => k _.
rewrite /enum_prob patchE; case: ifPn => nX; rewrite ?mul0e//.
rewrite diracE; have [kA|] := boolP (_ \in A).
  by rewrite mule1 setIidr// => _ /= ->; exact: set_mem.
rewrite notin_setE => kA.
rewrite mule0 (disjoints_subset _ _).2 ?preimage_set0 ?measure0//.
by apply: subsetCr; rewrite sub1set inE.
Qed.

Lemma sum_enum_prob : \sum_(n <oo) (enum_prob X) n = 1.
Proof.
have := distribution_dRV measurableT.
rewrite probability_setT/= => /esym; apply: eq_trans.
by rewrite [RHS]eseries_mkcond; apply: eq_eseriesr => k _; rewrite diracT mule1.
Qed.

End distribution_dRV.

Section discrete_distribution.
Local Open Scope ereal_scope.
Context d (T : measurableType d) (R : realType) (P : probability T R).

Lemma dRV_expectation (X : {dRV P >-> R}) :
  P.-integrable [set: T] (EFin \o X) ->
  'E_P[X] = \sum_(n <oo) enum_prob X n * (dRV_enum X n)%:E.
Proof.
move=> ix; rewrite unlock.
rewrite -[in LHS](_ : \bigcup_k (if k \in dRV_dom X then
    X @^-1` [set dRV_enum X k] else set0) = setT); last first.
  apply/seteqP; split => // t _.
  exists ((dRV_enum X)^-1%function (X t)) => //.
  case: ifPn=> [_|].
    by rewrite invK// inE.
  by rewrite notin_setE/=; apply; apply: funS.
have tA : trivIset (dRV_dom X) (fun k => [set dRV_enum X k]).
  by move=> i j iX jX [r [/= ->{r}]] /inj; rewrite !inE; exact.
have {tA}/trivIset_mkcond tXA :
    trivIset (dRV_dom X) (fun k => X @^-1` [set dRV_enum X k]).
  apply/trivIsetP => /= i j iX jX ij.
  move/trivIsetP : tA => /(_ i j iX jX) Aij.
  by rewrite -preimage_setI Aij ?preimage_set0.
rewrite integral_bigcup //; last 2 first.
  - by move=> k; case: ifPn.
  - apply: (integrableS measurableT) => //.
    by rewrite -bigcup_mkcond; exact: bigcup_measurable.
transitivity (\sum_(i <oo)
  \int[P]_(x in (if i \in dRV_dom X then X @^-1` [set dRV_enum X i] else set0))
    (dRV_enum X i)%:E).
  apply: eq_eseriesr => i _; case: ifPn => iX.
    by apply: eq_integral => t; rewrite in_setE/= => ->.
  by rewrite !integral_set0.
transitivity (\sum_(i <oo) (dRV_enum X i)%:E *
  \int[P]_(x in (if i \in dRV_dom X then X @^-1` [set dRV_enum X i] else set0))
    1).
  apply: eq_eseriesr => i _; rewrite -integralZl//; last 2 first.
    - by case: ifPn.
    - apply/integrableP; split => //.
      rewrite (eq_integral (cst 1%E)); last by move=> x _; rewrite abse1.
      rewrite integral_cst//; last by case: ifPn.
      rewrite mul1e (@le_lt_trans _ _ 1%E) ?ltey//.
      by case: ifPn => // _; exact: probability_le1.
  by apply: eq_integral => y _; rewrite mule1.
apply: eq_eseriesr => k _; case: ifPn => kX.
  rewrite /= integral_cst//= mul1e probability_distribution muleC.
  by rewrite distribution_dRV_enum.
by rewrite integral_set0 mule0 /enum_prob patchE (negbTE kX) mul0e.
Qed.

Definition pmf (X : {RV P >-> R}) (r : R) : R := fine (P (X @^-1` [set r])).

Lemma expectation_pmf (X : {dRV P >-> R}) :
    P.-integrable [set: T] (EFin \o X) -> 'E_P[X] =
  \sum_(n <oo | n \in dRV_dom X) (pmf X (dRV_enum X n))%:E * (dRV_enum X n)%:E.
Proof.
move=> iX; rewrite dRV_expectation// [in RHS]eseries_mkcond.
apply: eq_eseriesr => k _.
rewrite /enum_prob patchE; case: ifPn => kX; last by rewrite mul0e.
by rewrite /pmf fineK// fin_num_measure.
Qed.

End discrete_distribution.

(* TODO: move *)
Lemma onem_nonneg_proof (R : numDomainType) (p : {nonneg R}) :
  (p%:num <= 1 -> 0 <= `1-(p%:num))%R.
Proof. by rewrite /onem/= subr_ge0. Qed.

Definition onem_nonneg (R : numDomainType) (p : {nonneg R})
   (p1 : (p%:num <= 1)%R) :=
  NngNum (onem_nonneg_proof p1).

Section bernoulli.
Local Open Scope ereal_scope.
Variables (R : realType) (p : {nonneg R}) (p1 : (p%:num <= 1)%R).

Definition bernoulli : set bool -> \bar R := measure_add
  (mscale p (dirac true)) (mscale (onem_nonneg p1) (dirac false)).

HB.instance Definition _ := Measure.on bernoulli.

Let bernoulli_setT : bernoulli [set: _] = 1.
Proof.
rewrite /bernoulli/= measure_addE/= /mscale/= !diracT !mule1.
by rewrite -EFinD add_onemK.
Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ R bernoulli bernoulli_setT.

Lemma integral_bernoulli (f : bool -> \bar R) : (forall x, 0 <= f x) ->
  \int[bernoulli]_y (f y) = p%:num%:E * f true + (`1-(p%:num))%:E * f false.
Proof.
move=> f0.
rewrite ge0_integral_measure_sum// 2!big_ord_recl/= big_ord0 adde0/=.
by rewrite !ge0_integral_mscale//= !integral_dirac//= !diracT !mul1e.
Qed.

End bernoulli.

(* TODO: move *)
Lemma sumbool_ler {R : realDomainType} (x y : R) : (x <= y)%R + (x > y)%R.
Proof. by have [_|_] := leP x y; [exact: inl|exact: inr]. Qed.

Lemma measurable_fun_TF d1 (T1 : measurableType d1) (D : set T1) (f : T1 -> bool) :
  measurable (D `&` f @^-1` [set true]) ->
  measurable (D `&` f @^-1` [set false]) -> measurable_fun D f.
Proof.
move=> mT mF mD /= Y mY.
have := @subsetT _ Y; rewrite setT_bool => YT.
move: mY; have [-> _|-> _|-> _ |-> _] := subset_set2 YT.
- by rewrite preimage0 ?setI0.
- exact: mT.
- exact: mF.
- by rewrite -setT_bool preimage_setT setIT.
Qed.

Lemma measurable_and d1 (T1 : measurableType d1) (D : set T1)
  (f : T1 -> bool) (g : T1 -> bool) :
  measurable_fun D f -> measurable_fun D g ->
  measurable_fun D (fun x => f x && g x).
Proof.
move=> mf mg mD; apply: measurable_fun_TF => //.
- rewrite [X in measurable X](_ : _ =
    D `&` f @^-1` [set true] `&` (D `&` g @^-1` [set true])); last first.
    rewrite setICA !setIA setIid -setIA; congr (_ `&` _).
    by apply/seteqP; split => x /andP.
  by apply: measurableI; [exact: mf|exact: mg].
- rewrite [X in measurable X](_ : _ =
    D `&` f @^-1` [set false] `|` (D `&` g @^-1` [set false])); last first.
    rewrite -setIUr; congr (_ `&` _).
    apply/seteqP; split => x /=.
      by case: (f x); case: (g x); [|right|left|left].
    by case: (f x); case: (g x) => //= -[].
  by apply: measurableU; [exact: mf|exact: mg].
Qed.

Lemma measurable_fun_pow d (T : measurableType d) (R : realType) (D : set T)
    (f : T -> R) n : measurable_fun D f ->
  measurable_fun D (fun x => f x ^+ n).
Proof.
move=> mf.
exact: (@measurable_comp _ _ _ _ _ _ setT (fun x : R => x ^+ n) _ f).
Qed.

Section bernoulli_total.
Local Open Scope ring_scope.
Variable R : realType.
Implicit Type p : R.

Definition bernoulli0 := @bernoulli R 0%:nng ler01.

HB.instance Definition _ := Probability.on bernoulli0.

Definition bernoulliT p : probability bool R :=
  if sumbool_ler 0 p is inl l0p then
    if sumbool_ler (NngNum l0p)%:num 1%R is inl lp1 then
      bernoulli lp1
    else bernoulli0
  else bernoulli0.

Lemma bernoulliTE p U : 0 <= p <= 1 ->
  (bernoulliT p U = p%:E * \d_true U + (`1-p)%:E * \d_false U)%E.
Proof.
move=> /andP[p0 p1].
rewrite /bernoulliT; case: sumbool_ler => [{}p0/=|]; last first.
  by rewrite ltNge p0.
case: sumbool_ler => [{}p1/=|]; last by rewrite ltNge p1.
by rewrite /bernoulli/= measure_addE.
Qed.

Lemma bernoulliT_le1 p U : (bernoulliT p U <= 1)%E.
Proof.
rewrite /bernoulliT; case: sumbool_ler => //= p0; last first.
  by rewrite probability_le1.
by case: sumbool_ler => //= p1; rewrite probability_le1.
Qed.

Lemma measurable_bernoulliT :
  measurable_fun setT (bernoulliT : R -> pprobability bool R).
Proof.
apply: (@measurability _ _ _ _ _ _
 (@pset _ _ _ : set (set (pprobability _ R)))) => //.
move=> _ -[_ [r r01] [Ys mYs <-]] <-; apply: emeasurable_fun_infty_o => //=.
rewrite /bernoulliT.
have := @subsetT _ Ys; rewrite setT_bool => UT.
have [->|->|->|->] /= := subset_set2 UT.
- rewrite [X in measurable_fun _ X](_ : _ = cst 0%E)//.
  by apply/funext => x/=; case: sumbool_ler.
- rewrite [X in measurable_fun _ X](_ : _ =
    (fun x => if 0 <= x <= 1 then x%:E else 0%E))//.
    apply: measurable_fun_ifT => //=; apply: measurable_and => //;
    apply: (measurable_fun_bool true) => //=.
      rewrite (_ : _ @^-1` _ = `[0, +oo[%classic)//.
      by apply/seteqP; split => [x|x] /=; rewrite in_itv/= andbT.
    by rewrite (_ : _ @^-1` _ = `]-oo, 1]%classic).
  apply/funext => x/=; case: sumbool_ler => /= x0.
    case: sumbool_ler => /= x1.
      rewrite x0 x1/= /bernoulli/= measure_addE/= /mscale/= !diracE.
      by rewrite mem_set//= memNset//= mule0 adde0 mule1.
    rewrite x0/= leNgt x1/= /bernoulli0 /bernoulli /= measure_addE/= /mscale/=.
    by rewrite mul0e add0e diracE memNset//= mule0.
  rewrite leNgt x0/= /bernoulli0 /bernoulli /= measure_addE/= /mscale/=.
  by rewrite mul0e add0e diracE memNset//= mule0.
- rewrite [X in measurable_fun _ X](_ : _ =
    (fun x => if 0 <= x <= 1 then (`1-x)%:E else 1%E))//.
    apply: measurable_fun_ifT => //=.
      apply: measurable_and => //; apply: (measurable_fun_bool true) => //=.
        rewrite (_ : _ @^-1` _ = `[0, +oo[%classic)//.
        by apply/seteqP; split => [x|x] /=; rewrite in_itv/= andbT.
      by rewrite (_ : _ @^-1` _ = `]-oo, 1]%classic).
    exact/EFin_measurable_fun/measurable_funB.
  apply/funext => x/=; case: sumbool_ler => /= x0.
    case: sumbool_ler => /= x1.
      rewrite /bernoulli/= measure_addE/= /mscale/=.
      by rewrite !diracE memNset//= mule0 add0e mem_set//= mule1 x0 x1.
    rewrite /bernoulli0 /bernoulli /= measure_addE/= /mscale/=.
    by rewrite mul0e add0e onem0 mul1e diracE mem_set//= x0/= leNgt x1.
  rewrite /bernoulli0 /bernoulli /= measure_addE/= /mscale/=.
  by rewrite mul0e add0e onem0 mul1e diracE mem_set//= leNgt x0.
- rewrite [X in measurable_fun _ X](_ : _ = cst 1%E)//; apply/funext => x/=.
  case: sumbool_ler => /= x0.
    case: sumbool_ler => /= x1.
      rewrite /bernoulli/= measure_addE/=.
      by rewrite /mscale/= -setT_bool !diracT !mule1 -EFinD add_onemK.
    rewrite /bernoulli0 /bernoulli/= measure_addE/=.
    by rewrite /mscale/= -setT_bool !diracT mul0e mule1 add0e onem0.
  rewrite /bernoulli0 /bernoulli/= measure_addE/=.
  by rewrite /mscale/= -setT_bool !diracT mul0e add0e mule1 onem0.
Qed.

Lemma measurable_bernoulliT2 U : measurable U ->
  measurable_fun setT (bernoulliT ^~ U : R -> \bar R).
Proof.
by move=> ?; exact: (measurable_kernel (kprobability measurable_bernoulliT)).
Qed.

Lemma integral_bernoulliT p (f : bool -> \bar R) :
    0 <= p <= 1 -> (forall x, 0 <= f x)%E ->
  (\int[bernoulliT p]_y (f y) = p%:E * f true + (`1-p)%:E * f false)%E.
Proof.
move=> /andP[p0 p1] f0; rewrite /bernoulliT; case: sumbool_ler => [? /=|].
  case: (sumbool_ler p 1) => [? /=|]; last by rewrite ltNge p1.
  by rewrite integral_bernoulli.
by rewrite ltNge p0.
Qed.

End bernoulli_total.
Arguments bernoulliT {R}.
Arguments measurable_bernoulliT {R}.

Section binomial_probability.
Local Open Scope ring_scope.
Context {R : realType} (n : nat) (p : {nonneg R}) (p1 : p%:num <= 1).

Definition bin_prob (k : nat) : {nonneg R} :=
  (p%:num^+k * (NngNum (onem_ge0 p1))%:num^+(n-k)%N *+ 'C(n, k))%:nng.

Lemma bin_prob0 : bin_prob 0 = ((NngNum (onem_ge0 p1))%:num^+n)%:nng.
Proof.
rewrite /bin_prob bin0 subn0/=; apply/val_inj => /=.
by rewrite expr0 mul1r mulr1n.
Qed.

Lemma bin_prob1 :
  bin_prob 1 = (p%:num * (NngNum (onem_ge0 p1))%:num^+(n-1)%N *+ n)%:nng.
Proof. by rewrite /bin_prob bin1/=; apply/val_inj => /=; rewrite expr1. Qed.

Definition binomial_prob : set nat -> \bar R :=
  msum (fun k => mscale (bin_prob k) \d_k) n.+1.

HB.instance Definition _ := Measure.on binomial_prob.

Let binomial_setT : binomial_prob [set: _] = 1%:E.
Proof.
rewrite /binomial_prob /msum /mscale /bin_prob/= /mscale/=.
under eq_bigr do rewrite diracT mule1.
rewrite sumEFin.
under eq_bigr do rewrite mulrC.
by rewrite -exprDn_comm ?subrK ?expr1n//; exact: mulrC.
Qed.

HB.instance Definition _ :=
  Measure_isProbability.Build _ _ R binomial_prob binomial_setT.

Lemma integral_binomial (f : nat -> \bar R) : (forall x, 0 <= f x)%E ->
  (\int[binomial_prob]_y (f y) = \sum_(k < n.+1) (bin_prob k)%:num%:E * f k)%E.
Proof.
move=> f0; rewrite ge0_integral_measure_sum//=; apply: eq_bigr => i _.
by rewrite ge0_integral_mscale//= integral_dirac//= diracT mul1e.
Qed.

End binomial_probability.

Section binomial_total.
Local Open Scope ring_scope.
Variables (R : realType) (n : nat).
Implicit Type p : R.

Definition binomial_prob0 := @binomial_prob R 0 0%:nng ler01.

Definition binomial_probT p : probability nat R :=
  if sumbool_ler 0 p is inl l0p then
    if sumbool_ler (NngNum l0p)%:num 1 is inl lp1 then
      @binomial_prob R n (NngNum l0p) lp1
    else binomial_prob0
  else binomial_prob0.

Lemma measurable_binomial_probT :
  measurable_fun setT (binomial_probT : R -> pprobability _ _).
Proof.
apply: (@measurability _ _ _ _ _ _
  (@pset _ _ _ : set (set (pprobability _ R)))) => //.
move=> _ -[_ [r r01] [Ys mYs <-]] <-; apply: emeasurable_fun_infty_o => //=.
rewrite /binomial_probT/=.
set f := (X in measurable_fun _ X).
rewrite (_ : f = fun x => if 0 <= x <= 1 then (\sum_(m < n.+1)
      if sumbool_ler 0 x is inl l0p then
        if sumbool_ler x 1 is inl lp1 then
           mscale (@bin_prob _ n (NngNum l0p) lp1 m) (\d_(nat_of_ord m)) Ys
         else
          (x ^+ m * `1-x ^+ (n - m) *+ 'C(n, m))%:E * \d_(nat_of_ord m) Ys
      else (x ^+ m * `1-x ^+ (n - m) *+ 'C(n, m))%:E * \d_(nat_of_ord m) Ys)%E
   else \d_0%N Ys)//.
  move=> _; apply: measurable_fun_ifT => //=.
    apply: measurable_and => //; apply: (measurable_fun_bool true) => //=.
      rewrite (_ : _ @^-1` _ = `[0, +oo[%classic)//.
      by apply/seteqP; split => [x|x] /=; rewrite in_itv/= andbT.
    by rewrite (_ : _ @^-1` _ = `]-oo, 1]%classic).
  apply: emeasurable_fun_sum => m /=.
  rewrite /mscale/= [X in measurable_fun _ X](_ : _ = (fun x =>
    (x ^+ m * `1-x ^+ (n - m) *+ 'C(n, m))%:E * \d_(nat_of_ord m) Ys)%E); last first.
    by apply:funext => x; case: sumbool_ler => // x0; case: sumbool_ler.
  apply: emeasurable_funM => //; apply/EFin_measurable_fun => //.
  under eq_fun do rewrite -mulr_natr.
  do 2 apply: measurable_funM => //.
  exact/measurable_fun_pow/measurable_funB.
rewrite {}/f; apply/funext => x.
case: sumbool_ler => /= x0; last first.
  rewrite leNgt x0/= /binomial_prob /= /msum big_ord_recl/= big_ord0 /mscale.
  by rewrite bin_prob0/= expr0 mul1e adde0.
rewrite x0/=; case: sumbool_ler => /= x1; last first.
  rewrite (leNgt x) x1/= /binomial_prob /msum big_ord_recl/=/=.
  by rewrite bin_prob0/= big_ord0 adde0 /mscale/= expr0 mul1e.
by rewrite x1.
Qed.

Lemma integral_binomial_probT p (p0 : 0 <= p) (p1 : (NngNum p0)%:num <= 1)
    (f : nat -> \bar R) : (forall x, 0 <= f x)%E ->
  (\int[binomial_probT p]_y (f y) = \sum_(k < n.+1) (bin_prob n p1 k)%:num%:E * f k)%E.
Proof.
move=> f0; rewrite /binomial_probT/=; case: sumbool_ler => [? /=|]; last first.
  by rewrite ltNge p0.
case: sumbool_ler => [?/=|]; last by rewrite ltNge p1.
by rewrite integral_binomial.
Qed.

End binomial_total.
Arguments binomial_probT {R}.
Arguments measurable_binomial_probT {R}.

Section uniform_probability.
Local Open Scope ring_scope.
Context (R : realType) (a b : R).

Definition uniform_pdf x := if a <= x <= b then (b - a)^-1 else 0.

Lemma uniform_pdf_ge0 x : a < b -> 0 <= uniform_pdf x.
Proof.
move=> ab; rewrite /uniform_pdf; case: ifPn => // axb.
by rewrite invr_ge0// ltW// subr_gt0.
Qed.

Lemma measurable_uniform_pdf : measurable_fun setT uniform_pdf.
Proof.
rewrite /uniform_pdf /=; apply: measurable_fun_if => //=.
apply: measurable_and => //.
  apply: (measurable_fun_bool true) => //=.
  rewrite (_ : _ @^-1` _ = `[a, +oo[%classic)//.
  by apply/seteqP; split => [z|z] /=; rewrite in_itv/= andbT.
apply: (measurable_fun_bool true) => //=.
by rewrite (_ : _ @^-1` _ = `]-oo, b]%classic).
Qed.

Local Notation mu := lebesgue_measure.

Lemma integral_uniform_pdf U :
  (\int[mu]_(x in U) (uniform_pdf x)%:E =
   \int[mu]_(x in U `&` `[a, b]) (uniform_pdf x)%:E)%E.
Proof.
rewrite [RHS]integral_mkcondr/=; apply: eq_integral => x xU.
rewrite patchE; case: ifPn => //.
rewrite notin_set/= in_itv/= => /negP/negbTE xab.
by rewrite /uniform_pdf xab.
Qed.

Lemma integral_uniform_pdf1 A (ab : a < b) : `[a, b] `<=` A ->
  (\int[mu]_(x in A) (uniform_pdf x)%:E = 1)%E.
Proof.
move=> abA; rewrite integral_uniform_pdf setIidr//.
rewrite (eq_integral (fun=> (b - a)^-1%:E)); last first.
  by move=> x; rewrite inE/= in_itv/= /uniform_pdf => ->.
rewrite integral_cst//= lebesgue_measure_itv/= lte_fin.
by rewrite ab -EFinD -EFinM mulVf// gt_eqF// subr_gt0.
Qed.

Definition uniform_prob (ab : a < b) : set _ -> \bar R :=
  fun U => (\int[mu]_(x in U) (uniform_pdf x)%:E)%E.

Hypothesis ab : (a < b)%R.

Let uniform0 : uniform_prob ab set0 = 0.
Proof. by rewrite /uniform_prob integral_set0. Qed.

Let uniform_ge0 U : (0 <= uniform_prob ab U)%E.
Proof.
by apply: integral_ge0 => /= x Ux; rewrite lee_fin uniform_pdf_ge0.
Qed.

Lemma integrable_uniform_pdf :
  mu.-integrable setT (fun x => (uniform_pdf x)%:E).
Proof.
apply/integrableP; split.
  by apply: measurableT_comp => //; exact: measurable_uniform_pdf.
under eq_integral.
  move=> x _; rewrite gee0_abs//; last first.
    by rewrite lee_fin uniform_pdf_ge0.
  over.
by rewrite /= integral_uniform_pdf1 ?ltry// -subr_gt0.
Qed.

Let uniform_sigma_additive : semi_sigma_additive (uniform_prob ab).
Proof.
move=> /= F mF tF mUF; rewrite /uniform_prob; apply: cvg_toP.
  apply: ereal_nondecreasing_is_cvgn => m n mn.
  apply: lee_sum_nneg_natr => // k _ _.
  by apply: integral_ge0 => /= x Fkx; rewrite lee_fin uniform_pdf_ge0.
rewrite ge0_integral_bigcup//=.
- by apply: integrableS; [| | | exact: integrable_uniform_pdf].
- by move=> x _; rewrite lee_fin uniform_pdf_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _ (uniform_prob ab)
  uniform0 uniform_ge0 uniform_sigma_additive.

Let uniform_setT : uniform_prob ab [set: _] = 1%:E.
Proof. by rewrite /uniform_prob /mscale/= integral_uniform_pdf1. Qed.

HB.instance Definition _ := @Measure_isProbability.Build _ _ R
  (uniform_prob ab) uniform_setT.

Lemma dominates_uniform_prob : uniform_prob ab `<< mu.
Proof.
move=> A mA muA0; rewrite /uniform_prob integral_uniform_pdf.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  apply: integral_ge0 => x [Ax /=]; rewrite in_itv /= => xab.
  by rewrite lee_fin uniform_pdf_ge0.
apply: (@le_trans _ _
    (\int[mu]_(x in A `&` `[a, b]%classic) (b - a)^-1%:E))%E; last first.
  rewrite integral_cst//= ?mul1e//.
    by rewrite pmule_rle0 ?lte_fin ?invr_gt0// ?subr_gt0// -muA0 measureIl.
  exact: measurableI.
apply: ge0_le_integral => //=.
- exact: measurableI.
- by move=> x [Ax]; rewrite /= in_itv/= => axb; rewrite lee_fin uniform_pdf_ge0.
- by apply/EFin_measurable_fun/measurable_funTS; exact: measurable_uniform_pdf.
- by move=> x [Ax _]; rewrite lee_fin invr_ge0// ltW// subr_gt0.
- by move=> x [Ax]; rewrite in_itv/= /uniform_pdf => ->.
Qed.

Let integral_uniform_indic E : measurable E ->
  (\int[uniform_prob ab]_x (\1_E x)%:E =
   (b - a)^-1%:E * \int[mu]_(x in `[a, b]) (\1_E x)%:E)%E.
Proof.
move=> mE; rewrite integral_indic//= /uniform_prob setIT -ge0_integralZl//=.
- rewrite [LHS]integral_mkcond/= [RHS]integral_mkcond/=.
  apply: eq_integral => x _; rewrite !patchE; case: ifPn => xE.
    case: ifPn.
      rewrite inE/= in_itv/= => xab.
      by rewrite /uniform_pdf xab indicE xE mule1.
    by rewrite notin_set/= in_itv/= => /negP/negbTE; rewrite /uniform_pdf => ->.
  case: ifPn => //.
  by rewrite inE/= in_itv/= => axb; rewrite indicE (negbTE xE) mule0.
- exact/EFin_measurable_fun/measurable_indic.
- by move=> x _; rewrite lee_fin.
- by rewrite lee_fin invr_ge0// ltW// subr_gt0.
Qed.

Let integral_uniform_nnsfun (f : {nnsfun _ >-> R}) :
  (\int[uniform_prob ab]_x (f x)%:E =
   (b - a)^-1%:E * \int[mu]_(x in `[a, b]) (f x)%:E)%E.
Proof.
under [LHS]eq_integral do rewrite fimfunE -fsumEFin//.
rewrite [LHS]ge0_integral_fsum//; last 2 first.
  - by move=> r; exact/EFin_measurable_fun/measurableT_comp.
  - by move=> n x _; rewrite EFinM nnfun_muleindic_ge0.
rewrite -[RHS]ge0_integralZl//; last 3 first.
  - exact/EFin_measurable_fun/measurable_funTS.
  - by move=> x _; rewrite lee_fin.
  - by rewrite lee_fin invr_ge0// ltW// subr_gt0.
under [RHS]eq_integral.
  move=> x xD; rewrite fimfunE -fsumEFin// ge0_mule_fsumr; last first.
    by move=> r; rewrite EFinM nnfun_muleindic_ge0.
  over.
rewrite [RHS]ge0_integral_fsum//; last 2 first.
  - by move=> r; apply/EFin_measurable_fun; do 2 apply/measurableT_comp => //.
  - move=> n x _; rewrite EFinM mule_ge0//; last by rewrite nnfun_muleindic_ge0.
    by rewrite lee_fin invr_ge0// ltW// subr_gt0.
apply: eq_fsbigr => r _; rewrite ge0_integralZl//.
- by rewrite !integralZl_indic_nnsfun//= integral_uniform_indic// muleCA.
- exact/EFin_measurable_fun/measurableT_comp.
- by move=> t _; rewrite nnfun_muleindic_ge0.
- by rewrite lee_fin invr_ge0// ltW// subr_gt0.
Qed.

Lemma integral_uniform (f : _ -> \bar R) :
  measurable_fun setT f -> (forall x, 0 <= f x)%E ->
  (\int[uniform_prob ab]_x f x = (b - a)^-1%:E * \int[mu]_(x in `[a, b]) f x)%E.
Proof.
move=> mf f0.
have [f_ [ndf_ f_f]] := approximation measurableT mf (fun y _ => f0 y).
transitivity (lim (\int[uniform_prob ab]_x (f_ n x)%:E @[n --> \oo])%E).
  rewrite -monotone_convergence//=.
  - apply: eq_integral => ? /[!inE] xD; apply/esym/cvg_lim => //=.
    exact: f_f.
  - by move=> n; exact/EFin_measurable_fun/measurable_funTS.
  - by move=> n ? _; rewrite lee_fin.
  - by move=> ? _ ? ? mn; rewrite lee_fin; exact/lefP/ndf_.
rewrite [X in _ = (_ * X)%E](_ : _ = lim
    (\int[mu]_(x in `[a, b]) (f_ n x)%:E @[n --> \oo])%E); last first.
  rewrite -monotone_convergence//=.
  - by apply: eq_integral => ? /[!inE] xD; apply/esym/cvg_lim => //; exact: f_f.
  - by move=> n; exact/EFin_measurable_fun/measurable_funTS.
  - by move=> n ? _; rewrite lee_fin.
  - by move=> ? _ ? ? /ndf_ /lefP; rewrite lee_fin.
rewrite -limeMl//.
  by apply: congr_lim; apply/funext => n /=; exact: integral_uniform_nnsfun.
apply/ereal_nondecreasing_is_cvgn => x y xy; apply: ge0_le_integral => //=.
- by move=> ? _; rewrite lee_fin.
- exact/EFin_measurable_fun/measurable_funTS.
- by move=> ? _; rewrite lee_fin.
- exact/EFin_measurable_fun/measurable_funTS.
- by move=> ? _; rewrite lee_fin; move/ndf_ : xy => /lefP.
Qed.

End uniform_probability.
