Require Import String.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp.classical Require Import mathcomp_extra boolp classical_sets.
From mathcomp.classical Require Import functions cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure numfun lebesgue_integral kernel prob_lang.
Require Import lang_syntax_util lang_syntax.
From mathcomp Require Import ring lra.

(******************************************************************************)
(*   Examples using the Probabilistic Programming Language of lang_syntax.v   *)
(*                                                                            *)
(* bernoulli13_score := normalize (                                           *)
(*   let x := sample (bernoulli 1/3) in                                       *)
(*   let _ := if x then score (1/3) else score (2/3) in                       *)
(*   return x)                                                                *)
(* bernoulli12_score := normalize (                                           *)
(*   let x := sample (bernoulli 1/2) in                                       *)
(*   let _ := if x then score (1/3) else score (2/3) in                       *)
(*   return x)                                                                *)
(* hard_constraint := let x := Score {0}:R in return TT                       *)
(* sample_pair_syntax := normalize (                                          *)
(*   let x := sample (bernoulli 1/2) in                                       *)
(*   let y := sample (bernoulli 1/3) in                                       *)
(*   return (x, y))                                                           *)
(* associativity of let-in expressions                                        *)
(* staton_bus_syntax == example from [Staton, ESOP 2017]                      *)
(* staton_busA_syntax == same as staton_bus_syntax module associativity of    *)
(*   let-in expression                                                        *)
(* commutativity of let-in expressions                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(* letin' versions of rewriting laws *)
Lemma letin'_sample_bernoulli d d' (T : measurableType d)
    (T' : measurableType d') (R : realType)(r : {nonneg R}) (r1 : (r%:num <= 1)%R)
    (u : R.-sfker bool * T ~> T') x y :
  letin' (sample_cst (bernoulli r1)) u x y =
  r%:num%:E * u (true, x) y + (`1- (r%:num))%:E * u (false, x) y.
Proof.
rewrite letin'E/=.
rewrite ge0_integral_measure_sum// 2!big_ord_recl/= big_ord0 adde0/=.
by rewrite !ge0_integral_mscale//= !integral_dirac//= indicT 2!mul1e.
Qed.

Section letin'_return.
Context d d' d3 (X : measurableType d) (Y : measurableType d')
  (Z : measurableType d3) (R : realType).

Lemma letin'_kret (k : R.-sfker X ~> Y)
  (f : Y * X -> Z) (mf : measurable_fun setT f) x U :
  measurable U ->
  letin' k (ret mf) x U = k x (curry f ^~ x @^-1` U).
Proof.
move=> mU; rewrite letin'E.
under eq_integral do rewrite retE.
rewrite integral_indic ?setIT// -[X in measurable X]setTI.
exact: (measurableT_comp mf).
Qed.

Lemma letin'_retk (f : X -> Y) (mf : measurable_fun setT f)
    (k : R.-sfker Y * X ~> Z) x U :
  measurable U -> letin' (ret mf) k x U = k (f x, x) U.
Proof.
move=> mU; rewrite letin'E retE integral_dirac ?indicT ?mul1e//.
exact: (measurableT_comp (measurable_kernel k _ mU)).
Qed.

End letin'_return.

Section letin'_ite.
Context d d2 d3 (T : measurableType d) (T2 : measurableType d2)
  (Z : measurableType d3) (R : realType).
Variables (k1 k2 : R.-sfker T ~> Z)
  (u : R.-sfker Z * T ~> T2)
  (f : T -> bool) (mf : measurable_fun setT f)
  (t : T) (U : set T2).

Lemma letin'_iteT : f t -> letin' (ite mf k1 k2) u t U = letin' k1 u t U.
Proof.
move=> ftT.
rewrite !letin'E/=.
apply: eq_measure_integral => V mV _.
by rewrite iteE ftT.
Qed.

Lemma letin'_iteF : ~~ f t -> letin' (ite mf k1 k2) u t U = letin' k2 u t U.
Proof.
move=> ftF.
rewrite !letin'E/=.
apply: eq_measure_integral => V mV _.
by rewrite iteE (negbTE ftF).
Qed.

End letin'_ite.
(* /letin' versions of rewriting laws *)

Local Open Scope lang_scope.

Lemma execP_letinL {R : realType} g t1 t2 x (e1 : @exp R P g t1) (e1' : exp P g t1)
   (e2 : exp P ((x, t1) :: g) t2) :
  forall U, measurable U ->
  execP e1 = execP e1' ->
  execP [let x := e1 in e2] ^~ U = execP [let x := e1' in e2] ^~ U.
Proof.
by move=> U mU e1e1'; rewrite !execP_letin e1e1'.
Qed.

Lemma execP_letinR {R : realType} g t1 t2 x (e1 : @exp R P g t1)
    (e2 : exp P _ t2) (e2' : exp P ((x, t1) :: g) t2) :
  forall U, measurable U ->
  execP e2 = execP e2' ->
  execP [let x := e1 in e2] ^~ U = execP [let x := e1 in e2'] ^~ U.
Proof.
by move=> U mU e1e1'; rewrite !execP_letin e1e1'.
Qed.

Local Close Scope lang_scope.

Section simple_example.
Local Open Scope lang_scope.
Import Notations.
Context (R : realType).

Lemma exec_normalize_return g x r :
  projT1 (@execD _ g _ [Normalize return r:R]) x = \d_r :> probability _ R.
Proof.
by rewrite execD_normalize execP_return execD_real/= normalize_kdirac.
Qed.

End simple_example.

Section bernoulli_examples.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Import Notations.
Context {R : realType}.

Definition bernoulli13_score (x := "x") (y := "y") := [Normalize
  let x := Sample {@exp_bernoulli R [::] (1 / 3%:R)%:nng (p1S 2)} in
  let y := if #x then Score {(1 / 3)}:R else Score {(2 / 3)}:R in
  return #x].

Lemma exec_bernoulli13_score :
  execD (exp_bernoulli (1 / 5%:R)%:nng (p1S 4)) = execD bernoulli13_score.
Proof.
apply: eq_execD.
rewrite execD_bernoulli/= /bernoulli13_score execD_normalize 2!execP_letin.
rewrite execP_sample/= execD_bernoulli/= execP_if /= exp_var'E.
rewrite (execD_var "x")/= !execP_return/= 2!execP_score 2!execD_real/=.
apply: funext=> g; apply: eq_probability => U.
rewrite normalizeE !letin'E/=.
under eq_integral.
  move=> x _.
  rewrite !letin'E.
  under eq_integral do rewrite retE /=.
  over.
rewrite !integral_measure_add //=; last by move=> b _; rewrite integral_ge0.
rewrite !ge0_integral_mscale //=; last 2 first.
  by move=> b _; rewrite integral_ge0.
  by move=> b _; rewrite integral_ge0.
rewrite !integral_dirac// !indicE !in_setT !mul1e.
rewrite iteE/= !ge0_integral_mscale//=.
rewrite ger0_norm//; last by lra.
rewrite !integral_indic//= !iteE/= /mscale/=.
rewrite setTI diracE !in_setT !mule1.
rewrite ger0_norm//; last by lra.
rewrite -EFinD/= eqe ifF; last first.
  apply/negbTE/negP => /orP[/eqP|//].
  by rewrite /onem; lra.
rewrite !letin'E/= !iteE/=.
rewrite !ge0_integral_mscale//=.
rewrite ger0_norm//; last by lra.
rewrite !integral_dirac//= !indicE !in_setT /= !mul1e ger0_norm//; last by lra.
rewrite exp_var'E (execD_var "x")/=.
rewrite /bernoulli/= measure_addE/= /mscale/= !mul1r.
rewrite muleDl//; congr (_ + _)%E;
  rewrite -!EFinM;
  congr (_%:E);
  by rewrite indicE /onem; case: (_ \in _); field.
Qed.

Definition bernoulli12_score := [Normalize
  let "x" := Sample {@exp_bernoulli R [::] (1 / 2)%:nng (p1S 1)} in
  let "r" := if #{"x"} then Score {(1 / 3)}:R else Score {(2 / 3)}:R in
  return #{"x"}].

Lemma exec_bernoulli12_score :
  execD (exp_bernoulli (1 / 3%:R)%:nng (p1S 2)) = execD bernoulli12_score.
Proof.
apply: eq_execD.
rewrite execD_bernoulli/= /bernoulli12_score execD_normalize 2!execP_letin.
rewrite execP_sample/= execD_bernoulli/= execP_if /= exp_var'E.
rewrite (execD_var "x")/= !execP_return/= 2!execP_score 2!execD_real/=.
apply: funext=> g; apply: eq_probability => U.
rewrite normalizeE !letin'E/=.
under eq_integral.
  move=> x _.
  rewrite !letin'E.
  under eq_integral do rewrite retE /=.
  over.
rewrite !integral_measure_add //=; last by move=> b _; rewrite integral_ge0.
rewrite !ge0_integral_mscale //=; last 2 first.
  by move=> b _; rewrite integral_ge0.
  by move=> b _; rewrite integral_ge0.
rewrite !integral_dirac// !indicE !in_setT !mul1e.
rewrite iteE/= !ge0_integral_mscale//=.
rewrite ger0_norm//; last by lra.
rewrite !integral_indic//= !iteE/= /mscale/=.
rewrite setTI diracE !in_setT !mule1.
rewrite ger0_norm//; last by lra.
rewrite -EFinD/= eqe ifF; last first.
  apply/negbTE/negP => /orP[/eqP|//].
  by rewrite /onem; lra.
rewrite !letin'E/= !iteE/=.
rewrite !ge0_integral_mscale//=.
rewrite ger0_norm//; last by lra.
rewrite !integral_dirac//= !indicE !in_setT /= !mul1e ger0_norm//; last by lra.
rewrite exp_var'E (execD_var "x")/=.
rewrite /bernoulli/= measure_addE/= /mscale/= !mul1r.
rewrite muleDl//; congr (_ + _)%E;
  rewrite -!EFinM;
  congr (_%:E);
  by rewrite indicE /onem; case: (_ \in _); field.
Qed.

(* https://dl.acm.org/doi/pdf/10.1145/2933575.2935313 (Sect.4) *)
Definition bernoulli14_score52_syntax0 := [Normalize
  let "x" := Sample {@exp_bernoulli R [::] (1 / 4%:R)%:nng (p1S 3)} in
  let "r" := if #{"x"} then Score {5}:R else Score {2}:R in
  return #{"x"}].

Axiom p511 : ((5%:R / 11%:R)%:nng%:num <= (1 : R)).

Lemma exec_bernoulli14_score52_syntax0 :
  execD bernoulli14_score52_syntax0 = execD (exp_bernoulli (5%:R / 11%:R)%:nng p511).
Proof.
apply: eq_execD.
rewrite execD_bernoulli/= execD_normalize 2!execP_letin.
rewrite execP_sample/= execD_bernoulli/= execP_if /= !exp_var'E.
rewrite !execP_return/= 2!execP_score 2!execD_real/=.
rewrite !(execD_var "x")/=.
apply: funext=> g; apply: eq_probability => U.
rewrite normalizeE !letin'E/=.
under eq_integral.
  move=> x _.
  rewrite !letin'E.
  under eq_integral do rewrite retE /=.
  over.
rewrite !integral_measure_add //=; last by move=> b _; rewrite integral_ge0.
rewrite !ge0_integral_mscale //=; last 2 first.
  by move=> b _; rewrite integral_ge0.
  by move=> b _; rewrite integral_ge0.
rewrite !integral_dirac// !indicE !in_setT !mul1e.
rewrite iteE/= !ge0_integral_mscale//=.
rewrite ger0_norm/=; last by lra.
rewrite !integral_indic//= !iteE/= /mscale/=.
rewrite setTI diracE !in_setT !mule1.
rewrite ger0_norm/=; last by lra.
rewrite -EFinD/= eqe ifF; last first.
  apply/negbTE/negP => /orP[/eqP|//].
  by rewrite /onem; lra.
rewrite !letin'E/= !iteE/=.
rewrite !ge0_integral_mscale//=.
rewrite ger0_norm/=; last by lra.
rewrite !integral_dirac//= !indicE !in_setT /= !mul1e ger0_norm//.
rewrite /bernoulli/= measure_addE/= /mscale/= !mul1r.
rewrite muleDl//; congr (_ + _)%E;
  rewrite -!EFinM;
  congr (_%:E);
  by rewrite indicE /onem; case: (_ \in _); field.
Qed.

End bernoulli_examples.

Section hard_constraint'.
Context d d' (X : measurableType d) (Y : measurableType d') (R : realType).

Definition fail' :=
  letin' (score (@measurable_cst _ _ X _ setT (0%R : R)))
        (ret (@measurable_cst _ _ _ Y setT point)).

Lemma fail'E x U : fail' x U = 0.
Proof. by rewrite /fail' letin'E ge0_integral_mscale//= normr0 mul0e. Qed.

End hard_constraint'.
Arguments fail' {d d' X Y R}.

(* hard constraints to express score below 1 *)
Lemma score_fail' d (X : measurableType d) {R : realType}
    (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
  score (kr r%:num) =
  letin' (sample_cst (bernoulli r1) : R.-pker X ~> _)
         (ite macc0of2 (ret ktt) fail').
Proof.
apply/eq_sfkernel => x U.
rewrite letin'E/= /sample; unlock.
rewrite integral_measure_add//= ge0_integral_mscale//= ge0_integral_mscale//=.
rewrite integral_dirac//= integral_dirac//= !indicT/= !mul1e.
by rewrite /mscale/= iteE//= iteE//= fail'E mule0 adde0 ger0_norm.
Qed.

Section hard_constraint.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Import Notations.
Context {R : realType} {str : string}.

Definition hard_constraint g : @exp R _ g _ :=
  [let str := Score {0}:R in return TT].

Lemma exec_hard_constraint g mg U : execP (hard_constraint g) mg U = fail' (false, tt) U.
Proof.
rewrite execP_letin execP_score execD_real execP_return execD_unit/=.
rewrite letin'E integral_indic//= /mscale/= normr0 mul0e.
by rewrite /fail' letin'E/= ge0_integral_mscale//= normr0 mul0e.
Qed.

Lemma exec_score_fail (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
  execP (g := [::]) [Score {r%:num}:R] =
  execP [let "x" := Sample {exp_bernoulli r r1} in
         if #{"x"} then return TT else {hard_constraint _}].
Proof.
rewrite execP_score execD_real /= score_fail'.
rewrite execP_letin execP_sample/= execD_bernoulli execP_if execP_return.
rewrite execD_unit/= exp_var'E (execD_var "x")/=.
apply: eq_sfkernel=> /= -[] U.
rewrite 2!letin'E/=.
apply: eq_integral => b _.
rewrite 2!iteE//=.
case: b => //=.
by rewrite (@exec_hard_constraint [:: ("x", Bool)]).
Qed.

End hard_constraint.

Section sample_pair.
Local Open Scope lang_scope.
Local Open Scope ring_scope.
Import Notations.
Context {R : realType} {str0 str1 : string}.

Definition sample_pair_syntax0 : @exp R _ [::] _ :=
  [let "x" := Sample {exp_bernoulli (1 / 2)%:nng (p1S 1)} in
   let "y" := Sample {exp_bernoulli (1 / 3%:R)%:nng (p1S 2)} in
   return (%{"x"}, %{"y"})].

Definition sample_pair_syntax : exp _ [::] _ :=
  [Normalize {sample_pair_syntax0}].

Lemma exec_sample_pair_true_and_true :
  @execP R [::] _ sample_pair_syntax0 tt [set p | p.1 && p.2] = (1 / 6)%:E.
Proof.
rewrite !execP_letin !execP_sample !execD_bernoulli execP_return /=.
rewrite execD_pair (execD_var "x") (execD_var "y") /=.
rewrite letin'E integral_measure_add//= !ge0_integral_mscale//= /onem.
rewrite !integral_dirac//= !indicE !in_setT/= !mul1e.
rewrite !letin'E !integral_measure_add//= !ge0_integral_mscale//= /onem.
rewrite !integral_dirac//= !indicE !in_setT/= !mul1e !diracE.
rewrite mem_set// memNset//=.
by congr (_%:E); lra.
Qed.

Lemma exec_sample_pair_true_or_true :
  (projT1 (execD sample_pair_syntax)) tt [set p | p.1 || p.2] =
  (2 / 3)%:E.
Proof.
rewrite execD_normalize.
rewrite normalizeE/=.
rewrite !execP_letin !execP_sample !execD_bernoulli execP_return /=.
rewrite execD_pair (execD_var "x") (execD_var "y") /=.
rewrite !letin'E integral_measure_add//= !ge0_integral_mscale//= /onem.
rewrite !integral_dirac//= !indicE !in_setT/= !mul1e.
rewrite !letin'E !integral_measure_add//= !ge0_integral_mscale//= /onem.
rewrite !integral_dirac//= !indicE !in_setT/= !mul1e !diracE.
rewrite mem_set// memNset//= !mule1 eqe ifF; last first.
  apply/negbTE/negP => /orP[/eqP|//].
  by rewrite /onem; lra.
rewrite !letin'E !integral_measure_add //= !ge0_integral_mscale //= /onem.
rewrite !integral_dirac//= !indicE !in_setT/= !mul1e !diracE.
rewrite mem_set// memNset//= mule0 adde0 !mule1.
by congr (_%:E); field.
Qed.

Lemma exec_sample_pair_true_and_false :
  @execP R [::] _ sample_pair_syntax0 tt [set (true, false)] = (1 / 3)%:E.
Proof.
rewrite !execP_letin !execP_sample !execD_bernoulli execP_return /=.
rewrite execD_pair (execD_var "x") (execD_var "y") /=.
rewrite letin'E integral_measure_add//= !ge0_integral_mscale//= /onem.
rewrite !integral_dirac//= !indicE !in_setT/= !mul1e.
rewrite !letin'E !integral_measure_add//= !ge0_integral_mscale//= /onem.
rewrite !integral_dirac//= !indicE !in_setT/= !mul1e !diracE.
rewrite memNset// mem_set// !memNset//=.
rewrite /= !mule0 mule1 !add0e mule0 adde0.
congr (_%:E); lra.
Qed.

End sample_pair.

Section letinA.
Local Open Scope lang_scope.
Variable R : realType.

Lemma letinA g x y t1 t2 t3 (xg : x \notin dom ((y, t2) :: g))
  (e1 : @exp R P g t1)
  (e2 : exp P [:: (x, t1) & g] t2)
  (e3 : exp P [:: (y, t2) & g] t3) :
  forall U, measurable U ->
  execP [let x := e1 in
         let y := e2 in
         {@exp_weak _ _ [:: (y, t2)] _ _ (x, t1) e3 xg}] ^~ U =
  execP [let y :=
           let x := e1 in e2 in
         e3] ^~ U.
Proof.
move=> U mU; apply/funext=> z1.
rewrite !execP_letin.
rewrite (execP_weak [:: (y, t2)]).
apply: letin'A => //= z2 z3.
rewrite /kweak /mctx_strong /=.
by destruct z3.
Qed.

Corollary letinA12 : forall U, measurable U ->
  @execP R [::] _ [let "y" := return {1}:R in
                   let "x" := return {2}:R in
                   return %{"x"}] ^~ U =
  @execP R [::] _ [let "x" :=
                   let "y" := return {1}:R in return {2}:R in
                   return %{"x"}] ^~ U.
Proof.
move=> U mU.
rewrite !execP_letin !execP_return !execD_real !execD_var /=.
apply: funext=> x.
exact: letin'A.
Qed.

End letinA.

Section staton_bus.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Import Notations.
Context {R : realType}.

Definition staton_bus_syntax0 : @exp R _ [::] _ :=
  [let "x" := Sample {exp_bernoulli (2 / 7%:R)%:nng p27} in
   let "r" := if #{"x"} then return {3}:R else return {10}:R in
   let "_" := Score {exp_poisson 4 [#{"r"}]} in
   return %{"x"}].

Definition staton_bus_syntax := [Normalize {staton_bus_syntax0}].

Let sample_bern : R.-sfker munit ~> mbool := sample_cst (bernoulli p27).

Let ite_3_10 : R.-sfker mbool * munit ~> (mR R) :=
  ite macc0of2 (ret k3) (ret k10).

Let score_poisson4 : R.-sfker mR R * (mbool * munit) ~> munit :=
  score (measurableT_comp (measurable_poisson 4) macc0of2).

Let kstaton_bus' :=
  letin' sample_bern
    (letin' ite_3_10
      (letin' score_poisson4 (ret macc2of4'))).

Lemma eval_staton_bus0 : staton_bus_syntax0 -P> kstaton_bus'.
Proof.
apply: eval_letin; first by apply: eval_sample; exact: eval_bernoulli.
apply: eval_letin.
  apply/evalP_if; [|exact/eval_return/eval_real..].
  rewrite exp_var'E.
  by apply/execD_evalD; rewrite (execD_var "x")/=; congr existT.
apply: eval_letin.
  apply/eval_score/eval_poisson.
  rewrite exp_var'E.
  by apply/execD_evalD; rewrite (execD_var "r")/=; congr existT.
apply/eval_return.
by apply/execD_evalD; rewrite (execD_var "x")/=; congr existT.
Qed.

Lemma exec_staton_bus0 : execP staton_bus_syntax0 = kstaton_bus'.
Proof.
rewrite 3!execP_letin execP_sample/= execD_bernoulli.
rewrite /kstaton_bus'; congr letin'.
rewrite !execP_if !execP_return !execD_real/=.
rewrite exp_var'E (execD_var "x")/=.
have -> : measurable_acc_typ [:: Bool] 0 = macc0of2 by [].
congr letin'.
rewrite execP_score execD_poisson/=.
rewrite exp_var'E (execD_var "r")/=.
have -> : measurable_acc_typ [:: Real; Bool] 0 = macc0of2 by [].
congr letin'.
by rewrite (execD_var "x") /=; congr ret.
Qed.

Lemma exec_staton_bus : execD staton_bus_syntax =
  existT _ (normalize kstaton_bus' point) (measurable_mnormalize _).
Proof. by rewrite execD_normalize exec_staton_bus0. Qed.

Let poisson4 := @poisson R 4%N.

Let staton_bus_probability U :=
  ((2 / 7)%:E * (poisson4 3)%:E * \d_true U +
  (5 / 7)%:E * (poisson4 10)%:E * \d_false U)%E.

Lemma exec_staton_bus0' U :
  execP staton_bus_syntax0 tt U = staton_bus_probability U.
Proof.
rewrite exec_staton_bus0 /staton_bus_probability /kstaton_bus'.
rewrite letin'_sample_bernoulli.
rewrite -!muleA; congr (_ * _ + _ * _)%E.
- rewrite letin'_iteT// letin'_retk// letin'_kret// /score_poisson4.
  by rewrite /score/= /mscale/= ger0_norm//= poisson_ge0// /acc0of2/=.
- by rewrite onem27.
- rewrite letin'_iteF// letin'_retk// letin'_kret// /score_poisson4.
  by rewrite /score/= /mscale/= ger0_norm//= poisson_ge0// /acc0of2/=.
Qed.

End staton_bus.

(* same as staton_bus module associativity of letin *)
Section staton_busA.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Import Notations.
Context {R : realType}.

Definition staton_busA_syntax0 : @exp R _ [::] _ :=
  [let "x" := Sample {exp_bernoulli (2 / 7%:R)%:nng p27} in
   let "_" :=
     let "r" := if #{"x"} then return {3}:R else return {10}:R in
     Score {exp_poisson 4 [#{"r"}]} in
   return #{"x"}].

Definition staton_busA_syntax : exp _ [::] _ :=
  [Normalize {staton_busA_syntax0}].

Let sample_bern : R.-sfker munit ~> mbool := sample_cst (bernoulli p27).

Let ite_3_10 : R.-sfker mbool * munit ~> (mR R) :=
  ite macc0of2 (ret k3) (ret k10).

Let score_poisson4 : R.-sfker mR R * (mbool * munit) ~> munit :=
  score (measurableT_comp (measurable_poisson 4) macc0of3').

(* same as kstaton_bus _ (measurable_poisson 4) but expressed with letin'
   instead of letin *)
Let kstaton_busA' :=
  letin' sample_bern
  (letin'
    (letin' ite_3_10
      score_poisson4)
    (ret macc1of3')).
(*TODO: Lemma kstaton_bus'E : kstaton_bus' = kstaton_bus _ (measurable_poisson 4).
Proof.
apply/eq_sfkernel => -[] U.
rewrite /kstaton_bus' /kstaton_bus.
rewrite letin'_letin.
rewrite /sample_bern.
congr (letin _ _ tt U).

apply: eq_sfkernel => /= -[[] b] V.
rewrite /mswap letin'_letin /letin/=.
rewrite /ite_3_10.*)

Lemma eval_staton_busA0 : staton_busA_syntax0 -P> kstaton_busA'.
Proof.
apply: eval_letin; first by apply: eval_sample; exact: eval_bernoulli.
apply: eval_letin.
  apply: eval_letin.
    apply/evalP_if; [|exact/eval_return/eval_real..].
    rewrite exp_var'E.
    by apply/execD_evalD; rewrite (execD_var "x")/=; congr existT.
  apply/eval_score/eval_poisson.
  rewrite exp_var'E.
  by apply/execD_evalD; rewrite (execD_var "r")/=; congr existT.
apply/eval_return.
by apply/execD_evalD; rewrite exp_var'E (execD_var "x")/=; congr existT.
Qed.

Lemma exec_staton_busA0 : execP staton_busA_syntax0 = kstaton_busA'.
Proof.
rewrite 3!execP_letin execP_sample/= execD_bernoulli.
rewrite /kstaton_busA'; congr letin'.
rewrite !execP_if !execP_return !execD_real/=.
rewrite exp_var'E (execD_var "x")/=.
have -> : measurable_acc_typ [:: Bool] 0 = macc0of2 by [].
congr letin'.
  rewrite execP_score execD_poisson/=.
  rewrite exp_var'E (execD_var "r")/=.
  by have -> : measurable_acc_typ [:: Real; Bool] 0 = macc0of3' by [].
by rewrite exp_var'E (execD_var "x") /=; congr ret.
Qed.

Lemma exec_statonA_bus : execD staton_busA_syntax =
  existT _ (normalize kstaton_busA' point) (measurable_mnormalize _).
Proof. by rewrite execD_normalize exec_staton_busA0. Qed.

(* equivalence between staton_bus and staton_busA *)
Lemma staton_bus_staton_busA :
  execP staton_bus_syntax0 = @execP R _ _ staton_busA_syntax0.
Proof.
rewrite /staton_bus_syntax0 /staton_busA_syntax0.
rewrite execP_letin.
rewrite [in RHS]execP_letin.
congr (letin' _).
set e1 := exp_if _ _ _.
set e2 := exp_score _.
set e3 := (exp_return _ in RHS).
pose f := @found _ Unit "x" Bool [::].
have r_f : "r" \notin [seq i.1 | i <- ("_", Unit) :: untag (ctx_of f)] by [].
have H := @letinA _ _ _ _ _ _
  (lookup Unit (("_", Unit) :: untag (ctx_of f)) "x")(*t3*)
  r_f e1 e2 e3.
apply/eq_sfkernel => /= x U.
have mU :
  (@mtyp_disp R (lookup Unit (("_", Unit) :: untag (ctx_of f)) "x")).-measurable U.
  by [].
move: H => /(_ U mU) /(congr1 (fun f => f x)) <-.
set e3' := exp_return _.
set e3_weak := exp_weak _ _ _ _.
rewrite !execP_letin.
suff: execP e3' = execP (e3_weak e3 r_f) by move=> <-.
rewrite execP_return/= execD_var/= /e3_weak.
rewrite (@execP_weak R [:: ("_", Unit)] (untag (ctx_of f)) ("r", Real) _ e3 r_f).
rewrite execP_return exp_var'E/= (execD_var "x") //=.
by apply/eq_sfkernel => /= -[[] [a [b []]]] U0.
Qed.

Let poisson4 := @poisson R 4%N.

Lemma exec_staton_busA0' U : execP staton_busA_syntax0 tt U =
  ((2 / 7%:R)%:E * (poisson4 3%:R)%:E * \d_true U +
  (5%:R / 7%:R)%:E * (poisson4 10%:R)%:E * \d_false U)%E.
Proof. by rewrite -staton_bus_staton_busA exec_staton_bus0'. Qed.

End staton_busA.

Section variables.
Local Open Scope lang_scope.
Import Notations.
Context (R : realType).

Definition v1 x : @exp R P [::] _ := [
  let x := return {1}:R in
  return %x].

Definition v2 (a b c d : string) (H : infer (b != a)) : @exp R P [::] _ := [
  let a := return {1}:R in
  let b := return {true}:B in
  (* let c := return {3}:R in
  let d := return {4}:R in *)
  return (#a, #b)].

(* Problem: pair of variables *)
Definition v3 (a b c d : string) (H1 : infer (b != a)) (H2 : infer (c != a))
  (H3 : infer (c != b)) (H4 : infer (a != b)) (H5 : infer (a != c)) 
  (H6 : infer (b != c)) : @exp R P [::] _ := [
  let a := return {1}:R in
  let b := return {2}:R in
  let c := return {3}:R in
  (* let d := return {4}:R in *)
  (* return (#b, #a)]. *)
  return {@exp_pair R [:: (c, _); (b, _); (a, _)] _ _ (exp_var' a _) (exp_var' b _)}].

End variables.

Section letinC.
Local Open Scope lang_scope.
Variable (R : realType).

Require Import Classical_Prop.

Lemma letinC g t1 t2 (e1 : @exp R P g t1) (e2 : @exp R P g t2)
  (str1 str2 : string)
  (* (str1 := "x") (str2 := "y") *)
  (H1 : infer (str2 != str1)) (H2 : infer (str1 != str2))
  (xl : str1 \notin dom g) (yl : str2 \notin dom g) :
  forall U, measurable U ->
  execP [
    let str1 := e1 in
    let str2 := {exp_weak _ [::] _ (str1, t1) e2 xl} in
    return (#str1, #str2)] ^~ U =
  execP [
    let str2 := e2 in
    let str1 := {exp_weak _ [::] _ (str2, t2) e1 yl} in
    (* return (#str1, #str2)] *)
    return {@exp_pair R [:: (str1, t1), (str2, t2) & g] _ _ [#str1] [#str2]}]
    ^~ U.
Proof.
move=> U mU; apply/funext => x.
rewrite 4!execP_letin.
rewrite 2!(execP_weak [::] g).
rewrite 2!execP_return/=.
rewrite 2!execD_pair/=.
rewrite !exp_var'E.
- apply/(ctx_prf_tail _ H1)/ctx_prf_head.
- apply/ctx_prf_head.
- apply/ctx_prf_head.
- apply/(ctx_prf_tail _ H2)/ctx_prf_head.
- move=> h1 h2 h3 h4.
  (* set f1 := (found str1 t1 ((str2, t2) :: g)). *)
  set g1 := [:: (str2, t2), (str1, t1) & g].
  set g2 := [:: (str1, t1), (str2, t2) & g].
  (*
  rewrite (@execD_var _ g2 str1 h2).
  have : projT2 (execD [% str1 h4]) = macc1of3'. *)
(*
  have H := (@letin'C _ _ _ _ _ _ R (execP e1) [the R.-sfker _ ~> _ of kweak [::] g (str1, t1) (execP e2)] (execP e2) [the R.-sfker _ ~> _ of kweak [::] g (str2, t2) (execP e1)]).
*)
  (* have ? := (@execP_weak R [::] g (str1, t1) t2 e2 xl).
  (* rewrite letin'C. *)
  rewrite (@execD_var R g1 str1 h4). *)
  (* rewrite (_ : execD [% str1 h4] = existT _ (acc_typ (map snd g1) 1)
                                    (measurable_acc_typ (map snd g1) 1))/=; last first. *)
  (* rewrite -exp_var'E. *)
  rewrite /execD/=.
  case: cid => x0 [mx0 p].
  case: cid => mx0' p' //=.
  case: cid => x1 [mx1 p1] /=.
  case: cid => mx1' p1' /=.
  case: cid => x2 [mx2 p2] /=.
  case: cid => x3 [mx3 p3] /=.
  case: cid => mx2' p2' /=.
  case: cid => mx3' p3' /=.
  have ? : mx0 = mx0'.
  exact: Prop_irrelevance.
  subst mx0'.
  have ? : mx1 = mx1'.
  exact: Prop_irrelevance.
  have ? : mx2 = mx2'.
  exact: Prop_irrelevance.
  have ? : mx3 = mx3'.
  exact: Prop_irrelevance.
  subst mx1' mx2' mx3'.
  clear p' p1' p2' p3'.
  have ? : x0 = @acc1of3' _ _ _ _ _ (projT2 (measurable_of_seq (map snd g))).
    have : (exp_var str1 h4 : (@exp R D _ _)) -D> (@acc1of3' _ _ _ _ _ (projT2 (measurable_of_seq (map snd g)))) ; macc1of3'.
      set localg := @untag stype_eqType (@ctx_of stype_eqType Unit str1 t1
        (@recurse stype_eqType Unit str1 t1 str2 t2 H1 (@found stype_eqType Unit str1 t1 g))).

      set Y : exp D localg t1 := exp_var str1 h4.
      have K1 := @eval_var R localg str1.
      pose X : @exp R D localg (lookup Unit localg str1) := [%str1].
      cbv zeta in K1.
      rewrite -/X in K1.

      Fail Check X = Y.
      have ? : t1 = lookup Unit localg str1 by [].
      pose from_exp_t1 Z := @eq_rect _ t1 (@exp R D localg) Z _ h4.
      pose to_exp_t1 Z := @eq_rect _ _ (@exp R D localg) Z _ (esym h4).
      Check X = from_exp_t1 Y.

      have XY : X = from_exp_t1 Y.
        rewrite /from_exp_t1.
        clear.
        rewrite {}/X {}/Y.
        rewrite {}/localg.
        move: h4.
        move H : (untag _) => h.
        clear H.
        move=> h4.
        subst t1.
        exact: eq_rect_eq.

      have YX : Y = to_exp_t1 X.
        rewrite /to_exp_t1.
        clear.
        rewrite {}/X {}/Y.
        rewrite {}/localg.
        move: h4.
        move H : (untag _) => h.
        clear H.
        move=> h4.
        subst t1.
        exact: eq_rect_eq.

      rewrite YX.

      Fail Check execD X = execD Y.
      pose from_semval_t1 Z := (@eq_rect _ _ (fun x => {f : dval R localg x & measurable_fun [set: mctx localg] f}) Z _ h4).
      Check execD X = from_semval_t1 (execD Y).
      pose to_semval_t1 Z := (@eq_rect _ _ (fun x => {f : dval R localg x & measurable_fun [set: mctx localg] f}) Z _ (esym h4)).

      set semval0 := (X in _ -D> X; _) in K1.
      set msemval0 := (X in _ -D> _; X) in K1.

      pose type_of_acc1of3' :=
        (projT2 (@measurable_of_typ R t2) * (projT2 (@measurable_of_typ R t1) * projT2 (@measurable_of_seq  R [seq i.2 | i <- g])))%type ->
       projT2 (@measurable_of_typ R t1).
      set type_of_semval0 := projT2 (@measurable_of_seq R [seq i.2 | i <- localg]) -> projT2 (@measurable_of_typ R (nth Unit [seq i.2 | i <- localg] (index str1 (dom localg)))).
      have K3 : type_of_semval0 = type_of_acc1of3'.
        rewrite /type_of_semval0/= /type_of_acc1of3'/=.
        by rewrite (negbTE H1)//= eqxx//.
      Fail Check acc1of3' (T2:=projT2 (measurable_of_seq [seq i.2 | i <- g])) = semval0.
      pose from_type_of_semval0 Z := (@eq_rect _ _ (fun x => x) Z _ K3).
      Check acc1of3' (T2:=projT2 (measurable_of_seq [seq i.2 | i <- g])) = from_type_of_semval0 semval0.

      have access_function_eq : acc1of3' (T2:=projT2 (measurable_of_seq [seq i.2 | i <- g])) = from_type_of_semval0 semval0.
        clear.
        rewrite {}/from_type_of_semval0.
        rewrite {}/semval0 in K3 *.
        have K3' : type_of_semval0 = type_of_acc1of3' by done.
        rewrite (Prop_irrelevance K3 K3').

      Fail apply: eval_var.
        admit.
      admit.
move=> K.
    exact: (evalD_uniq p K).
  subst.
  have -> : mx0 = @macc1of3' _ _ _ _ _ _.
  done.
  have ? : x1 = @acc0of3' _ _ _ _ _ _.
  admit.
  subst.
  have -> : mx1 = @macc0of3' _ _ _ _ _ _.
  done.
  have ? : x2 = @acc0of3' _ _ _ _ _ _.
  admit.
  subst.
  have -> : mx2 = @macc0of3' _ _ _ _ _ _.
  done.
  have ? : x3 = @acc1of3' _ _ _ _ _ _.
  admit.
  subst.
  have -> : mx3 = @macc1of3' _ _ _ _ _ _.
  done.
  by apply: letin'C.
Abort.

Lemma letinC g t1 t2 (e1 : @exp R P g t1) (e2 : @exp R P g t2)
  (str1 str2 : string)
  (* (str1 := "x") (str2 := "y") *)
  (H1 : infer (str2 != str1)) (H2 : infer (str1 != str2))
  (xl : str1 \notin dom g) (yl : str2 \notin dom g) :
  forall U, measurable U ->
  execP [
    let str1 := e1 in
    let str2 := {exp_weak _ [::] _ (str1, t1) e2 xl} in
    return (#str1, #str2)] ^~ U =
  execP [
    let str2 := e2 in
    let str1 := {exp_weak _ [::] _ (str2, t2) e1 yl} in
    (* return (#str1, #str2)] *)
    return {@exp_pair R [:: (str1, t1), (str2, t2) & g] _ _ [#str1] [#str2]}]
    ^~ U.
Proof.
move=> U mU; apply/funext => x.
rewrite 4!execP_letin.
rewrite 2!(execP_weak [::] g).
rewrite 2!execP_return/=.
rewrite 2!execD_pair/=.
rewrite !exp_var'E.
- apply/(ctx_prf_tail _ H1)/ctx_prf_head.
- apply/ctx_prf_head.
- apply/ctx_prf_head.
- apply/(ctx_prf_tail _ H2)/ctx_prf_head.
- move=> h1 h2 h3 h4.
  rewrite (_ : execD (exp_var str1 h4) = existT _ (acc_typ (map snd _) 1) (measurable_acc_typ (map snd _) 1)); last first.
  apply/execD_evalD.
  have h4' : t1 = lookup Unit (untag (ctx_of (recurse t2 (found str1 t1 g)))) str1.
    done.
  have Htmp : h4 = h4' Unit by done.
  rewrite (_ : h4 = h4' Unit)//.

  (* move: h4.
  rewrite /lookup /= (negbTE H1) eqxx/=. *)

  admit.
  rewrite (_ : execD (exp_var str2 h3) = existT _ (acc_typ (map snd _) 0) (measurable_acc_typ (map snd _) 0)); last first.
  admit.
  rewrite /=.
  have -> : measurable_acc_typ [:: t2, t1 & map snd g] 0 = macc0of3' by [].
  have -> : measurable_acc_typ [:: t2, t1 & map snd g] 1 = macc1of3' by [].
  rewrite (letin'C _ _ (execP e2)
    [the R.-sfker _ ~> _ of @kweak _ [::] _ (str2, t2) _ (execP e1)]);
    [ |by [] | by [] |by []].
  rewrite (_ : execD (exp_var str2 h1) = existT _ (acc_typ (map snd _) 1) (measurable_acc_typ (map snd _) 1)); last first.
  admit.
  rewrite (_ : execD (exp_var str1 h2) = existT _ (acc_typ (map snd _) 0) (measurable_acc_typ (map snd _) 0)); last first.
  admit.
  have -> : measurable_acc_typ [:: t1, t2 & map snd g] 0 = macc0of3' by [].
  by have -> : measurable_acc_typ [:: t1, t2 & map snd g] 1 = macc1of3' by [].
Abort.
         
(* Lemma letinC g t1 t2 (e1 : @exp R P g t1) (e2 : @exp R P g t2)
  (str0 := "x") (str1 := "y") (xl : str0 \notin dom g) (yl : str1 \notin dom g) :
  let h1 := tmp e1 e2 xl yl in
  let h2 := tmp e1 e2 xl yl in
  forall (U : set (mtyp (Pair (untag_typ (typ_of h1)) (untag_typ (typ_of h2))))), measurable U ->
  execP [let str0 := e1 in
         let str1 := {exp_weak _ [::] _ (str0, t1) e2 xl} in
         return (%str0, %str1)] ^~ U =
  execP [let str1 := e2 in
         let str0 := {exp_weak _ [::] _ (str1, t2) e1 yl} in
         return (%str0, %str1)] ^~ U. *)

(* version parameterized by any context g *)
Lemma letinC g t1 t2 (e1 : @exp R P g t1) (e2 : exp P g t2)
  (xl : "x" \notin dom g) (yl : "y" \notin dom g) :
  forall U, measurable U ->
  execP [let "x" := e1 in
         let "y" := {exp_weak _ [::] _ ("x", t1) e2 xl} in
         return (%{"x"}, %{"y"})] ^~ U =
  execP [let "y" := e2 in
         let "x" := {exp_weak _ [::] _ ("y", t2) e1 yl} in
         return (%{"x"}, %{"y"})] ^~ U.
Proof.
move=> U mU; apply/funext => x.
rewrite 4!execP_letin.
rewrite 2!(execP_weak [::] g).
rewrite 2!execP_return/=.
rewrite 2!execD_pair/=.
rewrite !(execD_var "x")/=.
rewrite !(execD_var "y")/=.
have -> : measurable_acc_typ [:: t2, t1 & map snd g] 0 = macc0of3' by [].
have -> : measurable_acc_typ [:: t2, t1 & map snd g] 1 = macc1of3' by [].
rewrite (letin'C _ _ (execP e2)
  [the R.-sfker _ ~> _ of @kweak _ [::] _ ("y", t2) _ (execP e1)]);
  [ |by [] | by [] |by []].
have -> : measurable_acc_typ [:: t1, t2 & map snd g] 0 = macc0of3' by [].
by have -> : measurable_acc_typ [:: t1, t2 & map snd g] 1 = macc1of3' by [].
Qed.

(* specialized to a concrete context *)
Lemma letinC_list (g := [:: ("a", Unit); ("b", Bool)]) t1 t2
    (e1 : @exp R P g t1)
    (e2 : exp P g t2) :
  forall U, measurable U ->
  execP [let "x" := e1 in
         let "y" := e2 :+ {"x"} in
         return (%{"x"}, %{"y"})] ^~ U =
  execP [let "y" := e2 in
         let "x" := e1 :+ {"y"} in
         return (%{"x"}, %{"y"})] ^~ U.
Proof.
move=> U mU.
exact: letinC.
Qed.

End letinC.
