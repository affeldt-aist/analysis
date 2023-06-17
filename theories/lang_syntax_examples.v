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
(* staton_bus_syntax == example from [Staton, ESOP 2017]                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section staton_bus.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Import Notations.
Context {R : realType}.

Goal (ret (kr 3) : R.-sfker _ ~> (mR R)) tt [set: R] = 1%:E.
Proof. rewrite /= diracE in_setT //. Qed.

Definition staton_bus_syntax0 : @exp R _ [::] _ :=
  [let "x" := Sample {exp_bernoulli (2 / 7%:R)%:nng p27} in
   let "r" := if #{"x"} then return {3}:R else return {10}:R in
   let "_" := Score {exp_poisson 4 [#{"r"}]} in
   return %{"x"}].

Definition staton_bus_syntax : exp _ [::] _ :=
  [Normalize {staton_bus_syntax0}].

Let sample_bern : R.-sfker munit ~> mbool :=
  sample_cst [the probability _ _ of bernoulli p27].

Let ite_3_10 :
  R.-sfker [the measurableType _ of (mbool * munit)%type] ~> (mR R) :=
  ite macc0of2 (ret k3) (ret k10).

Let score_poisson4 :
  R.-sfker [the measurableType _ of (mR R * (mbool * munit))%type] ~> munit :=
  score (measurableT_comp (measurable_poisson 4) (@macc0of2 _ _ _ _)).

(* same as kstaton_bus _ (measurable_poisson 4) but expressed with letin'
   instead of letin *)
Let kstaton_bus' :=
  letin' sample_bern
    (letin' ite_3_10
      (letin' score_poisson4 (ret macc2of4'))).

(*Lemma kstaton_bus'E : kstaton_bus' = kstaton_bus _ (measurable_poisson 4).
Proof.
apply/eq_sfkernel => -[] U.
rewrite /kstaton_bus' /kstaton_bus.
rewrite letin'_letin.
rewrite /sample_bern.
congr (letin _ _ tt U).

apply: eq_sfkernel => /= -[[] b] V.
rewrite /mswap letin'_letin /letin/=.
rewrite /ite_3_10.*)

(*Variables (d d' d3 d4 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (U : measurableType d4).

Lemma mkwap_letin (l : R.-sfker (X * U)%type ~> Y)
    (k : R.-sfker ((X * U) * Y)%type ~> Z) :
  mkswap (letin l k) = letin (mkswap l) k.
*)

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

End staton_bus.

Section bernoulli_example.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Import Notations.
Context {R : realType}.

Let p13 : (1 / 3%:R)%:nng%:num <= 1 :> R. Proof. by rewrite p1S. Qed.

Definition bernoulli12_score := [Normalize
  let "x" := Sample {@exp_bernoulli R [::] (1 / 2%:R)%:nng p12} in
  let "r" := if #{"x"} then Score {(1 / 3)}:R else Score {(2 / 3)}:R in
  return #{"x"}].

Lemma exec_bernoulli_score :
  execD (exp_bernoulli (1 / 3%:R)%:nng p13) = execD bernoulli12_score.
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

End bernoulli_example.

Section score_fail.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Import Notations.
Context {R : realType}.

(* lhs *)
Definition scorer (r : {nonneg R}) : exp P [::] Unit := [Score {r%:num}:R].

Definition ex_fail g : @exp R P g Unit :=
  [let "x" := Score {0}:R in return TT].

Lemma ex_fail_fail g x U : execP (ex_fail g) x U = fail tt U.
Proof.
rewrite execP_letin execP_score execD_real execP_return execD_unit/=.
rewrite letin'E integral_indic//= /mscale/= normr0 mul0e.
by rewrite /kcomp /kscore /= ge0_integral_mscale//= normr0 mul0e.
Qed.

(* rhs *)
Definition iffail (r : {nonneg R}) (r1 : (r%:num <= 1)%R) : exp P [::] Unit :=
  [let "x" := Sample {exp_bernoulli r r1} in
  if #{"x"} then return TT else {ex_fail _}].

Lemma ex_score_fail r (r1 : (r%:num <= 1)%R) :
  execP (scorer r) = execP (iffail r1).
Proof.
rewrite /scorer /iffail.
rewrite execP_score execD_real /= score_fail.
rewrite execP_letin execP_sample/= execD_bernoulli execP_if execP_return.
rewrite execD_unit exp_var'E (execD_var "x")/=.
apply: eq_sfkernel=> /= x U.
rewrite /kcomp/= letin'E/=.
apply: eq_integral => b _.
rewrite 2!iteE.
case: b => //=.
by rewrite (@ex_fail_fail [:: ("x", Bool)]).
Qed.

End score_fail.

(* TODO: move *)
Lemma normalize_kdirac (R : realType)
    d (T : measurableType d) d' (T' : measurableType d') (x : T) (r : T') P :
  normalize (kdirac (measurable_cst r)) P x = \d_r :> probability T' R.
Proof.
apply: eq_probability => U.
rewrite normalizeE /= diracE in_setT/=.
by rewrite onee_eq0/= indicE in_setT/= -div1r divr1 mule1.
Qed.

Section normalize_return.
Local Open Scope lang_scope.
Import Notations.
Context (R : realType).

Goal execP [return {1}:R] = ret (kr 1) :> pval R [::] _.
Proof. by rewrite execP_return execD_real. Qed.

Goal projT1 (execD [Normalize return {1}:R]) =
  normalize (ret (kr 1)) point :> dval R [::] _.
Proof. by rewrite execD_normalize execP_return execD_real. Qed.

Lemma exec_normalize_return g x r :
  projT1 (@execD _ g _ [Normalize return {r}:R]) x = \d_r
  :> probability _ R.
Proof.
by rewrite execD_normalize execP_return execD_real/= normalize_kdirac.
Qed.

Goal @ret _ _ _ _ R _ (kr 1) tt [set (1%R : mR R)] = 1%:E.
Proof. by rewrite retE diracE/= mem_set. Qed.

End normalize_return.

Section sample_pair.
Local Open Scope lang_scope.
Local Open Scope ring_scope.
Import Notations.
Context (R : realType).

Definition exp_sample_pair : exp D [::] _ :=
  [Normalize let "x" := Sample {exp_bernoulli (1 / 2%:R)%:nng (p1S R 1)} in
   let "y" := Sample {exp_bernoulli (1 / 3%:R)%:nng (p1S R 2)} in
   return (%{"x"}, %{"y"})].

Lemma exec_sample_pair :
  (projT1 (execD exp_sample_pair)) tt [set p | p.1 || p.2 = true] = (2 / 3%:R)%:E.
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

Goal @execP R [::] _ [let "x" := Sample {exp_bernoulli (1 / 2%:R)%:nng p12} in
       let "y" := Sample {exp_bernoulli (1 / 3%:R)%:nng (p1S R 2)} in
       return (%{"x"}, %{"y"})] tt [set p | p.1 && p.2] = (1 / 6%:R)%:E.
Proof.
rewrite !execP_letin !execP_sample !execD_bernoulli execP_return /=.
rewrite execD_pair (execD_var "x") (execD_var "y") /=.
rewrite letin'E integral_measure_add//= !ge0_integral_mscale//= /onem.
rewrite !integral_dirac//= !indicE !in_setT/= !mul1e.
rewrite !letin'E !integral_measure_add//= !ge0_integral_mscale//= /onem.
rewrite !integral_dirac//= !indicE !in_setT/= !mul1e !diracE.
rewrite mem_set// memNset//=.
congr (_%:E); lra.
Qed.

Goal @execP R [::] _ [let "x" := Sample {exp_bernoulli (1 / 2%:R)%:nng (p1S R 1)} in
       let "y" := Sample {exp_bernoulli (1 / 3%:R)%:nng (p1S R 2)} in
       return (%{"x"}, %{"y"})] tt [set (true, false)] = (1 / 3%:R)%:E.
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

Section letinC.
Local Open Scope lang_scope.
Variable R : realType.

Lemma ex_var_ret g :
  @execP R g _ [let "x" := return {1}:R in return #{"x"}] =
  letin' (ret (kr 1)) (ret (@macc0of2 _ _ _ _)).
Proof.
rewrite execP_letin execP_return execD_real/=; congr letin'.
by rewrite execP_return exp_var'E (execD_var "x")/=; congr ret.
Qed.

(* generic version *)
Lemma letinC g t1 t2 (e1 : @exp R P g t1) (e2 : exp P g t2)
  (xl : "x" \notin map fst g) (yl : "y" \notin map fst g) :
  forall U, measurable U ->
  execP [let "x" := e1 in
         let "y" := {@exp_weak _ _ [::] _ _ ("x", t1) e2 xl} in
         return (%{"x"}, %{"y"})] ^~ U =
  execP [let "y" := e2 in
         let "x" := {@exp_weak _ _ [::] _ _ ("y", t2) e1 yl} in
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
  ([the R.-sfker _ ~> _ of @kweak _ [::] _ ("y", t2) _ (execP e1)]));
  [ |by [] | by [] |by []].
have -> : measurable_acc_typ [:: t1, t2 & map snd g] 0 = macc0of3' by [].
by have -> : measurable_acc_typ [:: t1, t2 & map snd g] 1 = macc1of3' by [].
Qed.

(* letinC with a concrete context *)
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

Lemma letinC12 : forall U, measurable U ->
  @execP R [::] _ [let "x" := return {1}:R in
                   let "y" := return {2}:R in
                   return (%{"x"}, %{"y"})] ^~ U =
  execP [let "y" := return {2}:R in
         let "x" := return {1}:R in
         return (%{"x"}, %{"y"})] ^~ U.
Proof.
move=> U mU.
apply: funext => x.
rewrite !execP_letin !execP_return !execD_real !execD_pair.
rewrite (execD_var "x")/=.
rewrite (execD_var "y")/=.
(* TODO: Use letinC *)
Abort.

(* TODO *)
Lemma execP_LetInL g t1 t2 x (e1 : @exp R P g t1) (e1' : exp P g t1)
   (e2 : exp P ((x, t1) :: g) t2) :
  forall U, measurable U ->
  execP e1 = execP e1' ->
  execP [let x := e1 in e2] ^~ U =
  execP [let x := e1' in e2] ^~ U.
Proof.
by move=> U mU e1e1'; rewrite !execP_letin e1e1'.
Qed.

Lemma execP_LetInR g t1 t2 x (e1 : @exp R P g t1)
    (e2 : exp P _ t2) (e2' : exp P ((x, t1) :: g) t2) :
  forall U, measurable U ->
  execP e2 = execP e2' ->
  execP [let x := e1 in e2] ^~ U =
  execP [let x := e1 in e2'] ^~ U.
Proof.
by move=> U mU e1e1'; rewrite !execP_letin e1e1'.
Qed.

End letinC.

Section letinA.
Local Open Scope lang_scope.
Variable R : realType.

Lemma letinA g x y t1 t2 t3 (xg : x \notin map fst ((y, t2) :: g))
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

Lemma letinA12 : forall U, measurable U ->
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

Lemma letin'_sample_bernoulli d d' (T : measurableType d)
    (T' : measurableType d') (R : realType)(r : {nonneg R}) (r1 : (r%:num <= 1)%R)
    (u : R.-sfker [the measurableType _ of (bool * T)%type] ~> T') x y :
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

Lemma letin'_retk
  (f : X -> Y) (mf : measurable_fun setT f)
  (k : R.-sfker [the measurableType _ of (Y * X)%type] ~> Z)
  x U : measurable U ->
  letin' (ret mf) k x U = k (f x, x) U.
Proof.
move=> mU; rewrite letin'E retE integral_dirac ?indicT ?mul1e//.
exact: (measurableT_comp (measurable_kernel k _ mU)).
Qed.

End letin'_return.

Section letin'_ite.
Context d d2 d3 (T : measurableType d) (T2 : measurableType d2)
  (Z : measurableType d3) (R : realType).
Variables (k1 k2 : R.-sfker T ~> Z)
  (u : R.-sfker [the measurableType _ of (Z * T)%type] ~> T2)
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

Module StatonBusA.
Section staton_bus.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Import Notations.
Context {R : realType}.

Definition staton_bus_syntax0 : @exp R _ [::] _ :=
  [let "x" := Sample {exp_bernoulli (2 / 7%:R)%:nng p27} in
   let "_" :=
     let "r" := if #{"x"} then return {3}:R else return {10}:R in
     Score {exp_poisson 4 [#{"r"}]} in
   return %{"x"}].

Definition staton_bus_syntax : exp _ [::] _ :=
  [Normalize {staton_bus_syntax0}].

Let sample_bern : R.-sfker munit ~> mbool :=
  sample_cst [the probability _ _ of bernoulli p27].

Let ite_3_10 :
  R.-sfker [the measurableType _ of (mbool * munit)%type] ~> (mR R) :=
  ite macc0of2 (ret k3) (ret k10).

Let score_poisson4 :
  R.-sfker [the measurableType _ of (mR R * (mbool * munit))%type] ~> munit :=
  score (measurableT_comp (measurable_poisson 4) macc0of3').

(* same as kstaton_bus _ (measurable_poisson 4) but expressed with letin'
   instead of letin *)
Let kstaton_bus' :=
  letin' sample_bern
  (letin'
    (letin' ite_3_10
      score_poisson4)
    (ret macc1of3')).

Lemma eval_staton_bus0 : staton_bus_syntax0 -P> kstaton_bus'.
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
  by have -> : measurable_acc_typ [:: Real; Bool] 0 = macc0of3' by [].
by rewrite (execD_var "x") /=; congr ret.
Qed.

Let poisson4 := @poisson R 4%N.

Lemma exec_staton_bus0' t U : execP staton_bus_syntax0 t U =
  ((2 / 7%:R)%:E * (poisson4 3%:R)%:E * \d_true U +
  (5%:R / 7%:R)%:E * (poisson4 10%:R)%:E * \d_false U)%E.
Proof.
rewrite exec_staton_bus0.
rewrite /kstaton_bus'.
rewrite letin'_sample_bernoulli.
rewrite -!muleA; congr (_ * _ + _ * _)%E.
- rewrite letin'_kret//.
  rewrite letin'_iteT//.
  rewrite letin'_retk//.
  rewrite /score_poisson4.
  rewrite /score/= /mscale/= ger0_norm//= poisson_ge0//.
  by rewrite /acc0of3'/=.
- by rewrite onem27.
- rewrite letin'_kret//.
  rewrite letin'_iteF//.
  rewrite letin'_retk//.
  rewrite /score_poisson4.
  rewrite /score/= /mscale/= ger0_norm//= poisson_ge0//.
  by rewrite /acc0of3'/=.
Qed.

Lemma exec_staton_bus : execD staton_bus_syntax =
  existT _ (normalize kstaton_bus' point) (measurable_mnormalize _).
Proof. by rewrite execD_normalize exec_staton_bus0. Qed.

End staton_bus.

End StatonBusA.

Section staton_bus_letinA.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Import Notations.
Context {R : realType}.

Lemma test :
  execP staton_bus_syntax0 = @execP R _ _ StatonBusA.staton_bus_syntax0.
Proof.
rewrite /staton_bus_syntax0.
rewrite /StatonBusA.staton_bus_syntax0.
rewrite execP_letin.
rewrite [in RHS]execP_letin.
congr (letin' _).
pose f := @found _ Unit "x" Bool [::].
have r_f : "r" \notin [seq i.1 | i <- ("_", Unit) :: untag (ctx_of f)] by [].
set e1 := exp_if _ _ _.
set e2 := exp_score _.
set e3 := (exp_return _ in RHS).
apply/eq_sfkernel => /= x U.
have Htmp := @letinA _ _ _ _ _ _ (lookup Unit (("_", Unit) :: untag (ctx_of f)) "x")(*t3*) r_f e1 e2 e3.

have mU : (@mtyp_disp R (lookup Unit (("_", Unit) :: untag (ctx_of f)) "x")).-measurable U.
  simpl.
  rewrite /lookup/=.
  rewrite /mtyp_disp /=.
  by [].
move: Htmp.
move=> /(_ U mU).
move=> /(congr1 (fun f => f x)).
move=> <-.
set e3' := exp_return _.
set e3'' := exp_weak _ _ _ _.
rewrite !execP_letin.
have: execP e3' = execP (e3'' e3 r_f).
rewrite /e3'.
rewrite execP_return/= execD_var/=.
rewrite /e3''.
have -> := @execP_weak R [:: ("_", Unit)] (untag (ctx_of f)) ("r", Real) _ e3 r_f.
rewrite /= /e3.
rewrite execP_return execD_var//=.
by apply/eq_sfkernel => /= -[[] [a [b []]]] U0.
by move=> <-.
Qed.

End staton_bus_letinA.
