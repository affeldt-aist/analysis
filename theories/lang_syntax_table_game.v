Require Import String.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp.classical Require Import mathcomp_extra boolp classical_sets.
From mathcomp.classical Require Import functions cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences esum measure.
Require Import charge lebesgue_measure numfun lebesgue_integral kernel.
Require Import prob_lang lang_syntax_util lang_syntax lang_syntax_examples.
From mathcomp Require Import ring lra.

(**md**************************************************************************)
(* # Eddy's table game example                                                *)
(*                                                                            *)
(* ref:                                                                       *)
(* - Chung-chieh Shan, Equational reasoning for probabilistic programming,    *)
(*   POPL TutorialFest 2018                                                   *)
(*   https://homes.luddy.indiana.edu/ccshan/rational/equational-handout.pdf   *)
(* - Sean R Eddy, What is Bayesian statistics?, Nature Biotechnology 22(9),   *)
(*   1177--1178 (2004)                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Open Scope ereal_scope.
Lemma letin'_sample_uniform {R : realType} d d' (T : measurableType d)
    (T' : measurableType d') (a b : R) (ab : (a < b)%R)
    (u : R.-sfker [the measurableType _ of (_ * T)%type] ~> T') x y :
  measurable y ->
  letin' (sample_cst (uniform_prob ab)) u x y =
  (b - a)^-1%:E * \int[lebesgue_measure]_(x0 in `[a, b]) u (x0, x) y.
Proof.
move=> my; rewrite letin'E/=.
rewrite integral_uniform//=.
move => _ /= Y mY /=.
have /= := measurable_kernel u _ my measurableT _ mY.
move/measurable_ysection => /(_ R x) /=.
set A := (X in measurable X).
set B := (X in _ -> measurable X).
suff : A = B by move=> ->.
rewrite {}/A {}/B !setTI /ysection/= (*TODO: lemma?*) /preimage/=.
by apply/seteqP; split => [z|z] /=; rewrite inE/=.
Qed.

Local Open Scope lang_scope.
Lemma execP_letin_uniform {R : realType}
  g t str (s0 s1 : exp P ((str, Real) :: g) t) :
  (forall (p : R) x U, (0 <= p <= 1)%R ->
    execP s0 (p, x) U = execP s1 (p, x) U) ->
  forall x U, measurable U ->
  execP [let str := Sample {@exp_uniform _ g 0 1 (@ltr01 R)} in {s0}] x U =
  execP [let str := Sample {@exp_uniform _ g 0 1 (@ltr01 R)} in {s1}] x U.
Proof.
move=> s01 x U mU.
rewrite !execP_letin execP_sample execD_uniform/=.
rewrite !letin'_sample_uniform//.
congr *%E.
apply: eq_integral => p p01.
apply: s01.
by rewrite inE in p01.
Qed.
Local Close Scope lang_scope.
Local Close Scope ereal_scope.

Section bounded.
Local Open Scope ring_scope.
Local Open Scope lang_scope.
Local Open Scope ereal_scope.
Context {R : realType}.

Lemma bounded_id_01 : [bounded x0 | x0 in `[0%R, 1%R]%classic : set R].
Proof.
exists 1%R; split => // y y1.
near=> M => /=.
rewrite (le_trans _ (ltW y1))//.
near: M.
move=> M /=.
rewrite in_itv/= => /andP[M0 M1].
by rewrite ler_norml M1 andbT (le_trans _ M0).
Unshelve. all: by end_near. Qed.

Lemma bounded_onem_01 : [bounded (`1- x : R) | x in `[0%R, 1%R]%classic : set R].
Proof.
exists 1%R; split => // y y1.
near=> M => /=.
rewrite (le_trans _ (ltW y1))//.
near: M.
move=> M /=.
rewrite in_itv/= => /andP[M0 M1].
rewrite ler_norml (@le_trans _ _ 0%R)//=.
  by rewrite lerBlDr addrC -lerBlDr subrr.
by rewrite onem_ge0.
Unshelve. all: by end_near. Qed.

Lemma bounded_cst_01 (x : R) : [bounded x | _ in `[0%R, 1%R]%classic : set R].
Proof.
exists `|x|%R; split.
  by rewrite num_real.
move=> y y1/= z.
rewrite in_itv/= => /andP[z0 z1].
by rewrite (le_trans _ (ltW y1)).
Qed.

Lemma bounded_norm (f : R -> R) :
  [bounded f x | x in (`[0%R, 1%R]%classic : set R)] <->
  [bounded normr (f x) | x in (`[0%R, 1%R]%classic : set R)].
Proof.
split.
  move=> [M [Mreal HM]].
  exists `|M|%R; split; first by rewrite normr_real.
  move=> r Mr x/= x01.
  by rewrite ger0_norm// HM// (le_lt_trans _ Mr)// ler_norm.
move=> [M [Mreal HM]].
exists `|M|%R; split; first by rewrite normr_real.
move=> r Mr x/= x01.
rewrite -[leLHS]ger0_norm// HM//.
by rewrite (le_lt_trans _ Mr)// ler_norm.
Qed.

Lemma boundedMl k (f : R -> R) :
  [bounded f x | x in (`[0%R, 1%R]%classic : set R)] ->
  [bounded (k * f x)%R | x in (`[0%R, 1%R]%classic : set R)].
Proof.
move=> [M [Mreal HM]].
exists `|k * M|%R; split; first by rewrite normr_real.
move=> r kMr x/= x01.
rewrite normrM.
have [->|k0] := eqVneq k 0%R.
  by rewrite normr0 mul0r (le_trans _ (ltW kMr)).
rewrite -ler_pdivlMl ?normr_gt0//.
apply: HM => //.
rewrite ltr_pdivlMl ?normr_gt0//.
rewrite (le_lt_trans _ kMr)//.
by rewrite normrM ler_pM2l ?normr_gt0// ler_norm.
Qed.

Lemma bounded_casino23 :
  [bounded normr (56 * x ^+ 5 * (1 - x) ^+ 3)%R : R |
   x in (`[0%R, 1%R]%classic : set R)].
Proof.
rewrite (@eq_fun _ _ _ (fun x => normr (56 * (x ^+ 5 * (1 - x) ^+ 3))))//; last first.
  by move=> x; rewrite -mulrA.
apply/(bounded_norm _).1.
apply: boundedMl.
apply/(bounded_norm _).2.
exact: bounded_norm_expn_onem.
Qed.

End bounded.

Lemma measurable_bernoulli_expn {R : realType} U n :
  measurable_fun [set: salgebraType (R.-ocitv.-measurable)]
    (fun x : salgebraType (R.-ocitv.-measurable) => bernoulli ((1 - x) ^+ n) U).
Proof.
apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
by apply: measurable_fun_pow => //=; exact: measurable_funB.
Qed.

Lemma integrable_bernoulli_beta_nat_pdf {R : realType} U : measurable U ->
  (@lebesgue_measure R).-integrable [set: salgebraType (R.-ocitv.-measurable)]
    (fun x => (bernoulli (1 - (1 - x) ^+ 3) U * (beta_nat_pdf 6 4 x)%:E)%E).
Proof.
move=> mU.
have ? : measurable_fun [set: salgebraType (R.-ocitv.-measurable)]
    (fun x => bernoulli (1 - (1 - x) ^+ 3) U).
  apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
  apply: measurable_funB => //; apply: measurable_fun_pow => //.
  exact: measurable_funB.
apply/integrableP; split => /=.
  apply: emeasurable_funM => //.
  apply/EFin_measurable_fun.
  exact: measurable_beta_nat_pdf.
apply: (@le_lt_trans _ _ (\int[lebesgue_measure]_(x in `[0%R, 1%R]) (beta_nat_pdf 6 4 x)%:E))%E.
  rewrite [leRHS]integral_mkcond /=.
  apply: ge0_le_integral => //=.
  - apply: measurableT_comp => //; apply: emeasurable_funM => //.
    by apply/EFin_measurable_fun; exact: measurable_beta_nat_pdf.
  - move=> x _ /=; rewrite patchE; case: ifPn => // _.
    by rewrite lee_fin beta_nat_pdf_ge0.
  - apply: (measurable_restrict (E := setT) _ _ _ _).1 => //.
    apply/measurable_funTS/measurableT_comp => //.
    exact: measurable_beta_nat_pdf.
  - move=> x _.
    rewrite patchE; case: ifPn.
      rewrite inE/= in_itv/= => /andP[x0 x1].
      rewrite gee0_abs//.
        rewrite gee_pMl// ?probability_le1//.
          by rewrite ge0_fin_numE// (le_lt_trans (probability_le1 _ _))// ltry.
        by rewrite lee_fin beta_nat_pdf_ge0.
      by rewrite mule_ge0// lee_fin beta_nat_pdf_ge0.
    rewrite notin_setE/= in_itv/= => /negP; rewrite negb_and -!ltNge => /orP[x0|x1].
      by rewrite /beta_nat_pdf /ubeta_nat_pdf (leNgt 0) x0/= mul0r mule0 abse0.
    by rewrite /beta_nat_pdf /ubeta_nat_pdf (leNgt x) x1/= andbF mul0r mule0 abse0.
apply: (@le_lt_trans _ _
    (\int[lebesgue_measure]_(x in `[0%R, 1%R]) (beta_nat_norm 6 4)^-1%:E)%E); last first.
  by rewrite integral_cst//= lebesgue_measure_itv/= lte01 EFinN sube0 mule1 ltry.
apply: ge0_le_integral => //=.
- by move=> ? _; rewrite lee_fin beta_nat_pdf_ge0.
- by apply/measurable_funTS/measurableT_comp => //; exact: measurable_beta_nat_pdf.
- by move=> ? _; rewrite lee_fin invr_ge0// beta_nat_norm_ge0.
- by move=> x _; rewrite lee_fin beta_nat_pdf_le_beta_nat_norm.
Qed.

Section casino_programs.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := lebesgue_measure.

Definition casino0 : @exp R _ [::] _ :=
 [Normalize
  let "p" := Sample {exp_uniform 0 1 (@ltr01 R)} in
  let "a1" := Sample {exp_binomial 8 [#{"p"}]} in
  let "_" := if #{"a1"} == {5}:N then return TT else Score {0}:R in
  let "a2" := Sample {exp_binomial 3 [#{"p"}]} in
  return {1}:N <= #{"a2"}].

Definition tail1 : @exp R _ [:: ("_", Unit); ("a1", Nat) ; ("p", Real)] _ :=
  [Sample {exp_bernoulli [{1}:R - {[{1}:R - #{"p"}]} ^+ {3%nat}]}].

Definition tail2 : @exp R _ [:: ("_", Unit); ("p", Real)] _ :=
  [Sample {exp_bernoulli [{1}:R - {[{1}:R - #{"p"}]} ^+ {3%nat}]}].

Definition tail3 : @exp R _ [:: ("p", Real); ("_", Unit)] _ :=
  [Sample {exp_bernoulli [{1}:R - {[{1}:R - #{"p"}]} ^+ {3%nat}]}].

Definition casino1 : @exp R _ [::] _ :=
 [Normalize
  let "p" := Sample {exp_uniform 0 1 (@ltr01 R)} in
  let "a1" := Sample {exp_binomial 8 [#{"p"}]} in
  let "_" := if #{"a1"} == {5}:N then return TT else Score {0}:R in
  {tail1}].

Definition casino2 : @exp R _ [::] _ :=
 [Normalize
  let "p" := Sample {exp_uniform 0 1 (@ltr01 R)} in
  let "_" :=
    Score {[{56}:R * #{"p"} ^+ {5%nat} * {[{1}:R - #{"p"}]} ^+ {3%nat}]} in
  {tail2}].

Definition casino2' : @exp R _ [::] _ :=
 [Normalize
  let "p" := Sample {exp_beta 1 1} in
  let "_" := Score
    {[{56}:R * #{"p"} ^+ {5%nat} * {[{1}:R - #{"p"}]} ^+ {3%N}]} in
  {tail2}].

Definition casino3 : @exp R _ [::] _ :=
 [Normalize
  let "_" := Score {1 / 9}:R in
  let "p" := Sample {exp_beta 6 4} in
  {tail3}].

Definition casino4 : @exp R _ [::] _ :=
 [Normalize
  let "_" := Score {1 / 9}:R in
  Sample {exp_bernoulli [{10 / 11}:R]}].

Definition casino5 : @exp R _ [::] _ :=
  [Normalize Sample {exp_bernoulli [{10 / 11}:R]}].

End casino_programs.
Arguments tail1 {R}.
Arguments tail2 {R}.

Section casino01.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := lebesgue_measure.

Let casino01_subproof
  (x : mctx (untag (ctx_of (recurse Unit (recurse Nat (found "p" Real [::])))))) U :
  (0 <= x.2.2.1 <= 1)%R ->
  execP [let "a2" := Sample {exp_binomial 3 [#{"p"}]} in
         return {1}:N <= #{"a2"}] x U =
  execP (@tail1 R) x U.
Proof.
move=> x01.
rewrite /tail1.
(* reduce lhs *)
rewrite execP_letin execP_sample execD_binomial/= execP_return/= execD_rel/=.
rewrite exp_var'E (execD_var_erefl "p")/=.
rewrite exp_var'E (execD_var_erefl "a2")/=.
rewrite execD_nat/=.
rewrite [LHS]letin'E/=.
(* reduce rhs *)
rewrite execP_sample/= execD_bernoulli/= (@execD_bin _ _ binop_minus)/=.
rewrite execD_real/= execD_pow/= (@execD_bin _ _ binop_minus)/= execD_real/=.
rewrite (execD_var_erefl "p")/=.
exact/integral_binomial_prob.
Qed.

Lemma casino01 : execD (@casino0 R) = execD (@casino1 R).
Proof.
rewrite /casino0 /casino1.
apply: congr_normalize => y A.
apply: execP_letin_uniform => // p [] B p01.
apply: congr_letinr => a1 V0.
apply: congr_letinr => -[] V1.
exact: casino01_subproof.
Qed.

End casino01.

Section casino12.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := lebesgue_measure.

Let casino12_subproof (y : @mctx R [::]) (V : set (@mtyp R Bool))
  (p : R)
  (x : projT2 (existT measurableType default_measure_display unit))
  (U : set (mtyp Bool))
  (p0 : (0 <= p)%R)
  (p1 : (p <= 1)%R) :
  \int[binomial_prob 8 p]_y0
     execP [let "_" := if #{"a1"} == {5} :N then return TT else Score {0}:R in {tail1}]
       (y0, (p, x)) U =
  \int[mscale (NngNum (normr_ge0 (56 * p ^+ 5 * (1 - p) ^+ 3))) \d_tt]_y0
     execP tail2 (y0, (p, x)) U.
Proof.
rewrite integral_binomial//=.
rewrite (bigD1 (inord 5))//=.
rewrite big1 ?adde0; last first.
  move=> i Hi5.
  rewrite execP_letin/= execP_if/= execD_rel/=.
  rewrite exp_var'E/= (execD_var_erefl "a1")/=.
  rewrite execD_nat/= execP_score/= execD_real/= execP_return/=.
  rewrite letin'E iteE/=.
  move: i Hi5.
  move=> [[|[|[|[|[|[|[|[|[|//]]]]]]]]]]//= Hi Hi5;
  rewrite ?ge0_integral_mscale//= ?execD_real/= ?normr0 ?(mul0e,mule0)//.
  suff: false by [].
  move/negbTE: Hi5 => <-.
  by apply/eqP/val_inj => /=; rewrite inordK.
(* reduce lhs *)
rewrite execP_letin/= execP_if/= execD_rel/=.
rewrite exp_var'E/= (execD_var_erefl "a1")/=.
rewrite execD_nat/= execP_score/= execD_real/= execP_return/=.
rewrite letin'E iteE/=.
rewrite inordK// eqxx.
rewrite integral_dirac//= execD_unit/= diracE mem_set// mul1e.
(* reduce rhs *)
rewrite ge0_integral_mscale//=.
rewrite integral_dirac//= diracE mem_set// mul1e.
rewrite ger0_norm ?mulr_ge0 ?subr_ge0//.
rewrite -mulrA mulr_natl.
(* same score *)
congr *%E.
(* the tails are the same module the shape of the environment *)
rewrite /tail1 /tail2 !execP_sample/=.
rewrite !execD_bernoulli/=.
rewrite !(@execD_bin _ _ binop_minus)/=.
rewrite !execD_pow/=.
rewrite !execD_real/=.
rewrite !(@execD_bin _ _ binop_minus)/=.
by rewrite !execD_real/= !exp_var'E/= !(execD_var_erefl "p")/=.
Qed.

Lemma casino12 : execD (@casino1 R) = execD (@casino2 R).
Proof.
apply: congr_normalize => y V.
apply: execP_letin_uniform => //.
move=> p x U /andP[p0 p1].
(* reduce the lhs *)
rewrite execP_letin execP_sample execD_binomial/=.
rewrite letin'E/=.
rewrite [in LHS]exp_var'E/= (execD_var_erefl "p")/=.
(* reduce the rhs *)
rewrite [in RHS]execP_letin execP_score/=.
rewrite letin'E/=.
do 2 rewrite (@execD_bin _ _ binop_mult)/=/=.
rewrite [in RHS]exp_var'E/=.
rewrite execD_pow/=.
rewrite (execD_var_erefl "p")/=.
rewrite execD_pow/=.
rewrite (@execD_bin _ _ binop_minus)/=/=.
rewrite 2!execD_real/=.
rewrite (execD_var_erefl "p")/=.
exact: casino12_subproof.
Qed.

End casino12.

Section casino23.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := lebesgue_measure.

Lemma casino22' : execD (@casino2 R) = execD (@casino2' R).
Proof.
apply: congr_normalize => // x U.
apply: congr_letinl => // y V.
rewrite !execP_sample execD_uniform/= execD_beta_nat/=.
by rewrite beta11_uniform.
Qed.

Let H1 U : measurable_fun [set: g_sigma_algebraType (R.-ocitv.-measurable)]
  (fun x => bernoulli (1 - (1 - x) ^+ 3) U).
Proof.
apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
apply: measurable_funB => //.
apply: measurable_fun_pow.
exact: measurable_funB.
Qed.

Let H2 U a b : (\int[beta_nat a b]_x `|bernoulli (1 - (1 - x) ^+ 3) U| < +oo :> \bar R)%E.
Proof.
apply: (@le_lt_trans _ _ (\int[beta_nat a b]_x 1)%E).
  apply: ge0_le_integral => //=.
    exact/measurableT_comp.
  move=> x _.
  by rewrite gee0_abs// probability_le1.
by rewrite integral_cst//= mul1e -ge0_fin_numE// beta_nat_fin_num.
Qed.

Let H3 U :
  (beta_nat 1 1).-integrable [set: g_sigma_algebraType (R.-ocitv.-measurable)]
  (fun x => bernoulli (1 - (1 - x) ^+ 3) U * (normr (56 * x ^+ 5 * (1 - x) ^+ 3))%:E).
Proof.
apply/integrableP; split.
  apply: emeasurable_funM => //.
  apply/EFin_measurable_fun => //.
  apply: measurableT_comp => //.
  apply: measurable_funM => //.
    exact: measurable_funM.
  apply: measurable_fun_pow => //.
  exact: measurable_funB.
rewrite beta11_uniform.
rewrite integral_uniform//=.
  rewrite subr0 invr1 mul1e.
  suff : (mu.-integrable `[0%R, 1%R]
    (fun y : R => bernoulli (1 - (1 - y) ^+ 3) U *
                  (normr (56 * y ^+ 5 * (1 - y) ^+ 3))%:E))%E.
    by move=> /integrableP[].
  apply: integrableMl => //=.
  - apply/integrableP; split.
      exact: measurable_funTS.
    have := H2 U 1%N 1%N.
    rewrite beta11_uniform.
    rewrite integral_uniform//=; last first.
      exact: measurableT_comp.
    by rewrite subr0 invr1 mul1e.
  apply: @measurableT_comp => //.
  apply: measurable_funM => //.
    exact: measurable_funM.
  apply: measurable_fun_pow => //.
    exact: measurable_funB.
  exact: bounded_casino23.
apply: @measurableT_comp => //.
apply: emeasurable_funM => //.
do 2 apply: @measurableT_comp => //.
apply: measurable_funM => //.
  exact: measurable_funM.
by apply: measurable_fun_pow => //; exact: measurable_funB.
Qed.

Lemma casino23 : execD (@casino2' R) = execD (@casino3 R).
Proof.
apply: congr_normalize => x U.
rewrite !execP_letin !execP_sample !execP_score !execD_beta_nat.
rewrite !execD_bernoulli/= !(@execD_bin _ _ binop_mult).
do 2 (rewrite !execD_pow !(@execD_bin _ _ binop_minus) !execD_real/=).
rewrite !exp_var'E !(execD_var_erefl "p")/=.
rewrite !letin'E/= ![in RHS]ge0_integral_mscale//=.
under eq_integral => y _.
  rewrite letin'E/=.
  rewrite integral_cst//= /mscale/= diracT mule1.
  over.
rewrite /=.
rewrite integral_beta_nat//=; last 2 first.
  - apply: emeasurable_funM => //.
    apply/EFin_measurable_fun.
    apply: measurableT_comp => //.
    apply: measurable_funM => //.
      exact: measurable_funM.
    apply: measurable_fun_pow => //.
    exact: measurable_funB.
  - have := H3 U.
    by move=> /integrableP[].
rewrite ger0_norm// integral_dirac// diracT mul1e letin'E/=.
rewrite integral_beta_nat/=; [|by []|by []|exact: H2].
rewrite -integralZl//=; last exact: integrable_bernoulli_beta_nat_pdf.
apply: eq_integral => y _.
rewrite /beta_nat_pdf /ubeta_nat_pdf.
case: ifPn; last first.
  by rewrite !(mul0r,mulr0,mule0).
move=> /andP[y0 y1].
rewrite [RHS]muleCA -!muleA.
congr *%E.
rewrite /= !expr0 mulr1 !div1r.
rewrite ger0_norm//; last first.
  by rewrite mulr_ge0 ?exprn_ge0 ?subr_ge0// mulr_ge0// exprn_ge0.
rewrite -!EFinM; congr EFin.
by rewrite !beta_nat_normE/= factE/= /onem; lra.
Qed.

End casino23.

Section casino34.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := lebesgue_measure.

Lemma integral_bernoulli_beta_nat_pdf' (f : _ -> R) U : measurable_fun setT f ->
  (forall x, x \in (`[0%R, 1%R]%classic : set R) -> 0 <= f x <= 1)%R ->
  \int[mu]_(y in `[0%R, 1%R]) (bernoulli (1 - f y) U * (beta_nat_pdf 6 4 y)%:E) =
  (\d_true U + \d_false U) * beta_nat 6 4 setT -
  \int[mu]_(y in `[0%R, 1%R])
    (bernoulli (f y) U * (beta_nat_pdf 6 4 y)%:E).
Proof.
move=> mf f01.
have f0 x : x \in (`[0%R, 1%R]%classic : set R) -> (0 <= f x)%R.
  by move => /f01/andP[].
have f1 x : x \in (`[0%R, 1%R]%classic : set R) -> (f x <= 1)%R.
  by move => /f01/andP[].
under eq_integral => x.
  move=> x01.
  rewrite bernoulliE//=; last first.
    by rewrite subr_ge0 f1//= lerBlDr addrC -lerBlDr subrr f0.
  over.
rewrite /=.
under [LHS]eq_integral.
  rewrite /= => x _.
  rewrite onemK muleDl//.
  over.
rewrite /=.
rewrite ge0_integralD//=; last 4 first.
  move=> x x01; rewrite mule_ge0// ?lee_fin ?beta_nat_pdf_ge0//.
  by rewrite mulr_ge0// subr_ge0// f1// inE.
  apply: measurable_funTS; apply: emeasurable_funM => //.
    by apply: emeasurable_funM => //; apply/EFin_measurable_fun/measurable_funB.
  by apply/EFin_measurable_fun; apply: measurable_beta_nat_pdf.
  by move=> x x01; rewrite mule_ge0// ?lee_fin ?beta_nat_pdf_ge0// mulr_ge0// f0// inE.
  apply: measurable_funTS; apply: emeasurable_funM => //.
    by apply: emeasurable_funM; apply/EFin_measurable_fun.
  by apply/EFin_measurable_fun; exact: measurable_beta_nat_pdf.
under eq_integral do rewrite muleAC/=.
rewrite ge0_integralZr//=; last 2 first.
  apply: measurable_funTS; apply: emeasurable_funM => //.
    by apply/EFin_measurable_fun/measurable_funB.
  by apply/EFin_measurable_fun; exact: measurable_beta_nat_pdf.
  move=> x x01.
  by rewrite mule_ge0// lee_fin// ?subr_ge0// ?f1// ?inE// beta_nat_pdf_ge0.
under [X in _ + X = _]eq_integral do rewrite muleAC/=.
rewrite [X in _ + X = _]ge0_integralZr//=; last 2 first.
  apply: measurable_funTS; apply: emeasurable_funM => //.
    exact/EFin_measurable_fun.
  by apply/EFin_measurable_fun; exact: measurable_beta_nat_pdf.
  by move=> x x01; rewrite mule_ge0// lee_fin// ?f0// ?inE// beta_nat_pdf_ge0.
under [in RHS]eq_integral => x x01.
  rewrite bernoulliE//=; last by rewrite f0//= f1.
  rewrite muleDl//.
  over.
rewrite /= ge0_integralD//=; last 4 first.
  move=> x x01; rewrite mule_ge0// ?lee_fin ?beta_nat_pdf_ge0// mulr_ge0// f0//.
  by rewrite inE.
  apply: measurable_funTS; apply: emeasurable_funM => //.
    by apply: emeasurable_funM => //; apply/EFin_measurable_fun.
  by apply/EFin_measurable_fun; exact: measurable_beta_nat_pdf.
  move=> x x01; rewrite mule_ge0// ?lee_fin ?beta_nat_pdf_ge0// mulr_ge0//.
  by rewrite subr_ge0 f1// inE.
  apply: measurable_funTS;apply: emeasurable_funM => //.
    by apply: emeasurable_funM => //; apply/EFin_measurable_fun/measurable_funB.
  by apply/EFin_measurable_fun; exact: measurable_beta_nat_pdf.
under [X in _ = _ - (X + _)]eq_integral do rewrite muleAC/=.
rewrite [X in _ = _ - (X + _)]ge0_integralZr//=; last 2 first.
  apply: measurable_funTS => //; apply: emeasurable_funM => //.
    by apply/EFin_measurable_fun.
  by apply/EFin_measurable_fun; exact: measurable_beta_nat_pdf.
  by move=> x x01; rewrite mule_ge0// lee_fin// ?f0// ?inE// beta_nat_pdf_ge0.
under [X in _ = _ - (_ + X)]eq_integral do rewrite muleAC/=.
rewrite [X in _ = _ - (_ + X)]ge0_integralZr//=; last 2 first.
  apply: measurable_funTS => //; apply: emeasurable_funM => //.
    by apply/EFin_measurable_fun/measurable_funB.
  by apply/EFin_measurable_fun; exact: measurable_beta_nat_pdf.
  move=> x x01; rewrite mule_ge0// lee_fin// ?beta_nat_pdf_ge0//.
  by rewrite subr_ge0 f1// inE.
rewrite oppeD//; last first.
  rewrite ge0_adde_def// inE mule_ge0// integral_ge0//= => x x01;
  by rewrite mule_ge0 ?lee_fin ?beta_nat_pdf_ge0// ?subr_ge0 ?f0 ?f1 ?inE//.
rewrite addrA.
rewrite -mulNe.
 rewrite -integral_ge0N//=; last first.
  by move=> x x01; rewrite mule_ge0 ?lee_fin ?beta_nat_pdf_ge0// f0// inE.
rewrite -mulNe.
rewrite -integral_ge0N//=; last first.
  by move=> x x01; rewrite mule_ge0 ?lee_fin ?beta_nat_pdf_ge0// subr_ge0 f1// inE.
under [X in _ = (_ + _ + X * _)%E]eq_integral.
  move=> /= y _.
  rewrite /onem mulrBl mul1r opprB EFinB.
  over.
rewrite /=.
rewrite [in RHS]muleDl//; last first.
  by rewrite beta_nat_fin_num.
rewrite -addeA.
rewrite addeACA.
rewrite [in RHS](muleC _ (\d_false U)).
rewrite -muleDr//; last first.
  by rewrite fin_num_adde_defr// beta_nat_fin_num.
rewrite [in RHS](muleC _ (\d_true U)).
rewrite -muleDr//; last first.
  by rewrite fin_num_adde_defr// beta_nat_fin_num.
have ? : (beta_nat 6 4).-integrable [set: salgebraType (R.-ocitv.-measurable)] (EFin \o (fun=> 1%R)).
  apply/integrableP; split.
    exact/EFin_measurable_fun.
  rewrite integral_beta_nat//=.
    under eq_integral do rewrite normr1 mul1e.
    rewrite /=.
    have /integrableP[_] := @integrable_beta_nat_pdf R 6 4.
    under eq_integral.
      move=> /= x.
      rewrite ger0_norm ?beta_nat_pdf_ge0//.
      over.
    by rewrite /=.
  rewrite integral_cst//= !normr1 mul1e.
  by rewrite -ge0_fin_numE// beta_nat_fin_num.
have ? : lebesgue_measure.-integrable [set: salgebraType (R.-ocitv.-measurable)]
    (EFin \o (fun x : salgebraType (R.-ocitv.-measurable) => (f x * beta_nat_pdf 6 4 x)%R)).
    apply/integrableP; split.
      apply/EFin_measurable_fun.
      apply/measurable_funM => //.
      exact: measurable_beta_nat_pdf.
    rewrite /=.
    rewrite [ltLHS](_ : _ = \int[lebesgue_measure]_(x in `[0%R, 1%R])
        (normr (f x * beta_nat_pdf 6 4 x))%:E); last first.
      rewrite [RHS]integral_mkcond /=.
      apply: eq_integral => x _.
      rewrite patchE; case: ifPn => //.
      rewrite notin_setE/= in_itv/= => /negP; rewrite negb_and -!ltNge => /orP[x0|x1].
      by rewrite /beta_nat_pdf /ubeta_nat_pdf leNgt x0/= mul0r mulr0 normr0.
      by rewrite /beta_nat_pdf /ubeta_nat_pdf (leNgt x) x1 andbF mul0r mulr0 normr0.
    apply: (@le_lt_trans _ _ (\int[lebesgue_measure]_(x in `[0%R, 1%R]) (beta_nat_norm 6 4)^-1%:E)).
      apply: ge0_le_integral => //=.
        apply: measurable_funTS; apply: measurableT_comp => //=.
        apply: measurableT_comp => //=; apply: measurable_funM => //=.
        exact: measurable_beta_nat_pdf.
      by move=> _ _; rewrite lee_fin invr_ge0// beta_nat_norm_ge0.
    move=> x x01.
    rewrite ger0_norm//; last first.
      by rewrite mulr_ge0// ?f0 ?inE// beta_nat_pdf_ge0.
    rewrite lee_fin.
    rewrite -[leRHS]mul1r.
    rewrite ler_pM// ?beta_nat_pdf_ge0// ?f0 ?f1 ?inE//.
    exact: beta_nat_pdf_le_beta_nat_norm.
    rewrite integral_cst//=.
    by rewrite lebesgue_measure_itv//= lte01 EFinN sube0 mule1 ltry.
rewrite [in LHS](muleC _ (\d_false U)).
rewrite [in LHS](muleC _ (\d_true U)).
congr (_ * _ + _ * _).
  under eq_integral do rewrite EFinB muleBl// mul1e.
  rewrite integralB_EFin//=; last first.
    by apply: (@integrableS _ _ _ _ setT) => //.
    apply: (@integrableS _ _ _ _ setT) => //.
    exact: integrable_beta_nat_pdf.
  under [in RHS]eq_integral do rewrite EFinN EFinM.
  rewrite [X in _ = _ + X]integral_ge0N //; last first.
    move=> x x01.
    by rewrite mule_ge0// lee_fin// ?f0 ?inE// beta_nat_pdf_ge0.
  rewrite /=.
  congr (_ - _).
  by rewrite -integral_beta_nat_pdf// int_beta_nat_pdf01.
rewrite integralB_EFin//=.
- rewrite addeCA.
  rewrite -integral_beta_nat_pdf// int_beta_nat_pdf01 subee ?adde0//.
  by rewrite integral_beta_nat_pdf// beta_nat_fin_num.
- exact: (@integrableS _ _ _ _ setT).
- by apply: (@integrableS _ _ _ _ setT) => //; exact: integrable_beta_nat_pdf.
Qed.

Lemma integral_bernoulli_beta_nat_pdf (f : _ -> R) U p :
  measurable_fun setT f ->
  (forall x, x \in (`[0%R, 1%R]%classic : set R) -> 0 <= f x <= 1)%R ->
  (\int[mu]_(y in `[0%R, 1%R]) (bernoulli (f y) U * (beta_nat_pdf 6 4 y)%:E) =
    p%:E * \d_true U +
    (beta_nat 6 4 [set: _] - p%:E) * \d_false U)%E
  ->
  (\int[mu]_(y in `[0%R, 1%R]) (bernoulli (1 - f y) U * (beta_nat_pdf 6 4 y)%:E) =
    (beta_nat 6 4 [set: _] - p%:E) * \d_true U +
    p%:E * \d_false U)%E.
Proof.
move=> mf f01 H.
rewrite integral_bernoulli_beta_nat_pdf'//= H.
rewrite oppeD// muleDl ?beta_nat_fin_num//=.
rewrite addeACA EFinN EFinM muleC -muleBl//; last first.
  by rewrite fin_num_adde_defr// beta_nat_fin_num.
rewrite (muleC (\d_false U)) -muleBl//; last first.
  by rewrite fin_num_adde_defr// beta_nat_fin_num.
congr +%E.
rewrite oppeD// ?fin_num_adde_defr ?beta_nat_fin_num//.
by rewrite addeA subee ?beta_nat_fin_num// EFinN oppeK add0e.
Qed.

Lemma casino34' U :
  @execP R [::] _ [let "p" := Sample {exp_beta 6 4} in
         Sample {exp_bernoulli [{[{1}:R - #{"p"}]} ^+ {3%N}]}] tt U =
  @execP R [::] _ [Sample {exp_bernoulli [{1 / 11}:R]}] tt U.
Proof.
rewrite execP_letin !execP_sample execD_beta_nat !execD_bernoulli/=.
rewrite execD_pow/= (@execD_bin _ _ binop_minus) !execD_real/=.
rewrite exp_var'E (execD_var_erefl "p")/=.
(* TODO: generalize *)
rewrite letin'E/=.
transitivity (\int[beta_nat 6 4]_(y in `[0%R, 1%R]%classic : set R)
    bernoulli ((1 - y) ^+ 3) U)%E.
  rewrite integral_beta_nat//; last 2 first.
    by apply: measurable_funTS; apply: measurable_bernoulli_expn.
    apply: (le_lt_trans _ (integral_beta_bernoulli_expn_lty 3 6 4 U)).
    apply: ge0_subset_integral => //=; apply: measurableT_comp => //=.
    apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
    by apply: measurable_fun_pow => //=; exact: measurable_funB.
  rewrite integral_beta_nat//; last 2 first.
    exact: measurable_bernoulli_expn.
    exact: integral_beta_bernoulli_expn_lty.
  rewrite [RHS]integral_mkcond/=; apply: eq_integral => x _ /=.
  rewrite patchE; case: ifPn => //.
  rewrite /beta_nat_pdf /ubeta_nat_pdf notin_setE/= in_itv/= => /negP/negbTE ->.
  by rewrite mul0r mule0.
have := (@beta_nat_bernoulliE R 6 4 0 3 U) isT isT.
rewrite /beta_nat_bernoulli /ubeta_nat_pdf /=.
under eq_integral.
  move=> x.
  rewrite inE /=in_itv/= => ->.
  rewrite expr0 mul1r.
  over.
rewrite /= => ->; congr bernoulli.
by rewrite /div_beta_nat_norm addn0 !beta_nat_normE/= !factE/=; field.
Qed.

Lemma casino34 : execD (@casino3 R) = execD (@casino4 R).
Proof.
apply: congr_normalize => y V.
apply: congr_letinr => x U.
rewrite execP_letin !execP_sample execD_beta_nat !execD_bernoulli/=.
rewrite (@execD_bin _ _ binop_minus) execD_pow/= (@execD_bin _ _ binop_minus).
rewrite !execD_real/= exp_var'E (execD_var_erefl "p")/=.
transitivity (\int[beta_nat 6 4]_y bernoulli (1 - (1 - y) ^+ 3) U : \bar R)%E.
  by rewrite /beta_nat_bernoulli !letin'E/= /onem.
rewrite bernoulliE//=; last lra.
rewrite integral_beta_nat//; last first.
  by have := @integral_beta_bernoulli_onem_lty R _ _ _ U.
  apply: (measurableT_comp (measurable_bernoulli2 _)) => //.
  apply: measurable_funB => //; apply: measurable_fun_pow => //.
  exact: measurable_funB.
transitivity (\int[mu]_(x in `[0%R, 1%R]) (bernoulli (1 - (1 - x) ^+ 3) U *
                                           (beta_nat_pdf 6 4 x)%:E) : \bar R)%E.
  rewrite [RHS]integral_mkcond; apply: eq_integral => z _.
  rewrite /= patchE; case: ifPn => //.
  rewrite notin_setE /= in_itv /= => /negP.
  rewrite negb_and -!ltNge => /orP[z0|z1].
    by rewrite /beta_nat_pdf /ubeta_nat_pdf leNgt z0/= mul0r mule0.
  by rewrite /beta_nat_pdf /ubeta_nat_pdf (leNgt z) z1/= andbF mul0r mule0.
rewrite (@integral_bernoulli_beta_nat_pdf (fun x => (1 - x) ^+ 3)%R U (1 / 11))//=; last 3 first.
  by apply: measurable_fun_pow => //; exact: measurable_funB.
  move=> z.
  rewrite inE/= in_itv/= => /andP[z0 z1].
  rewrite exprn_ge0 ?subr_ge0//= exprn_ile1// ?subr_ge0//.
  by rewrite lerBlDr addrC -lerBlDr subrr.
  transitivity (beta_nat_bernoulli 6 4 0 3 U : \bar R).
    rewrite /beta_nat_bernoulli /ubeta_nat_pdf/= /onem.
    rewrite [RHS]integral_beta_nat//; last 2 first.
      apply: (measurableT_comp (measurable_bernoulli2 _)) => //.
      apply: measurable_fun_if => //.
        by apply: measurable_and => //; exact: measurable_fun_ler.
      apply: measurable_funTS; apply: measurable_funM => //.
      by apply: measurable_fun_pow => //; exact: measurable_funB.
    rewrite (le_lt_trans _ (integral_beta_bernoulli_expn_lty 3 6 4 U))//.
    rewrite integral_mkcond /=; apply: ge0_le_integral => //=.
      by move=> z _; rewrite patchE expr0 mul1r; case: ifPn.
      apply: (measurable_restrict _ _ _ _).1 => //.
      apply: measurable_funTS; apply: measurableT_comp => //=.
      apply: (measurableT_comp (measurable_bernoulli2 _)) => //=.
      apply: measurable_fun_if => //=.
        by apply: measurable_and => //; exact: measurable_fun_ler.
      apply: measurable_funTS; apply: measurable_funM => //.
      by apply: measurable_fun_pow => //; exact: measurable_funB.
      by apply/measurableT_comp => //; exact: measurable_bernoulli_expn.
      move=> z _; rewrite patchE; case: ifPn => //.
         by rewrite inE/= in_itv /= => ->; rewrite expr0 mul1r.
      by move=> _; exact: abse_ge0.
    apply: eq_integral => z z01.
    rewrite inE/= in_itv/= in z01.
    by rewrite z01 expr0 mul1r.
  rewrite beta_nat_bernoulliE//= bernoulliE//=; last first.
    by rewrite div_beta_nat_norm_ge0// div_beta_nat_norm_le1.
  rewrite probability_setT.
  by congr (_ * _ + _ * _)%:E; rewrite /onem;
    rewrite /div_beta_nat_norm !beta_nat_normE/= !factE/=; field.
congr (_ * _ + _ * _)%E.
  by rewrite probability_setT -EFinD; congr EFin; lra.
by congr _%:E; rewrite /onem; lra.
Qed.

End casino34.

Section casino45.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope lang_scope.
Context (R : realType).
Local Notation mu := lebesgue_measure.

Lemma normalize_score_bernoulli g p q (p0 : (0 < p)%R) (q01 : (0 <= q <= 1)%R) :
  @execD R g _ [Normalize let "_" := Score {p}:R in
                Sample {exp_bernoulli [{q}:R]}] =
  execD [Normalize Sample {exp_bernoulli [{q}:R]}].
Proof.
apply: eq_execD.
rewrite !execD_normalize_pt/= !execP_letin !execP_score.
rewrite !execP_sample !execD_bernoulli !execD_real/=.
apply: funext=> x.
apply: eq_probability=> /= y.
rewrite !normalizeE/=.
rewrite !bernoulliE//=; [|lra..].
rewrite !diracT !mule1 -EFinD add_onemK onee_eq0/=.
rewrite !letin'E.
under eq_integral.
  move=> x0 _ /=.
  rewrite !bernoulliE//=; [|lra..].
  rewrite !diracT !mule1 -EFinD add_onemK.
  over.
rewrite !ge0_integral_mscale//= (ger0_norm (ltW p0))//.
rewrite integral_dirac// !diracT !indicT /= !mule1.
rewrite gt_eqF ?lte_fin//=.
rewrite integral_dirac//= diracT !mul1e !mulr1.
rewrite addrCA subrr addr0 invr1 mule1.
rewrite !bernoulliE//=; [|lra..].
by rewrite muleAC -EFinM divff// ?gt_eqF// mul1r EFinD.
Qed.

Lemma casino45 : execD (@casino4 R) = execD (@casino5 R).
Proof. by rewrite normalize_score_bernoulli//; lra. Qed.

End casino45.

Lemma casino {R : realType} : projT1 (execD (@casino0 R)) tt = projT1 (execD (@casino5 R)) tt.
Proof.
by rewrite casino01 casino12 casino22' casino23 casino34 casino45.
Qed.
