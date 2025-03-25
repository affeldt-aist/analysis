From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import rat.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop.
From mathcomp Require Import interval_inference reals ereal topology normedtype.
From mathcomp Require Import sequences esum measure lebesgue_measure numfun.
From mathcomp Require Import lebesgue_integral exp kernel trigo prob_lang.
From mathcomp Require Import realfun charge probability derive ftc.
From mathcomp Require Import gauss_integral.

(**md**************************************************************************)
(* # Semantics of a probabilistic programming language using s-finite kernels *)
(*                                                                            *)
(* First example of Section 4.1 in [Equation (10), Staton, ESOP 2017].        *)
(* Another example from Section 4.2 in [Equation (13), Staton, ESOP 2017].    *)
(* (The latter is wip.)                                                       *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.ExtraDef Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section gauss.
Variable R : realType.
Local Open Scope ring_scope.

Definition gauss_pdf := @normal_pdf R 0 1.

(* TODO: move to probability.v *)
Lemma normal_pdf_gt0 m s x : 0 < s -> 0 < normal_pdf m s x :> R.
Proof.
move=> s0; rewrite /normal_pdf gt_eqF// mulr_gt0 ?expR_gt0// invr_gt0.
by rewrite sqrtr_gt0 pmulrn_rgt0// mulr_gt0 ?pi_gt0// exprn_gt0.
Qed.

Lemma gauss_pdf_gt0 x : 0 < gauss_pdf x.
Proof. exact: normal_pdf_gt0. Qed.

Definition gauss_prob := @normal_prob R 0 1.

HB.instance Definition _ := Probability.on gauss_prob.

Lemma gauss_prob_dominates : gauss_prob `<< lebesgue_measure.
Proof. exact: normal_prob_dominates. Qed.

Lemma continuous_gauss_pdf x : {for x, continuous gauss_pdf}.
Proof. exact: continuous_normal_pdf. Qed.

End gauss.

Section gauss_lebesgue.
Context d (T : measurableType d) (R : realType).
Notation mu := (@lebesgue_measure R).

Let f1 (x : g_sigma_algebraType (R.-ocitv.-measurable)) := (gauss_pdf x)^-1.

Let f1E (x : R) : f1 x = (Num.sqrt (pi *+ 2) * expR (- (- x ^+ 2 / 2)))%R.
Proof.
rewrite /f1 /gauss_pdf /normal_pdf oner_eq0 /normal_pdf0.
rewrite /normal_peak expr1n mul1r /normal_fun subr0 expr1n.
by rewrite invfM invrK -expRN.
Qed.

Let f1_gt0 (x : R) : (0 < f1 x)%R.
Proof. by rewrite f1E mulr_gt0 ?expR_gt0// sqrtr_gt0 mulrn_wgt0// pi_gt0. Qed.

Lemma measurable_fun_f1 : measurable_fun setT f1.
Proof.
apply: continuous_measurable_fun => x.
apply: (@continuousV _ _ (@gauss_pdf R)).
  by rewrite gt_eqF// gauss_pdf_gt0.
exact: continuous_gauss_pdf.
Qed.

Lemma integral_mgauss01 : forall U, measurable U ->
  \int[(@gauss_prob R)]_(y in U) (f1 y)%:E =
  \int[mu]_(x0 in U) (gauss_pdf x0 * f1 x0)%:E.
Proof.
move=> U mU.
under [in RHS]eq_integral do rewrite EFinM/= muleC.
rewrite /=.
rewrite -(@Radon_Nikodym_SigmaFinite.change_of_variables
    _ _ _ _ (@lebesgue_measure R))//=; last 3 first.
  exact: gauss_prob_dominates.
  by move=> /= x; rewrite lee_fin ltW.
  apply/measurable_EFinP.
  apply: measurable_funTS.
  exact: measurable_fun_f1.
apply: ae_eq_integral => //=.
- apply: emeasurable_funM => //.
    apply/measurable_funTS/measurableT_comp => //.
    exact: measurable_fun_f1.
  apply: (measurable_int mu).
  apply: (integrableS _ _ (@subsetT _ _)) => //=.
  apply: Radon_Nikodym_SigmaFinite.f_integrable => /=.
  exact: gauss_prob_dominates.
- apply: emeasurable_funM => //.
    apply/measurable_funTS/measurableT_comp => //.
    exact: measurable_fun_f1.
  apply/measurable_funTS/measurableT_comp => //.
  exact: measurable_normal_pdf.
- apply: ae_eq_mul2l => /=.
  rewrite /Radon_Nikodym_SigmaFinite.f/=.
  case: pselect => [gauss_prob_dom|]; last first.
    by move=> /(_ (@gauss_prob_dominates R)).
  case: cid => //= h [h1 h2 h3] gauss_probE.
  apply: integral_ae_eq => //=.
  + exact: integrableS h3.
  + apply/measurable_funTS/measurableT_comp => //.
    exact: measurable_normal_pdf.
  + by move=> E EU mE; rewrite -gauss_probE.
Qed.

Let mf1 : measurable_fun setT f1.
Proof.
apply: (measurable_comp (F := [set r : R | r != 0%R])) => //.
- exact: open_measurable.
- by move=> /= r [t _ <-]; rewrite gt_eqF// gauss_pdf_gt0.
- apply: open_continuous_measurable_fun => //.
  by apply/in_setP => x /= x0; exact: inv_continuous.
- exact: measurable_normal_pdf.
Qed.

Definition staton_lebesgue : R.-sfker T ~> _ :=
  letin (sample_cst (@gauss_prob R : pprobability _ _))
  (letin
    (score (measurableT_comp mf1 macc1of2))
    (ret macc1of3)).

Lemma staton_lebesgueE x U : measurable U ->
  staton_lebesgue x U = lebesgue_measure U.
Proof.
move=> mU; rewrite [in LHS]/staton_lebesgue/=.
rewrite [in LHS]letinE /=.
transitivity (\int[(@gauss_prob R)]_(y in U) (f1 y)%:E).
  rewrite -[in RHS](setTI U) integral_mkcondr/=.
  apply: eq_integral => //= r _.
  rewrite letinE/= ge0_integral_mscale//= ger0_norm//; last first.
    by rewrite invr_ge0// normal_pdf_ge0.
  rewrite integral_dirac// diracT mul1e/= diracE epatch_indic/=.
  by rewrite indicE.
rewrite integral_mgauss01//.
transitivity (\int[lebesgue_measure]_(x in U) (\1_U x)%:E).
  apply: eq_integral => /= y yU.
  by rewrite /f1 divrr ?indicE ?yU// unitfE gt_eqF// gauss_pdf_gt0.
by rewrite integral_indic//= setIid.
Qed.

End gauss_lebesgue.

Notation left_continuous f :=
  (forall x, f%function @ at_left x --> f%function x).

Lemma left_continuousW (R : numFieldType) (f : R -> R) :
  continuous f -> left_continuous f.
Proof. by move=> cf x; exact/cvg_at_left_filter/cf. Qed.

Section derivable_oy_continuous_bnd.
Context {R : realType}.

Lemma derivable_oy_continuous_bnd_within (f : R -> R^o) (x : R) :
  derivable_oy_continuous_bnd f x -> {within `[x, +oo[, continuous f}.
Proof.
move=> [/= df fx]; apply/subspace_continuousP => z /=.
rewrite in_itv/= andbT; rewrite le_eqVlt => /predU1P[<-{z}|xz].
  have := cvg_at_right_within fx; apply: cvg_trans; apply: cvg_app.
  by apply: within_subset => z/=; rewrite in_itv/= => /andP[].
apply: cvg_within_filter.
have := df z; rewrite in_itv/= andbT => /(_ xz) /derivable1_diffP.
exact/differentiable_continuous.
Qed.

End derivable_oy_continuous_bnd.

Section Gamma.
Context {R : realType}.

Let mu := @lebesgue_measure R.

Definition Gamma (a : R) : \bar R :=
  (\int[mu]_(x in `[0%R, +oo[) (x`^  (a - 1) * expR (- x))%:E)%E.

Let I n := \int[mu]_(x in `[0%R, +oo[) (x ^+ n * expR (- x))%:E.

End Gamma.

Definition Rfact {R : realType} (x : R) := Gamma (x + 1)%R.

Section poisson.
Variable R : realType.
Local Open Scope ring_scope.
Notation mu := (@lebesgue_measure R).
Hypothesis integral_poisson_density : forall k,
  (\int[mu]_x (@poisson_pdf R k x)%:E = 1%E)%E.

(* density function for poisson *)
Definition poisson1 := @poisson_pdf R 1%N.

Lemma poisson1_ge0 (x : R) : 0 <= poisson1 x.
Proof. exact: poisson_pdf_ge0. Qed.

Definition mpoisson1 (V : set R) : \bar R :=
  (\int[lebesgue_measure]_(x in V) (poisson1 x)%:E)%E.

Lemma measurable_fun_poisson1 : measurable_fun setT poisson1.
Proof. exact: measurable_poisson_pdf. Qed.

Let mpoisson10 : mpoisson1 set0 = 0%E.
Proof. by rewrite /mpoisson1 integral_set0. Qed.

Lemma mpoisson1_ge0 A : (0 <= mpoisson1 A)%E.
Proof.
apply: integral_ge0 => x Ax.
by rewrite lee_fin poisson1_ge0.
Qed.

Let mpoisson1_sigma_additive : semi_sigma_additive mpoisson1.
Proof.
move=> /= F mF tF mUF.
rewrite /mpoisson1/= integral_bigcup//=; last first.
  apply/integrableP; split.
    apply/measurable_EFinP.
    exact: measurable_funS (measurable_poisson_pdf _).
  rewrite (_ : (fun x => _) = (EFin \o poisson1)); last first.
    by apply/funext => x; rewrite gee0_abs// lee_fin poisson1_ge0//.
  apply: le_lt_trans.
    apply: (@ge0_subset_integral _ _ _ _ _ setT) => //=.
      by apply/measurable_EFinP; exact: measurable_poisson_pdf.
    by move=> ? _; rewrite lee_fin poisson1_ge0//.
  by rewrite /= integral_poisson_density// ltry.
apply: is_cvg_ereal_nneg_natsum_cond => n _ _.
by apply: integral_ge0 => /= x ?; rewrite lee_fin poisson1_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  mpoisson1 mpoisson10 mpoisson1_ge0 mpoisson1_sigma_additive.

Let mpoisson1_setT : mpoisson1 [set: _] = 1%E.
Proof. exact: integral_poisson_density. Qed.

HB.instance Definition _ := @Measure_isProbability.Build _ _ R
  mpoisson1 mpoisson1_setT.

Definition poisson' := [the probability _ _ of mpoisson1].

End poisson.

(* Staton's definition of the counting measure
   Staton ESOP 2017, Sect. 4.2, equation (13)  *)
Section staton_counting.
Context d (X : measurableType d).
Variable R : realType.
Notation mu := (@lebesgue_measure R).
Import Notations.
Hypothesis integral_poisson_density : forall k,
  (\int[mu]_x (@poisson_pdf R k x)%:E = 1%E)%E.

Let f1 x := (poisson1 (x : R)) ^-1.

Let mf1 : measurable_fun setT f1.
rewrite /f1 /poisson1 /poisson_pdf.
apply: (measurable_comp (F := [set r : R | r != 0%R])) => //.
- exact: open_measurable.
- move=> /= r [t ? <-].
  by case: ifPn => // t0; rewrite gt_eqF ?mulr_gt0 ?expR_gt0//= invrK ltr0n.
- apply: open_continuous_measurable_fun => //.
  by apply/in_setP => x /= x0; exact: inv_continuous.
- exact: measurable_poisson_pdf.
Qed.

Definition staton_counting : R.-sfker X ~> _ :=
  letin (sample_cst (@poisson' R integral_poisson_density : pprobability _ _))
    (letin
    (score (measurableT_comp mf1 macc1of2))
    (ret macc1of3)).

End staton_counting.

Section exponential_pdf.
Context {R : realType}.
Notation mu := lebesgue_measure.
Variable (mean : R).
Hypothesis mean0 : (0 < mean)%R.

Definition exponential_pdf' (x : R) := (mean^-1 * expR (- x / mean))%R.
Definition exponential_pdf := exponential_pdf' \_ `[0%R, +oo[.

Lemma exponential_pdf_ge0 (x : R) : (0 <= exponential_pdf x)%R.
Proof.
apply: restrict_ge0 => {}x _.
apply: mulr_ge0; last exact: expR_ge0.
by rewrite invr_ge0 ltW.
Qed.

Lemma continuous_exponential_pdf' : continuous exponential_pdf'.
Proof.
move=> x.
apply: (@continuousM _ R^o (fun=> mean^-1) (fun x0 => (expR (- x0 / mean)))).
  exact: cst_continuous.
apply: continuous_comp; last exact: continuous_expR.
apply: continuousM; last exact: cst_continuous.
exact: (@opp_continuous _ R^o).
Qed.

Lemma measurable_exponential_pdf : measurable_fun setT exponential_pdf.
Proof.
apply/measurable_restrict => //; apply: measurable_funTS.
apply: continuous_measurable_fun.
exact: continuous_exponential_pdf'.
Qed.

Lemma exponential_pdfE (x : R) : (0 <= x)%R ->
  exponential_pdf x = exponential_pdf' x.
Proof.
move=> x0; rewrite /exponential_pdf patchE ifT//.
by rewrite inE/= in_itv/= x0.
Qed.

Lemma in_continuous_exponential_pdf :
  {in `]0, +oo[%R, continuous exponential_pdf}.
Proof.
move=> x; rewrite in_itv/= andbT => x0.
apply/(@cvgrPdist_lt _ R^o) => e e0; near=> y.
rewrite 2?exponential_pdfE ?ltW//; last first.
  by near: y; exact: lt_nbhsr.
near: y; move: e e0; apply/(@cvgrPdist_lt _ R^o).
apply: continuous_comp => //.
exact: continuous_exponential_pdf'.
Unshelve. end_near. Qed.

Lemma within_continuous_exponential_pdf : {within [set` `[0, +oo[%R],
  continuous exponential_pdf}.
Proof.
apply/continuous_within_itvcyP; split.
  exact: in_continuous_exponential_pdf.
apply/(@cvgrPdist_le _ R^o) => e e0; near=> t.
rewrite 2?exponential_pdfE//.
near: t; move: e e0; apply/cvgrPdist_le.
apply: cvg_at_right_filter.
exact: continuous_exponential_pdf'.
Unshelve. end_near. Qed.

End exponential_pdf.

Definition exponential {R : realType} (m : R) :=
  fun V => (\int[lebesgue_measure]_(x in V) (exponential_pdf m x)%:E)%E.

Section exponential.
Context {R : realType}.
Local Open Scope ring_scope. (* remove in probability.v *)
Notation mu := lebesgue_measure.
Variable (mean : R).
Hypothesis mean0 : (0 < mean)%R.

Lemma derive1_exponential_in_itvcy :
 {in `]0, +oo[%R,
(fun x1 => - (expR : R^o -> R^o) (- x1 / mean))^`()%classic =1 exponential_pdf mean}.
Proof.
move=> z; rewrite in_itv/= andbT => z0.
rewrite derive1_comp// derive1N// derive1_id derive1_comp//.
rewrite derive1Mr// derive1N// derive1_id.
rewrite mulNr mul1r -2!mulrN opprK mulr1 mulrC derive1E.
have/funeqP -> := @derive_expR R.
by rewrite exponential_pdfE ?ltW.
Qed.

Let cexp : continuous (fun z : R^o => expR (- z / mean)).
Proof.
move=> z.
apply: continuous_comp; last exact: continuous_expR.
apply: continuousM; last exact: cst_continuous.
exact: opp_continuous.
Qed.

Lemma exponential_itv_0bnd (x : R) : 0 < x ->
  exponential mean `[0, x] = (1 - (expR (- x / mean))%:E)%E.
Proof.
move=> x0.
rewrite (_: 1 = - (- expR (- 0%R / mean))%:E)%E; last first.
  by rewrite mulNr mul0r oppr0 expR0 EFinN oppeK.
rewrite addeC.
apply: (@continuous_FTC2 _ _ (fun x => - (expR (- x / mean)))) => //.
    apply: (@continuous_subspaceW R^o _ _ [set` `[0, +oo[%R]).
      by apply: subset_itvl; rewrite bnd_simp.
    exact: within_continuous_exponential_pdf.
  split.
  - by move=> z _; apply: ex_derive.
  - by apply/cvg_at_right_filter; apply: cvgN; exact: cexp.
  - by apply/cvg_at_left_filter; apply: cvgN; exact: cexp.
move=> z; rewrite in_itv/= => /andP[z0 _].
apply: derive1_exponential_in_itvcy.
by rewrite in_itv/= andbT.
Qed.

Lemma integral_exponential_pdf :
  (\int[mu]_x (exponential_pdf mean x)%:E = 1)%E.
Proof.
have mEex : measurable_fun setT (EFin \o exponential_pdf mean).
  apply/measurable_EFinP.
  exact: measurable_exponential_pdf.
rewrite -(setUv `[0, +oo[%classic) ge0_integral_setU//; last 4 first.
- exact: measurableC.
- by rewrite setUv.
- by move=> x _; rewrite lee_fin exponential_pdf_ge0.
- exact/disj_setPCl.
rewrite [X in _ + X]integral0_eq ?adde0; last first.
  by move=> x x0; rewrite /exponential_pdf patchE ifF// memNset.
rewrite (@ge0_continuous_FTC2y _ _
  (fun x => - (expR (- x / mean))) _ 0)//; last 5 first.
- by move=> x _; apply: exponential_pdf_ge0.
- exact: within_continuous_exponential_pdf.
- rewrite -oppr0; apply: (@cvgN _ R^o).
  rewrite (_: (fun x => expR (- x / mean)) =
                    (fun z => expR (- z)) \o (fun z => z / mean)); last first.
    by apply: eq_fun => x; rewrite mulNr.
  apply: (@cvg_comp _ R^o _ _ _ _ (pinfty_nbhs R)); last exact: cvgr_expR.
  apply: gt0_cvgMly => //.
  by rewrite invr_gt0.
- apply: (@cvgN _ R^o).
  apply: cvg_at_right_filter.
  exact: cexp.
- exact: derive1_exponential_in_itvcy.
by rewrite EFinN oppeK add0e oppr0 mul0r expR0.
Qed.

Lemma integrable_exponential :
  mu.-integrable setT (EFin \o (exponential_pdf mean)).
Proof.
have mEex : measurable_fun setT (EFin \o exponential_pdf mean).
  by apply/measurable_EFinP; exact: measurable_exponential_pdf.
apply/integrableP; split => //.
under eq_integral do rewrite /= ger0_norm ?exponential_pdf_ge0//.
by rewrite /= integral_exponential_pdf ltry.
Qed.

Local Notation exponential := (exponential mean).

Let exponential0 : exponential set0 = 0%E.
Proof. by rewrite /exponential integral_set0. Qed.

Let exponential_ge0 A : (0 <= exponential A)%E.
Proof.
rewrite /exponential integral_ge0//= => x _.
by rewrite lee_fin exponential_pdf_ge0.
Qed.

Let exponential_sigma_additive : semi_sigma_additive exponential.
Proof.
move=> /= F mF tF mUF; rewrite /exponential; apply: cvg_toP.
  apply: ereal_nondecreasing_is_cvgn => m n mn.
  apply: lee_sum_nneg_natr => // k _ _; apply: integral_ge0 => /= x Fkx.
  by rewrite lee_fin; apply: exponential_pdf_ge0.
rewrite ge0_integral_bigcup//=.
- apply/measurable_funTS/measurableT_comp => //.
  exact: measurable_exponential_pdf.
- by move=> x _; rewrite lee_fin exponential_pdf_ge0.
Qed.

HB.instance Definition _ := isMeasure.Build _ _ _
  exponential exponential0 exponential_ge0 exponential_sigma_additive.

Let exponential_setT : exponential [set: _] = 1%E.
Proof. by rewrite /exponential integral_exponential_pdf. Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ R exponential exponential_setT.

End exponential.
