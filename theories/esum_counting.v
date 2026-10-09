From HB Require Import structures.
From mathcomp Require Import boot order algebra.
From mathcomp.classical Require Import boolp classical_sets mathcomp_extra functions.
From mathcomp Require Import xfinmap constructive_ereal reals discrete.
From mathcomp Require Import realseq realsum.
From mathcomp Require Import topology esum sequences normedtype ereal.
From mathcomp Require Import cardinality fsbigop.
From mathcomp Require Import numfun measurable_realfun.
From mathcomp Require Import measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import random_variable radon_nikodym.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.  (* remove this line when requiring MathComp >= 2.6 *)

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Notation simpm := Monoid.simpm.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Import HBNNSimple.
Import MeasurableR.

(* NB: PR 2123 already merged *)
Lemma esum_bigcup_set {R : realType} (T1 T2 : choiceType) (K : set T1)
    (J : T1 -> set T2) (a : T2 -> \bar R) :
    trivIset setT J -> (forall x, (0 <= a x)%E) ->
  (\esum_(i in \bigcup_(k in K) J k) a i =
   \esum_(k in K) \esum_(j in J k) a j)%E.
Proof.
move=> tJ a0; rewrite esum_esum//; apply: reindex_esum => //; split.
- by move=> [/= i j] [Ki Jij]; exists i.
- move=> [/= i1 j1] [/= i2 j2] /set_mem/= [Ki1 Jij1] /set_mem/= [Ki2 Jij2] /= j12.
  have iE : i1 = i2.
    by apply: (tJ i1 i2) => //; exists j1; split=> //; rewrite j12.
  by rewrite iE j12.
- by move=> j [i Ki Jij]/=; exists (i, j).
Qed.

(* TODO: PR. *)
Definition induced_measure {d} {T : measurableType d} {R : realType}
    (mu : {measure set T -> \bar R}) (f : T -> R)
    (mf : measurable_fun [set: T] f)
    (f0 : forall x, (0 <= f x)%R) :=
  fun A => (\int[mu]_(t in A) (f t)%:E)%E.

Section induced_measure.
Context {d} {T : measurableType d} {R : realType}
  (mu : {measure set T -> \bar R}) (f : T -> R).

Hypotheses (mf : measurable_fun [set: T] f)
  (f0 : forall x, (0 <= f x)%R).

Local Notation m' := (induced_measure mu mf f0).

Let m'0 : m' set0 = 0.
Proof. exact: integral_set0. Qed.

Let m'_ge0 A : (0 <= m' A)%E.
Proof. by apply: integral_ge0 => t At; rewrite lee_fin. Qed.

Let m'_semi_sigma_additive : semi_sigma_additive m'.
Proof.
by apply: semi_sigma_additive_nng_induced => //; exact/measurable_EFinP.
Qed.

HB.instance Definition _ := isMeasure.Build d T R m'
  m'0 m'_ge0 m'_semi_sigma_additive.

End induced_measure.

Section integral_induced_measure.
Context {d} {T : measurableType d} {R : realType}
  (mu : {measure set T -> \bar R}) (h : T -> R).

Hypothesis mh : measurable_fun [set: T] h.
Hypothesis h0 : forall x, (0 <= h x)%R.

Let mu' : {measure set _ -> \bar _} := induced_measure mu mh h0.

Lemma integral_induced_measure_indic (A : set T) : measurable A ->
  \int[mu]_x ((\1_A x)%:E * (h x)%:E) = mu' A.
Proof.
move=> mA; rewrite [RHS]integral_mkcond; apply: eq_integral => x _.
rewrite patchE indicE; case: ifP => _; first by rewrite mul1e.
by rewrite mul0e.
Qed.

Lemma integral_induced_measureMindic (r : R) (A : set T) : measurable A ->
  (0 <= r)%R ->
  \int[mu]_x (r%:E * (\1_A x)%:E * (h x)%:E) = r%:E * mu' A.
Proof.
move=> mA r0.
under eq_integral do rewrite -muleA.
rewrite ge0_integralZl//=.
- apply: emeasurable_funM => //; by apply /measurable_EFinP.
- by move=> x _; apply: mule_ge0; rewrite ?lee_fin.
- by rewrite integral_induced_measure_indic.
Qed.

Lemma sintegral_induced_measure (g : {nnsfun T >-> R}) :
  sintegral mu' g = \int[mu]_x ((g x)%:E * (h x)%:E).
Proof.
transitivity (\sum_(r \in range g)
    \int[mu]_x (r%:E * (\1_(g @^-1` [set r]) x)%:E * (h x)%:E)).
  rewrite sintegralE; apply: eq_fsbigr => r /set_mem[x0 _ <-].
  by rewrite integral_induced_measureMindic.
transitivity (\int[mu]_x (\sum_(r \in range g)
    ((r * (\1_(g @^-1` [set r]) x))%:E * (h x)%:E))).
  rewrite ge0_integral_fsum//=.
  - move=> r.
    under eq_fun do rewrite EFinM -muleA.
    apply: measurable_funeM.
    by apply: emeasurable_funM => //; exact/measurable_EFinP.
  - move=> r x _; have [r0|r0] := leP 0%R r.
      by rewrite mule_ge0// lee_fin// mulr_ge0.
    by rewrite preimage_nnfun0// indic0/= mulr0 mul0e.
apply: eq_integral => x _.
rewrite -ge0_mule_fsuml; first by move=> _ [t _ <-]; rewrite lee_fin mulr_ge0.
by rewrite fsumEFin// [in RHS](fimfunE g).
Qed.

Lemma integral_induced_measure (f : T -> \bar R) :
    measurable_fun [set: T] f -> (forall x, 0 <= f x) ->
  \int[mu']_x f x = \int[mu]_x (f x * (h x)%:E).
Proof.
move=> mf f0.
pose g := nnsfun_approx measurableT mf.
pose gE := fun n => EFin \o g n.
have mgE n : measurable_fun [set: T] (EFin \o g n) by exact/measurable_EFinP.
have gE_ge0 n x : 0 <= gE n x by rewrite lee_fin.
have nd_gE x : {homo gE ^~ x : n p / (n <= p)%O >-> n <= p}.
  by move=> *; exact/lefP/nd_nnsfun_approx.
transitivity (limn (fun n => \int[mu']_x gE n x)).
  rewrite -monotone_convergence//; apply: eq_integral => t _.
  by apply/esym/cvg_lim => //; exact: cvg_nnsfun_approx.
transitivity (limn (fun n => \int[mu]_x (gE n x * (h x)%:E))).
  apply: congr_lim; apply/funext => n.
  by rewrite integralT_nnsfun sintegral_induced_measure.
have mgEh n : measurable_fun [set: T] (fun x => gE n x * (h x)%:E).
  by apply: emeasurable_funM => //; exact/measurable_EFinP.
have gEh_ge0 n x : 0 <= gE n x * (h x)%:E by rewrite mule_ge0// lee_fin.
have nd_gEh x :
    {homo (fun n => gE n x * (h x)%:E) : n p / (n <= p)%O >-> n <= p}.
  by move=> p q pq; rewrite lee_wpmul2r ?lee_fin//; exact: nd_gE.
rewrite -monotone_convergence//.
apply: eq_integral => x _.
apply: cvg_lim => //; apply: cvgeZr => //.
exact: cvg_nnsfun_approx.
Qed.

End integral_induced_measure.

(* -------------------------------------------------------------------- *)
Definition discrete_measurable_space (T : choiceType) : Type := T.

HB.instance Definition _ (T : choiceType) :=
  Choice.on (discrete_measurable_space T).

HB.instance Definition _ (T : choiceType) := @isMeasurable.Build
  default_measure_display
  (discrete_measurable_space T) discrete_measurable discrete_measurable0
  discrete_measurableC discrete_measurableU.

Lemma esum_setT_discrete {R : realType} (T : choiceType) (f : T -> \bar R) :
  (\esum_(x in [set: discrete_measurable_space T]) f x
     = \esum_(x in [set: T]) f x)%E.
Proof.
by apply: (@reindex_esum R T (discrete_measurable_space T)
          [set: T] [set: discrete_measurable_space T] id f); split.
Qed.

(* -------------------------------------------------------------------- *)
Section Counting.
Context d (T : measurableType d) (R : realType).
Hypothesis msingl : forall i : T, measurable [set i].

Lemma counting_esum_cst (c : R) (A : set T) : (0 <= c)%R ->
  (c%:E * @counting T R A = \esum_(x in A) c%:E)%E.
Proof.
move=> c0.
have [-> | c_neq] := eqVneq c 0%R.
  by rewrite mul0e; apply/esym/esum1.
have c_pos : (0 < c)%R by rewrite lt_def c_neq.
have [finA|infA] := pselect (finite_set A).
+ rewrite /counting (asboolT finA).
  rewrite esum_fset// fsbig_finite//=.
  rewrite sumEFin big_const_seq count_predT iter_addr addr0.
  by rewrite -EFinM mulr_natr.
+ rewrite /counting asboolF//=.
  rewrite mulry gtr0_sg// mul1e.
  apply/esym/eqyP => r r0.
  have [B BA Brc] := infinite_set_fset (Num.Def.truncn (c^-1 * r)).+1 infA.
  apply: esum_ge => // ; exists [set` B].
    by split=> //; apply/subsetP => x; rewrite inE => /BA.
  rewrite fsbig_finite//= set_fsetK sumEFin big_const_seq count_predT.
  rewrite iter_addr addr0 -mulr_natr lee_fin -ler_pdivrMl//.
  apply: (@le_trans _ _ (((Num.Def.truncn (c^-1 * r)).+1)%:R)).
    exact: ltW (truncnS_gt _).
  rewrite ler_nat.
  exact: Brc.
Qed.

Lemma sintegral_counting_esum (h : {nnsfun T >-> R}) :
  (sintegral (@counting T R) h = \esum_(x in [set: T]) (h x)%:E)%E.
Proof.
rewrite sintegralE //=.
transitivity (\sum_(c \in range h)
                \esum_(x in (h @^-1` [set c] : set T)) (h x)%:E)%E.
+ apply: eq_fsbigr => c /set_mem/= -[x _ <-{c}].
  rewrite counting_esum_cst//.
  by apply: (eq_esum _ (fun=> (h x)%:E)) => x0 ->.
+ rewrite -esum_fset//.
  + by move=> ? _; apply: esum_ge0 => ? _; rewrite lee_fin.
  rewrite -esum_bigcup_set.
  + exact: trivIset_preimage1.
  + by move=> ?; rewrite lee_fin.
  + suff -> : \bigcup_(c in range h) h @^-1` [set c] = [set: T] by [].
    apply/seteqP; split => [//|y _].
    by exists (h y); [exists y|].
Qed.

Lemma measurable_fin_set (A : set T) :
  finite_set A -> measurable A.
Proof.
move=> finA; rewrite -[A]bigcup_id.
by apply: fin_bigcup_measurable => // i _; exact: msingl.
Qed.

Lemma integral_set1 f i :
  (\int[@counting T R]_(x in [set i]) f x = f i)%E.
Proof.
transitivity (\int[@counting T R]_(x in [set i]) cst (f i) x)%E.
+ by apply: eq_integral => x /set_mem/= ->.
rewrite (integral_cst _ (msingl i)) -[X in _ = X](mule1 (f i)).
congr (f i * _)%E => /=.
rewrite /counting (asboolT (finite_set1 i)).
by rewrite fset_set1 cardfs1.
Qed.

Lemma integral_sum f :
  measurable_fun [set: T] f ->
  forall A : set T, finite_set A ->
  (forall x, (0 <= f x)%E) ->
  (\int[@counting T R]_(x in A) f x = \sum_(x \in A) f x)%E.
Proof.
move=> mf A finA f0.
rewrite fsbig_finite//=.
rewrite (eq_bigr (fun i => (\int[@counting T R]_(x in [set i]) f x)%E)).
+ by move => ??;rewrite integral_set1.
rewrite -ge0_integral_bigsetU //=.
- exact: fset_uniq.
- by move=> i j _ _ [x [-> ->]].
- exact: measurable_funTS.
- by rewrite (@bigsetU_fset_set _ _ _ _ finA) bigcup_id.
Qed.

Lemma integral_counting_esum (f : T -> \bar R) :
  measurable_fun [set: T] f ->
  (forall x, (0 <= f x)%E) ->
  (\int[@counting T R]_x f x = \esum_(x in [set: T]) f x)%E.
Proof.
move=> mf f0 ; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite ge0_integralTE //=.
  apply: ge_ereal_sup => /= _ [h /= hf] <-.
  rewrite sintegral_counting_esum.
  apply: le_esum => x _; exact: hf.
- rewrite ge0_esum //; apply: ge_ereal_sup => /= _ [A [finA _] <-].
  rewrite -integral_sum//.
  apply: ge0_subset_integral => //.
  exact : (measurable_fin_set finA).
Qed.

Lemma integral_counting_esum_set (A : set T) (f : T -> \bar R) :
  measurable A ->
  measurable_fun [set: T] f ->
  (forall x, (0 <= f x)%E) ->
  (\int[@counting T R]_(x in A) f x = \esum_(x in A) f x)%E.
Proof.
move=> mA mf f0; rewrite integral_mkcond integral_counting_esum.
- by apply/(measurable_restrict _ mA measurableT); rewrite setTI; exact: measurable_funTS.
- by move=> x; rewrite patchE; case: ifP.
- rewrite [RHS]esum_mkcond; apply: eq_esum => x _.
  by rewrite patchE.
Qed.

End Counting.
