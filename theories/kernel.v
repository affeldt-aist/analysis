(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

HB.mixin Record isKernel (d d' : measure_display)
    (R : realType) (X : measurableType d) (Y : measurableType d')
    (k : X -> {measure set Y -> \bar R}) := {
  kernelP : forall U, measurable_fun setT (k ^~ U)
}.

#[short(type=kernel)]
HB.structure Definition Kernel (d d' : measure_display)
    (R : realType) (X : measurableType d) (Y : measurableType d') :=
  {k & isKernel d d' R X Y k}.
Notation "X ^^> Y" := (kernel _ X Y) (at level 42).

HB.mixin Record isProbabilityKernel (d d' : measure_display)
    (R : realType) (X : measurableType d) (Y : measurableType d')
    (k : X -> {measure set Y -> \bar R})
    of isKernel d d' R X Y k := {
  prob_kernelP : forall x : X, k x [set: Y] = 1
}.

HB.structure Definition ProbKernel (d d' : measure_display)
    (R : realType) (X : measurableType d) (Y : measurableType d') :=
  {k & isProbabilityKernel d d' R X Y k }.
(* TODO: warning *)

Section sum_of_kernels.
Variables (d d' : measure_display) (R : realType).
Variables (X : measurableType d) (Y : measurableType d').
Variable k : (kernel R X Y)^nat.

Definition sum_of_kernels : X -> {measure set Y -> \bar R} :=
  fun x => [the measure _ _ of mseries (k ^~ x) 0].

Lemma kernel_measurable_fun_sum_of_kernels (U : set Y) :
  measurable_fun setT (sum_of_kernels ^~ U).
Proof.
rewrite /sum_of_kernels /= /mseries.
rewrite [X in measurable_fun _ X](_ : _ =
  (fun x => elim_sup (fun n => \sum_(0 <= i < n) k i x U))); last first.
  apply/funext => x; rewrite -lim_mkord is_cvg_elim_supE.
    by rewrite -lim_mkord.
  exact: is_cvg_nneseries.
apply: measurable_fun_elim_sup => n.
by apply: emeasurable_fun_sum => *; exact/kernelP.
Qed.

HB.instance Definition _ :=
  isKernel.Build d d' R X Y sum_of_kernels
    kernel_measurable_fun_sum_of_kernels.

End sum_of_kernels.

Lemma proposition1 (d d' : measure_display)
  (R : realType) (X : measurableType d) (Y : measurableType d')
  (k : (X ^^> Y)^nat) (f : Y -> \bar R) x :
  (forall y, 0 <= f y) ->
  measurable_fun setT f ->
  \int[sum_of_kernels k x]_y (f y) = \sum_(i <oo) \int[k i x]_y (f y).
Proof.
by move=> f0 mf; rewrite /sum_of_kernels/= ge0_integral_measure_series.
Qed.

HB.mixin Record isFiniteKernel (d d' : measure_display)
    (R : realType) (X : measurableType d) (Y : measurableType d')
    (k : X -> {measure set Y -> \bar R})
    of isKernel d d' R X Y k := {
  finite_kernelP : exists r : {posnum R}, forall x, k x [set: Y] < r%:num%:E
}.

#[short(type=finite_kernel)]
HB.structure Definition FiniteKernel (d d' : measure_display)
    (R : realType) (X : measurableType d) (Y : measurableType d') :=
  {k & isFiniteKernel d d' R X Y k }.

HB.mixin Record isSFiniteKernel (d d' : measure_display)
    (R : realType) (X : measurableType d) (Y : measurableType d')
    (k : X -> {measure set Y -> \bar R})
    of isKernel d d' R X Y k := {
  sfinite_kernelP : exists k_ : (finite_kernel R X Y)^nat, forall x U,
    k x U = \sum_(i <oo) k_ i x U
    (* k x = [the measure _ _ of mseries (k_ ^~ x) 0] *)
}.

#[short(type=sfinite_kernel)]
HB.structure Definition SFiniteKernel (d d' : measure_display)
    (R : realType) (X : measurableType d) (Y : measurableType d') :=
  {k & isSFiniteKernel d d' R X Y k}.

Section star_is_kernel.
Variables (d d' : _) (R : realType) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType (d, d').-prod).
Variable k : kernel R [the measurableType _ of (X * Y)%type] Z.
Variable l : kernel R X Y.

Definition star : X -> set Z -> \bar R := fun x U => \int[l x]_y k (x, y) U.

Let star0 (x : X) : star x set0 = 0.
Proof.
by rewrite /star (eq_integral (cst 0)) ?integral0// => y _; rewrite measure0.
Qed.

Let star_ge0 (x : X) (U : set Z) : 0 <= star x U.
Proof. by apply: integral_ge0 => y _; exact: measure_ge0. Qed.

Let star_sigma_additive (x : X) : semi_sigma_additive (star x).
Proof.
move=> U mU tU mUU.
rewrite [X in _ --> X](_ : _ =
  \int[l x]_y (\sum_(n <oo) k (x, y) (U n)))%E; last first.
  apply: eq_integral => V _.
  by apply/esym/cvg_lim => //; exact/measure_semi_sigma_additive.
apply/cvg_closeP; split.
  by apply: is_cvg_nneseries => n _; exact: integral_ge0.
rewrite closeE// integral_sum// => n.
move: (@kernelP _ _ R _ _ k (U n)) => /measurable_fun_prod1.
exact.
Qed.

HB.instance Definition _ (x : X) :=
  isMeasure.Build _ R _ (star x) (star0 x) (star_ge0 x) (@star_sigma_additive x).

Definition mstar (x : X) := [the measure _ _ of star x].

End star_is_kernel.

Lemma pollard_hodai (d d' : measure_display)
  (R : realType)
  (X : measurableType d)
  (Y : measurableType d')
  (k : (X * Y)%type -> \bar R)
  (mk : measurable_fun setT k)
  (l : finite_kernel R X Y) :
measurable_fun [set: X] (fun x : X => \int[l x]_y k (x, y)).
Proof.
have k0 : (forall t : X * Y, True -> 0 <= k t).
  admit.
have [k_ [ndk_ k_k]] := @approximation _ _ _ _ measurableT k mk k0.
simpl in *.
rewrite (_ : (fun x => \int[l x]_y k (x, y)) =
             (fun x => elim_sup (fun n => \int[l x]_y (k_ n (x, y))%:E))); last first.
  apply/funeqP => x.
  transitivity (lim (fun n : nat => \int[l x]_y (k_ n (x, y))%:E)); last first.
    admit.
  rewrite -monotone_convergence//.
  - admit.
  - move=> n.
    apply/EFin_measurable_fun.
    admit.
  - admit.
  - move=> y _ m n mn.
    rewrite lee_fin.
    have := ndk_ _ _ mn.
    admit.
apply: measurable_fun_elim_sup => n.
rewrite (_ :
  (fun x : X => \int[l x]_y (k_ n (x, y))%:E) =
  (fun x : X => sintegral (l x) (fun y => k_ n (x, y)))); last first.
  apply/funext => x.
  Fail have := @integralT_nnsfun _ _ _ (l x) (fun y : Y => k_ n (x, y)).
  admit.
pose f x := (fun y : Y => k_ n (x, y)).
rewrite (_ : (fun x : X => sintegral (l x) (f x)) =
  (fun x : X =>
\sum_(x' \in range (f x)) (x'%:E * (l x) (f x @^-1` [set x']))
)); last first.
  apply/funext => x'.
  by rewrite sintegralE.
have [r lr] := @finite_kernelP _ _ _ _ _ l.
have rfx : {fset R}.
  admit.
  rewrite (_ :
  (fun x : X => \sum_(x' \in range (f x)) x'%:E * l x (f x @^-1` [set x'])) =
  (fun x : X => \sum_(x' <- rfx) x'%:E * l x (f x @^-1` [set x']))
); last first.
  admit.
apply: emeasurable_fun_sum => m.
suff: measurable_fun [set: X] (fun x : X => l x (f x @^-1` [set m])).
  admit.
have := @kernelP _ _ _ _ _ l.
(* TODO: use finiteness *)
Admitted.

Section star_is_kernel2.
Variables (d d' : _) (R : realType) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType (d, d').-prod).
Variable k : finite_kernel R [the measurableType _ of (X * Y)%type] Z.
Variable l : finite_kernel R X Y.

Lemma star_measurable U : measurable_fun setT (star k l ^~ U).
Proof.
(* k is a bounded measurable function *)
(* l is a finite kernel *)
rewrite /star.
apply (@pollard_hodai _ _ R X Y (fun xy => k xy U)).
apply (@kernelP _ _ R [the measurableType (d, d').-prod of (X * Y)%type] Z k U).
Qed.

HB.instance Definition _ :=
  isKernel.Build _ _ R X Z (mstar k l) star_measurable.

End star_is_kernel2.

Section star_is_finite_kernel.
Variables (d d' : _) (R : realType) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType (d, d').-prod).
Variable k : finite_kernel R [the measurableType _ of (X * Y)%type] Z.
Variable l : finite_kernel R X Y.

Lemma star_finite : exists r : {posnum R}, forall x, star k l x [set: Z] < r%:num%:E.
Proof.
have [r hr] := @finite_kernelP _ _ _ _ _ k.
have [s hs] := @finite_kernelP _ _ _ _ _ l.
exists (PosNum [gt0 of (r%:num * s%:num)%R]) => x.
rewrite /star.
apply: (@le_lt_trans _ _ (\int[l x]__ r%:num%:E)).
  apply ge0_le_integral => //.
  - have := @kernelP _ _ _ _ _ k setT.
    exact/measurable_fun_prod1.
  - exact/measurable_fun_cst.
  - by move=> y _; apply/ltW/hr.
by rewrite integral_cst//= EFinM lte_pmul2l.
Qed.

HB.instance Definition _ :=
  isFiniteKernel.Build _ _ R X Z (mstar k l) star_finite.

End star_is_finite_kernel.

Section star_is_sfinite_kernel.
Variables (d d' : _) (R : realType) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType (d, d').-prod).
Variable k : sfinite_kernel R [the measurableType _ of (X * Y)%type] Z.
Variable l : sfinite_kernel R X Y.

Lemma star_sfinite : exists k_ : (finite_kernel R X Z)^nat, forall x U,
  star k l x U = \sum_(i <oo) k_ i x U.
Proof.
have [k_ hk_] := @sfinite_kernelP _ _ _ _ _ k.
have [l_ hl_] := @sfinite_kernelP _ _ _ _ _ l.
pose K := [the kernel _ _ _ of sum_of_kernels k_].
pose L := [the kernel _ _ _ of sum_of_kernels l_].
have H1 x U : star k l x U = star K L x U.
  rewrite /star /L /K /=.
  have -> : l x = [the measure _ _ of mseries (fun x0 : nat => l_ x0 x) 0].
    apply/eq_measure/funeqP => V.
    by rewrite hl_.
  apply eq_integral => y _.
  suff: k (x, y) = [the measure _ _ of mseries (fun x0 : nat => k_ x0 (x, y)) 0].
    by move=> ->.
  apply/eq_measure/funeqP => V.
  by rewrite hk_.
have H2 x U : star K L x U =
  \int[mseries (l_ ^~ x) 0]_y (\sum_(i <oo) k_ i (x, y) U).
  rewrite /star /L /=.
  by apply eq_integral => y _.
have H3 x U : \int[mseries (l_ ^~ x) 0]_y (\sum_(i <oo) k_ i (x, y) U) =
   \sum_(i <oo) \int[mseries (l_ ^~ x) 0]_y (k_ i (x, y) U).
   rewrite integral_sum//= => n.
   have := @kernelP _ _ _ _ _ (k_ n) U.
   by move/measurable_fun_prod1; exact.
have H4 x U : \sum_(i <oo) \int[mseries (l_ ^~ x) 0]_y (k_ i (x, y) U) =
  \sum_(i <oo) \sum_(j <oo) \int[l_ j x]_y k_ i (x, y) U.
  apply: eq_nneseries => i _.
  rewrite proposition1//.
   have := @kernelP _ _ _ _ _ (k_ i) U.
   by move/measurable_fun_prod1; exact.
have H5 x U : \sum_(i <oo) \sum_(j <oo) \int[l_ j x]_y k_ i (x, y) U =
  \sum_(i <oo) \sum_(j <oo) star (k_ i) (l_ j) x U.
  apply eq_nneseries => i _.
  by apply eq_nneseries => j _.
suff: exists k_0 : (finite_kernel R X Z) ^nat,
    forall x U, \sum_(i <oo) \sum_(j <oo) star (k_ i) (l_ j) x U = \sum_(i <oo) k_0 i x U.
  move=> [kl_ hkl_]; exists kl_ => x U.
  by rewrite H1 H2 H3 H4 H5 hkl_.
(*pose KL_ : (finite_kernel R X Z) ^nat := fun i =>
  [the finite_kernel _ _ _ of sum_of_kernels
    (fun j => [the finite_kernel _ _ _ of mstar (k_ i) (l_ j)])].
by exists KL_ => x U; apply eq_nneseries => i _.*)
Admitted.

Fail HB.instance Definition _ :=
  isSFiniteKernel.Build _ _ R X Z (mstar k l) star_sfinite.

End star_is_sfinite_kernel.

Lemma lemma3 d d' (R : realType) (X : measurableType d)
    (Y : measurableType d') (Z : measurableType (d, d').-prod)
    (k : sfinite_kernel R [the measurableType _ of (X * Y)%type] Z)
    (l : sfinite_kernel R X Y) : forall x f, measurable_fun setT f ->
  \int[star k l x]_z f z = \int[l x]_y (\int[k (x, y)]_z f z).
Proof.
move=> x f mf.
have [k_ hk_] := @sfinite_kernelP _ _ _ _ _ k.
have [l_ hl_] := @sfinite_kernelP _ _ _ _ _ l.
transitivity (\int[mseries (fun i => [the measure _ _ of mseries (fun j => mstar (k_ i) (l_ j) x) 0]) 0]_z f z).
  admit.
rewrite ge0_integral_measure_series//; last admit.
simpl.
(* TODO *)
Admitted.
