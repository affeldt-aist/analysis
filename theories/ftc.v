(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import finmap fingroup perm rat.
 Require Import boolp reals ereal classical_sets signed topology numfun.
Require Import mathcomp_extra functions normedtype.
From HB Require Import structures.
Require Import sequences esum measure fsbigop cardinality real_interval.
Require Import realfun.
Require Import lebesgue_measure lebesgue_integral smeasure radon_nikodym.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* TODO: move *)
Notation right_continuous f :=
  (forall x, f%function @ at_right x --> f%function x).

Lemma right_continuousW (R : numFieldType) (f : R -> R) :
  continuous f -> right_continuous f.
Admitted.

HB.mixin Record isCumulative (R : numFieldType) (f : R -> R) := {
  cumulative_is_nondecreasing : {homo f : x y / x <= y} ;
  cumulative_is_right_continuous : right_continuous f }.

#[short(type=cumulative)]
HB.structure Definition Cumulative (R : numFieldType) :=
  { f of isCumulative R f }.

Arguments cumulative_is_nondecreasing {R} _.
Arguments cumulative_is_right_continuous {R} _.

Lemma nondecreasing_right_continuousP (R : numFieldType) (a : R) (e : R)
    (f : cumulative R) :
  e > 0 -> exists d : {posnum R}, f (a + d%:num) <= f a + e.
Admitted.

Section id_is_cumulative.
Variable R : realType.

Let id_nd : {homo @idfun R : x y / x <= y}.
Admitted.

Let id_rc : right_continuous (@idfun R).
Admitted.

HB.instance Definition _ := isCumulative.Build R idfun id_nd id_rc.
End id_is_cumulative.

(* TODO: move and use in lebesgue_measure.v? *)
Lemma le_inf (R : realType) (S1 S2 : set R) :
  -%R @` S2 `<=` down (-%R @` S1) -> nonempty S2 -> has_inf S1
    -> (inf S1 <= inf S2)%R.
Admitted.

Definition EFinf {R : numDomainType} (f : R -> R) : \bar R -> \bar R :=
  fun x => if x is r%:E then (f r)%:E else x.

Lemma nondecreasing_EFinf (R : realDomainType) (f : R -> R) :
  {homo f : x y / (x <= y)%R} -> {homo EFinf f : x y / (x <= y)%E}.
Admitted.

Section hlength.
Local Open Scope ereal_scope.
Variables (R : realType) (f : R -> R).
Let g : \bar R -> \bar R := EFinf f.

Implicit Types i j : interval R.
Definition itvs : Type := R.

Definition hlength (A : set itvs) : \bar R := let i := Rhull A in g i.2 - g i.1.
Lemma hlength0 : hlength (set0 : set R) = 0.
Admitted.

Lemma hlength_singleton (r : R) : hlength `[r, r] = 0.
Proof.
Admitted.

Lemma hlength_itv i : hlength [set` i] = if i.2 > i.1 then g i.2 - g i.1 else 0.
Admitted.

Lemma hlength_setT : hlength setT = +oo%E :> \bar R.
Admitted.

Lemma hlength_finite_fin_num i : neitv i -> hlength [set` i] < +oo ->
  ((i.1 : \bar R) \is a fin_num) /\ ((i.2 : \bar R) \is a fin_num).
Admitted.

Lemma finite_hlengthE i : neitv i -> hlength [set` i] < +oo ->
  hlength [set` i] = (fine (g i.2))%:E - (fine (g i.1))%:E.
Admitted.

Lemma hlength_itv_bnd (a b : R) (x y : bool): (a <= b)%R ->
  hlength [set` Interval (BSide x a) (BSide y b)] = (f b - f a)%:E.
Admitted.

Lemma hlength_infty_bnd b r :
  hlength [set` Interval -oo%O (BSide b r)] = +oo :> \bar R.
Admitted.

Lemma hlength_bnd_infty b r :
  hlength [set` Interval (BSide b r) +oo%O] = +oo :> \bar R.
Admitted.

Lemma pinfty_hlength i : hlength [set` i] = +oo ->
  (exists s r, i = Interval -oo%O (BSide s r) \/ i = Interval (BSide s r) +oo%O)
  \/ i = `]-oo, +oo[.
Admitted.

Lemma hlength_ge0 (ndf : {homo f : x y / (x <= y)%R}) i : 0 <= hlength [set` i].
Admitted.

Local Hint Extern 0 (0%:E <= hlength _) => solve[apply: hlength_ge0] : core.

Lemma hlength_Rhull (A : set R) : hlength [set` Rhull A] = hlength A.
Admitted.

Lemma le_hlength_itv (ndf : {homo f : x y / (x <= y)%R}) i j :
  {subset i <= j} -> hlength [set` i] <= hlength [set` j].
Admitted.

Lemma le_hlength (ndf : {homo f : x y / (x <= y)%R}) :
  {homo hlength : A B / A `<=` B >-> A <= B}.
Admitted.

End hlength.
Arguments hlength {R}.
#[global] Hint Extern 0 (0%:E <= hlength _) => solve[apply: hlength_ge0] : core.

Section itv_semiRingOfSets.
Variable R : realType.
Implicit Types (I J K : set R).
Definition ocitv_type : Type := R.

Definition ocitv := [set `]x.1, x.2]%classic | x in [set: R * R]].

Lemma is_ocitv a b : ocitv `]a, b]%classic.
Admitted.
Hint Extern 0 (ocitv _) => solve [apply: is_ocitv] : core.

Lemma ocitv0 : ocitv set0.
Admitted.
Hint Resolve ocitv0 : core.

Lemma ocitvP X :
  ocitv X <-> X = set0 \/ exists2 x, x.1 < x.2 & X = `]x.1, x.2]%classic.
Admitted.

Lemma ocitvD : semi_setD_closed ocitv.
Admitted.

Lemma ocitvI : setI_closed ocitv.
Admitted.

Variable d : measure_display.

HB.instance Definition _ := @isSemiRingOfSets.Build d ocitv_type
  (Pointed.class R) ocitv ocitv0 ocitvI ocitvD.

Definition itvs_semiRingOfSets := [the semiRingOfSetsType d of ocitv_type].

Lemma hlength_semi_additive (f : R -> R) :
  semi_additive (hlength f : set ocitv_type -> _).
Admitted.

Hint Extern 0 (measurable _) => solve [apply: is_ocitv] : core.

Lemma hlength_sigma_finite (f : R -> R) :
  sigma_finite [set: ocitv_type] (hlength f).
Admitted.

Lemma hlength_ge0' (f : cumulative R) (I : set ocitv_type) :
  measurable I -> (0 <= hlength f I)%E.
Admitted.

HB.instance Definition _ (f : cumulative R) :=
  isAdditiveMeasure.Build _ R _ (hlength f : set ocitv_type -> _)
    (hlength_ge0' f) (hlength_semi_additive f).

Lemma hlength_content_sub_fsum (f : cumulative R) (D : {fset nat}) a0 b0
    (a b : nat -> R) : (forall i, i \in D -> a i <= b i) ->
    `]a0, b0] `<=` \big[setU/set0]_(i <- D) `] a i, b i]%classic ->
  f b0 - f a0 <= \sum_(i <- D) (f (b i) - f (a i)).
Admitted.

Lemma hlength_sigma_sub_additive (f : cumulative R) :
  sigma_sub_additive (hlength f : set ocitv_type -> _).
Admitted.

Let gitvs := [the measurableType _ of salgebraType ocitv].

Definition lebesgue_stieltjes_measure (f : cumulative R) :=
  Hahn_ext [the additive_measure _ _ of hlength f : set ocitv_type -> _ ].

End itv_semiRingOfSets.
Arguments lebesgue_stieltjes_measure {R}.

Section lebesgue_stieltjes_measure_itv.
Variables (d : measure_display) (R : realType) (f : cumulative R).

Let m := lebesgue_stieltjes_measure d f.

Let g : \bar R -> \bar R := EFinf f.

Let lebesgue_stieltjes_measure_itvoc (a b : R) :
  (m `]a, b] = hlength f `]a, b])%classic.
Admitted.

End lebesgue_stieltjes_measure_itv.

Example lebesgue_measure d (R : realType)
    : set [the measurableType (d.-measurable).-sigma of salgebraType (d.-measurable)] -> \bar R :=
  lebesgue_stieltjes_measure _ [the cumulative _ of @idfun R].

(* ----- End Stieltjes. -----*)

(* with ref to A Course in Functional Analysis and Measure Theory *)

Section with_ref.

(* 7.2 *)
Variable d : measure_display.
Variable R : realType.

(*
Definition Newton_Leibniz_fomula (f' f : R -> R) (a b : R) :
  (\int[@lebesgue_measure d R]_(x in `]a, b]) f' x)%:E= hlength f `]a, b].
*)

(* 7.2.1 *)



(* 7.2.3 *)

Section Variation.

Variable R :realType.

Definition variation (f : R -> R) (a b: R) :=
  sup [set x : R | exists (n : nat) (p : nat -> R),
     p 0%nat = a /\ p n = b /\ (forall k, p k < p k.+1)
        /\ x = \sum_(i < n) `| f (p i) - f (p i.+1) |].

(* bouded variation*)
Definition is_BV f a b := ((variation f a b)%:E < +oo)%E.

Lemma BV_nondecreasing : forall a b f, is_BV f a b ->
  {homo (fun x => variation f a x) : x y / x <= y}.
Admitted.

Lemma BVf_nondecreasing : forall a b f, is_BV f a b ->
  {homo (fun x => variation f a x - f x) : x y / x <= y}.
Admitted.

Lemma 7211 : forall f, right_continuous f /\ is_BV f a b ->
right_continuous (fun x => variation f a x) on [a, b].

Lemma 7211' : forall f, right_continuous f /\ is_BV f a b ->
right_continuous (fun x => variation f a x - f x) on [a, b].

End Variation.


Section abs_cont_properties.

Local Open Scope ereal_scope.

Lemma abs_contE (R : realType)
  (mu nu : {smeasure set R -> \bar R}):
    nu `<< mu <-> forall e, 0 < e -> exists d, 0 < d /\
      (forall S, (measurable S /\ mu S < d) -> nu S < e).
Proof.
move=> /=.
split.
  move=> nudommu e e0.
Admitted.

(* Need lebesgue_stieltjes measure*)
Lemma abs_continuous_fun_measure d (R : realType)
    (f : R -> R) : forall a b : R,
    abs_continuous_function f (a, b) ->
      smrestr (hlength f) ([set` Interval -oo%O (BSide false b)]%E) `<< smrestr (@lebesgue_measure d R) `[a, b].
Proof.
Admitted.

(* abs_cont -> abs_cont_fun *)
Lemma abs_continuous_measure_fun d (R : realType)     (nu : {smeasure R -> \bar R}) : forall a b : R,
      

End abs_cont_properties.


Theorem FTC2 (d : measure_display) (R : realType) (f : R -> R) (a b : R)
     (f_abscont : abs_continuous_function f (a, b) )
       : exists f' : R -> \bar R, summable `[a, b] f' /\
         {ae (@lebesgue_measure (ocitv_display R) R), forall x, x \in `[a, b] ->f' x \is a fin_num}
           /\ forall x, x \in `[a, b] ->
                        (f x - f a)%:E = (integral (@lebesgue_measure (ocitv_display R) R) `[a ,x] f').
Proof.
pose Lambda_f := lebesgue_stieltjes_measure d f.
have f' := Radon_Nikodym Lambda_f.
Abort.
