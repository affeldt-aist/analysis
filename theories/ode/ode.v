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

Reserved Notation "\vint [ mu ]_ ( i 'in' D ) F"
  (at level 36, F at level 36, i, D at level 60,
  format "'[' \vint [ mu ]_ ( i  'in'  D ) '/  '  F ']'").
Reserved Notation "\vint [ mu ]_ i F"
  (F at level 36, i at level 0,
    right associativity, format "'[' \vint [ mu ]_ i '/  '  F ']'").

(* TODO: move *)
Section row_Rintegral.
Context {R : realType} (d : measure_display) {T : measurableType d}.
Variable (mu : {measure set T -> \bar R}).
Variable (D : set T) (n : nat).

Definition rowRintegral (f : T -> 'rV[R]_n) : 'rV[R]_n :=
  \row_i (\int[mu]_(x in D) (f x) ord0 i).

Local Notation "\vint_ i F" :=
    (rowRintegral (fun i => F)%R) (at level 36, i at level 0,
  format "'[' \vint_ i '/  '  F ']'")  : ring_scope.

Lemma rowRintegralE (f : T -> 'rV[R]_n) i :
  (\vint_x f x) ord0 i = \int[mu]_(x in D) (f x) ord0 i.
Proof. by rewrite /rowRintegral mxE. Qed.

End row_Rintegral.

Notation "\vint [ mu ]_ ( x 'in' D ) f" :=
  (rowRintegral mu D (fun x => f)%R) : ring_scope.
Notation "\vint [ mu ]_ x f" :=
  (rowRintegral mu setT (fun x => f)%R) : ring_scope.

Section rowRintegral.
Context {R : realType}.
Let mu := @lebesgue_measure R.

Lemma rowRintegral_set1 n (f : R -> 'rV[R]_n) (r : R) :
  \vint[mu]_(x in [set r]) f x = 0.
Proof. by apply/rowP => i; rewrite !mxE Rintegral_set1. Qed.
Lemma eq_rowRintegral n (D : set R) (f : R -> 'rV[R]_n) (g : R -> 'rV[R]_n):
 {in D, f =1 g} -> \vint[mu]_(x in D) f x = \vint[mu]_(x in D) g x.
Proof.
  move => h.
  apply /rowP => i.
  rewrite !rowRintegralE.
  apply eq_Rintegral => /= x Dx.
  by rewrite h.
Qed.

End rowRintegral.

Definition picard_from_cont' {R : realType} n (U := 'rV[R]_n) (u0 : U) (r : R)
  (B := closed_ball u0 r) (f : R -> U -> U) (g : R -> U) (a b : R)
    (imageg : g @` `[a, b] `<=` B) : R -> U :=
  fun t => u0 + (\vint[lebesgue_measure]_(x in `[a, t]) f x (g x))%R.

Section vector_continuous.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.

Lemma within_continuous_coord (h : R -> U) D :
  {within D, continuous h} <-> forall i, {within D, continuous (fun x => h x ord0 i)}.
Proof.
split=> [Dh i|H].
- apply/subspace_continuousP => /= x Dx.
  have /subspace_continuousP/(_ x Dx) H := Dh.
  apply: ((@cvg_comp _ _ _ h (fun z => z ord0 i)) _ _ _ H).
  exact: coord_continuous.
- apply/subspace_continuousP => /= x Dx.
  apply/cvgrPdist_le => /= e e0.
  rewrite near_withinE.
  near=> t => Dt.
  rewrite /Num.norm/= mx_normrE.
  apply/(bigmax_le _ (ltW e0)) => /= -[i j] _ /=.
  rewrite {i}(ord1 i) !mxE.
  move: j Dt.
  near: t.
  apply: filter_forall => /= i.
  have /subspace_continuousP/(_ x Dx) := H i.
  move/cvgrPdist_le => /(_ _ e0).
  rewrite near_withinE.
  exact.
Unshelve. all: by end_near. Qed.

End vector_continuous.
Section picard_from_cont'.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
Context {n : nat}.
Let U := 'rV[R]_n.
(*Let U := R.*)

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
apply/within_continuous_coord => i.
rewrite /picard_from_cont'.
suff: {within `[a, b], continuous (fun t => \int[mu]_(x0 in `[a, t]) (f x0 (g x0)) ord0 i)}.
  move=> abf x.
  rewrite (_ : (fun x0 : R => (u0 + \vint[mu]_(x1 in `[a, x0]) f x1 (g x1))%E ord0 i) =
               (fun x0 : R => u0 ord0 i + \int[mu]_(x1 in `[a, x0]) (f x1 (g x1)) ord0 i)); last first.
    apply/funext=> x0.
    by rewrite mxE rowRintegralE.
  apply: cvgD.
    exact: cvg_cst.
  exact: abf.
move=> /= x.
apply: parameterized_integral_continuous => //.
apply: continuous_compact_integrable; first exact: segment_compact.
move=> {x}.
move: i.
apply/within_continuous_coord.
exact: (within_continuous_lipschitz cg k0 lip2 cont1).
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
Let U := 'rV[R]_n.

(*Let U := R.*)
Variables (f : R -> U -> U) (a b : R).
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.

Definition picard_from_cont
  (k : R) (lcf_x : {in `[a, b]%R, forall x, k.-lipschitz_B (f x)})
  (cf_y : {in B, forall y, {within `[a, b], continuous f ^~ y}})
  (g : R -> U) : R -> U :=
match pselect (g @` `[a, b] `<=` B) with
| left imageg => @picard_from_cont' R n u0 r%:num f g a b imageg
| _ => cst 0
end.

End picard_from_cont.

Lemma closed_ball_vecE {R : realType}  {n} (x0 : 'rV[R]_n) (r : {posnum R}) x : closed_ball x0 r%:num x <-> forall i, closed_ball (x0 ord0 i) r%:num (x ord0 i). 
Proof.
split.
- rewrite closed_ballE /closed_ball_ //=.
  rewrite /Num.norm/=.
  rewrite mx_normrE.
  move => h i.
  rewrite closed_ballE /closed_ball_ //=.
  apply /le_trans/h.
  have -> : (x0 ord0 i - x ord0 i = (x0 - x) ord0 i) by rewrite !mxE.
  exact: (le_bigmax _ _ (ord0,i)).
move => h.
rewrite closed_ballE /closed_ball_ //=.
rewrite [in leLHS]/Num.norm/= mx_normrE.
apply: bigmax_le => //= -[i j] _.
simpl.
rewrite {i}(ord1 i)/=.
move /(_ j) :h.
rewrite closed_ballE /closed_ball_ //=.
by rewrite !mxE.
Qed.

(* second, we define picard_to_cont
   that takes a function continuous over a closed ball
   and returns a function continuous over a closed ball *)
Section vector_measure.

Local Notation mu := lebesgue_measure.
Lemma measurable_fun_bigmaxr
  (d : measure_display) (T : measurableType d) (R : realType)
   (D : set T) (n : nat)
  (f : 'I_n -> T -> R) :
  d.-measurable D ->
  (forall i, measurable_fun D (f i)) ->
  measurable_fun D (fun x => \big[maxr/0]_(i < n) f i x).
Proof.
move=> mD mf.
elim: n f mf => [|n IH] f mf.
- have  ->: (fun x : T => \big[maxr/0]_(i < 0) f i x) = 0.
    apply funext => x.
    by rewrite big_ord0.
  exact: measurable_cst.

have ->:  (fun x : T => \big[maxr/0]_(i < n.+1) f i x) = fun x => maxr (f ord0 x) (\big[maxr/0]_(i < n) (f (lift ord0 i) x)).
  by apply funext => x;apply big_ord_recl.
  apply measurable_maxr.
  apply mf.
  apply IH.
  move => i.
  apply mf.
Qed.

Lemma vec_norm_le_sum {R : realType} {n : nat} (x : 'rV[R]_n) : `| x | <=  \sum_(i < n) `|x ord0 i|.
Proof.                                                 
  rewrite  {1}/Num.norm/= mx_normrE.
   apply: bigmax_le => /=;first by apply sumr_ge0 => i _; exact: normr_ge0.
   move =>  [i0 i] _ /=.
   rewrite {i0}(ord1 i0)/=.
   rewrite (bigD1 i) //= lerDl.
  apply sumr_ge0 => j _; exact: normr_ge0.
Qed.

Lemma vmeasurable_norm {R: realType} {n : nat} (D : set R) (F : R -> 'rV[R]_n):
   measurable D -> (forall i, measurable_fun D (fun t => F t ord0 i)) ->
  measurable_fun D (Num.norm \o F).
Proof.
move=> mD h.
have -> : normr \o F = (fun x => \big[maxr/0]_(i < n) `| F x ord0 i |).
  apply funext => x.
  rewrite  {1}/Num.norm/= mx_normrE.
  rewrite (reindex (fun i : 'I_n => (ord0, i))) => //=.
  exists (@snd 'I_1 'I_n) => /=.
  + by move => i.
  + move => [i j] /= _.
    by rewrite {i}(ord1 i)/=.
 apply (measurable_fun_bigmaxr   ) => //= i.
 apply measurableT_comp => //=.
 apply normr_measurable.
Qed.

Lemma vintegrable_norm {R: realType} {n : nat} (D : set R) (F : R -> 'rV[R]_n):
  measurable D -> (forall i, mu.-integrable D (EFin \o (fun t => F t ord0 i))) ->
  mu.-integrable D (EFin \o (Num.norm \o F)).
Proof.

move => mD intf.
apply (le_integrable (mu:=lebesgue_measure) mD (f := EFin \o (normr \o F)) (g := EFin \o fun x => (\sum_(i < n) `| F x ord0 i|))).
  apply/measurable_EFinP.
  apply vmeasurable_norm => // i.
  have /integrableP[+ _]/= := intf i.
  by move/measurable_EFinP.
  move => /= x0 Dx0.
  rewrite normr_id.
  rewrite lee_fin.
  rewrite ger0_norm.
  apply vec_norm_le_sum.
  apply sumr_ge0 => i _; exact: normr_ge0.
have -> :
(EFin \o (fun x => \sum_(i < n) `|F x ord0 i|)) = (fun x => (\sum_(i < n) `|F x ord0 i|%:E)).
   by apply funext => x;rewrite sumEFin.
apply integrable_sum => //=.
move => i _.
apply integrable_norm => /=.
apply intf.
Qed.

End vector_measure.

Section picard_to_cont.
Context {R : realType} {n : nat}.

Let U := 'rV[R]_n.
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

Local Notation picard_from_cont_not := (@picard_from_cont _ n f a (a + Delta) u0 r k lip2_Delta cont1_Delta).

Lemma Delta_gt0 : 0 < Delta.
Proof.
rewrite lt_min subr_gt0 ab/= lt_min mulr_gt0//=.
  by rewrite divr_gt0.
rewrite invr_gt0// ltr_wpDr//.
  exact: hmax_ge0.
by rewrite mulr_gt0.
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
  forall i,
  mu.-integrable `[a, y] (EFin \o (fun t : R => f t (F t) ord0 i)).
Proof.
move => yaaDelta ab0r i.
apply: continuous_compact_integrable; first exact: segment_compact.
move: (yaaDelta); rewrite  in_itv/= => /andP[ay yaDelta].
move: i.
apply/within_continuous_coord.
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
Lemma picard_from_cont_simpl g t :
  [set g x | x in `[a, (a + Delta)%E]] `<=` closed_ball u0 r%:num ->
  picard_from_cont_not g t = u0 + (\vint[mu]_(x in `[a, t]) f x (g x))%R.
Proof.
rewrite /picard_from_cont_not; case: pselect => [| // ] .
by rewrite /picard_from_cont'.
Qed.

Lemma lipschitz_componentE x :   k.-lipschitz_B (f x) <-> forall i, k.-lipschitz_B (fun y => f x y ord0 i).
Proof.
split.
- move => lip i /= [x1 x2] /= Bx12.
  move /(_ (x1,x2) Bx12) : lip.
  apply le_trans => /=.
  rewrite /Num.norm/= mx_normrE.
  have -> : (f x x1 ord0 i - f x x2 ord0 i = (f x x1 - f x x2) ord0 i) by rewrite !mxE.
  exact: (le_bigmax _ _ (ord0,i)).
move => h /= [x1 x2] Bx12 /=.
rewrite [in leLHS]/Num.norm/= mx_normrE.
apply/bigmax_le.
by rewrite mulr_ge0 //= ltW.
move => //= -[i j] _ /=.
rewrite {i}(ord1 i)/=.
move /(_ j (x1,x2) Bx12) : h.
by rewrite !mxE /=.
Qed.




Lemma set_fun_picard_to_cont : set_fun restrictedV restrictedV picard_to_cont.
Proof.
move=> F.
rewrite /restrictedV/= => invariant _/= [y yaaDelta <-].
rewrite /picard_to_cont.
rewrite /B.
apply closed_ball_vecE => i.
rewrite closed_ball_itv//=.
rewrite in_itv//=.
rewrite [X in _ <= X <= _](_ : _ = (picard_from_cont_not F) y ord0 i); last first.
  have /eqmod_on_itv : (repr (\pi_(V)%qT (picard_from_cont_not F)) =
       picard_from_cont_not F %[mod V])%qT.
    by rewrite reprK.
  move=> <-//.
  have aDeltab : (a + Delta) <= b.
    by rewrite -lerBrDl ge_min lexx.
  by rewrite inE/=.
rewrite /picard_from_cont_not.
case: pselect => /= abu0r; last first.
  done.
rewrite /picard_from_cont' //=.
rewrite mxE/=.
rewrite -ler_distl.
rewrite -addrA subrKC.
rewrite rowRintegralE.
rewrite (le_trans (le_normr_Rintegral _ _))//=.
  apply integrable_comp; first by [].
  apply: subset_trans abu0r.
  apply/image_subset/subset_itvl; rewrite bnd_simp.
  by move : yaaDelta; rewrite in_itv /= => /andP[].
have integrable2 : mu.-integrable `[a, y] (EFin \o (fun x => f x (F x) ord0 i)).
  apply integrable_comp => //=.
  apply: subset_trans abu0r.
  apply/image_subset/subset_itvl; rewrite bnd_simp.
  by move : yaaDelta;rewrite in_itv /= => /andP[].
have integrable1 : mu.-integrable `[a, y]
    (fun x : g_sigma_algebraType (R.-ocitv).-measurable =>
     (`|f x (F x) ord0 i - f x u0 ord0 i|%:E + `|f x u0 ord0 i|%:E)).
  rewrite integrableD//=.
    apply integrable_norm => /=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinD.
    rewrite integrableD //=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinN.
    rewrite integrableN //=.
    apply continuous_compact_integrable => //=; first exact: segment_compact.
    apply within_continuous_coord.
    apply /continuous_subspaceW/cont1_Delta.
      apply: subset_itvl; rewrite bnd_simp.
      by move : yaaDelta;rewrite in_itv /= => /andP[].
    rewrite /B inE.
    exact: closed_ballxx.
  apply integrable_norm => /=.
  apply continuous_compact_integrable => //=; first exact: segment_compact.
  apply within_continuous_coord.
  apply/continuous_subspaceW/cont1_Delta.
    apply: subset_itvl; rewrite bnd_simp.
    by move : yaaDelta;rewrite in_itv /= => /andP[].
  rewrite /B inE.
  exact: closed_ballxx.
rewrite (@le_trans _ _ (\int[mu]_(x in `[a, y]) (`|f x (F x) ord0 i - f x u0 ord0 i| + `|f x u0 ord0 i|)))//.
  apply: le_Rintegral => //=.
  - exact: integrable_norm.
  - move=> x xay.
    by rewrite (le_trans _ (ler_normD _ _))// subrK.
rewrite (@le_trans _ _ (\int[mu]_(x in `[a, y]) (k * `|F x   - u0  | + hmax)))//.
  apply: le_Rintegral => //=.
  - under [x in integrable _ _  x]eq_fun do rewrite EFinD.
    rewrite integrableD //=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinM.
    rewrite integrableMr //=.
    exact: bounded_cst.
    apply: vintegrable_norm.
    apply measurable_itv.
    move => j //=.
    under [x in integrable _ _  x]eq_fun do rewrite !mxE EFinB.
    rewrite integrableB //=.
    apply continuous_compact_integrable => //; first exact: segment_compact.
    apply within_continuous_coord.
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
      rewrite lipschitz_componentE.
      move/(_ i (F x, u0)).
      simpl.
      apply.
      split => /=.
        apply: invariant => /=.
        exists x => //.
        move : xay.
        apply: subset_itvl.
        rewrite bnd_simp.
        by rewrite (itvP yaaDelta).
      by apply: closed_ballxx.
    apply (@le_trans  _ _ `| f x u0 |).
    rewrite {2}/Num.norm/= mx_normrE /=.
    apply: (le_bigmax _ _ (ord0,i)).
    rewrite /hmax.
    rewrite ub_le_sup//.
      have [M [Mb1 Mb2]] : bounded_set [set `|f t u0| | t in `[a,b]].
        apply/compact_bounded/continuous_compact; last exact: segment_compact.
        apply: within_continuous_comp_norm.
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
    apply: vintegrable_norm.
    apply measurable_itv.
    move => j /=.
    under [x in integrable _ _  x]eq_fun do rewrite !mxE EFinB.
    rewrite integrableB //=.
    apply continuous_compact_integrable => //.
    exact: segment_compact.
    apply within_continuous_coord.
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
      rewrite closed_ballE /closed_ball_ //=.
      by rewrite distrC.
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


Lemma picard_to_cont_init g :
  [set g x | x in `[a, (a + Delta)%E]] `<=` closed_ball u0 r%:num ->
  picard_from_cont_not g a = u0.
Proof.
move => h.
by rewrite picard_from_cont_simpl// set_itv1 rowRintegral_set1 addr0.
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

Definition measure_rV_display : measure_display -> measure_display.
Proof. exact. Qed.

Section measurable_rV.
Context {d} {T : sigmaRingType d}.
Variable n : nat.

Let coors : 'I_n -> 'rV[T]_n -> T := fun i x => x ord0 i.

Let rV_set0 : g_sigma_preimage coors set0.
Proof. exact: sigma_algebra0. Qed.

Let rV_setC A : g_sigma_preimage coors A -> g_sigma_preimage coors (~` A).
Proof. exact: sigma_algebraC. Qed.

Let rV_bigcup (F : _^nat) : (forall i, g_sigma_preimage coors (F i)) ->
  g_sigma_preimage coors (\bigcup_i (F i)).
Proof. exact: sigma_algebra_bigcup. Qed.

HB.instance Definition _ := @isMeasurable.Build (measure_rV_display d)
  'rV[T]_n (g_sigma_preimage coors) rV_set0 rV_setC rV_bigcup.

End measurable_rV.

(* (* see measurable_fun_tnthP *) *)
(* Lemma rV_measurable_fun {d} {T : measurableType d} {R : realType} *)
(*   (D : set T) n (f : T -> 'rV[R]_n) : *)
(*   measurable_fun D f <-> forall i, measurable_fun D (fun t => f t ord0 i). *)
(* Proof. *)
(* split => [mf i mD /= Y mY|mf mD /= Y mY]. *)
(*   admit. *)
(* admit. *)
(* Admitted. *)

(* Definition proj (T : Type) n (A : set (n.-tuple T)) (i : 'I_n) : set T := *)
(*   [set t | exists x, A x /\ t = tnth x i]. *)

(* Lemma vnormr_measurable {R : realType} n (D : set 'rV[R]_n) : *)
(*   measurable_fun D (@Num.norm R 'rV[R]_n). *)
(* Proof. *)
(* move=> mD /= Y mY. *)
(* rewrite /normr/=. *)
(* Admitted. *)

(* Lemma vintegrable_norm {d} {T : measurableType d} {R : realType} *)
(*   (mu : {measure set T -> \bar R}) (D : set T) n (f : T -> 'rV[R]_n) : *)
(*   (forall i, mu.-integrable D (EFin \o (fun t => f t ord0 i))) -> *)
(*   mu.-integrable D (EFin \o (Num.norm \o f)). *)
(* Proof. *)
(* move=> intf. *)
(* apply/integrableP; split. *)
(*   apply/measurable_EFinP. *)
(*   apply/measurableT_comp. *)
(*     exact: vnormr_measurable. *)
(*   apply/rV_measurable_fun => i. *)
(*   have /integrableP[+ _]/= := intf i. *)
(*   by move/measurable_EFinP. *)
(* rewrite (@le_lt_trans _ _ *)
(*     (\big[maxe/-oo]_(i < n) \int[mu]_(x in D) `|f x ord0 i|%:E )%E)//. *)
(*   rewrite /=. *)
(*   under eq_integral do rewrite normr_id. *)
(*   rewrite [in leLHS]/Num.norm/=. *)
(*   under eq_integral do rewrite mx_normrE. *)
(*   admit. *)
(* apply: bigmax_lt => //= i _. *)
(* have /integrableP[_]/= := intf i. *)
(* exact. *)



Section picard_to_cont_normedtype4.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.

Variable f : R -> U -> U.
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
Notation Vr := (@restrictedV _ n f a b k ab u0 r k0 rho).

Check @cst (subspace `[a, a + Delta f a b k u0 r rho]) U u0 : {fun `[a, a + Delta f a b k u0 r rho] >-> [set: U]}.

Check @cst (subspace `[a, a + Delta f a b k u0 r rho]) U u0 : continuousType (subspace `[a, a + Delta f a b k u0 r rho]) U.

(* Check @cst (subspace `[a, a + Delta f a b k u0 r rho]) R u0 : continuousFunType `[a, a + Delta f a b k u0 r rho] [set: R]. *)
Lemma restrictedVball : Vr = @closed_ball R V
  (pi V (@cst (subspace `[a, a + Delta f a b k u0 r rho]) U u0)) r%:num.
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
  @picard_to_cont R n f a b k ab u0 r k0 lip2 cont1 rho.

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
rewrite [in leLHS]/Num.norm/= mx_normrE.
apply: bigmax_le => //= -[i j] _.
rewrite {i}(ord1 i)/=.
rewrite mxE rowRintegralE mxE rowRintegralE.
have integrable1 : mu.-integrable `[a, t] (EFin \o (fun x0 => f x0 (x x0) ord0 j)).
  apply integrable_comp => //=.
  move => _ [x0 h] <-.
  apply: Hg => /=.
  exists x0 => //.
  apply/subset_itvl/h; rewrite bnd_simp.
  by move: tNdd; rewrite !in_itv/= => /andP[] .
have integrable2 : mu.-integrable `[a, t] (EFin \o(fun x0 => f x0 (y x0) ord0 j)).
  apply integrable_comp => //=.
  move => _ [x0 h] <-.
  apply: Hg2 => /=.
  exists x0 => //.
  apply/subset_itvl/h; rewrite bnd_simp.
  by move: tNdd; rewrite !in_itv/= => /andP[] .
rewrite -RintegralB//=.
rewrite (le_trans (le_normr_Rintegral _ _))//=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinB.
    rewrite integrableB //=.
 have integrable3 : mu.-integrable `[a, t] (fun x0 => `|x x0 - y x0|%:E). 
 rewrite /=.
 apply : vintegrable_norm.
   apply measurable_itv.
   move => i.
   under [x in integrable _ _  x]eq_fun do rewrite !mxE EFinB. 
   rewrite integrableB //=.
   apply continuous_compact_integrable => //=.
    exact: segment_compact.
   apply within_continuous_coord.
   apply /continuous_subspaceW/cts_fun.
   apply: subset_itvl.
   rewrite bnd_simp.
   by move : tNdd;rewrite in_itv /= => /andP[].
   apply continuous_compact_integrable => //=.
   exact: segment_compact.
   apply within_continuous_coord.
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
    have Bxy : B (x x0) /\ B (y x0).
      split.
        apply: Vrx => /=.
        exists x0 => //.
        apply/subset_itvl/x0at.
        by move: tNdd; rewrite in_itv/= => /andP[Ndt].
      apply: Vry => /=.
      exists x0 => //.
      apply/subset_itvl/x0at.
      by move: tNdd; rewrite in_itv/= => /andP[Ndt].
    move=> /(_ Bxy); apply: le_trans.
    rewrite [in leRHS]/Num.norm/= mx_normrE.
    apply: le_trans; last first.
      apply: le_bigmax => /=.
      exact: (ord0, j).
    by rewrite /= !mxE.
  by rewrite RintegralZl.
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

Definition row_vector {R : realType} (n : nat) := 'rV[R]_n.

HB.instance Definition _ {R : realType} (n : nat) := Complete.on (@row_vector R n).
HB.instance Definition _ {R : realType} (n : nat) := NormedModule.on (@row_vector R n).
(*HB.instance Definition _ {R : realType} (n : nat) := CompleteNormedModule.on (@row_vector R n).*)

Section pointwise_derivable.
Context {R : realFieldType} {V W : normedModType R} {m n : nat}.
Implicit Types M : V -> 'M[R]_(m, n).

Definition derivable_mx M t v :=
  forall i j, derivable (fun x => M x i j) t v.

(* NB: from robot-rocq *)
Lemma derivable_mxP M t v : derivable_mx M t v <-> derivable M t v.
Proof.
split; rewrite /derivable_mx /derivable.
- move=> H.
  apply/cvg_ex => /=.
  pose l := \matrix_(i < m, j < n) sval (cid ((cvg_ex _).1 (H i j))).
  exists l.
  apply/cvgrPdist_le => /= e e0.
  near=> x.
  rewrite /Num.Def.normr/= mx_normrE.
    apply: (bigmax_le _ (ltW e0)) => /= i _.
  rewrite !mxE/=.
  move: i.
  near: x.
  apply: filter_forall => /= i.
  exact: ((@cvgrPdist_le _ _ _ _ (dnbhs_filter 0) _ _).1
    (svalP (cid ((cvg_ex _).1 (H i.1 i.2)))) _ e0).
- move=> /cvg_ex[/= l Hl] i j.
  apply/cvg_ex; exists (l i j).
  apply/cvgrPdist_le => /= e e0.
  move/cvgrPdist_le : Hl => /(_ _ e0)[/= r r0] H.
  near=> x.
  apply: le_trans; last first.
    apply: (H x).
    rewrite /ball_/=.
    rewrite sub0r normrN.
    near: x.
    exact: dnbhs0_lt.
    near: x.
    exact: nbhs_dnbhs_neq.
  rewrite [leRHS]/Num.Def.normr/= mx_normrE.
  apply: le_trans; last exact: le_bigmax.
  by rewrite /= !mxE.
Unshelve. all: by end_near. Qed.

End pointwise_derivable.

Section pointwise_derive.
Local Open Scope classical_set_scope.
Context {R : realFieldType} {V W : normedModType R} .

(* NB: from robot-rocq *)
Lemma derive_mx {m n : nat} (M : V -> 'M[R]_(m, n)) t v :
  derivable M t v ->
  'D_v M t = \matrix_(i < m, j < n) 'D_v (fun t => M t i j) t.
Proof.
move=> /cvg_ex[/= l Hl]; apply/cvg_lim => //=.
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : (Hl) => /(_ (e / 2)).
rewrite divr_gt0// => /(_ isT)[d /= d0 dle].
near=> x.
rewrite [in leLHS]/Num.Def.normr/= mx_normrE.
apply/(bigmax_le _ (ltW e0)) => -[/= i j] _.
rewrite [in leLHS]mxE/= [X in _ + X]mxE -[X in X - _](subrK (l i j)).
rewrite -(addrA (_ - _)) (le_trans (ler_normD _ _))// (splitr e) lerD//.
- rewrite mxE.
  suff : (h^-1 *: (M (h *: v + t) i j - M t i j)) @[h --> 0^'] --> l i j.
    move/cvg_lim => /=; rewrite /derive /= => ->//.
    by rewrite subrr normr0 divr_ge0// ltW.
  apply/cvgrPdist_le => /= r r0.
  move/cvgrPdist_le : Hl => /(_ r r0)[/= s s0] sr.
  near=> y.
  have : `|l - y^-1 *: (M (y *: v + t) - M t)| <= r.
    rewrite sr//=; last by near: y; exact: nbhs_dnbhs_neq.
    by rewrite sub0r normrN; near: y; exact: dnbhs0_lt.
  apply: le_trans.
  rewrite [in leRHS]/Num.Def.normr/= mx_normrE.
  by under eq_bigr do rewrite !mxE; exact: (le_bigmax _ _ (i, j)).
- rewrite mxE.
  have : `|l - x^-1 *: (M (x *: v + t) - M t)| <= e / 2.
    apply: dle => //=; last by near: x; exact: nbhs_dnbhs_neq.
    by rewrite sub0r normrN; near: x; exact: dnbhs0_lt.
  apply: le_trans.
  rewrite [in leRHS]/Num.Def.normr/= mx_normrE/=.
  under eq_bigr do rewrite !mxE.
  apply: le_trans; last exact: le_bigmax.
  by rewrite !mxE.
Unshelve. all: by end_near. Qed.

End pointwise_derive.

Section integral_ode.

Context {R : realType} {n : nat}.
Notation U := (@row_vector R n).

Variables (f : R -> U -> U) (t0 t1 : R)  (u0 : U) (phi : R-> U) (k : R) (r : {posnum R}).
Hypothesis k0 : 0 < k.
Hypothesis t01 : t0 < t1.

Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[t0, t1]%R, forall x : R, k.-lipschitz_B (f x)}.
Hypothesis cont1 : {in B, forall y, {within `[t0, t1], continuous f ^~ y}}.
Hypothesis cont_phi : {within `[t0, t1], continuous phi}.
Hypothesis phi_bound : [set phi x | x in `[t0, t1]] `<=` closed_ball u0 r%:num.

Let mu := @lebesgue_measure R.

Definition is_integral_sol_on   :=
  phi t0 = u0 /\
  forall t, `[t0, t1] t ->
    phi t = phi t0 + (\vint[mu]_(s in `[t0, t]) f s (phi s))%R.

(* Definition is_integral_sol_on_open   := *)
(*   phi t0 = u0 /\ *)
(*   forall t, `]t0, t1[ t -> *)
(*     phi t = phi t0 + (\vint[mu]_(s in `[t0, t]) f s (phi s))%R. *)

(* Lemma integral_sol_open_closed : is_integral_sol_on_open -> is_integral_sol_on. *)
(* Proof. *)
(*  move => [h0 h1]. *)
(* split => //. *)
(* move => t. *)
(* case: (eqVneq t t0) => [-> _|Ht0]. *)
(*   by rewrite set_itv1 rowRintegral_set1 addr0. *)
(* rewrite /=in_itv/= => /andP [ht0 ht1]. *)
(* apply h1. *)
(* by rewrite /=in_itv/=ht1//= lt_neqAle ht0/= eq_sym Ht0. *)
(* Qed. *)

Definition is_sol_on   :=
  phi t0 = u0 /\
  {in `]t0, t1[, forall x, derivable phi x 1 /\ phi^`() x = f x (phi x)}.


Lemma picard_iterator_within_cont  i:  {within `[t0,t1], continuous (fun x0 : R => f x0 (phi x0) ord0 i)}.
Proof.
move: i.
apply/within_continuous_coord.
by apply: (within_continuous_lipschitz _ k0 _ (u0 := u0) (r := r)).
Qed.

Lemma picard_iterator_cont  i t :  t \in `]t0, t1[ ->  {for t, continuous (fun x0 : R => f x0 (phi x0) ord0 i)}.
move => tad.
rewrite inE in tad.
apply: (within_continuous_continuous _ _ tad) => //.
exact: picard_iterator_within_cont.
Qed.

(* Lemma Rintegral_itv_open_closed (a b : R) (g : R -> R) : *)
(*   \int[mu]_(x in `]a, b[) g x *)
(*   = \int[mu]_(x in `[a, b]) g x. *)
(* Proof. *)
(* rewrite Rintegral_itv_obnd_cbnd. *)
(* rewrite Rintegral_itv_bndo_bndc //. *)
(* Admitted. *)

Lemma picard_iterator_integrable i :  mu.-integrable `[t0, t1]
        (EFin \o (fun x : R => f x (phi x) ord0 i)).
Proof.
apply: continuous_compact_integrable; first exact: segment_compact.
apply picard_iterator_within_cont.
Qed.


Lemma integral_sol_iff_sol : is_integral_sol_on  <-> is_sol_on.
Proof.
split.
- 
  move => [hinit h];split => // t tab.
  move : (tab).
  rewrite inE /= in_itv /= => /andP[ta tb].
  have -> : phi^`() t  = (fun x => phi t0 + \vint[mu]_(s in `[t0, x]) f s (phi s))^`() t.
    apply/eq_on_itv_deriv/tab => x xt01;apply h.
    rewrite inE in xt01.
    by apply: subset_itv_oo_cc.
    (* move : xt01 . *)
    (* Search "itv" "subs". *)
    (* rewrite inE/=!in_itv/= => /andP [xt01 xt01']. *)
    (* by rewrite ltW. *)
  suff hi: forall i, derivable (fun x => phi x ord0 i) t 1 /\  (fun x : R => (phi t0 + \vint[mu]_(s in `[t0, x]) f s (phi s))%E)^`() t ord0 i = f t (phi t) ord0 i.
    split.
    apply /derivable_mxP.
    rewrite /derivable_mx => i j.
    have [? _] := (hi j).
    by rewrite ord1.
    apply/rowP => j.
    have [_ ?] := (hi j).
    by [].
  move => j.
  have [H1 H2] := @continuous_FTC1_closed _ (fun x => f x (phi x) ord0 j)
                    t0 t t1 tb (picard_iterator_integrable j) ta (picard_iterator_cont tab).
   have Hderivable : derivable (fun x : R => \vint[mu]_(x0 in `[t0, x]) f x0 (phi x0)) t 1.
      apply/(@derivable_mxP R R) => i0 i; rewrite (ord1 i0){i0}/=.
    have [?] := @continuous_FTC1_closed _ (fun x => f x (phi x) ord0 i)
                    t0 t t1 tb (picard_iterator_integrable i) ta (picard_iterator_cont tab).
      rewrite /rowRintegral.
      rewrite [X in derivable X t 1](_ : _ =
          (fun x : R => \int[mu]_(x0 in `[t0, x]) f x0 (phi x0) ord0 i)); last first.
        by apply/funext => x; rewrite mxE.
      by [].
     rewrite derive1E deriveD /=; last 2 first. 
      exact: derivable_cst.
      exact: Hderivable.
    split.
    apply: (near_eq_derivable (f := (fun x =>  (phi t0 + \vint[mu]_(s in `[t0, x]) f s (phi s)) ord0 j))) => //=.
    near=>t'.
    rewrite  (h t') //.
    rewrite /=in_itv/=.
    apply /andP;split.
    apply ltW.
    near:t'.
    by apply: lt_nbhsr.    
    apply ltW.
    near:t'.
    by apply: lt_nbhsl.    
    have -> :  (fun x : R => (phi t0 + \vint[mu]_(s in `[t0, x]) f s (phi s))%E ord0 j) = cst (phi t0 ord0 j)  +  (fun x : R =>  (\vint[mu]_(s in `[t0, x]) (f s (phi s))) ord0 j).
      apply funext => x.
      by rewrite mxE.
    apply derivableD.
    by apply derivable_cst.
    move /derivable_mxP : Hderivable.
    apply.
    rewrite -!derive1E derive1_cst add0r -H2 -/mu.
    rewrite !derive1E derive_mx//.
    rewrite mxE/=.
    congr ('D_1 _ t).
    apply/funext => t'.
    by rewrite mxE.
move => [hinit h];split => // t tab.
have := tab.
rewrite /=in_itv/= => /andP [ta tb].
apply/rowP => i.
rewrite mxE rowRintegralE.
move : ta.
rewrite le_eqVlt => /orP [/eqP <- | ta].
by rewrite set_itv1 Rintegral_set1 addr0.
rewrite /Rintegral.
have cont_phii :  {within `[t0, t1], continuous (fun x => phi x ord0 i)}.
by move:i;apply /within_continuous_coord.
rewrite (@continuous_FTC2 _ (fun x => f x (phi x) ord0 i) (fun x => phi x ord0 i) _ _ ta).
by rewrite -EFinB subrKC.
apply: continuous_subspaceW; last exact: picard_iterator_within_cont.
by apply: subset_itvl.
split.
move => t' tx'.
have xt' : t' \in `]t0, t1[.
rewrite inE.
by apply/ subset_itvl/tx'.
by have [/derivable_mxP + _] := h _ xt'.
by move /(continuous_within_itvP _ t01) : cont_phii => [_ + _].
have cont_phii' :  {within `[t0, t], continuous fun x0 : R => phi x0 ord0 i}.
apply:continuous_subspaceW;last apply cont_phii.
by apply:subset_itvl. 
by move /(continuous_within_itvP _ ta) : cont_phii' => [ _ _ +].
move => x  xt.
have xt' : x \in `]t0, t1[.
rewrite inE.
by apply/ subset_itvl/xt.
have [_ +] := h _ xt'.
rewrite !derive1E derive_mx/=;last by apply h.
move => <-.
rewrite mxE//.
Unshelve. all: by end_near. Qed.

End integral_ode.
Section picard.
Context {R : realType} {n : nat}.
Notation U := (@row_vector R n).

Variables (f : R -> U -> U) (a b : R) (k : R) (u0 : U) (r : {posnum R}).
Hypothesis ab : a < b.
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (f x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous f ^~ y}}.
Variable rho : {posnum R}.
Hypothesis rho1 : rho%:num < 1.
(*Variable y_ : R -> R.
Hypothesis y_init_t : y_ 0 = 0.*)

(*Hypothesis dtwok : d0%:num < (2 * k)^-1.*)

Definition tmp : is_contraction (contrac ab k0 lip2 cont1 rho) :=
  (@is_contraction_picard_to_cont R n f a b ab k k0 u0 r lip2 cont1 rho rho1).

Import Cont_on_seg_quot.

Check U : completeType.
Check U : completePseudoMetricType R.
Check U : normedModType R.
Check U : completeNormedModType R.

Notation V := (@quot_continuousFunType R U _ _ (ltW (aaDelta_subproof f ab u0 r k0 rho))).

Check V : completeNormedModType _.

Lemma Vr0 : (@restrictedV R n f a b k ab u0 r k0 rho : set V) !=set0.
Proof.
exists (pi V (cst u0)).
move => _ [y x0] <-.
suff -> : quot_continuousFunType_to_fun (\pi_(V)%qT (cst u0)) y = u0.
  exact: closed_ballxx.
rewrite /quot_continuousFunType_to_fun/=.
have /eqmod_on_itv : (repr (\pi_(V)%qT (cst u0)) = cst u0 %[mod V])%qT by rewrite reprK.
apply.
by rewrite inE.
Qed.

Notation Vr := (@restrictedV R n f a b k ab u0 r k0 rho).

Lemma closed_Vr : closed Vr.
Proof. by rewrite restrictedVball; exact: closed_ball_closed. Qed.

Let phioo : V :=
  sval (cid2 (@banach_fixed_point R V Vr
  (@contrac R n f a b ab k k0 u0 r lip2 cont1 rho)
  (@is_contraction_picard_to_cont _ n f a b ab k k0 u0 r lip2 cont1 rho rho1)
  closed_Vr
  Vr0)).

Let phiooE : phioo = (@contrac _ n f a b ab _ k0 u0 r lip2 cont1 rho) phioo.
Proof. by rewrite {}/phioo; case: cid2. Qed.

Let mu := @lebesgue_measure R.

Lemma contrac_simpl g t : Vr g ->  t \in `[a, (a + Delta f a b k u0 r rho)%E] ->
  (@contrac _ n f a b ab _ k0 u0 r lip2 cont1 rho) g t =
  u0 + (\vint[mu]_(x in `[a, t]) f x (g x))%R.
Proof.
by move=> Vrg taad; rewrite /contrac eval_mod_on_itv //; exact: picard_from_cont_simpl.
Qed.


Lemma picard_lindeloef_integral_version : is_integral_sol_on f a (a + (Delta f a b k u0 r rho)) u0 phioo.
Proof.
have Vrphioo : Vr phioo.
  by apply (svalP (cid2 (@banach_fixed_point R V Vr _
    (@is_contraction_picard_to_cont R n f _ _ ab k k0 u0 r lip2 cont1 _ rho1) closed_Vr Vr0))).
have h0 : phioo a = u0.
  rewrite phiooE.
  rewrite /contrac.
  rewrite eval_mod_on_itv; last first.
    by rewrite inE/= in_itv/= lexx (ltW (aaDelta_subproof f ab u0 r k0 rho)).
  by rewrite /picard_from_cont /= picard_to_cont_init.
split => //.
move => t tad.
rewrite {1}phiooE.
rewrite eval_mod_on_itv; last by rewrite inE.
rewrite h0.
apply : picard_from_cont_simpl.
exact Vrphioo.
Qed.

Theorem picard_lindeloeff_unique (phioo' : V) : Vr phioo' -> (forall t, t \in `[a, a+Delta f a b k u0 r rho] -> phioo' t = u0 + \vint[mu]_(x in `[a, t]) f x (phioo' x)%R) ->  phioo = phioo'.
Proof.
  move => Vrphioo' h.
  have Vrphioo : Vr phioo.
  by apply (svalP (cid2 (@banach_fixed_point R V Vr _
    (@is_contraction_picard_to_cont R n f _ _ ab k k0 u0 r lip2 cont1 _ rho1) closed_Vr Vr0))).
    
  apply (contraction_fixpoint_unique tmp Vrphioo Vrphioo') => //=.
  rewrite -(reprK  phioo').
  apply /eqquotP.
  rewrite /Quotient.equiv/=. 
  rewrite inE /submod_itv.
  apply/funext => x.
  rewrite /patch;case: ifPn => [xK | xKnot] => //.
  rewrite /quot_continuousFunType_to_fun /=.
  rewrite !fctE.
  rewrite !reprK.
  rewrite picard_from_cont_simpl //=.
  have -> : (repr phioo' x = phioo' x) by [].
  rewrite h //.
  by rewrite subrr.
Qed.

Theorem picard_lindelof_existence : phioo a = u0 /\
  {in `]a, a + Delta f a b k u0 r rho[, forall x, phioo^`() x = f x (phioo x)}.
Proof.
have Vrphioo : Vr phioo.
  by apply (svalP (cid2 (@banach_fixed_point R V Vr _
    (@is_contraction_picard_to_cont R n f _ _ ab k k0 u0 r lip2 cont1 _ rho1) closed_Vr Vr0))).
split.
- rewrite phiooE.
  rewrite /contrac.
  rewrite eval_mod_on_itv; last first.
    by rewrite inE/= in_itv/= lexx (ltW (aaDelta_subproof f ab u0 r k0 rho)).
  by rewrite /picard_from_cont /= picard_to_cont_init.
- move => t tad.
  rewrite {1}phiooE.
  apply/rowP => j.
  have altd:  a < (a + Delta f a b k u0 r rho)%E by rewrite ltrDl Delta_gt0.
  suff -> : (contrac ab k0 lip2 cont1 rho phioo)^`() t =
           (fun x0 => (u0 + (\vint[mu]_(x in `[a, x0]) f x (phioo x))%R))^`() t.
    move : (tad).
    rewrite inE /= in_itv /= => /andP[ta taDelta].
    have Fint i : mu.-integrable `[a, (a + Delta f a b k u0 r rho)%E]
        (EFin \o (fun x : R => f x (phioo x) ord0 i)).
      apply integrable_comp => //.
      by rewrite in_itv /= lexx ltW.
    have Fcont i : {for t, continuous (fun x0 : R => f x0 (phioo x0) ord0 i)}.
      rewrite inE in tad.
      apply: (within_continuous_continuous _ _ tad) => //.
      clear Fint.
      move: i.
      apply/within_continuous_coord.
      apply: (within_continuous_lipschitz _ k0 _ (u0 := u0) (r := r)).
      exact: cts_fun.
      exact: lip2_Delta.
      exact: cont1_Delta.
      exact: Vrphioo.
    have [H1 H2] := @continuous_FTC1_closed _ (fun x => f x (phioo x) ord0 j)
                    a t _ taDelta (Fint j) ta (Fcont j).
    have Hderivable : derivable (fun x : R => \vint[mu]_(x0 in `[a, x]) f x0 (phioo x0)) t 1.
      apply/(@derivable_mxP R R) => i0 i; rewrite (ord1 i0){i0}/=.
      have [?] := @continuous_FTC1_closed _ (fun x => f x (phioo x) ord0 i)
                  a t _ taDelta (Fint i) ta (Fcont i).
      rewrite /rowRintegral.
      rewrite [X in derivable X t 1](_ : _ =
          (fun x : R => \int[mu]_(x0 in `[a, x]) f x0 (phioo x0) ord0 i)); last first.
        by apply/funext => x; rewrite mxE.
      by [].
    rewrite derive1E deriveD /=; last 2 first.
      exact: derivable_cst.
      exact: Hderivable.
    rewrite -!derive1E derive1_cst add0r -H2 -/mu.
    rewrite !derive1E derive_mx//.
    rewrite mxE/=.
    congr ('D_1 _ t).
    apply/funext => t0.
    by rewrite mxE.
rewrite /contrac /picard_to_cont /picard_from_cont.
move : t tad.
apply : eq_on_itv_deriv.
move => t tad /=.
rewrite -(@picard_from_cont_simpl _ _ _ a b k _ r lip2 cont1 rho) //=.
rewrite eval_mod_on_itv => //.
by rewrite inE;apply: subset_itv_oo_cc;rewrite -inE.
Qed.

Definition picard_local_sol := phioo.

Lemma picard_lindelof_in_ball (t : R) :
  `[a, (a + Delta f a b k u0 r rho)%E] t ->
  closed_ball u0 r%:num (phioo t).
Proof.
move => taad.
have Vrphioo : Vr phioo.
  (* same proof pattern you already use several times *)
  by apply (svalP (cid2 (@banach_fixed_point R V Vr _
      (@is_contraction_picard_to_cont R n f _ _ ab k k0 u0 r lip2 cont1 _ rho1)
      closed_Vr Vr0))).

have image_phioo : phioo @` `[a, (a + Delta f a b k u0 r rho)%E]
                   `<=` closed_ball u0 r%:num.
  by move: Vrphioo.

apply image_phioo.
by exists t.
Qed.


End picard.


Lemma rowRintegral_itv_split
  {R : realType} (n : nat)
  (F : R -> 'rV[R]_n) (t0 t1 t2 : R) :
  t0 <= t1 <= t2 ->
  (forall i,  lebesgue_measure.-integrable `[t0, t2] (EFin \o (fun x : R => F x ord0 i))) ->
  \vint[lebesgue_measure]_(s in `[t0, t2]) F s
  =
  \vint[lebesgue_measure]_(s in `[t0, t1]) F s
  +
  \vint[lebesgue_measure]_(s in `[t1, t2]) F s.
Proof.
move=> /andP[t0t1 t1t2] intF.
apply/rowP=> i.
rewrite !rowRintegralE !mxE.
apply/eqP.
rewrite addrC -subr_eq.
apply/eqP.
rewrite (@Rintegral_itvB _ (fun x => F x ord0 i)  (BLeft t0) (BRight t2) t1) //=.
apply Rintegral_itv_obnd_cbnd.
apply (@integrableS _ _ _ lebesgue_measure `[t0, t2] `]t1,t2] (EFin \o (fun x => F x ord0 i))) =>//.
by apply:subset_itvScc.
Qed.

Section picard_extension.

Context {R : realType} {n : nat}.
Notation U := (@row_vector R n).

Variables (f : R -> U -> U) (a b c : R)  (u0 : U) (phi1 : R-> U) (phi2 : R -> U).
Hypothesis ab : a < b.
Hypothesis bc : b < c.
Hypothesis cont1 : {within `[a,b], continuous (fun x => f x (phi1 x))}.
Hypothesis cont2 : {within `[b,c], continuous (fun x => f x (phi2 x))}.
Hypothesis matchb : phi1 b = phi2 b.


Lemma continuous_within_ext {A B : topologicalType} (g h : A -> B) D :{in D, g =1 h} -> {within D, continuous g } -> {within D, continuous h}.
Proof.
  move => h1 h2.
  apply subspace_continuousP.
  move => x Dx.
  apply : cvg_trans.
  apply (fmap_within_eq (g := g)) => //.
  apply nbhs_filter.
  move => x' Dx' .
  symmetry.
  by apply h1.
  rewrite <-h1.
  move /subspace_continuousP : h2.
  by apply.
  by rewrite inE.
Qed.

Lemma solution_extends : is_integral_sol_on f a b u0   phi1 -> is_integral_sol_on f  b c (phi1 b) phi2 -> is_integral_sol_on f a c u0 (patch phi2 `[a,b] phi1) .
Proof.
move => [p0a p0s ] [p1a p1s].
have h0 :  patch phi2 `[a, b] phi1 a = u0.
   rewrite /patch.
   case: ifPn => [xK | xKnot] => //.
   move /negP : xKnot.
   by rewrite inE/=in_itv/=lexx ltW.
  split => //.
  rewrite h0.
  move => t tac.
  rewrite /patch.
  case: ifPn => [xK | xKnot] => /=.
- rewrite inE in xK.
  rewrite p0s // p0a.
  apply /rowP => i.
  rewrite !mxE.
  congr (_ + _)%E.
  apply eq_Rintegral => /= x xat.
  suff ->: (x \in `[a,b]) by [].
  move : xat xK.
  rewrite !inE /= !in_itv /= => /andP [xat1 xat2] /andP [tab1 tab2].
  apply /andP;split => //.
  by apply /le_trans/tab2.
have tbc : t \in `[b, c].
  move  : tac.
  move /negP : xKnot.
  rewrite !inE /= !in_itv /=.
  have /orP := le_total b t.
  case => // -> h1 /andP [h2 ->] //.
  by move : h1;rewrite h2.
  rewrite (rowRintegral_itv_split (t1 := b) (F := (fun x => f x (patch phi2 `[a,b] phi1 x)))).
rewrite inE in tbc.
rewrite p1s //.
suff  : phi2 b = u0 + \vint[lebesgue_measure]_(s in `[a, b]) f s (patch phi2 `[a, b] phi1 s).
  rewrite /GRing.add /= addmxA => ->;congr (addmx _).
  apply eq_rowRintegral => /= x xbt.
  rewrite /patch;case: ifPn => [ | ] => //.
  rewrite inE/=in_itv/= => /andP [_ xleb].
  move : xbt.
  rewrite !inE/=!in_itv/= => /andP [h _].
  suff -> : x = b by rewrite p1a.
  apply le_anti.
  by rewrite xleb /=.
rewrite p1a p0s;last by rewrite /=in_itv/=ltW//=.
rewrite p0a.
congr (_ + _)%E.
rewrite /patch.
by apply eq_rowRintegral => /= x ->.
by rewrite ltW //=; move : tbc; rewrite inE /= in_itv /= => /andP [-> _].
move => i.
have cont' : {within `[a, t], continuous (fun x => f x (patch phi2 `[a, b] phi1 x) ord0 i) }.
have -> : `[a,t] = `[a,b] `|`  `[b,t].
apply funext => x.
apply propext.
rewrite /=!in_itv/=.
split.
move => /andP [ax xt].
rewrite ax xt //=.
have /orP := le_total b x.
case => -> //=.
by right.
by left.
case.
move => /andP [-> h1] //=.
apply (@le_trans _ _ b) => //.
move : tbc.
by rewrite inE/=in_itv/= => /andP [-> _].
move => /andP [h1 ->] //=.
apply /andP;split=>//.
apply (@le_trans _ _ b) => //.
by apply ltW.
apply: (withinU_continuous (@itv_closed _ _ a b) (@itv_closed _ _ b t)).
move : i.
apply /within_continuous_coord.
have eq1 : {in `[a,b], (fun x0 => f x0 (phi1 x0)) =1 (fun x0 => f x0 (patch phi2 `[a,b] phi1 x0))}.
  move => x0 x0ab.
  by rewrite /patch x0ab.
apply (continuous_within_ext eq1).
exact: cont1. 
move : i.
apply /within_continuous_coord.
have eq2 : {in `[b,c], (fun x0 => f x0 (phi2 x0)) =1 (fun x0 => f x0 (patch phi2 `[a,b] phi1 x0))}.
  move => x0 x0ab.
  rewrite /patch;case: ifPn => [xab | xabnot] => //.
  suff -> : (x0 = b) by rewrite matchb.
  apply le_anti.
  move : x0ab xab.
  by rewrite !inE/=!in_itv/= => /andP [-> _] /andP [_ ->].
apply /continuous_subspaceW/(continuous_within_ext eq2)/cont2.
apply: subset_itvl.
move : tbc.
by rewrite inE/=in_itv/= => /andP [_ +].
apply continuous_compact_integrable => //.
exact: segment_compact.
Qed.
End picard_extension.

Section picard_local.

Context {R : realType} {n : nat}.
Notation U := (@row_vector R n).

Variables (f : R -> U -> U) (a b : R) (k : R) (u0 : U) (r : {posnum R}).
Hypothesis ab : a < b.
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (f x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous f ^~ y}}.
Local Lemma half_pos : 0 < (1 / 2 : R).
Proof. by apply divr_gt0. Qed.

Let rho : {posnum R} := PosNum half_pos.

Local Lemma rho1 : rho%:num < 1.
  rewrite /rho/=.
  rewrite ltr_pdivrMr //.
  rewrite mul1r //.
  by rewrite -subr_gt0.
Qed.


Definition local_solution := repr (picard_local_sol ab k0 lip2 cont1 rho1).
Definition ls_delta := Delta  f a b k u0 r rho.

Lemma ls_delta_ab : ls_delta <= b-a.
Proof. by rewrite /ls_delta/Delta ge_min lexx. Qed.

Lemma solution_local_solution : is_sol_on f a (a + ls_delta) u0 local_solution.
Proof.
apply /(integral_sol_iff_sol (k:=k) (r:=r)) => //.
by rewrite ltrDl Delta_gt0.
move => t td.
apply lip2.
move : td.
rewrite /=!in_itv/= => /andP [-> h] /=.
apply (le_trans h).
rewrite -lerBrDl.
exact: ls_delta_ab.
move =>  /= x xB  .
apply /continuous_subspaceW/cont1=>//.
apply: subset_itvl => //=.
rewrite bnd_simp -lerBrDl.
exact: ls_delta_ab.
rewrite /local_solution.
exact: cts_fun.
move => _ [t tad] <-.
by apply picard_lindelof_in_ball.
by apply picard_lindeloef_integral_version.
Qed.

Lemma solution_stays_in_ball : {in `[a, (a + Delta f a b k u0 r rho)%E], forall t, closed_ball u0 r%:num (local_solution t)}.
Proof.
move => t.
rewrite inE => tad.
apply (picard_lindelof_in_ball  tad).
Qed.

Lemma solution_continuous : {within `[a, (a + Delta f a b k u0 r rho)%E], continuous local_solution}.
Proof. exact: cts_fun. Qed.

Theorem picard_lindeloeff_local : exists sol delta, delta > 0 /\ is_sol_on f a (a+delta) u0 sol /\ {in `[a, a +delta], forall t, closed_ball u0 r%:num (sol t)} /\ {within `[a, a + delta], continuous sol}.
Proof.
exists (repr (picard_local_sol ab k0 lip2 cont1 rho1)).
exists (Delta f a b k u0 r rho).
split; first by apply Delta_gt0.
split; [| split].
exact: solution_local_solution.
exact: solution_stays_in_ball.
exact: solution_continuous.
Qed.
End picard_local.

Section solution_unique.
Context {R : realType} {n : nat}.
Notation U := (@row_vector R n).

Variables (f : R -> U -> U) (a b : R) (k : R) (u0 : U) (r : {posnum R}) (sol sol' : R -> U).
Hypothesis ab : a < b.
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (f x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous f ^~ y}}.
Hypothesis cont_sol :  {within `[a, b], continuous sol}.
Hypothesis cont_sol' :  {within `[a, b], continuous sol'}.


Lemma solution_unique : is_sol_on f a b u0 sol -> is_sol_on f a b u0 sol' -> {in `[a,b], sol =1 sol'}.
Proof.
rewrite -!(integral_sol_iff_sol (r := r) (k:=k)) => //.
move => h1 h2 t tab.
have /=:= (picard_lindeloeff_unique lip2 cont1 rho1).
Admitted.
End solution_unique.

Section picard_autonomous.
Context {R : realType} {n : nat}.
Notation U := (@row_vector R n).

Variables (f : U -> U)  (k : R) (u0 : U) (r : {posnum R}).
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : k.-lipschitz_B f.

Definition is_sol_autonomous t0 t1 (sol : R -> U) := sol t0 = u0 /\ {in `]t0, t1[, forall x, derivable sol x 1 /\ sol^`() x = f (sol x)}.
Definition ft (t : R) x := f x.

Lemma ft_lip2 a b:  {in `[a, b]%R, forall x, k.-lipschitz_B (ft x)}.
Proof.
  move => x abx.
  apply lip2.
Qed.

Lemma ft_cont1 a b : {in B, forall y, {within `[a, b], continuous ft ^~ y}}.
Proof.
  move => /= x Bx.
  rewrite /ft.
  apply: cst_continuous_subspace.
Qed.

Lemma autonomous_solution t0 t1 phi : is_sol_autonomous t0 t1 phi <-> is_sol_on ft t0 t1 u0 phi.
Proof. by []. Qed.

Theorem picard_lindeloef_autonomous t0 : exists sol delta, delta > 0 /\ is_sol_autonomous t0 (t0+delta) sol /\ {in `[t0, t0 + delta], forall t, closed_ball u0 r%:num (sol t)} /\ {within `[t0,t0+delta], continuous sol}.
Proof.
  have t0d : (t0 < t0 + 1).
    by rewrite -ltrBlDl subrr.
  have [sol [d [d0 [solh [solb contb]]]]]:= (picard_lindeloeff_local t0d k0 (@ft_lip2 t0 (t0+1)) (@ft_cont1 t0 (t0+1))).
  by exists sol;exists d;split.
Qed.

End picard_autonomous.

Section locally_lipschitz.

Context {R : realType} {n : nat}.
Notation U := (@row_vector R n).

Variables (f : U -> U) .

Hypothesis locally_lipschitz : forall x, exists (r k : {posnum R}),  k%:num.-lipschitz_(closed_ball x r%:num) f.
Theorem picard_lindeloeff_ll u0 t0 : exists sol delta r, delta > 0 /\ is_sol_autonomous f u0 t0 (t0+delta) sol /\ {in `[t0, t0 + delta], forall t, closed_ball u0 r (sol t)}.
Proof.
  have [/= r [k lip]]:= locally_lipschitz u0.
  have  [| sol [Delta [Delta0 [solP [scont sb]]]]] := picard_lindeloef_autonomous  _ lip t0  => //.
  by exists sol, Delta, r%:num.
Qed.

End locally_lipschitz.
