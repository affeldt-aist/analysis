(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix interval poly.
From mathcomp Require Import generic_quotient ring_quotient.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import constructive_ereal.
From mathcomp Require Import functions reals interval_inference topology.
From mathcomp Require Import prodnormedzmodule tvs normedtype landau.
From mathcomp Require Import ereal sequences derive numfun measure realfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral ftc.
(**md**************************************************************************)
(* # ODE                                                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section setInterval.
Context {R : realType}.

Definition itv_bound_swap (i : interval R) :=
match i.1 with
| BSide b0 x =>
  match i.2 with
  | BSide b1 y => (Interval (BSide b0 y) (BSide b1 x))
  | BInfty b1 => (Interval (@BInfty _ b1) (BSide b1 x))
  end
| BInfty b0 =>
  match i.2 with
  | BSide b1 y => (Interval (BSide b0 y) (@BInfty _ b0))
  | BInfty b1 => (Interval (@BInfty _ b1) (@BInfty _ b0))
  end
end.

Definition setInterval (i : interval R) :=
  [set` i] `|` [set` itv_bound_swap i].

Lemma setInterval_le (i : interval R) :
  (i.1 <= i.2)%O ->
  setInterval i = [set` i].
Proof.
rewrite /setInterval.
case i => /=.
case=> [b0 x|b0]; case=> [b1 y|b1]; case: b0; case: b1.
all: rewrite bnd_simp /itv_bound_swap.
all: rewrite ?set_itvxx ?set_itv_ybnd ?set_itv_bndNy ?setU0//=.
- move=> xy; suff : `[y, x[ = set0 by (move=> ->; rewrite setU0).
  by rewrite set_itv_ge ?bnd_simp ?le_gtF.
- rewrite le_eqVlt => /predU1P[<- |xy].
    by rewrite set_itv1 setUid.
  suff : `[y, x] = set0 by (move=> ->; rewrite setU0).
  by rewrite set_itv_ge ?bnd_simp ?lt_geF.
- move=> xy; suff : `]y, x[ = set0 by (move=> ->; rewrite setU0).
  by rewrite set_itv_ge ?bnd_simp ?le_gtF ?ltW.
- move=> xy; suff : `]y, x] = set0 by (move=> ->; rewrite setU0).
  by rewrite set_itv_ge ?bnd_simp ?le_gtF.
Qed.

Lemma setInterval_ge (i : interval R) :
  (i.2 <= i.1)%O ->
  setInterval i = [set` itv_bound_swap i].
Proof.
rewrite /setInterval.
case i => /=.
case=> [b0 x|b0]; case=> [b1 y|b1]; case: b0; case: b1.
all: rewrite bnd_simp /itv_bound_swap.
all: rewrite ?set_itvxx ?set_itv_ybnd ?set_itv_bndNy ?set0U//=.
- move=> yx; suff : `[x, y[ = set0 by (move=> ->; rewrite set0U).
  by rewrite set_itv_ge ?bnd_simp ?le_gtF.
- move=> yx; suff : `[x, y] = set0 by (move=> ->; rewrite set0U).
  by rewrite set_itv_ge ?bnd_simp ?lt_geF.
- move=> yx; suff : `]x, y[ = set0 by (move=> ->; rewrite set0U).
  by rewrite set_itv_ge ?bnd_simp ?le_gtF.
- move=> yx; suff : `]x, y] = set0 by (move=> ->; rewrite set0U).
  by rewrite set_itv_ge ?bnd_simp ?le_gtF.
Qed.

End setInterval.

(* NB: attempt by Ishiguro-san to rewrite FTC2 with a notation
  for integral that can be swapped (int_a^b = - int_b^a) *)
(* TODO: maybe not needed right now *)

Notation "`[| x , y |]" := (setInterval (Interval (BLeft x) (BRight y))).
Notation "`]| x , y |[" := (setInterval (Interval (BRight x) (BLeft y))).

Section inteitv.
Local Open Scope ereal_scope.

Context {R : realType}.
Let mu := (@lebesgue_measure R).

(*
TODO restore

Definition inteitv (a b : R) f :=
  if (a < b)%R then \int[mu]_(x in `[a, b]) f x
               else - \int[mu]_(x in `[b, a]) f x.

Definition derivable_oo_within_continuous (f : R -> R) a b :=
  {in `]|a, b|[, forall x : R, derivable f x 1} /\
  {within `[|a, b|], continuous f}.

Lemma continuous_FTC2_inteitv (f F : R -> R) a b :
  {within `[|a, b|], continuous f} ->
  derivable_oo_within_continuous F a b -> (* not derivable_oo_continuous_bnd *)
  {in `]|a, b|[%R, F^`()%classic =1 f} ->
  inteitv a b (EFin \o f) = (F b)%:E - (F a)%:E.
Proof.
have [] := ltP a b.
  move=> ab.
  rewrite setInterval_le ?bnd_simp ?ltW// => cf.
  move=> [].
  rewrite setInterval_le ?bnd_simp// => dF.
  rewrite setInterval_le ?bnd_simp ?ltW//.
  move/continuous_within_itvP => -[] // _ Fa Fb dFf.
  rewrite /inteitv ab.
  rewrite (@continuous_FTC2 _ f F)//.
    by split => // x xab; apply: dF; rewrite inE/=.
  by move=> x xab; apply: dFf; rewrite inE/=.
rewrite le_eqVlt => /predU1P[-> |ba].
  by rewrite /inteitv ltxx set_itv1 integral_set1 oppe0 subee.
rewrite setInterval_ge ?bnd_simp// => cf.
move=> [].
rewrite setInterval_ge ?bnd_simp ?ltW// => dF.
rewrite setInterval_ge ?bnd_simp//.
move/continuous_within_itvP => -[] // _ Fa Fb dFf.
rewrite /inteitv ifF; last first.
  by apply/negP/negP; rewrite le_gtF ?ltW.
rewrite (@continuous_FTC2 _ f F)// ?oppeB 1?addeC//.
  by split => // x xab; apply: dF; rewrite inE/=.
by move=> x xab; apply: dFf; rewrite inE/=.
Qed.
*)

End inteitv.

(*
Reserved Notation "\int [ mu ]_( x $ a ~ b ) F"
  (at level 36, F at level 36, mu at level 10,
  format "'[' \int [ mu ]_( x $ a ~ b )  '/  '  F ']'").
Notation "\int [ mu ]_( x $ a ~ b ) f" :=
  (inteitv a b (fun x => f)).
*)

(* We define the type of functions that are continuous over a closed interval *)

HB.mixin Record isContFunSeg (R : realType) (a b : R) (f : R -> R) :=
  { contFunSeg : {within `[a, b], continuous f} }.

#[short(type="contFunSegType")]
HB.structure Definition ContFunSeg (R : realType) (a b : R) :=
  {f of isContFunSeg R a b f & @Fun R R `[a, b] [set: R] f}.

(* TODO: factory Lmodule is normed *)

HB.instance Definition _ (R : realType) (a b : R) :=
  gen_eqMixin (contFunSegType a b).
HB.instance Definition _ (R : realType) (a b : R) :=
  gen_choiceMixin (contFunSegType a b).

Section contfunseg_pred.
Context {R : realType}.
Variables a b : R.

Definition contfunseg : {pred R -> R}
  := mem [set f | squashed (@ContFunSeg R a b f)].
Definition contfunseg_key : pred_key contfunseg. Proof. exact. Qed.
Canonical contfunseg_keyed := KeyedPred contfunseg_key.

End contfunseg_pred.

(* NB(rei): was this just motivated by generic predicates such as rpredD?
or more generally by stability of "cont. over [a,b]"?
anyway, maybe not needed right now *)
Section contfun.
Context {R : realType}.
Variables a b : R.
Notation T := (contFunSegType a b).

Section Sub.
Context (f : R -> R) (fP : f \in contfunseg a b).

Definition contfunseg_Sub_subproof := unsquash (set_mem fP).
#[local] HB.instance Definition _ := contfunseg_Sub_subproof.
 Definition contfunseg_Sub : contFunSegType a b :=  {| ContFunSeg.sort := f; ContFunSeg.class := contfunseg_Sub_subproof |}.

End Sub.

Lemma contfunseg_rect (K : T -> Type) :
  (forall f (Pf : f \in contfunseg a b), K (contfunseg_Sub Pf)) ->
  forall u : T, K u.
Proof.
move=> Ksub [f Pf].
rewrite (_ : K _  = K (contfunseg_Sub (mem_set (squash Pf))))//.
rewrite /contfunseg_Sub /contfunseg_Sub_subproof /= mem_setK.
rewrite /unsquash; case : cid => // /= => x _.
congr (K (ContFunSeg.Pack _)).
move : Pf x => [[H1] [H2]] [[?] [?]].
by rewrite (Prop_irrelevance H1) (Prop_irrelevance H2).
Qed.

Lemma contfunseg_valP f (Pf : f \in contfunseg a b) :
  contfunseg_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ := isSub.Build _ _ T contfunseg_rect contfunseg_valP.

Lemma contfunseg_eqP (f g : contFunSegType a b) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; exact/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of contFunSegType a b by <:].

Lemma cst_is_fun x : @isFun R R `[a, b] [set: R] (cst x).
Proof. by constructor. Qed.

HB.instance Definition _ x := (cst_is_fun x).

Lemma cst_continuous_subspace (r : R) :
  {within `[a, b], continuous (cst r)}.
Proof.
apply: continuous_subspaceT.
exact: cst_continuous.
Qed.

HB.instance Definition _ x := isContFunSeg.Build R a b (@cst R R x)
  (@cst_continuous_subspace x).

End contfun.

Section contfun_realType.
Context {R : realType}.
Variables a b : R.

(*
HB.instance Definition _ := @isContFun.Build R a b
_ _ _ rT
  (@normr rT rT) (@normr_measurable rT setT).
*)

End contfun_realType.

(*
Section contfun_measurableType.
Context {d1} {T1 : measurableType d1} {d2} {T2 : measurableType d2}
  {d3} {T3 : measurableType d3}.
Variables (f : {contfun T2 >-> T3}) (g : {contfun T1 >-> T2}).

Lemma measurableT_comp_subproof : measurable_fun setT (f \o g).
Proof. exact: measurableT_comp. Qed.

HB.instance Definition _ := isMeasurableFun.Build _ _ _ _ (f \o g)
  measurableT_comp_subproof.

End contfun_measurableType.
*)

Section ring.
Context {R : realType} (a b : R).

Lemma contfunseg_subring_closed : subring_closed (@contfunseg R a b).
Proof.
split=> [|f g|f g]; rewrite !inE/=.
- apply: squash.
  exact: ContFunSeg.class.
- move=> /unsquash cf /unsquash cg.
  apply: squash.
  pose f' : contFunSegType a b  := HB.pack f cf.
  pose g' : contFunSegType a b  := HB.pack g cg.
  rewrite [f]/(f' : _ -> _).
  rewrite [g]/(g' : _ -> _).
  move: {f g cf cg} f' g' => f g.
  have isfun_fg : @isFun R R `[a, b] [set: R] (f \- g) by constructor.
  have iscontfun_fg : @isContFunSeg R a b (f \- g).
    constructor.
    move=> x.
    by apply: continuousB; exact: contFunSeg.
  by split.
- move=> /unsquash cf /unsquash cg.
  apply: squash.
  pose f' : contFunSegType a b  := HB.pack f cf.
  pose g' : contFunSegType a b  := HB.pack g cg.
  rewrite [f]/(f' : _ -> _).
  rewrite [g]/(g' : _ -> _).
  move: {f g cf cg} f' g' => f g.
  have isfun_fg : @isFun R R `[a, b] [set: R] (f \- g) by constructor.
  have iscontfun_fg : @isContFunSeg R a b (f \* g).
    constructor.
    move=> x.
    by apply: (@continuousM _ (subspace `[a, b])); exact: contFunSeg.
  by split.
Qed.

HB.instance Definition _ := GRing.isSubringClosed.Build _
  (@contfunseg R a b) contfunseg_subring_closed.
HB.instance Definition _ := [SubChoice_isSubComRing of @contFunSegType R a b by <:].

Lemma contfun_scaler_closed : GRing.scaler_closed (@contfunseg R a b).
Proof.
move=> r f; rewrite 2!inE/=.
move/unsquash => [[cf _]].
apply: squash.
split => //.
constructor.
move=> x.
apply: continuousZ.
  exact: cst_continuous.
exact: cf.
Qed.

HB.instance Definition _ := GRing.isScaleClosed.Build _ _
  (@contfunseg R a b) contfun_scaler_closed.

Fail Check @contFunSegType R a b : lmodType _.

HB.instance Definition _ :=
  [SubZmodule_isSubLmodule of @contFunSegType R a b by <:].

Check @contFunSegType R a b : lmodType _.

(*
Implicit Types (f g : {contfun aT >-> rT}).

Lemma contfun0 : (0 : {contfun aT >-> rT}) =1 cst 0 :> (_ -> _). Proof. by []. Qed.
Lemma contfun1 : (1 : {contfun aT >-> rT}) =1 cst 1 :> (_ -> _). Proof. by []. Qed.
Lemma contfunN f : - f = \- f :> (_ -> _). Proof. by []. Qed.
Lemma contfunD f g : f + g = f \+ g :> (_ -> _). Proof. by []. Qed.
Lemma contfunB f g : f - g = f \- g :> (_ -> _). Proof. by []. Qed.
Lemma contfunM f g : f * g = f \* g :> (_ -> _). Proof. by []. Qed.
Lemma contfun_sum I r (P : {pred I}) (f : I -> {contfun aT >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma contfun_prod I r (P : {pred I}) (f : I -> {contfun aT >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma contfunX f n : f ^+ n = (fun x => f x ^+ n) :> (_ -> _).
Proof. by apply/funext=> x; elim: n => [|n IHn]//; rewrite !exprS contfunM/= IHn. Qed.

HB.instance Definition _ f g := MeasurableFun.copy (f \+ g) (f + g).
HB.instance Definition _ f g := MeasurableFun.copy (\- f) (- f).
HB.instance Definition _ f g := MeasurableFun.copy (f \- g) (f - g).
HB.instance Definition _ f g := MeasurableFun.copy (f \* g) (f * g).

Definition mindic (D : set aT) of measurable D : aT -> rT := \1_D.

Lemma mindicE (D : set aT) (mD : measurable D) :
  mindic mD = (fun x => (x \in D)%:R).
Proof. by rewrite /mindic funeqE => t; rewrite indicE. Qed.

HB.instance Definition _ D mD := @isMeasurableFun.Build _ _ aT rT (mindic mD)
  (@measurable_indic _ aT rT setT D mD).

Definition indic_contfun (D : set aT) (mD : measurable D) : {contfun aT >-> rT} :=
  mindic mD.

HB.instance Definition _ k f := MeasurableFun.copy (k \o* f) (f * cst k).
Definition scale_contfun k f : {contfun aT >-> rT} := k \o* f.

Lemma max_contfun_subproof f g : @isMeasurableFun d _ aT rT (f \max g).
Proof. by split; apply: measurable_maxr. Qed.

HB.instance Definition _ f g := max_contfun_subproof f g.

Definition max_contfun f g : {contfun aT >-> _} := f \max g.

End ring.
Arguments indic_contfun {d aT rT} _.
(* TODO: move earlier?*)
#[global] Hint Extern 0  (measurable_fun _ (\1__ : _ -> _)) =>
  (exact: measurable_indic ) : core.

Section sfun_pred.
Context {d} {aT : sigmaRingType d} {rT : realType}.
Definition sfun : {pred _ -> _} := [predI @contfun _ _ aT rT & ficontfun].
Definition sfun_key : pred_key sfun. Proof. exact. Qed.
Canonical sfun_keyed := KeyedPred sfun_key.
Lemma sub_sfun_contfun : {subset sfun <= contfun}. Proof. by move=> x /andP[]. Qed.
Lemma sub_sfun_ficontfun : {subset sfun <= ficontfun}. Proof. by move=> x /andP[]. Qed.
End sfun_pred.

Section sfun.
Context {d} {aT : measurableType d} {rT : realType}.
Notation T := {sfun aT >-> rT}.
Notation sfun := (@sfun _ aT rT).
Section Sub.
Context (f : aT -> rT) (fP : f \in sfun).
Definition sfun_Sub1_subproof :=
  @isMeasurableFun.Build d _ aT rT f (set_mem (sub_sfun_contfun fP)).
#[local] HB.instance Definition _ := sfun_Sub1_subproof.
Definition sfun_Sub2_subproof :=
  @FiniteImage.Build aT rT f (set_mem (sub_sfun_ficontfun fP)).

Import HBSimple.

#[local] HB.instance Definition _ := sfun_Sub2_subproof.
Definition sfun_Sub := [sfun of f].
End Sub.

Lemma sfun_rect (K : T -> Type) :
  (forall f (Pf : f \in sfun), K (sfun_Sub Pf)) -> forall u : T, K u.
Proof.
move=> Ksub [f [[Pf1] [Pf2]]]; have Pf : f \in sfun by apply/andP; rewrite ?inE.
have -> : Pf1 = set_mem (sub_sfun_contfun Pf) by [].
have -> : Pf2 = set_mem (sub_sfun_ficontfun Pf) by [].
exact: Ksub.
Qed.

Import HBSimple.

Lemma sfun_valP f (Pf : f \in sfun) : sfun_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ := isSub.Build _ _ T sfun_rect sfun_valP.

Lemma sfuneqP (f g : {sfun aT >-> rT}) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of {sfun aT >-> rT} by <:].

(* NB: already instantiated in cardinality.v *)
HB.instance Definition _ x : @FIcontfun aT rT (cst x) := FIcontfun.on (cst x).

Definition cst_sfun x : {sfun aT >-> rT} := cst x.

Lemma cst_sfunE x : @cst_sfun x =1 cst x. Proof. by []. Qed.

End sfun.

(* a better way to refactor function stuffs *)
Lemma fctD (T : pointedType) (K : ringType) (f g : T -> K) : f + g = f \+ g.
Proof. by []. Qed.
Lemma fctN (T : pointedType) (K : ringType) (f : T -> K) : - f = \- f.
Proof. by []. Qed.
Lemma fctM (T : pointedType) (K : ringType) (f g : T -> K) : f * g = f \* g.
Proof. by []. Qed.
Lemma fctZ (T : pointedType) (K : ringType) (L : lmodType K) k (f : T -> L) :
   k *: f = k \*: f.
Proof. by []. Qed.
Arguments cst _ _ _ _ /.
Definition fctWE := (fctD, fctN, fctM, fctZ).

Section ring.
Context d (aT : measurableType d) (rT : realType).

Lemma sfun_subring_closed : subring_closed (@sfun d aT rT).
Proof.
by split=> [|f g|f g]; rewrite ?inE/= ?rpred1//;
   move=> /andP[/= mf ff] /andP[/= mg fg]; rewrite !(rpredB, rpredM).
Qed.

HB.instance Definition _ := GRing.isSubringClosed.Build _ sfun
  sfun_subring_closed.
HB.instance Definition _ := [SubChoice_isSubComRing of {sfun aT >-> rT} by <:].

Implicit Types (f g : {sfun aT >-> rT}).

Import HBSimple.

Lemma sfun0 : (0 : {sfun aT >-> rT}) =1 cst 0. Proof. by []. Qed.
Lemma sfun1 : (1 : {sfun aT >-> rT}) =1 cst 1. Proof. by []. Qed.
Lemma sfunN f : - f =1 \- f. Proof. by []. Qed.
Lemma sfunD f g : f + g =1 f \+ g. Proof. by []. Qed.
Lemma sfunB f g : f - g =1 f \- g. Proof. by []. Qed.
Lemma sfunM f g : f * g =1 f \* g. Proof. by []. Qed.
Lemma sfun_sum I r (P : {pred I}) (f : I -> {sfun aT >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma sfun_prod I r (P : {pred I}) (f : I -> {sfun aT >-> rT}) (x : aT) :
  (\sum_(i <- r | P i) f i) x = \sum_(i <- r | P i) f i x.
Proof. by elim/big_rec2: _ => //= i y ? Pi <-. Qed.
Lemma sfunX f n : f ^+ n =1 (fun x => f x ^+ n).
Proof. by move=> x; elim: n => [|n IHn]//; rewrite !exprS sfunM/= IHn. Qed.

HB.instance Definition _ f g := MeasurableFun.copy (f \+ g) (f + g).
HB.instance Definition _ f g := MeasurableFun.copy (\- f) (- f).
HB.instance Definition _ f g := MeasurableFun.copy (f \- g) (f - g).
HB.instance Definition _ f g := MeasurableFun.copy (f \* g) (f * g).
*)

End ring.

  (* TODO  rewrite rmorphD should work declare patch as a morphism: erestrictD, erestrictM,  *)
Lemma restrictD [T : pointedType] [R : realFieldType] (D : set T) (f g : T -> R) :
  (f \+ g)%R \_ D = (f \_ D \+ g \_ D)%R.
Proof.
rewrite /patch.
apply/funext => /= x.
case: ifPn => xD.
  by rewrite /GRing.add_fun xD.
by rewrite /GRing.add_fun (negbTE xD)// addr0.
Qed.

Lemma restrictM [T : pointedType] [R : realFieldType] (D : set T) (f g : T -> R) :
  (f \* g)%R \_ D = (f \_ D \* g \_ D)%R.
Proof.
rewrite /patch.
apply/funext => /= x.
case: ifPn => xD.
  by rewrite /GRing.mul_fun xD.
by rewrite /GRing.mul_fun (negbTE xD)// mulr0.
Qed.

Section ideal_definition.
Context {R : realType} (a b : R) (ab : a <= b).

Local Notation T := (contFunSegType a b).

#[using="ab"]
Definition ideal_itv : {pred T} := [pred f : T | f \_ `[a, b] == cst 0].

Lemma idealr_closed_itv : idealr_closed ideal_itv.
Proof.
split => /=.
- rewrite inE/=.
  apply/funext => x.
  rewrite patchE.
  by case: ifPn.
- rewrite inE/=.
  apply/negP => /eqP /(congr1 (@^~ a))/=.
  rewrite patchE ifT//=.
    by apply/eqP; rewrite oner_eq0.
  by rewrite inE/= in_itv/= lexx.
- move=> f u v.
  rewrite !inE => u0 v0.
  rewrite restrictD/= v0.
  rewrite restrictM u0.
  rewrite /GRing.mul_fun/= fctE.
  under eq_fun do rewrite mulr0.
  rewrite /GRing.add_fun.
  by under eq_fun do rewrite add0r.
Qed.

HB.instance Definition _ := isIdealr.Build _ ideal_itv idealr_closed_itv.

Check ideal_itv : zmodClosed _.

End ideal_definition.

Section contFunSeg_quotient.
Context {R : realType} (a b : R).

(*Definition eq_seg (f g : contFunSegType a b) := `[< {in `[a, b], f =1 g} >].

Let eq_seg_refl : reflexive eq_seg.
Proof. by move=> f; apply/asboolP => r. Qed.

Let eq_seg_sym : symmetric eq_seg.
Proof. by move=> f g; apply/idP/idP => /asboolP h; apply/asboolP => r /h. Qed.

(* TODO: wait for quotient *)
Let eq_seg_trans : transitive eq_seg.
Proof.
by move=> f g h /asboolP fg /asboolP gh; apply/asboolP => r rab; rewrite fg// gh.
Qed.

Canonical eq_seg_canonical :=
  EquivRel eq_seg eq_seg_refl eq_seg_sym eq_seg_trans.*)

Local Open Scope quotient_scope.
Context (ab : a <= b).

(*Definition quot_contFunSegType : Type := {eq_quot eq_seg}.*)
Definition quot_contFunSegType := {ideal_quot (ideal_itv ab)}.
(*Definition quot_contFunSegType : quotType (contFunSegType a b) := {ideal_quot (ideal_itv ab)}.*)

(*HB.instance Definition _ := Choice.on quot_contFunSegType.
HB.instance Definition _ := EqQuotient.on quot_contFunSegType.*)

HB.instance Definition _ := NzRingQuotient.on quot_contFunSegType.

About ode_quot_contFunSegType__canonical__ring_quotient_NzRingQuotient.

Definition quot_contFunSegType_to_fun (f : quot_contFunSegType) : R -> R := repr f.
Coercion quot_contFunSegType_to_fun : quot_contFunSegType >-> Funclass.

Lemma eq_segP (f g : quot_contFunSegType) :
  reflect ({in `[a, b], f =1 g}) (f == g %[mod quot_contFunSegType]).
Proof.
apply/(iffP idP); rewrite eqmodE//=.
  rewrite /Quotient.equiv.
  rewrite inE.
  move=> fgab0 x xab.
  move/(congr1 (fun z => z x)) : fgab0.
  by rewrite patchE xab => /eqP; rewrite subr_eq0/= => /eqP.
move=> abfg.
rewrite /Quotient.equiv inE; apply/funext => y.
rewrite patchE.
case: ifPn => //= yab.
rewrite !fctE.
apply/eqP; rewrite subr_eq0; apply/eqP.
exact: abfg.
Qed.

End contFunSeg_quotient.

(*Section ring_structure_on_quotient_classes.
Context {R : realType} (a b : R) (ab : a <= b).

Local Notation T := (quot_contFunSegType ab).

Local Open Scope quotient_scope.

Let zero' : T := \pi_T (cst 0).

Let add' (f g : T) : T := \pi_T (repr f + repr g).

(*
Lemma pi_add' : {morph \pi_T : x y / x + y >-> (add' x y)}.
Proof.
move=> x y.
rewrite /add'.
have H u : repr (\pi_T u) = u %[mod T] by rewrite reprK.
rewrite /add'/=.
apply/eqmodP => /=.
have /eqmodP/asboolP/= Hx := H x.
have /eqmodP/asboolP/= Hy := H y.
apply/asboolP => z zab.
rewrite [LHS]/(x z + y z) /=.
by rewrite -Hx// -Hy//.
Qed.
(* NB: to be able to use piE *)
Canonical pi_add'_morph := PiMorph2 pi_add'.
*)

Let addrA' : associative (@GRing.add T).
Proof.
elim/quotW => -[f1 f2]. elim/quotW => -[f3 f4]. elim/quotW => -[e f].
rewrite !piE /=.
by rewrite addrA.
Qed.

Let addrC' : commutative add'.
Proof.
(* TODO: on the model of addrA' *)
Admitted.

Let add0r' : left_id zero' add'.
Proof.
(* TODO: on the model of addrA' *)
Admitted.

HB.instance Definition _ := @GRing.isNmodule.Build
  T zero' add' addrA' addrC' add0r'.

Let opp' : T -> T.
Proof.
(* TODO: on the model of addrA' *)
Admitted.

Let addNr' : left_inverse zero' opp' add'.
Proof.
(* TODO: on the model of addrA' *)
Admitted.

HB.instance Definition _ := @GRing.isZmodule.Build T
  zero' opp' add' addrA' addrC' add0r' addNr'.

End ring_structure_on_quotient_classes.
*)

Section zmodule_normed.
Context {R : realType} (a b : R) (ab : a <= b).

Definition infty_norm0 (f : {fun `[a, b]%classic >-> [set: R]}) :=
  sup ((Num.norm \o f) @` `[a, b]%classic).

Local Notation V := (quot_contFunSegType ab).

Definition infty_norm (f : V) := infty_norm0 (repr f).

Local Notation norm := infty_norm.

Lemma contFunSeg_norm0 (x : V) : b < a -> norm x = 0.
Proof.
move=> ba.
rewrite /norm /infty_norm0 [X in sup X](_ : _ = set0) ?sup0//.
rewrite -subset0 => /= f/= [r]; rewrite in_itv/= => /andP[ar rb] _.
by move: ba; rewrite ltNge (le_trans ar rb).
Qed.

Local Open Scope quotient_scope.

(* TODO: wait for quotient *)
Lemma contFunSeq_eq (f g : quot_contFunSegType ab) :
  f = g <-> {in `[a, b], repr f =1 repr g}.
Proof.
split=> [->//|fg].
Abort.

Local Lemma normr_has_sup (x : contFunSegType a b) :
  has_sup [set (normr \o x) x0 | x0 in `[a, b]].
Proof.
rewrite /has_sup; split.
  exists (`|x a|)=> /=.
  by exists a => //; rewrite in_itv/= lexx ab.
pose abs_x := normr \o x.
have [aeqb | aneqb] := eqVneq a b.
  subst b.
  exists (`| x a |) => z/= [r].
  rewrite in_itv/=.
  by rewrite -eq_le => /eqP <- <-.
have ab' : a < b.
  by rewrite lt_neqAle aneqb ab.
have cont_abs_x : {within `[a, b], continuous abs_x}.
  have /continuous_within_itvP : {within `[a, b], continuous x} by exact: contFunSeg.
  move=> /(_ ab')[H1 H2 H3].
  rewrite /abs_x.
  apply/continuous_within_itvP => //.
  split.
  - move=> y yab.
    apply: continuous_comp.
      exact: H1.
    exact: norm_continuous.
  - rewrite /=.
    apply: cvg_comp.
      exact: H2.
    exact: norm_continuous.
  - rewrite /=.
    apply: cvg_comp.
      exact: H3.
    exact: norm_continuous.
have [c cab abc] := @EVT_max _ abs_x _ _ ab cont_abs_x.
exists (`|x c|) => /= _ /= [z zab] <-.
exact: abc.
Qed.

Let normr_repr_has_sup (x : V) :
  has_sup [set (normr \o repr x) x0 | x0 in `[a, b]].
Proof. by apply normr_has_sup. Qed.

Lemma eqmod_on_itv f g :
  f = g %[mod V] -> {in `[a,b], f =1 g}.
Proof.
  move => /eqmodP + x xab.
  rewrite /Quotient.equiv_equiv /Quotient.equiv /= /ideal_itv /=.
  move/set_mem =>  H.
  apply subr0_eq.
  rewrite -[RHS]/(cst 0 x) -H patchE; case : ifPn => //. 
  by rewrite xab.
Qed.

Lemma infty_norm_itv_eq (f g :  contFunSegType a b):  {in `[a,b], f =1 g} -> infty_norm0 f = infty_norm0 g.
Proof.
  move => inab.
  rewrite /infty_norm0 /=;congr (sup _).
  apply/seteqP; split; move => _ [ y ? <- ]; exists y; by rewrite //= inab // inE.
 Qed.

Local Lemma sup_le A (x : R) : has_sup A -> A x -> x <= sup A.
Proof.
  move=> supA Ax.
  have /sup_upper_bound := supA.
  by move/(_ x Ax).
Qed.

Lemma ler_infty_normD (x y : V) : norm (x + y) <= norm x + norm y :> R.
Proof.
  rewrite /norm/= -sup_sumE//; last 2 first.
  exact: normr_repr_has_sup.
  exact: normr_repr_has_sup.
  apply: le_sup.
  - move=> A -[s sab] <-{A}.
    rewrite /down/=.
    eexists.
    split.
    exists (`|repr x s|).
    by exists s.
    exists (`|repr y s|).
    by exists s.
     reflexivity.
    suff  -> : (repr (x + y) s = repr x s + repr y s) by exact: ler_normD.
    suff /eqmod_on_itv ->: (repr (x+y) = repr x + repr y %[mod V]) =>//.
    by rewrite inE.
    rewrite Quotient.pi_add !reprK //.
   - by apply normr_repr_has_sup.
   - rewrite /has_sup.
     split.
     + exists ((normr \o repr x) a + (normr \o repr y) a)=> /=.
       exists ((normr \o repr x) a) => //; [exists a => //; rewrite in_itv/= lexx ab // | ].
       exists ((normr \o repr y) a) => //; exists a => //; rewrite in_itv/= lexx ab //.
    + rewrite /has_ubound.
      exists (sup [set (normr \o repr x) x0 | x0 in `[a, b]] + sup [set (normr \o repr y) x0 | x0 in `[a, b]]).
      apply ubP => _ [x0 xs] [y0 ys] <-.
      apply lerD;apply sup_le => //.
Qed.

Lemma infty_normr0_eq0 (x : V) : norm x = 0 -> x = 0.
Proof.
  rewrite /norm/infty_norm0 /=.
  move => H.
  rewrite -(reprK x)  -(reprK 0).
  apply /eqquotP.
  rewrite /Quotient.equiv_equiv/Quotient.equiv/=/ ideal_itv/=.
  apply mem_set; rewrite /cst /=.
  apply funext => x0 /=.
  rewrite patchE.
  case : ifPn => // /set_mem in_itv.
  rewrite /GRing.opp/GRing.add /=.
  have -> : ( {in `[a,b], repr (0 : V) =1 (0 : contFunSegType a b)}) => //.
  apply /eqmod_on_itv.
  rewrite reprK /GRing.zero /= /Quotient.zero /= -lock /= //.
  rewrite subr0.
  apply /eqP;rewrite -normr_le0.
  have := (sup_upper_bound (normr_repr_has_sup x)).
  rewrite H /ubound /=.
  move => H0.
  apply H0.
  exists x0 => //.
  by rewrite inE.
Qed.

Local Lemma has_sup_Mn (A : set R) n: has_sup A -> has_sup [set x *+n | x in A ].
Proof.
  move => [-[] x Ax [y uby]].
  split; first by exists (x *+ n);exists x.
  exists (y *+ n).
  move => _ [y0 Ay0 <-] .
  rewrite lerMn2r.
  by apply /orP;right;apply uby.
Qed.

Local Lemma sup_Mn (A : set R) n: has_sup A -> sup [set x *+n | x in A ] = sup A *+ n.
Proof.
move => ex_sup.
elim: n.
rewrite !mulr0n -(sup1 0);congr (sup _).
apply eq_set => /= z ;apply propext; split => [[x _ <- ] | ->]; rewrite ?normr0 => //.
case : ex_sup => -[] x Ax _;by exists x.
move => n IH.
rewrite !mulrS.
rewrite -IH /infty_norm0.
rewrite -sup_sumE => //; last by apply has_sup_Mn.
apply /eqP.
rewrite eq_le.
apply /andP;split; last first.
apply sup_le_ub.
case : ex_sup => -[] x Ax _;exists (x+x *+ n); exists x => //.
exists (x *+ n) => //.
by exists x.
move => _ /= [x Ax [_ [x0 Ax0] <-] <-].
have /orP[ xx0| xx0] := le_total x x0.
rewrite (@le_trans _ _ (x0 *+ n.+1)) //.
by rewrite mulrS lerD2r.
apply sup_le; first by apply has_sup_Mn.
by exists x0.
rewrite (@le_trans _ _ (x *+ n.+1)) //.
rewrite mulrS lerD2l.
by rewrite lerMn2r xx0 orbT.
apply sup_le; first by apply has_sup_Mn.
by exists x.
apply le_sup.
apply: subset_trans; last by apply: le_down.
move => _ [x Ax <-] /=.
exists x => //.
exists (x *+ n)=> //.
exists x => //.
by rewrite mulrS.
case : ex_sup => -[] x Ax _.
exists (x *+ n.+1)=> //=.
by exists x.
case : ex_sup => -[] x Ax [y uby].
split.
exists (x + x *+ n).
exists x => //.
exists (x *+ n) => //.
by exists x.
exists (y + y *+ n) => _ [x0 Ax0 [_ [x1 Ax1] <-] <-].
apply lerD;first by apply uby.
rewrite lerMn2r; apply /orP.
by right;apply uby.
Qed.

Local Lemma infty_norm0_eq0 : infty_norm0 (0 : contFunSegType a b) = 0.
Proof.
  rewrite /infty_norm0.
  rewrite -(sup1 0).
  f_equal.
  apply eq_set => /= z ;apply propext; split => [[x _ <- ] | ->]; rewrite ?normr0 => //.
  exists a; by [rewrite bound_itvE | rewrite normr0 ].
Qed.

Local Lemma infty_norm0rMn (x : contFunSegType a b) n : infty_norm0 (x *+ n) = infty_norm0 x *+ n.
Proof.
rewrite /infty_norm0.
rewrite -sup_Mn.
rewrite image_comp //=.
congr (sup _).
apply eq_imagel.
move => z _ /=.
rewrite -normrMn /=.
have /(congr1 (fun a => a z)) <- := (natmulfctE x n).
congr (normr (_ z)).
(* This is strange *)
elim: n x => //=.
move => n IH x.
by rewrite !mulrS -IH.
by apply normr_has_sup.
Qed.

Lemma infty_normrMn (x : V) n : norm (x *+ n) = norm x *+ n.
Proof.
  rewrite /norm.
  rewrite -infty_norm0rMn.
  apply infty_norm_itv_eq.
  move => x0 in_itv.
  suff /eqmod_on_itv ->: (repr (x *+ n) = repr x *+ n %[mod V]) =>//.
  elim n; [rewrite !mulr0n // reprK /GRing.zero /= /Quotient.zero /= -lock // | ].
  move => n' IHn'; rewrite reprK !mulrS.
  rewrite reprK in IHn'.
  rewrite Quotient.pi_add reprK.
  by move : IHn' <-.
Qed.

Let qnorm_piE' x : norm (\pi_V x) = infty_norm0 x.
Proof.
  rewrite /norm /=.
  have /eqmod_on_itv Heq : repr (\pi_V x) = x %[mod V] by rewrite reprK.
  by apply infty_norm_itv_eq.
Qed.

Lemma infty_normrN (x : V) : norm (- x) = norm x.
Proof.
  rewrite -(reprK x) /GRing.opp /= -Quotient.pi_opp !qnorm_piE' /norm /infty_norm0.
  f_equal.
  apply eq_set => /= x0.
  apply propext;split => [[x1 in_itv] | [x1 in_itv]] H;exists x1 =>//.
  rewrite -normrN //.
  rewrite normrN //.
Qed.
(* TODO: dev the theory of sup following the theory of ess_sup *)

Fail Check V : normedZmodType R.

HB.instance Definition _ := @Num.Zmodule_isNormed.Build R V
  norm ler_infty_normD infty_normr0_eq0 infty_normrMn infty_normrN.

Lemma qnorm_piE x : `|\pi_V x| = infty_norm0 x.
Proof. by rewrite /Num.norm /= qnorm_piE'. Qed.

Check V : normedZmodType R.

Check (pseudoMetric_normed V) : pseudoMetricType R.
Check (pseudoMetric_normed V) : normedZmodType R.

Fail Check (pseudoMetric_normed V) : normedModType R.

End zmodule_normed.

HB.about Lmodule_isNormed.

(* HB.factory Record Lmodule_isNormed (R : realType) M *)
(*     of GRing.Lmodule R M := { *)
(*  norm : M -> R; *)
(*  ler_normD : forall x y, norm (x + y) <= norm x + norm y ; *)
(* (* normrMn : forall x n, norm (x *+ n) = norm x *+ n ;*) *)
(*  normrN : forall x, norm (- x) = norm x ; *)
(*  normrZ : forall (l : R) (x : M), norm (l *: x) = `|l| * norm x ; *)
(*  normr0_eq0 : forall x : M, norm x = 0 -> x = 0 *)
(* }. *)

(* HB.builders Context R M of Lmodule_isNormed R M. *)

(* HB.about Num.Zmodule_isNormed.Build. *)
(* Lemma normrMn x n : norm (x *+ n) = norm x *+ n. *)
(* Proof. *)
(* move: x. *)
(* rewrite /=. *)
(* Admitted. (* from normrZ *) *)

(* HB.instance Definition _ := Num.Zmodule_isNormed.Build *)
(*   R M ler_normD normr0_eq0 normrMn normrN. *)

(* Check M : normedZmodType R. *)

(* Check (@pseudometric R M). *)

(* HB.saturate pseudometric. *)

(* Check (pseudometric M : pseudoMetricType R). *)

(* HB.instance Definition _ := PseudoMetric.copy M (pseudometric M). *)
(* HB.instance Definition _ := isPointed.Build M 0. *)

(* Lemma whatever : NormedZmod_PseudoMetric_eq R M. *)
(* Proof. *)
(* by constructor. *)
(* Qed. *)

(* HB.instance Definition _ := whatever. *)

(* Lemma coucou : PseudoMetricNormedZmod_Lmodule_isNormedModule R M. *)
(* Proof. *)
(* constructor. *)
(* exact: normrZ. *)
(* Qed. *)

(* HB.instance Definition _ := coucou. *)
(* HB.instance Definition _ := isPointed.Build M 0. *)

(* Check M : normedModType R. *)

(* HB.end. *)

(* The goal is to prove Picard-Lindel{\"o}of's theorem.

   For the proof of Picard-Linderl{\"o}f theorem, we should give an
   instance picard_to_cont : {fun U >-> U} for some subset U of
   contFunSegType where U satisfies
   U `<=` `[- d, d]
   g @` U `<=` `[- d, d]

   For that purpose, we define a function (picard_to_cont) that maps a
   function continuous over a segment to a function continuous over
   the same segment.

   This function is defined by integration.

   `limn n picard_to_cont (cst 0)' is solution of the ODE.
 *)

Section intermediate_lemma.
Context {R : realType}.
Variable d0 : {posnum R}.
Local Notation d := d0%:num.

Local Lemma imageg_closure (g : R -> R) : {within `[-d,d], continuous g} ->
  g @``]-d, d[ `<=` `]- d, d[ -> g @` `[-d, d] `<=` `[- d, d].
Proof.
move => cont_g imageg _ [] x /= + <-.
rewrite in_itv /= => /andP[+ +]/=.
have /continuous_within_itvP  :=  cont_g.
rewrite gtrN //; move => [] //=.
move => gcont gcontl gcontr.
have closedd :  closed `[(- d), d] by apply: interval_closed => //.
have h0  : forall x, (g x) \in `](- d), d[%R -> (g x) \in  `[(-d),d]%R by move=>y0;rewrite !in_itv //= => /andP[h1 h2]; rewrite !ltW //.
case: ltgtP => [hyd|_|<-] // => _.
  case: ltgtP => [hyd'|_|->] // => _.
  apply /h0/imageg.
  exists x => //=; rewrite in_itv /= hyd hyd' //.
  apply: (@closed_cvg  _ _ (d^'-) _ g `[(- d), d]) => //=.
  near=>t.
  apply /h0/imageg; exists t => //=.
  near:t.
  exists d => //=.
  move => x0 /= h h'.
  suff  : (-d < x0) by rewrite in_itv /= h' //=; move => -> //=.
  apply:  (lt_trans (_ : -d < 0)) => //.
  move /ltr_distlDr  : h.
  by rewrite ltrDr //.
move => _.
apply: (@closed_cvg  _ _ ((-d)^'+) _ g `[(- d), d]) => //=.
near=>t.
apply /h0/imageg; exists t => //=.
near:t.
exists d => //=.
move => x0 /= h h'.
suff  : (x0 < d) by rewrite in_itv /= h' //=; move => -> //=.
apply:  (lt_trans (_ : x0 < 0)) => //.
move /ltr_distlCDr  : h.
by rewrite addNr.
Unshelve. all: end_near. Qed.

Local Notation contFunBallType x := (contFunSegType (- x) x).

Local Lemma imageg_closure' (g : contFunBallType d)
    (imageg : g @` `]-d, d[ `<=` `]- d, d[) : g @` `[-d, d] `<=` `[- d, d].
Proof.
  apply imageg_closure => //=.
  apply contFunSeg.
Qed.

End intermediate_lemma.

Section lemmas_from_a_previous_tentative.
Context {R : realType}.

Local Lemma ball_minr (x a b : R): subset (ball  x (minr a b)) (ball x b).
Proof.
  have [le_xy | lt_yx] := lerP a b => //.
  rewrite /ball.
  move => /= x0 bx0.
  by apply /lt_le_trans/le_xy.
Qed.

Variable d0 : {posnum R}.
Local Notation d := d0%:num.

Local Lemma  cvg_at_left_bounded (h: R -> R) :
  {within `[-d, d], continuous h} ->
  [set h x | x in `](- d), d[] `<=` `](- d), d[ ->
    (-d < h d < d) /\ h x0 @[x0 --> d^'-] --> h d \/
    h d = d /\ h x0 @[x0 --> d^'-] --> (h d)^'- \/
    h d = -d /\ h x0 @[x0 --> d^'-] --> (h d)^'+.
Proof.
move => cont_h hd.
have hd' := imageg_closure cont_h hd.
have hds x: -d < x < d -> -d < h x /\ h x < d.
  move => h0.
  suff   :h x  \in `](- d), d[ by rewrite inE /= in_itv /= => h1;apply /andP.
  by rewrite inE;apply hd;exists x => //.
have hd's x : -d <= x <= d -> -d <= h x /\ h x <= d.
  move => h0.
  suff   :h x  \in `[(- d), d] by rewrite inE /= in_itv /= => h1;apply /andP.
  by rewrite inE;apply hd';exists x => //.
have [ltd | gtd | eqd] := (ltgtP (h d) d).
-  have [ltd' | gtd' | eqd'] := (ltgtP (h d) (-d)).
   suff : (h d) \in  `[(- d), d].
   rewrite inE /= in_itv //= => /andP [] h2.
   by have := le_lt_trans h2 ltd';rewrite ltxx.
   rewrite inE;apply: hd' => /=.
   by exists d => //=;rewrite in_itv /= /andP lexx ltW // gtrN //.
   left;split=>//.
   move/continuous_within_itvP:cont_h.
   by rewrite gtrN// => /(_ isT)[_ _ +].
   right;right.
   split => //.
   rewrite eqd'.
   move => U [e /= e0 B] /=.
   move/continuous_within_itvP:cont_h.
   rewrite gtrN// => /(_ isT)[_ _ +].
   rewrite eqd' cvgrPdist_lt => /(_ e).
   rewrite e0 => //= /(_ isT)[r /= r0] cont_f2.
   exists (minr d r) => //=.
   rewrite lt_min; apply /andP => //.
   move => x0 Bx0 x0d.
   apply B.
   apply cont_f2 => //.
   apply /ball_minr/Bx0.
   apply hds.
   apply /andP;split => //.
   apply /(lt_trans _ (_ : 0 < x0)) => //.
   suff /ltr_distlDr: ball d d x0 by rewrite -subr_gt0  addrK.
   rewrite minC in Bx0.
   apply /ball_minr/Bx0.
 - suff /(le_lt_trans ): (h d <= d).
   by move /(_ (h d)); rewrite gtd ltxx => H;have := (H isT).
   apply hd's.
   apply /andP;split;rewrite // ltW // gtrN //.
- right;left.
   split => //.
   rewrite eqd.
   move => U [e /= e0 B] /=.
   move/continuous_within_itvP:cont_h.
   rewrite gtrN// => /(_ isT)[_ _ +].
   rewrite eqd cvgrPdist_lt => /(_ e).
   rewrite e0 => //= /(_ isT)[r /= r0] cont_f2.
   exists (minr d r) => //=.
   rewrite lt_min; apply /andP => //.
   move => x0 Bx0 x0d.
   apply B.
   apply cont_f2 => //.
   apply /ball_minr/Bx0.
   apply hds.
   apply /andP;split => //.
   apply /(lt_trans _ (_ : 0 < x0)) => //.
   suff /ltr_distlDr: ball d d x0 by rewrite -subr_gt0  addrK.
   rewrite minC in Bx0.
   apply /ball_minr/Bx0.
Qed.

(*Local Lemma picard_from_cont'_isContFunSegBuild_new (g : contFunBallType d)
    (imageg : g @` `]-d, d[ `<=` `]- d, d[) :
  @isContFunSeg R (- d) d (picard_from_cont' imageg).
Proof.
constructor.
rewrite /picard_from_cont'.
move=> x.
apply: cvgB; last exact: cvg_cst.
apply: parameterized_integral_continuous; first exact/ltW/gtrN.
<<<<<<< HEAD
move=> {x}.
apply/continuous_within_itvP; [exact: gtrN | split].
- move=> x; rewrite in_itv/= => /andP[ndx dx].
=======
pose f' := uncurry f.
have cont12 : {in `[(- d), d] `*` `](- d), d[, continuous f'}.
  move=> [y1 y2].
  rewrite !inE => -[/= /[!in_itv]/= /andP[dy1 y1d] /andP[dy2 y2d]].
  rewrite /continuous_at.
  have /cont2 : y1 \in `[(- d), d] by rewrite inE/= in_itv/= dy1 .
  move/continuous_within_itvP; rewrite gtrN// => /(_ isT)[+ _ _].
  move/(_ y2).
  rewrite in_itv/= dy2 y2d => /(_ isT).
  rewrite /continuous_at => cont_f2.
  apply/cvgrPdist_le => /= e e0.
  move/cvgrPdist_le : cont_f2 => /(_ (e / 2)).
  rewrite divr_gt0// => /(_ isT)[r /= r0] cont_f2.
  near=> t.
  rewrite -(subrK (f y1 t.2) (f y1 y2)) -(addrA _ (f y1 t.2)) (le_trans (ler_normD _ _))//.
  rewrite (splitr e) lerD//.
  + apply: cont_f2.
    near: t.
    exists (ball y1 r, ball y2 r) => /=.
      split.
        by apply: nbhsx_ballx.
      by apply: nbhsx_ballx.
    by move=> z/= [].
  + rewrite /f'.
    rewrite (_ : uncurry f t = f t.1 t.2)//; last by destruct t.
    rewrite distrC.
    have : t.2 \in `[(- d), d].
      near: t.
      exists (ball y1 r, ball y2 (minr (d-y2) (y2 + d))).
        split.
          by apply: nbhsx_ballx.
        by apply : nbhsx_ballx; rewrite lt_min subr_gt0 y2d -(opprK d) subr_gt0 //=.
      move => z /= [] /= _.
      rewrite /ball /= lt_min  => /andP[H1 H2].
      rewrite inE /= in_itv /=.
      rewrite !ltW /= //.
        have /ltr_distlCDr /= := H1.
        by rewrite subrKC.
      have /ltr_distlBl /= := H2.
      by rewrite opprD addrA addrN add0r.
    move/lip1.
    rewrite /dominated_by/=.
    move/(_ (t.1, y1) (conj Logic.I Logic.I)) => /=.
    move/le_trans; apply.
    rewrite ler_pdivlMr ?ltr0n// mulrC mulrA.
    pose U := ball y1 (e / (2 * k)).
    pose V := ball y2 e.
    near: t.
    exists (U,V).
      split.
        apply: nbhsx_ballx; apply /divr_gt0 /mulr_gt0 => //=.
        by apply: (lt_le_trans (_ : 0 < 1)).
      by apply: nbhsx_ballx.
    rewrite /ball /=.
    move => z /= [] /= H _.
    rewrite mulrC ltW // distrC -ltr_pdivlMr // mulr_gt0 //=.
    by apply: (lt_le_trans (_ : 0 < 1)).
have cont_g := @contFunSeg _ _ _ g.
have /cont2 : d \in `[(- d), d] by rewrite inE/= in_itv/= lexx ltW // gtrN.
move/continuous_within_itvP; rewrite gtrN// => /(_ isT)[_ _ +].
move /cvgrPdist_le => /= rcont_f.
have rcont1 : f z.1 z.2 @[z --> (d^'-, d^'-)] --> f d d.
  apply/cvgrPdist_le => /= e e0.
  move /( _ (e/2)) : rcont_f.
  rewrite divr_gt0// => /(_ isT)[r /= r0] cont_f2.
  near=>t.
  rewrite -(subrK (f d t.2) (f d d)) -(addrA _ (f d t.2)) (le_trans (ler_normD _ _))//.
  rewrite (splitr e) lerD//.
    near:t.
    exists (ball d r, fun x => x < d /\ ball d r x) => //=.
    split;exists r => //=.
    move =>  [t1 t2] //= [_ [H1 H2]].
    by apply cont_f2 => //.
  near: t.
  exists ((ball d (minr (e/(2*k)) d)), fun t => t <d /\  ball d (minr (e/(2*k)) d) t) => //=.
    by split; exists (minr (e/(2*k)) d) => //=;
           by rewrite lt_min divr_gt0 //= mulr_gt0 //=; apply: (lt_le_trans (_ : 0 < 1)).
   move => [t1 t2] /= [H _].
   have h : t2 \in `[(- d), d].
     admit.
   move /(_ _ h): lip1.
   rewrite /dominated_by/=.
   move/(_ (d, t1) (conj Logic.I Logic.I)) => /=.
   move/le_trans; apply.
   rewrite ler_pdivlMr ?ltr0n// mulrC mulrA mulrC -ler_pdivlMr.
   apply ltW; apply (lt_le_trans H).
   rewrite ge_min lexx //.
   rewrite mulr_gt0 //.
   by apply: (lt_le_trans (_ : 0 < 1)).
have H1 : f x0 (g x0) @[x0 --> d^'-] --> f d (g d).
  have [[intd cvg] | [ [eqd cvg] | [eqd cvg] ] ] := (cvg_at_left_bounded cont_g imageg).
  - apply: continuous2_cvg => //.
    + have -> : (fun z => f z.1 z.2) = (fun z => f' z) by apply /funext=>[[z]].
      have -> : f d (g d) = f' (d,g d) by [].
      apply: cont12.
      rewrite inE /= !in_itv /=;split => //.
      by rewrite lexx //= ltW //= gtrN //.
    + by apply cvg_at_left_filter.
  - apply: (@cvg_comp2 _ _ _ _ (d^'-) ((d)^'-) ((g d)^'-) (nbhs (f d (g d)))) => //.
    rewrite eqd.
    by apply rcont1.
  - apply: (@cvg_comp2 _ _ _ _ (d^'-) ((d)^'-) ((g d)^'+) (nbhs (f d (g d)))) => //.
    rewrite eqd.
(*    by apply: rcont1.*)
    admit.
Abort.
=======*)
End lemmas_from_a_previous_tentative.

Section lip_implies_cont.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
Variables (f : R -> R -> R) (d0 : {posnum R}).
Local Notation d := d0%:num.
Variable k : R.
Hypothesis k1 : k > 0.

Hypothesis lip2 : {in `[- d, d], forall x, k.-lipschitz (f x)}.

(* TODO: generalize and PR *)
Lemma cont2 : {in `[- d, d], forall x, {within `[-d, d], continuous f x}}.
Proof.
move=> x xNdd.
apply/continuous_within_itvP.
  by rewrite gtrN//.
split.
- move=> y yNdd.
  move: (xNdd); have := @lip2 x => /[apply] kfx.
  rewrite /continuous_at.
  apply/cvgrPdist_le => /= e e0.
  near=> y'.
  move: kfx => /(_ (y, y'))/= => /(_ (conj Logic.I Logic.I)).
  move=> /le_trans; apply.
  rewrite -ler_pdivlMl// mulrC.
  near: y'.
  (* TODO(rei): investigate *)
  exists (e / k).
    by rewrite divr_gt0//.
  by move=> z/= => /ltW.
- apply/cvgrPdist_le => /= e e0.
  near=> y'.
  move: (xNdd); have := @lip2 x => /[apply].
  move=> /(_ (- d, y'))/= => /(_ (conj Logic.I Logic.I)).
  move=> /le_trans; apply.
  rewrite -ler_pdivlMl// mulrC.
  near: y'.
  (* TODO(rei): investigate *)
  exists (e / k) => /=.
    by rewrite divr_gt0//.
  by move=> z/= => /ltW.
- apply/cvgrPdist_le => /= e e0.
  near=> y'.
  move: (xNdd); have := @lip2 x => /[apply].
  move=> /(_ (y', d))/= => /(_ (conj Logic.I Logic.I)).
  rewrite distrC.
  move=> /le_trans; apply.
  rewrite -ler_pdivlMl// mulrC.
  near: y'.
  (* TODO(rei): investigate *)
  exists (e / k) => /=.
    by rewrite divr_gt0//.
  move=> z/= => /ltW.
  by rewrite distrC.
Unshelve. all: end_near. Qed.

End lip_implies_cont.

Section intermediate_lemma.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
Variables (f : R -> R -> R) (d0 : {posnum R}).
Local Notation d := d0%:num.
Local Notation contFunBallType x := (contFunSegType (- x) x).

Variable (g : contFunBallType d).

Variable k : R.
Hypothesis k0 : k > 0.
(* properties of the function f defining the differential equation: *)
(* k-lipschitz for all t *)
Hypothesis lip2 : {in `[- d, d], forall x, k.-lipschitz (f x)}.
(* within-continuous for all y *)
Hypothesis cont1 : {in `[- d, d], forall y, {within `[-d, d], continuous f ^~ y}}.

Local Lemma picard_from_cont'_isContFunSegBuild_helper
    (imageg : g @` `]-d, d[ `<=` `]- d, d[) :
  f x (g x) @[x --> (- d)^'+] --> f (- d) (g (- d)).
Proof.
pose f' := uncurry f.
pose fg := f' \o (fun x => (x, g x)).
suff : fg z @[z --> (- d)^'+] --> fg (- d) by [].
apply/cvgrPdist_le => /= e e0.
rewrite /fg/=.
have [|gNd_oowoR] :
    (g (- d) = - d \/ g (- d) = d) \/ g (- d) \in `](- d), d[.
  have : g (- d) \in `[(- d), d].
    apply/mem_set.
    apply: (imageg_closure (@contFunSeg _ _ _ g)) => //=.
    exists (- d) => //.
    by rewrite in_itv/= lexx ge0_cp.
  rewrite -setUitv1/=; last by rewrite bnd_simp ge0_cp.
  rewrite -setU1itv/=; last by rewrite bnd_simp gtrN.
  rewrite inE/= in_itv/= => -[[?|?]|?].
    by left; left.
    by right; rewrite inE/= in_itv/=.
    by left; right.
- have : - d \in `[(- d), d] by rewrite inE/= in_itv/= lexx ge0_cp.
  move/(cont2 k0 lip2)/continuous_within_itvP.
  rewrite gtrN// => /(_ isT)[_ cfright cfleft].
  have e20 : 0 < e / 2 by rewrite divr_gt0.
  move/cvgrPdist_le : cfright => /(_ _ e20)[r/= r0] H1.
  move/cvgrPdist_le : cfleft => /(_ _ e20)[r'/= r'0] H2.
  move=> gNd.
  near=> t.
  rewrite -(subrK (f (- d) (g t)) (f (- d) (g (- d)))).
  rewrite -!(addrA _ (f (- d) (g t))).
  rewrite (le_trans (ler_normD _ _))//.
  have gtd : g t \in `](- d), d[%R.
    apply: imageg => /=; exists t => //.
    rewrite in_itv/=; apply/andP; split => //.
    by near: t; apply: nbhs_right_lt; rewrite gtrN.
  rewrite (splitr e) lerD//.
  + move: gNd => [gNd|gNd].
    * rewrite gNd; apply: H1.
        rewrite /ball_/= -[X in `|X - _| ]gNd.
        near: t.
        have /continuous_within_itvP := @contFunSeg _ _ _ g.
        rewrite gtrN// => /(_ isT)[_ + _].
        by move/cvgrPdist_lt => /(_ _ r0); exact.
      by move: gtd; rewrite in_itv/= => /andP[].
    * rewrite gNd.
      apply: H2.
        rewrite /ball_/=.
        rewrite -[X in `|X - _| ]gNd.
        near: t.
        have /continuous_within_itvP := @contFunSeg _ _ _ g.
        rewrite gtrN// => /(_ isT)[_ + _].
        move/cvgrPdist_lt => /(_ _ r'0).
        exact.
      by move: gtd; rewrite in_itv/= => /andP[].
  + have : g t \in `[(- d), d].
      move/subset_itv_oo_cc : gtd => gtd.
      by rewrite inE/=.
    move/cont1.
    move/continuous_within_itvP.
    rewrite gtrN// => /(_ isT)[_ + _].
    move/cvgrPdist_le => /(_ (e / 2)).
    rewrite divr_gt0// => /(_ isT)[e1 /= e10].
    apply.
      rewrite /ball_/=.
      rewrite -opprB opprK normrN.
      rewrite gtr0_norm//; last first.
        rewrite -(opprK d).
        by rewrite subr_gt0//.
      rewrite -ltrBrDr.
      admit.
    admit.
+ move: (gNd_oowoR); rewrite inE/= => gNd_ooR.
  move: (gNd_oowoR).
  rewrite inE => /subset_itv_oo_cc gNd_ccR.
  have gNd_ccwoR : g (- d) \in `[(- d), d] by rewrite inE.
  have : (- d) \in `[(- d), d] by rewrite inE/= in_itv/= lexx/= ge0_cp.
  move/(cont2 k0 lip2)/continuous_within_itvP.
  rewrite gtrN// => /(_ isT)[cf _ _].
  have := cf _ gNd_ooR.
  rewrite /continuous_at.
  have e20 : 0 < e / 2 by rewrite divr_gt0.
  move/cvgrPdist_le => /(_ _ e20)[r/= r0] H1.
  near=> t.
  rewrite -(subrK (f (- d) (g t)) (f (- d) (g (- d)))).
  rewrite -!(addrA _ (f (- d) (g t))).
  rewrite (le_trans (ler_normD _ _))//.
  rewrite (splitr e) lerD//.
    apply: H1.
    rewrite /ball_/=.
    near: t.
    (* TODO: copipe *)
    have /continuous_within_itvP := @contFunSeg _ _ _ g.
    rewrite gtrN// => /(_ isT)[_ + _].
    move/cvgrPdist_lt => /(_ _ r0).
    exact.
  have : g t \in `[(- d), d].
    (* TODO: copipe *)
    apply/mem_set; apply: (@imageg_closure' _ _ g) => //=.
    exists t => //.
    rewrite in_itv/=; apply/andP; split => //.
    near: t.
    apply: nbhs_right_le.
    by rewrite gtrN.
  admit. (* similar as above *)
Unshelve. all: end_near. Admitted.

End intermediate_lemma.

Notation contFunBallType x := (contFunSegType (- x%:num) x%:num).

Definition contFunSegN {R : realType} (d0 : {posnum R})
  (g : R -> R) := g \o -%R.
Arguments contFunSegN {R} _ _.

Section contFunSegN.
Context {R : realType}.
Variable d0 : {posnum R}.
Local Notation d := d0%:num.

Let g'fun (g : contFunBallType d0) :
  set_fun `[- d, d] setT (contFunSegN d0 g).
Proof. by constructor => x/=. Qed.

HB.instance Definition _ (g : contFunBallType d0) :=
  @isFun.Build R R `[-d, d] setT (contFunSegN d0 g) (g'fun g).

(* TODO: should this be a lemma? about balls? *)
Let cg' (g : contFunBallType d0) :
  {within `[- d, d], continuous (contFunSegN d0 g)}.
Proof.
apply/continuous_within_itvP; first by rewrite gtrN.
have /continuous_within_itvP[] := @contFunSeg _ _ _ g.
  by rewrite gtrN.
move=> cg gR gL; split.
- move=> x xdd; apply: continuous_comp; first exact: continuousN.
  by apply: cg; rewrite oppr_itvoo opprK.
- by apply/cvg_at_leftNP; rewrite /contFunSegN/= opprK.
- by move/cvg_at_rightNP : gR; rewrite opprK.
Qed.

HB.instance Definition _ (g : contFunBallType d0) :=
  @isContFunSeg.Build R (- d0%:num) d0%:num (contFunSegN d0 g) (@cg' g).

End contFunSegN.

Definition picard_from_cont' {R : realType} (f : R -> R -> R) (g : R -> R)
    (d0 : {posnum R})
    (imageg : g @` `]- d0%:num, d0%:num[ `<=` `]- d0%:num, d0%:num[) : R -> R :=
  fun t => (\int[lebesgue_measure]_(x in `[- d0%:num, t]) f x (g x))%R.

(* first, we define picard_from_cont
   that takes a function continuous over a closed ball *)
Section picard_from_cont'.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
Variables (f : R -> R -> R) (d0 : {posnum R}).

Local Notation d := d0%:num.

Variable k : R.
Hypothesis k0 : k > 0.
(* properties of the function f defining the differential equation: *)
Hypothesis lip2 : {in `[- d, d], forall x, k.-lipschitz (f x)}.
Hypothesis cont1 : {in `[- d, d], forall y, {within `[-d, d], continuous f ^~ y}}.

Variable g : contFunBallType d0.
Hypothesis imageg : g @` `]- d, d[ `<=` `]- d, d[.

Lemma set_fun_picard_from_cont' :
  {homo picard_from_cont' f imageg : x / `[- d, d] x >-> [set: R] x}.
Proof. by []. Qed.

HB.instance Definition _ :=
  @isFun.Build _ _ `[- d, d] [set: R] (picard_from_cont' f imageg)
    (set_fun_picard_from_cont').

Lemma within_continuous_picard_from_cont' :
  {within `[- d, d], continuous (picard_from_cont' f imageg)}.
Proof.
rewrite /picard_from_cont'.
move=> x.
apply: parameterized_integral_continuous; first exact/ltW/gtrN.
apply: continuous_compact_integrable; first exact: segment_compact.
move=> {x}.
rewrite /=.
apply/continuous_within_itvP; [exact: gtrN | split].
- move=> x; rewrite in_itv/= => /andP[ndx dx].
  rewrite /continuous_at.
  pose f' := uncurry f.
  pose fg := f' \o (fun x => (x, g x)).
  have cont12 : {in `](- d), d[ `*` `](- d), d[, continuous f'}.
    move=> [y1 y2].
    rewrite !inE => -[/= /[!in_itv]/= /andP[dy1 y1d] /andP[dy2 y2d]].
    rewrite /continuous_at.
    have /(cont2 k0 lip2) : y1 \in `[(- d), d].
      by rewrite inE/= in_itv/= (ltW dy1) ltW.
    move/continuous_within_itvP; rewrite gtrN// => /(_ isT)[+ _ _].
    move/(_ y2).
    rewrite in_itv/= dy2 y2d => /(_ isT).
    rewrite /continuous_at => cont_f2.
    apply/cvgrPdist_le => /= e e0.
    move/cvgrPdist_le : cont_f2 => /(_ (e / 2)).
    rewrite divr_gt0// => /(_ isT)[r /= r0] cont_f2.
    near=> t.
    rewrite -(subrK (f y1 t.2) (f y1 y2)) -(addrA _ (f y1 t.2)) (le_trans (ler_normD _ _))//.
    rewrite (splitr e) lerD//.
      apply: cont_f2.
      near: t.
      exists (ball y1 r, ball y2 r) => /=.
        split.
          by apply: nbhsx_ballx.
        by apply: nbhsx_ballx.
      by move=> z/= [].
    rewrite /f'.
    rewrite (_ : uncurry f t = f t.1 t.2)//; last by destruct t.
    rewrite distrC.
    have : t.2 \in `[(- d), d].
      near: t.
      exists (ball y1 r, ball y2 (minr (d-y2) (y2 + d))).
        split.
          by apply: nbhsx_ballx.
        by apply : nbhsx_ballx; rewrite lt_min subr_gt0 y2d -(opprK d) subr_gt0 //=.
      move => z /= [] /= _.
      rewrite /ball /= lt_min  => /andP[H1 H2].
      rewrite inE /= in_itv /=.
      rewrite !ltW /= //.
        have /ltr_distlCDr /= := H1.
        by rewrite subrKC.
      have /ltr_distlBl /= := H2.
      by rewrite opprD addrA addrN add0r.
(*    move/lip1.
    rewrite /dominated_by/=.
    move/(_ (t.1, y1) (conj Logic.I Logic.I)) => /=.
    move/le_trans; apply.
    rewrite ler_pdivlMr ?ltr0n// mulrC mulrA.
    pose U := ball y1 (e / (2 * k)).
    pose V := ball y2 e.
    near: t.
    exists (U,V).
      split.
        apply: nbhsx_ballx; apply /divr_gt0 /mulr_gt0 => //=.
      by apply: nbhsx_ballx.
    rewrite /ball /=.
    move => z /= [] /= H _.
    rewrite mulrC ltW // distrC -ltr_pdivlMr // mulr_gt0 //=.*) admit.
  suff : fg z @[z --> x] --> fg x by [].
  apply: continuous_comp.
    red.
    rewrite /continuous_at.
    have := @cvg_pair _ _ _ (nbhs x) (nbhs x) (nbhs (g x)) _ _ _ id g.
    apply.
    exact: cvg_id.
    apply: (@within_continuous_continuous _ (- d) d).
      by rewrite gtrN.
    by have := @contFunSeg _ _ _ g.
    by rewrite in_itv/= ndx.
  apply: cont12.
  rewrite !inE; split => //=.
    by rewrite !in_itv/= ndx.
  rewrite !in_itv/=.
  have := @imageg (g x).
  rewrite /= in_itv/=; apply.
  exists x => //.
  by rewrite !in_itv/= ndx/=.
- exact: (picard_from_cont'_isContFunSegBuild_helper k0).
- apply/cvg_at_leftNP => /=.
  rewrite [X in X x @[x --> _] --> _](_ : _ =
      (fun x => f (- x) (g (- x)))); last exact/funext.
  rewrite [X in _ --> X](_ : _ = f (- - d) (g (- - d))); last first.
    by rewrite opprK.
  apply: (@picard_from_cont'_isContFunSegBuild_helper R
    (fun x => f (- x)) d0 (contFunSegN d0 g) _ k0) => /=.
  - move=> x xdd.
    (* TODO: this should be a lemma *)
    move=> [y1 y2] _/=.
(*    have /= := @lip1 x xdd (- y1, - y2).
    by rewrite opprK -(distrC y2) (addrC y2); apply.*) admit.
  - move=> x xdd.
    have := cont2 k0 lip2.
(*    rewrite inE/=.
    rewrite oppr_itvcc opprK.
    by rewrite inE in xdd.*) admit.
  - move=> /= _ [u udd] <-.
    rewrite /contFunSegN/=.
    apply: imageg => /=.
    exists (- u) => //.
    by rewrite oppr_itvoo opprK.
Unshelve. all: end_near. Admitted.

HB.instance Definition _ := @isContFunSeg.Build R (- d) d
  (picard_from_cont' f imageg)
  within_continuous_picard_from_cont'.

(*
move=> {x}.
have cont12' : {in `[(- d), d], forall x,  {within `[(- d), d], continuous (fun y => f' (x,y))}}.
  move => x xd //=.
  move /(_ x) : cont2.
  rewrite xd => /(_ isT).
  move/continuous_within_itvP; rewrite gtrN// => /(_ isT) [cont_f lcont_f rcont_f].
  apply/continuous_within_itvP; [exact: gtrN | split].
  move => y yd // .
  have <- : f' \o (fun y => (x,y)) = [eta f x] by apply/funext => z.
  apply continuous_comp => //=.
  red.
  rewrite /continuous_at.
  have := @cvg_pair _ _ _ (nbhs y) (nbhs x) (nbhs y) _ _ _ (cst x) id => //=.
  apply.
  exact: cvg_cst.
  exact: cvg_id.
  apply cont12.
  rewrite inE;split => //=.
  apply set_mem => //=.
  exact: lcont_f.
  exact: rcont_f.

have lcont_inside : -d < g d < d -> f x (g x) @[x --> d^'-] --> f d (g d).
  move => gxd //=.
  pose fg := f' \o (fun x => (x, g x)).
  suff : fg z @[z -->  d^'-] --> fg d by [].
  apply: (@cvg_comp _ _ _ (fun x => (x, g x)) f' (d)^'-).
  apply: (@cvg_pair _ _ _ ((d)^'-) (nbhs d) (nbhs (g d))  _ _ _ _ g).
  by apply: cvg_at_left_filter.
  have /continuous_within_itvP  :=  @contFunSeg _ _ _ g.
  by rewrite gtrN //; move => [] //= _ + _.
  apply: cont12.
  rewrite inE;split => //=.
  rewrite in_itv  /= lexx ltW  //=; exact: gtrN.

have lcont_inside' :  g d = d -> f x (g x) @[x --> d^'-] --> f d (g d).
  move => gxd //=.
  pose fg := f' \o (fun x => (x, g x)).
  suff : fg z @[z -->  d^'-] --> fg d by [].
  apply: (@cvg_comp _ _ _ (fun x => (x, g x)) f' (d)^'-).
  apply: (@cvg_pair _ _ _ ((d)^'-) (d^'-) ((g d)^'-)  _ _ _ _ g).
  exact cvg_id.
  admit.
  apply/cvgrPdist_le => /= e e0 //.
  rewrite /fg /=.
  near_simpl.
  rewrite -near2_pair.
  near=>t.
   rewrite -(subrK (f t.1 (g d)) (f d (g d))) -(addrA _ (f t.1 (g d))) (le_trans (ler_normD _ _))//.
  rewrite (splitr e) lerD//.
  near:t.
  suff /cvgrPdist_le : continuous_at d (f^~ (g d)) =>  /=.
  move /(_ (e/2)).
  rewrite divr_gt0 => // /(_ isT).
  move => [/= r r0 H].
  exists ((ball d r), (ball (g d) r)).
  split;by apply /cvg_at_left_filter/nbhsx_ballx.
  move => [t0 t1] H0 /=.
  by apply H;apply H0.
  rewrite /continuous_at.
  rewrite gxd.
  apply /cvgrPdist_le => /= e' e0' //.
  near=>t.
  move /(_ d): lip1.
  rewrite mem_set /=;[ | rewrite in_itv /= lexx ltW //=; exact: gtrN]  => /(_ isT).
   rewrite /dominated_by/=.
    move/(_ (t, d) (conj Logic.I Logic.I)) => /=.
    near:t.
    exists (e'/k).
    apply /divr_gt0 => //.
      by apply: (lt_le_trans (_ : 0 < 1)).
   move => x0 /= h.
   rewrite distrC.
   move/le_trans; apply.
   rewrite mulrC.
   rewrite distrC -ler_pdivlMr  //.
   by apply ltW.
    by apply: (lt_le_trans (_ : 0 < 1)).
    near:t.
    move /(_ d) : cont2.
    rewrite mem_set.
    move => /(_ isT) /continuous_within_itvP .
    rewrite gtrN //; move => [] //= _ _ +.
    rewrite cvgrPdist_le => /(_ (e/2)).
    rewrite divr_gt0 => // /(_ isT).
    move => [] /= r r0 h.
    rewrite gxd.
    rewrite /f' /=.
    exists (e,e).
  rewrite ler_pdivlMr ?ltr0n// mulrC mulrA.
    rewrite ler_pdivlMr ?ltr0n// mulrC mulrA.
  rewrite in_itv  /= lexx ltW  //=; exact: gtrN.

  move => [].
  admit.

  rewrite gxd.
  have /(_ (ball (f t.1 d) (e/2))) : (f t.1 x) @[x --> d^'-] --> f t.1 d.
  admit.
  near:t.
  move => H.
  move => [| /= r r0 H].
    by apply: nbhsx_ballx; apply /divr_gt0.
  near_simpl.
  specialize (h (ball (f t.1 d) (e/2))) => /=.
  move /(_ t.1) : cont2.
  s
  rewrite continuous_within_itvP.
  move /(_ (d,g d)) : cont12.
  Search continuous_at (_, _).
  apply cvg_id.
  near_simpl.
  rewrite mem_set /=;[ | rewrite in_itv /= lexx ltW //=; exact: gtrN]  => /(_ isT).
  rewrite continuous_within_itvP;[| exact:gtrN].
  move => [_ _ +].
  move /(_ (ball (f d d) (e/2))).
  move => [ | r /= r0 h].
    apply: nbhsx_ballx; apply /divr_gt0 => //.
  enough (t1 <  
  rewrite gxd => rcont_f.
  rewrite inE;split => //=.
  rewrite in_itv  /= lexx ltW  //=; exact: gtrN.
  apply gtrN.
  Search (_ < _).
  Check gtrN.
  apply/cvgrPdist_le => /= e e0 //.
  near_simpl.

  apply: cvg_comp.
  rewrite fmap_comp /=.

  Search nbhs "comp".
  apply: continuous_comp.
  red.
 rewrite /continuous_at.
 admit.
 red.
 rewrite /continuous_at.
 apply cont12.
 have := @cvg_pair _ _ _ (nbhs x) (nbhs x) (nbhs (g x)) _ _ _ id g.
  apply.
  exact: cvg_id.
  apply: (@within_continuous_continuous _ (- d) d).
  by rewrite gtrN.
  by have := @contFunSeg _ _ _ g.
  by rewrite in_itv/= ndx.
  apply: cont12.
  rewrite !inE; split => //=.
    by rewrite !in_itv/= ndx.
  rewrite !in_itv/=.
  have := imageg (g x).
  rewrite /= in_itv/=; apply.
  exists x => //.
  by rewrite !in_itv/= ndx/=.
apply/continuous_within_itvP; [exact: gtrN | split];last 2 first.
  pose fg := f' \o (fun x => (x, g x)).
  suff : fg z @[z -->  (- d)^'+] --> fg (-d) by [].
  rewrite /fg /=.
  have : (g (-d) = d \/ g (-d) = -d \/ -d < g (-d) < d).
  admit.
  case => [H0 | ].
  rewrite H0.
  apply: (@cvg_comp _ _ _ (fun x => (x, g x)) f' (-d)^'+).
  apply: (@cvg_pair _ _ _ ((-d)^'+) ((-d)^'+) ((g (-d))^'+)  _ _ _ _ g).
  exact: cvg_id.
  have /continuous_within_itvP  :=  @contFunSeg _ _ _ g.
  rewrite gtrN //; move => [] //= _ + _.
  admit.
  apply/cvgrPdist_le => /= e e0 //.
  have /continuous_within_itvP  :=  @contFunSeg _ _ _ g.
  rewrite gtrN //; move => [] //= _ + _.
  move => h.
  move => U [e /= e0  Ub].
  have [] := (h (ball d e)).
  rewrite H0.
     by apply: nbhsx_ballx.
   move => r /= r0 a.
   specialize (a (x0)).
   move => aa ab.
   apply: Ub.
   apply a => //.
   simpl in a.
   rewrite 
  Search nbhs at_right.
  rewrite nbhs_right_ltW.
  Search cvg_to at_right.

  admit.

  apply/cvgrPdist_le => /= e e0 //.
  near_simpl.
  (* apply (@cvg_pair _ _ _ ((-d)^'+) ((-d)^'+) (within (fun u => -d <= u <=d) (nbhs (g (-d)))) _ _ _ id g). *)
  admit.
  simpl.

  (* have /continuous_within_itvP  :=  @contFunSeg _ _ _ g. *)
  (* rewrite gtrN //; move => [] //= _ + _ //. *)
 (*  apply: cvg_trans. *)
 (*  apply h. *)
 (*  rewrite withinE. *)
 (*  simpl. *)
 (*  exact  *)
 (*  Check cvgrPdist_le. *)
 (*  apply: cvg_withinP. *)
 (*  apply /subspace_cvgP. *)
 (*  apply /(imageg_closure imageg) => //=. *)
 (*  exists (-d) =>//=. *)
 (* admit. *)
  (* have /continuous_within_itvP  :=  @contFunSeg _ _ _ g. *)
  (* rewrite gtrN //; move => [] //= _ h _ //. *)
  (* rewrite -nbhs_subspace_interior. *)
  (* rewrite nbhs_subspaceE. *)
  (* apply h. *)
  (* Unset Printing Notations. *)
  (* Unset Printing Notations. *)
  apply/cvgrPdist_le => /= e e0 //.
  near_simpl.
  rewrite -near2_pair /=.
  have /cont2 : -d \in `[(- d), d] by rewrite inE/=in_itv/= lexx ltW //;exact: gtrN.
  move/continuous_within_itvP; rewrite gtrN// => /(_ isT) [].
  move/(_ (g (-d))).
  have /continuous_within_itvP  :=  @contFunSeg _ _ _ g.
  rewrite gtrN //; move => [] //= _ + _.
  rewrite /continuous_at => lcont_g.
  move/cvgrPdist_le : lcont_g => /(_ (e / 2)).
  rewrite divr_gt0// => /(_ isT) [r /= r0] lcont_g.
  rewrite /continuous_at => cont_f.
  move  : cont_f => /(_ (g (-d))) => /cvgrPdist_le cont_f.
  move : cont_f => /(_ (e / 2)).
  near_simpl.
  rewrite divr_gt0// => /(_ isT) cont_f.
  near=>t.
  rewrite -(subrK (f (-d) t.2) (f (-d) (g (-d)))) -(addrA _ (f (-d) t.2)) (le_trans (ler_normD _ _))//.
  rewrite (splitr e) lerD//.
  move => 
  rewrite in_itv/= .
  rewrite /continuous_at => cont_f2.

  move/cvgrPdist_le : cont_f2 => /(_ (e / 2)).
  rewrite divr_gt0// => /(_ isT)[r /= r0] cont_f2.
  near=> t.
  
Search Order.lt GRing.opp Itv.r.
apply num_lt.
  move/(_ (t.1, y1) (conj Logic.I Logic.I)) => /=.
    move/le_trans; apply.
  apply:a => //.
  apply: cvg_at_right_filter => //.
  near_simpl.
  near=>t.
  admit.

  
  exis

  apply:a.
  near=>t.
  rewrite uncurry 
    apply.
    red.
    apply : cvg_pair.
  Unset Printing Notations.
  Search cvg_to "pair".
  apply : cvg_pa
move => x.
admit.
admit.
- 
  move=> x; rewrite in_itv/= => /andP[ndx dx].
>>>>>>> 1f76303a4 (wip)*)
(*   apply function_spaces.continuous_uncurry. *)
(*   rewrite /continuous_at. *)
(*   apply: cvg_comp. *)
(*   admit. *)
(*   have : f' z @[z  --> (x, g x)] --> f' (x ,(g x)).  *)
(*   apply contf'. *)
(*   Search cvg_to. *)
(*   About continuous_comp. *)
(* apply: (@continuous_comp _ _ _ (fun x => (x.1, - x.2)) (fun x => x.1 - x.2)). *)
(*   apply: cvg_pair; first exact: cvg_fst. *)
(*   by apply: continuous_comp; [exact: cvg_snd|exact: opp_continuous]. *)
(* exact: sub_continuous. *)
(*   apply: (@continuous2_cvg _ _ _ _ _ _ id g) => //. *)
(*   About cvg_pair. *)
(*   + have cont1 :  {in `[(- d), d], forall y : R,  {within `[(- d), d], continuous (fun x => f x y)}}. *)
(*     admit. *)

(*     have := @cont1 (g x).  *)
(*     rewrite inE /= in_itv /=. *)
(*     rewrite (_ :   -d <= g x <= d); last first. *)
(*     admit. *)
(*     move => /(_ isT). *)
(*     move => /(_ x). *)
(*     rewrite /continuous_at. *)
(*     apply: cvg_trans. *)
(*     move => /(_ (g x)). *)
(*     rewrite /continuous_at. *)

(*     have := @cont2 x.  *)
(*     rewrite inE /= in_itv /=. *)
(*     rewrite (ltW ndx) (ltW dx) /= => /(_ isT). *)
(*     move => /(_ (g x)). *)
(*     rewrite /continuous_at. *)

(*     apply : cvg_trans. *)
(*     have := (@contFunSeg _ _ _ g) => contg. *)
(*     apply /cvgrPdist_le. *)
(*     Locate continuous2_cvg. *)
(*     About  continuous2_cvg. *)
(*     About continuous_comp. *)
(*     near=> e. *)
(*     rewrite /=. *)
(*     near_simpl; near=> t. *)
(*     apply: (@le_trans _ _ ( `|f t.1 t.2 - f t.1 (g x)| + `|f t.1 (g x) - f x (g x)|)). *)
(*       rewrite (le_trans _ (Num.Theory.ler_normD _ _))//. *)
(*       by rewrite addrA subrK. *)
(*     rewrite (splitr e) lerD//. *)
(*       have : {within `[(- d), d], continuous f t.1}. *)
(*         apply: cont2. *)
(*         admit. *)
(*       move/(_ t.2). *)
(*       move/cvgrPdist_le. *)
(*       move/(_ (e / 2)). *)
(*       rewrite divr_gt0// => /(_ isT). *)
(*       rewrite /prop_near1/= !nbhsE/=. *)
(*       rewrite /nbhs/= => -[A oA]. *)
(*       apply. *)
(*       admit. *)
(*     admit. *)
(*   + suff : {in `]- d, d[, continuous g}. *)
(*       by apply; rewrite inE/= in_itv/= ndx dx. *)
(*     have : {within `[- d, d], continuous g} by exact: contFunSeg. *)
(*     have ndd : - d < d by rewrite gtrN. *)
(*     move/(continuous_within_itvP _ ndd) => [cg _ _]. *)
(*     by move=> r; rewrite inE/=; exact: cg. *)
(* - rewrite (_ : (fun x => f x (g x)) = (fun x => f (- x) (g (- x))) \o -%R); last first. *)
(*     admit. *)
(*   apply/cvg_at_leftNP. *)
(*   apply: (@cvg_comp _ _ _ -%R (fun x => f x (g x)) _ ((- d)^'+)). *)
(*   + by rewrite at_rightN. *)
(*   + admit. *)
(* - admit. *)
(* Admitted. *)

(*HB.instance Definition _ (g : contFunBallType d)
    (imageg : g @` `[- d, d] `<=` `[- d, d]) :=
  picard_from_cont'_isContFunSegBuild imageg.*)

(*Local Lemma continuous_picard_from_cont' (g : contFunBallType d)
    (imageg : g @` `[- d, d] `<=` `[- d, d]) :
  {within `[- d, d], continuous picard_from_cont' imageg}.*)
Local Lemma continuous_picard_from_cont' :
  {within `[- d, d], continuous picard_from_cont' f imageg}.
Proof. exact: contFunSeg. Abort.

End picard_from_cont'.

Section picard_from_cont.
Context {R : realType}.
Variables (f : R -> R -> R) (d0 : {posnum R}).
Local Notation d := d0%:num.

Local Notation V := (quot_contFunSegType (ge0_cp (ge0 d0)).2).

Definition picard_from_cont
  (k : R) (lcf_x : {in `[- d, d], forall x, k.-lipschitz (f x)})
  (cf_y : {in `[- d, d], forall y, {within `[-d, d], continuous f ^~ y}})
  (g : V) : R -> R :=
match pselect (g @` `]- d, d[ `<=` `]- d, d[) with
| left imageg => @picard_from_cont' R f g d0 imageg
| _ => cst 0
end.

End picard_from_cont.

(* second, we define picard_to_cont
   that takes a function continuous over a closed ball
   and returns a function continuous over a closed ball *)
Section picard_to_cont.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
(*Local Notation contFunBallType x := (contFunSegType (- x) x).*)
Variables (f : R -> R -> R) (d0 : {posnum R}) (k : R).
Local Notation d := d0%:num.
Hypothesis k1 : 0 < k.
Hypothesis lip2 : {in `[- d, d], forall x, k.-lipschitz (f x)}.
Hypothesis cont1 : {in `[- d, d], forall y, {within `[- d, d], continuous f ^~ y}}.

Local Notation picard_from_cont := (@picard_from_cont R f d0 k lip2 cont1).

Local Notation V := (quot_contFunSegType (ge0_cp (ge0 d0)).2).
Lemma set_fun_picard_from_cont (g : V) :
  set_fun `[-d, d] setT (picard_from_cont g).
Proof.
  by [].
Qed.

HB.instance Definition _ (g : V) := @isFun.Build
  R R `[-d, d] setT (picard_from_cont g) (set_fun_picard_from_cont g).

Lemma continuous_picard_from_cont (g : V) :
  {within `[- d, d], continuous (picard_from_cont g)}.
Proof.
have := (@contFunSeg _ _ _   g).
rewrite /picard_from_cont.
case: pselect => //=.
  move => a cg.
  apply: contFunSeg.
  + exact: k1.
  + exact : lip2.
  + exact : cont1.
move => _ _.
apply: continuous_subspaceT => z;apply: cvg_cst.
Qed.

HB.instance Definition _ (g : V) :=
  @isContFunSeg.Build R (- d) d
     (picard_from_cont g)
     (@continuous_picard_from_cont g).

Check fun g : V => (\pi_(V)%qT (picard_from_cont g )) : V.

Definition picard_to_cont x :=  \pi_V%qT (picard_from_cont x).

Lemma set_fun_picard_to_cont : set_fun [set: V] [set: V]
  picard_to_cont.
Proof.
by [].
Qed.

Fail Check picard_to_cont : {fun [set: V] >-> [set: V]}.

HB.instance Definition _ :=
    @isFun.Build _ _ _ _ picard_to_cont set_fun_picard_to_cont.

Check picard_to_cont : {fun [set: V] >-> [set: V]}.
(* still, we can't state that it is a contraction for typing reasons *)
Fail Lemma tmp : is_contraction (picard_to_cont
  : {fun [set: W] >-> [set: W]}).
About is_contraction.
End picard_to_cont.

Section picard_to_cont_normedtype.
Context {R : realType} {r s : R} (rs : r <= s).
Local Notation mu := lebesgue_measure.
Local Notation V := (quot_contFunSegType rs).

HB.instance Definition _ := PseudoMetric.copy V (pseudoMetric_normed V).
HB.instance Definition _ := isPointed.Build V 0.

End picard_to_cont_normedtype.

Section picard_to_cont_normedtype2.
Context {R : realType} {a b : R} (ab : a <= b).
Variables (f : R -> R -> R) (k : R).
Hypothesis lip2 : {in `[a, b], forall x, k.-lipschitz (f x)}.
Hypothesis cont1 : {in `[a, b], forall y, {within `[a, b], continuous f ^~ y}}.

Local Notation contFunBallType := (quot_contFunSegType ab).

Lemma is_normZmod_contFunBallType : NormedZmod_PseudoMetric_eq R (contFunBallType).
Proof.
by constructor.
Qed.

Fail Check contFunBallType : pseudoMetricNormedZmodType R.

HB.instance Definition _ := is_normZmod_contFunBallType.

Check contFunBallType : pseudoMetricNormedZmodType R.

(* TODO: equip contFunBallType d with the type of an Lmodule *)

Check contFunBallType : zmodType.

End picard_to_cont_normedtype2.

Section picard_to_cont_normedtype3.
Local Open Scope quotient_scope.
Context {R : realType} (r s : R) (rs : r <= s).

Notation V := (quot_contFunSegType rs).

Definition cont_scale (k : R) (v : V) : V := \pi_V (k *: repr v).

Import Quotient.

Let cont_scalerA a b v : cont_scale a (cont_scale b v) = cont_scale (a * b) v.
Proof.
rewrite /cont_scale.
have [-> | a0] := eqVneq a 0; first by rewrite !(scale0r,mul0r).
apply/eqmodP; rewrite /equiv_equiv/= /equiv/=.
rewrite -scalerA -scalerBr.
rewrite inE.
apply/funext => x/=.
rewrite patchE; case: ifPn => // xrs.
rewrite !fctE.
apply/eqP; rewrite scaler_eq0.
rewrite (negPf a0)/= subr_eq0.
apply/eqP.
case: piP => f.
by move/eqmod_on_itv => /(_ _ xrs) <-.
Qed.

Let cont_scale1r : left_id 1 cont_scale.
Proof.
move=> v.
rewrite /cont_scale/=.
rewrite [RHS](_ : _ = (\pi_V (repr v))%qT); last first.
  by rewrite reprK.
apply/eqmodP.
by rewrite scale1r.
Qed.

Let cont_scalerDr : right_distributive cont_scale +%R.
Proof.
move=> k b c.
rewrite /cont_scale/=.
have [-> | k0] := eqVneq k 0.
  by rewrite !scale0r piE//= add0r.
rewrite /cont_scale/=.
rewrite piE/=.
apply/eqmodP.
rewrite /equiv_equiv /equiv/=.
rewrite -scalerDr.
rewrite -scalerBr.
rewrite inE.
apply/funext => x/=.
rewrite patchE; case: ifPn => // xrs.
rewrite !fctE.
apply/eqP; rewrite scaler_eq0 (negPf k0)/=.
rewrite subr_eq0.
apply/eqP.
have := @eqmod_on_itv _ _ _ rs (repr (b + c)) (repr b + repr c).
move=> ->//.
rewrite pi_add//=.
by rewrite !reprK.
Qed.

(* TODO: PR *)
Lemma restrict0 [T : Type] (K : realFieldType) (D : set T) :
  (cst 0 : T -> K) \_ D = cst 0.
Proof.
apply/funext => x/=.
rewrite patchE.
by case: ifPn.
Qed.

Let cont_scalerDl : forall v, {morph cont_scale^~ v: a b / a + b}.
Proof.
move=> v a b.
rewrite /cont_scale.
rewrite piE/=.
apply/eqmodP; rewrite /equiv_equiv/= /equiv/=.
rewrite -scalerDl subrr.
rewrite inE/=.
by rewrite restrict0.
Qed.

HB.instance Definition _ :=
  @GRing.Zmodule_isLmodule.Build R V cont_scale cont_scalerA cont_scale1r cont_scalerDr
  cont_scalerDl.

Local Lemma sup_mult (A : set R) (a : R): has_sup A ->  sup [set normr a * x  | x in A ] = (normr a) * sup A  .
Proof.
move =>ex_sup.
have []:= ex_sup => -[] x Ax ub.
apply /eqP.
rewrite eq_le.
apply /andP;split.
apply sup_le_ub; first by exists (normr a * x); exists x.
move => _ [x0 Axo <-].
apply ler_wpM2l => //.
apply sup_le => //.
have [/eqP ->| ha0] := boolP (a == 0).
rewrite normr0 !mul0r .
suff ->:  [set 0 * x0 | x0 in A] = [set 0] by rewrite sup1 lexx.
apply/predeqP => x0 /=;split => [ [x1 _ <-] | -> ].
  by rewrite mul0r.
  by exists x => //=; rewrite  mul0r.
rewrite -ler_pdivlMl; last by rewrite normr_gt0.
apply sup_le_ub; first by apply ex_sup.
move => x0 Ax0.
rewrite ler_pdivlMl; last by rewrite normr_gt0.
apply sup_le.
split; first by exists (`|a| * x ); exists x.
have [x1 ubx1] := ub.
exists (`|a| * x1).
move => _ [x2 Ax2 <-].
apply ler_wpM2l => //.
by apply ubx1.
exists x0 => //.
Qed.

Local Lemma repr_mult l (x : V) a :   a \in `[r, s] -> repr (l *: x) a = l *: (repr x a). 
Proof.
    move =>ars.
    have : repr (l *: x) = l *: repr x %[mod V].
      by case: piP => //=.
    move/(@eqmod_on_itv _ _ _ rs (repr (l *: x)) (l *: repr x)).
    by move/(_ _ ars).
Qed.

Lemma is_pmnormedZmod_contFunBallType :
  PseudoMetricNormedZmod_Lmodule_isNormedModule R V.
Proof.
constructor.
move=> l x.
rewrite /Num.norm/=.
rewrite /infty_norm /infty_norm0 /=.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: sup_le_ub.
    exists (`|repr (l *: x) r|).
    rewrite /=.
    exists r => //.
    by rewrite in_itv/= lexx/=.
  move=> _/= [a ars] <-.
  rewrite repr_mult; last by rewrite inE.
  rewrite normrZ ler_wpM2l//.
  apply: sup_le.
  by apply normr_has_sup.
  by exists a.
  rewrite -sup_mult => //; last by apply normr_has_sup.
  apply le_sup; [ | | by apply normr_has_sup].
  move => _  [_ [x0 x0rs] <- <-].
  exists (normr l * (normr \o repr x) x0);split => //=;exists x0.
  by rewrite inE.
  rewrite repr_mult; last by rewrite inE.
  by rewrite normrZ.
  exists (normr (l * x r));exists (normr (repr x r)).
  exists r => //=.
    by rewrite in_itv/= lexx/=.
    by rewrite normrZ.
Qed.

(* similar to normr_has_sup *)

HB.instance Definition _ := Num.Zmodule_isNormed.Build
  R V (@ler_infty_normD R _ _ rs) (@infty_normr0_eq0 R _ _ rs)
  (@infty_normrMn R _ _ rs) (@infty_normrN R _ _ rs).

Fail Lemma ctr_picard : is_contraction (picard_to_cont lcf_x cf_y).

HB.instance Definition _ := is_pmnormedZmod_contFunBallType.

End picard_to_cont_normedtype3.

Section picard_to_cont_normedtype4.
Context {R : realType}.
Variable f : R -> R -> R.
Variable (d0 : {posnum R}).
Variable k : R.
Local Notation d := d0%:num.
Hypothesis k0 : 0 < k.
Hypothesis lip2 : {in `[- d, d], forall x, k.-lipschitz (f x)}.
Hypothesis cont1 : {in `[- d, d], forall y, {within `[- d, d], continuous f ^~ y}}.

Notation V := (quot_contFunSegType (ge0_cp (ge0 d0)).2).

Definition contrac : V -> V := @picard_to_cont R f d0 k k0 lip2 cont1.

Lemma set_fun_picard : set_fun [set: V] [set: V] contrac.
Proof.
by [].
Qed.

HB.instance Definition _ :=
  @isFun.Build _ _ setT setT contrac set_fun_picard.

Hypothesis dtwok : d0%:num < (2 * k)^-1.

Let twodk := (d0%:num * k) *+ 2.

Let twodk_ge0 : 0 <= twodk.
Proof. by rewrite /twodk mulrn_wge0// mulr_ge0// ltW. Qed.

Local Notation mu := (@lebesgue_measure _).

Lemma is_contraction_picard_to_cont : is_contraction contrac.
Proof.
rewrite /is_contraction.
rewrite /contraction.
rewrite /contrac.
rewrite /picard_to_cont.
rewrite /picard_from_cont.
rewrite /picard_from_cont'.
have twod0k : 0 <= 2 * d0%:num * k by rewrite mulr_ge0// ltW.
exists (NngNum twod0k).
split.
  by rewrite /= mulrAC mulrC -ltr_pdivlMr ?div1r// mulr_gt0.
move=> -[/= g h _ (* True /\ True ?! *)].
rewrite /contrac.
rewrite /picard_to_cont.
rewrite piE/=.
rewrite qnorm_piE.
rewrite /infty_norm0/=.
apply: sup_le_ub => //=.
  admit.
move=> _ /= [t tNdd <-].
rewrite /picard_from_cont/=.
case: pselect => /= Hg; last first.
  admit.
case: pselect => /= Hh; last first.
  admit.
rewrite /picard_from_cont'/=.
rewrite !fctE.
set a := \int[mu]_(x0 in `[(- d), t]) f x0 (g x0).
(*set a' := \int[mu]_(x0 in `[(- d), 0x]) f x0 (g x0).*)
set b := \int[mu]_(x0 in `[(- d), t]) f x0 (h x0).
(*set b' := \int[mu]_(x0 in `[(- d), 0x]) f x0 (h x0).*)
(*rewrite [X in `|X| ](_ : _ = (a - b) + (b' - a')); last first.
  rewrite -!addrA; congr +%R.
  by rewrite opprB addrC addrCA addrA.*)
rewrite {}/a {}/b (*{}/a' {}/b'*).
rewrite -RintegralB//=; last 2 first.
  admit.
  admit.
(*rewrite -RintegralB//=; last 2 first.
  admit.
  admit.*)
(* (le_trans (ler_normD _ _))// lerD//.*)
rewrite (le_trans (le_normr_Rintegral _ _))//=.
  admit.
rewrite (@le_trans _ _ (k * \int[mu]_(t0 in `[(- d), t]) `| g t0 - h t0|))//.
  rewrite (@le_trans _ _ (\int[mu]_(t0 in `[(- d), t]) (k * `|g t0 - h t0|)))//.
    (* TODO: prove ge0_le_Rintegral on the model of ge0_le_integral *)
    apply: le_Rintegral => //=; last 3 first.
      admit.
      admit.
    move=> x xNdt.
    have : x \in `[(- d), d]. admit.
    move/lip2.
    rewrite /dominated_by/= => /(_ (g x, h x)) /=.
    exact.
  rewrite RintegralZl//=.
  admit.
rewrite (@le_trans _ _ (k * \int[mu]_(t0 in `[(- d), t]) `|g - h| ))//.
  rewrite ler_pM2l//.
  apply: le_Rintegral => //=.
    admit.
    admit.
  move=> /= x xNdt.
  rewrite [leRHS]/Num.norm/=.
  rewrite /infty_norm.
  rewrite /infty_norm0/=.
  apply: sup_le => //=.
    admit. (* maybe something we already did... *)
  exists x; last first.
    admit.
  admit.
rewrite (@le_trans _ _ (k * `|g - h| * (t + d)))//.
rewrite -mulrA ler_wpM2l//; first exact: ltW.
  admit.
rewrite [leLHS]mulrAC.
rewrite ler_wpM2r//.
rewrite mulrC ler_pM2r//.
move: tNdd.
rewrite in_itv/= => /andP[Ndt td].
by rewrite mulr_natl mulr2n lerD//.
Admitted.

End picard_to_cont_normedtype4.

Section picard_sketch.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
Local Notation contFunBallType x := (@quot_contFunSegType R _ _ (ge0_cp (ge0 x)).2).

Variables (f : R -> R -> R) (d0 : {posnum R}) (k : R).
Local Notation d := d0%:num.
Hypothesis k0 : 0 < k.
Hypothesis lip2 : {in `[- d, d], forall x, k.-lipschitz (f x)}.
Hypothesis cont1 : {in `[- d, d], forall y, {within `[-d, d], continuous f ^~ y}}.
Variable y_ : R -> R.
Hypothesis y_init_t : y_ 0 = 0.

Hypothesis dtwok : d0%:num < (2 * k)^-1.

Definition tmp : is_contraction (contrac k0 lip2 cont1) :=
  (@is_contraction_picard_to_cont R f d0 k k0 lip2 cont1 dtwok).

Let phi0 : contFunBallType d0 := 0. (* 0 is init_y *)

Let phioo : contFunBallType d0 :=
  limn (fun n => iter n (contrac k0 lip2 cont1) phi0).

(* TODO: not d, some smaller e *)
Theorem picard_lindelof_existence :
  phioo 0 = 0 /\
  {in `]- d, d[, forall x, phioo^`() x = f x (phioo x)}.
Proof.
split.
  rewrite /phioo.
  (* contraction_cvg_fixed *)
  set picard_method : (contFunBallType d0) -> (contFunBallType d0) :=
    (fun (g : (contFunBallType d0)) => contrac k0 lip2 cont1 g).
  (* TODO: fix
  set picard_method : (contFunBallType d) -> (contFunBallType d) :=
    (fun (g : (contFunBallType d)) => (fun t =>
     init_y
       + (\int[mu]_(x in `[init_t - e, t]) f x (g x))%R
         - (\int[mu]_(x in `[init_t - e, init_t]) f x (g x))%R)).
     (* add properties which should be preserved *)
  *)
  (* TODO: what it rel?
  have : (forall g , {h | rel g h}).
    admit.
  *)
  (*
  TODO: fixme
  move/dependent_choice/(_ phi0); rewrite /rel => -[phi_ [phi0eq /all_and2[cphi iter_phi]]].
  *)
  have cphioo : {in `]- d, d] (* init_t - e, init_t + e[ *) , continuous phioo }.
    move=> x xte.
    apply/cvgrPdist_le => eps eps0.
    near \oo => N. (* forall n > N satisfies
         (forall x, `|phi_ N x - phioo x| < eps / 3 *)
    near (@GRing.zero R)^'+ => dlt. (* forall t in ball x t satisfies
         ( `|phi_ N x - phi_ N t| < eps / 3 *)
    exists dlt.
      admit.
    move=> t/= tadlt.
    rewrite (_ : eps = eps / 3 + (eps / 3 + eps / 3)); last first.
      admit.
    set phi_ := fun n => iter n (picard_to_cont k0 lip2 cont1) phi0.
    rewrite -[phioo x](subrK (phi_ N x)).
    rewrite -[_ + _]addrA.
    rewrite -{2}[phi_ N x](subrK (phi_ N t)).
    rewrite -[X in _ + X]addrA.
  (* TODO: fixme
    apply: (le_trans (ler_normD (phioo x - phi_ N x)%R _)); apply: lerD.
      admit.
    apply: (le_trans (ler_normD (phi_ N x - phi_ N t)%R _)); apply: lerD.
      admit.*)
    admit.
(* TODO: fixme exists phioo.
  split.
    apply/cvg_lim => //.
    apply: cvg_near_cst.
    apply/nearW => n.
    elim: n.
      by rewrite phi0eq.
    by move=> n IH; rewrite iter_phi -addrA subrr addr0.*)
  admit.
move=> x xte.
(* exact: contraction_cvg_fixed *)
admit.
Admitted.

End picard_sketch.

(* dy = f(t, y(t)), y(t0) = y0 *)
Record IVP (R : realType) := {
  time_domain : interval R ;
  open_time_domain : open [set` time_domain] ;
  value_domain : interval R ;
  rhs : R -> R -> R ;
  initial_time : R (* t0 *) ;
  initial_time_domain : initial_time \in time_domain ;
  initial_value : R (* y0 *) ;
  initial_value_domain : initial_value \in value_domain ;
}.

Section solution_of_an_IVP.
Context {R : realType}.
Variable pbm : @IVP R.

Let t0 := initial_time pbm.
Let y0 := initial_value pbm.
Let rhs := rhs pbm.

Definition solution (i : interval R) (y : R -> R) :=
  [/\ t0 \in i,
      open [set` i],
      y @` [set` time_domain pbm] `<=` [set` value_domain pbm],
      {in i, forall t, y^`() t = rhs t (y t)} &
      y t0 = y0 ].

Let i := time_domain pbm.
Let j := value_domain pbm.
Hypothesis rhs_cont : forall y, y \in j -> {in i, continuous (rhs ^~ y)}.
Hypothesis rhs_lip : forall x, x \in i -> [lipschitz rhs x y | y in [set: R]].

Let mu := @lebesgue_measure R.

Definition inte a b f :=
  if a < b then \int[mu]_(x in `[a, b]) f x else - \int[mu]_(x in `[b, a]) f x.

Reserved Notation "\int [ mu ]_( x $ a ~ b ) F"
  (at level 36, F at level 36, mu at level 10,
  format "'[' \int [ mu ]_( x $ a ~ b )  '/  '  F ']'").

Notation "\int [ mu ]_( x $ a ~ b ) f" :=
  (inte a b (fun x => f)).

Lemma picard : exists (i : interval R) (y : R -> R), solution i y.
Proof.
pose f (y : R -> R) (t : R) := y0 + \int[mu]_(x $ t0 ~ t) rhs x (y x).
(* have : is_contraction f. *)
Abort.

End solution_of_an_IVP.
