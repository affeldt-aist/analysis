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
  apply/eqquotP.
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
Variable u0 : R.
Variable r : {posnum R}.
Let B := closed_ball u0 r%:num.

Local Lemma imageg_closure (g : R -> R) : {within `[-d,d], continuous g} ->
  g @``]-d, d[ `<=` interior B -> g @` `[-d, d] `<=` B.
Proof.
move => cont_g imageg _ [] x /= + <-.
rewrite in_itv /= => /andP[+ +]/=.
have /continuous_within_itvP  :=  cont_g.
rewrite gtrN //; move => [] //=.
move => gcont gcontl gcontr.
have closedd :  closed `[(- d), d] by apply: interval_closed => //.
have h0 : forall x, (g x) \in (interior B : set R) -> (g x) \in B.
  move=> x0.
  rewrite /B interior_closed_ballE//.
  rewrite closed_ball_itv//.
  rewrite ball_itv 2!inE/=.
  by rewrite !in_itv //= => /andP[h1 h2]; rewrite !ltW //.
case: ltgtP => [hyd|_|<-] // => _.
  case: ltgtP => [hyd'|_|->] // => _.
  apply/set_mem.
  apply/h0.
  apply/mem_set/imageg => /=.
  exists x => //=; rewrite in_itv /= hyd hyd' //.
  apply: (@closed_cvg  _ _ (d^'-) _ g B) => //=.
    exact: closed_ball_closed.
  near=>t.
  apply/set_mem.
  apply/h0.
  apply/mem_set.
  apply/imageg; exists t => //=.
  near:t.
  exists d => //=.
  move => x0 /= h h'.
  suff  : (-d < x0) by rewrite in_itv /= h' //=; move => -> //=.
  apply:  (lt_trans (_ : -d < 0)) => //.
  move /ltr_distlDr  : h.
  by rewrite ltrDr //.
move => _.
apply: (@closed_cvg  _ _ ((-d)^'+) _ g B) => //=.
    exact: closed_ball_closed.
near=>t.
apply/set_mem.
apply/h0.
apply/mem_set.
apply/imageg; exists t => //=.
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
    (imageg : g @` `]-d, d[ `<=` interior B) : g @` `[-d, d] `<=` B.
Proof.
apply imageg_closure => //=.
by apply contFunSeg.
Qed.

End intermediate_lemma.

Section lemmas_from_a_previous_tentative.
Context {R : realType}.
Variables (u0 : R) (r : {posnum R}).
Let B := closed_ball u0 r%:num.

Local Lemma ball_minr (x a b : R): subset (ball  x (minr a b)) (ball x b).
Proof.
  have [le_xy | lt_yx] := lerP a b => //.
  rewrite /ball.
  move => /= x0 bx0.
  by apply /lt_le_trans/le_xy.
Qed.

Variable d0 : {posnum R}.
Local Notation d := d0%:num.

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
Variable (u0 : R) (r : {posnum R}).

Variable (g : R -> R).
Hypothesis cg : {within `[(- d), d], continuous g}.

Let B := closed_ball u0 r%:num.

Variable k : R.
Hypothesis k0 : k > 0.
(* properties of the function f defining the differential equation: *)
(* k-lipschitz for all t *)
Hypothesis lip2 : {in `[- d, d], forall x, k.-lipschitz_B (f x)}.
(* within-continuous for all y *)
Hypothesis cont1 : {in B, forall y, {within `[-d, d], continuous f ^~ y}}.

(* Local Lemma in_itv_cases (x  : R) : x \in `[-d, d] -> (x = -d \/ x = d) \/ x \in `]-d, d[. *)
(* Proof. *)
(*   rewrite -setUitv1/=; last by rewrite bnd_simp ge0_cp. *)
(*   rewrite -setU1itv/=; last by rewrite bnd_simp gtrN. *)
(*   rewrite inE/= in_itv/= => -[[?|?]|?]. *)
(*     by left; left. *)
(*     by right; rewrite inE/= in_itv/=. *)
(*     by left; right. *)
(* Qed. *)


Local Lemma picard_from_cont'_isContFunSegBuild_helper
    (imageg : g @` `]-d, d[ `<=` interior B) :
  f x (g x) @[x --> (- d)^'+] --> f (- d) (g (- d)).
Proof.
apply/cvgrPdist_le => /= e e0.
have dd : - d \in `[(- d), d] by rewrite inE/= in_itv/= lexx ge0_cp.

have e20 : 0 < e / 2 by rewrite divr_gt0.

(* use continuity in first variable *)
have c1_ineq :  \forall t \near (- d)^'+,  `|f (- d) (g (- d)) - f t (g (-d))| <= (e/2).
  have : g (- d) \in (B : set R).
   apply/mem_set.
   rewrite /B.
   apply: (imageg_closure cg) => //=.
   exists (- d) => //.
   by rewrite in_itv/= lexx ge0_cp.
  move /(cont1)/continuous_within_itvP. 
  rewrite gtrN// => /(_ isT)[_ + _].
  rewrite cvgrPdist_le /=.
  exact.

have gtd :  \forall t \near (- d)^'+, g t \in (interior B : set R).
  near=>t.
  apply/mem_set.
  apply: imageg => /=; exists t => //.
  rewrite in_itv/=; apply/andP; split => //.
  by near: t; apply: nbhs_right_lt; rewrite gtrN.

(* use continuity of g *)
have cg_ineq :  \forall t \near (- d)^'+,  `|(g (- d)) - (g t)| <= k^-1 *(e/2).
  have /continuous_within_itvP := cg.
  rewrite gtrN// => /(_ isT)[_ + _].
  move/cvgrPdist_le => /(_  (k^-1 * (e / 2)) ).
  apply.
  by rewrite mulr_gt0//invr_gt0.

(* use Lipschitz continuity *)
have c2_ineq :  \forall t \near (- d)^'+,  `|f t (g (- d)) - f t (g t)| <= (e/2).
  near=> t.
  have td' : t \in `[(- d), d].
    rewrite inE /= in_itv /=;apply /andP;split=>//.
    rewrite ltW//.
    near:t.
    apply: nbhs_right_lt => //.
    by apply gtrN.
  have gNdB: B (g (- d)).
    apply: (imageg_closure cg) => //.
    exists (- d) => //=.
    by rewrite inE in dd.
  have Bgt : B (g t).
    apply: (imageg_closure cg) => //.
    exists (t) => //=.
    by rewrite inE in td'.
  move: lip2 => /(_ _ td').
  move /(_ (g (-d), g t)) => /=.
  move=> /(_ (conj gNdB Bgt)).
  move/le_trans; apply.
  rewrite -ler_pdivlMl //.
  by near:t.
near=>t.
rewrite -(subrK (f t (g (-d))) (f (- d) (g (- d)))).
rewrite -!(addrA _ (f t (g (-d)))).
rewrite (le_trans (ler_normD _ _))//.
rewrite (splitr e) lerD//;  by near:t.
Unshelve. all: end_near. Qed.

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

Definition picard_from_cont' {R : realType} (U := R)
  (u0 : U) (r : R)
  (B := closed_ball u0 r)
  (f : R -> U -> R) (g : R -> U)
    (d0 : {posnum R})
    (imageg : g @` `]- d0%:num, d0%:num[ `<=` interior B) : R -> R :=
  fun t => (\int[lebesgue_measure]_(x in `[- d0%:num, t]) f x (g x))%R.

Lemma proveme {R : realType} (d : R) (g : R -> R) :
  {within `[(- d), d], continuous g} ->
  {within `[(- d), d], continuous (g \o -%R)}.
Admitted.

(* first, we define picard_from_cont
   that takes a function continuous over a closed ball *)
Section picard_from_cont'.
Context {R : realType}.
(*Variable U : normedModType R.*)
Let U := R.
Local Notation mu := lebesgue_measure.
Variables (f : R -> U -> R) (d0 : {posnum R}).
Variables (u0 : U) (r : {posnum R}).

Let B : set R := closed_ball u0 r%:num.

Local Notation d := d0%:num.

Variable k : R.
Hypothesis k0 : k > 0.
(* properties of the function f defining the differential equation: *)
Hypothesis lip2 : {in `[- d, d], forall x, k.-lipschitz_B (f x)}.
Hypothesis cont1 : {in B, forall y, {within `[-d, d], continuous f ^~ y}}.

Variable g : R -> U (*contFunBallType d0*).
Variable cg : {within `[-d, d], continuous g}.
Hypothesis imageg : g @` `]- d, d[ `<=` interior B.

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
  have cont12 : {in `](- d), d[ `*` B°, continuous f'}.
    move=> [y1 y2].
    rewrite !inE => -[/= /[!in_itv]/= /andP[dy1 y1d] By2].
    rewrite /continuous_at.
(*    have /cont1 : y2 \in (B° : set U).
      by exact/mem_set.
    move/continuous_within_itvP; rewrite gtrN// => /(_ isT)[+ _ _].
    move/(_ y1).
    rewrite in_itv/= dy1 y1d => /(_ isT).
    rewrite /continuous_at => cont_f1.
    apply/cvgrPdist_le => /= e e0.
    move/cvgrPdist_le : cont_f1 => /(_ (e / 2)).
    rewrite divr_gt0// => /(_ isT) cont_f1.
    near=> t.
    rewrite -(subrK (f t.1 y2) (f y1 y2)) -(addrA _ (f t.1 y2)).
    rewrite (le_trans (ler_normD _ _))//.
    rewrite (splitr e) lerD//.
    + near: t.
      near_simpl.
      have [r0 /= r0_gt0 Br0] := cont_f1.
      exists (ball y1 r0, ball y2 r0) => /=.
        by split; exact: nbhsx_ballx.
      by move=> [r1 u1] [/= + _]; exact: Br0.
    + have : t.1 \in `[(- d), d].
        rewrite inE /= in_itv /=.
        apply/andP; split.
          near: t.
          exists (ball y1 (d + y1), ball y2 (y1 + d)).
            split; apply: nbhsx_ballx.
              by rewrite -(opprK d) addrC subr_gt0.
            by  rewrite -(opprK d) subr_gt0.
          rewrite /ball /=.
          move =>  [r1 r2] /= [B1 _]  .
          rewrite ltW //.
          move /ltr_distlBl : B1.
          by rewrite opprD addrA addrC addrA addNr add0r.
        near: t.
        exists (ball y1 (d - y1), ball y2 (d - y1)).
          by split; apply: nbhsx_ballx; rewrite subr_gt0.
        rewrite /ball /=.
        move=> [r1 r2] /= [B1 _]  .
        rewrite ltW //.
        move/ltr_distlCDr : B1.
        by rewrite addrA addrC addrA addNr add0r.
      have Bt2 : B t.2.
        have :=
        admit.
      move/lip2.
      rewrite /dominated_by => /(_ (y2, t.2)).
        

      (conj Logic.I Logic.I)) /=.
      have -> : f t.1 t.2 = f' t by destruct t.
      move/le_trans;apply.
      rewrite -ler_pdivlMl //.
      near:t.
      exists (ball y1 e, ball y2 (k^-1 * (e / 2))).
      split; first by apply: nbhsx_ballx.
        apply: nbhsx_ballx.  rewrite mulr_gt0 //.
        rewrite invr_gt0 //.
        rewrite divr_gt0 //.
      move => z /= [] /=.
      rewrite /ball /= => h1 h2.
      by rewrite  ltW //.
  suff : fg z @[z --> x] --> fg x by [].
  apply: continuous_comp.
    red.
    rewrite /continuous_at.
    have := @cvg_pair _ _ _ (nbhs x) (nbhs x) (nbhs (g x)) _ _ _ id g.
    apply.
      exact: cvg_id.
    apply: (@within_continuous_continuous _ (- d) d).
      by rewrite gtrN.
    exact: cg.
    by rewrite in_itv/= ndx.
  rewrite /continuous_at/=.
  apply/cvgrPdist_le => /= e e0.
  have gxB : g x \in (interior B : set R).
    apply/mem_set/imageg => /=; exists x => //.
    by rewrite in_itv/= ndx dx.
  have H : r%:num - `|g x - u0| > 0.
    move: gxB.
    rewrite !interior_closed_ballE//.
    rewrite !ball_itv/= !inE/=.
    rewrite !in_itv/=/= => /andP[L1 L2].
    rewrite subr_gt0 ltr_norml.
    rewrite -ltrBlDr opprK addrC.
    rewrite L1/=.
    by rewrite ltrBlDl.
  near=> t.
  rewrite /f'.
  rewrite -(subrK (f t.1 (g x)) (f x (g x))) -(addrA _ (f t.1 (g x))).
  rewrite (le_trans (ler_normD _ _))//.
  rewrite (splitr e) lerD//.
  + near: t.
    near_simpl.
    have /cont1 : g x \in B.
      apply/mem_set.
      apply: interior_subset.
      apply/imageg => /=; exists x => //.
      by rewrite in_itv/= ndx dx.
    move/continuous_within_itvP.
    rewrite gtrN// => /(_ isT)[+ Htmp1 Htmp2].
    move/(_ x).
    rewrite /continuous_at.
    have e20 : 0 < e / 2 by rewrite divr_gt0.
    rewrite !in_itv/= ndx dx => /(_ isT).
    move/cvgrPdist_le => /(_ _ e20)[r0 /= r0_gt0 Br0].
    near=> t.
    apply: Br0 => //.
    rewrite /ball_/=.
    near: t.
    exists (ball x r0, ball (g x) r0) => /=.
      by split; exact: nbhsx_ballx.
    move=> [r1 u1] [/=].
    by rewrite /ball/=.
  + (*near: t.
    near_simpl.*)
    have := @lip2 t.1.
(*    rewrite inE/=(* TODO: understand what is going on with mem and %?!*).*)
    have t1dd : t.1 \in `[- d, d].
      near: t.
      exists (ball x (Num.min (d - x) (d + x)), setT) => /=.
        split.
          apply: nbhsx_ballx => //=.
          rewrite lt_min subr_gt0 dx/=.
          by rewrite -ltrBlDl sub0r.
        exact: filterT.
      move=> z [+ _].
      rewrite /ball/= inE/= in_itv/=.
      rewrite ltr_norml => /andP[H1 H2].
      apply/andP; split.
        move: H2.
        rewrite ltrBlDr -ltrBlDl => /ltW.
        apply: le_trans.
        rewrite -lerBlDr opprK addrC.
        rewrite lerBlDl.
        by rewrite ge_min lexx orbT.
      move: H1.
      rewrite -ltrBlDr opprK addrC ltrBlDl => /ltW.
      move/le_trans; apply.
      by rewrite -lerBrDr ge_min lexx.
    move/(_ t1dd).
    have t2B : t.2 \in (interior B : set R).
      near: t.
      exists (ball x (d - x), ball (g x) (r%:num - `|g x - u0|)).
        split; apply: nbhsx_ballx; rewrite subr_gt0 => //.
        by rewrite -subr_gt0.
      rewrite /ball /=.
      move=> [r1 r2] /= [B1 B2].
      suff : `|r2 - u0| < r%:num.
        rewrite !interior_closed_ballE//.
        by rewrite inE /ball/= distrC.
      rewrite -(subrK (g x) r2).
      rewrite -(addrA _ (g x)).
      rewrite (le_lt_trans (ler_normD _ _))//.
      by rewrite -ltrBrDr distrC.
    move/(_ (g x, t.2)).
    move/set_mem/interior_subset in gxB.
    move/set_mem/interior_subset in t2B.
    move/(_ (conj gxB t2B)).
    rewrite /=.
    rewrite [in uncurry _ _](_ : t = (t.1, t.2)); last first.
      by rewrite -surjective_pairing.
    move=> /le_trans; apply.
    rewrite -ler_pdivlMl//.
    near: t.
    exists (ball x (d - x), ball (g x) (k^-1 * (e / 2))) => /=.
      split; apply: nbhsx_ballx.
        by rewrite subr_gt0.
      by rewrite mulr_gt0// ?divr_gt0// invr_gt0.
    move=> [z1 z2] /= [_].
    by rewrite /ball/= => /ltW.
- by apply: (@picard_from_cont'_isContFunSegBuild_helper R f d0 u0 r g _ _ k0) => //.
- apply/cvg_at_leftNP => /=.
  rewrite [X in X x @[x --> _] --> _](_ : _ =
      (fun x => f (- x) (g (- x)))); last exact/funext.
  rewrite [X in _ --> X](_ : _ = f (- - d) (g (- - d))); last first.
    by rewrite opprK.
  apply: (@picard_from_cont'_isContFunSegBuild_helper R
    (fun x => f (- x)) d0 u0 r (fun x => g (- x)) _ _ k0) => /=.
  - by apply: proveme.
  - move=> x xdd.
    apply lip2.
    rewrite inE/=.
    rewrite oppr_itvcc opprK.
    by rewrite inE in xdd.
  - move=> y ydd.
    suff: {within `[(- d), d], continuous (f^~ y) \o -%R} by [].
    have := (cont1 ydd).
    rewrite !continuous_within_itvP;  try by rewrite gtrN.
    move => [fc fcl fcr].
    split.
    move => x xdd.
    rewrite /continuous_at.
    rewrite (cvg_compNP (f^~ y)).
    apply fc.
    rewrite oppr_itv opprK //=.
    by rewrite -cvg_at_leftNP /= opprK.
    by rewrite -(opprK d) -cvg_at_rightNP opprK.
  - move=> /= _ [u udd] <-.
    rewrite /contFunSegN/=.
    apply: imageg => /=.
    exists (- u) => //.
    by rewrite oppr_itvoo opprK.
Unshelve. all: end_near. Qed.*) Admitted.

HB.instance Definition _ := @isContFunSeg.Build R (- d) d
  (picard_from_cont' f imageg)
  within_continuous_picard_from_cont'.

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

(*gtrN : forall [R : numDomainType] [x : R], 0 < x -> - x < x

ge0_cp : forall [R : numDomainType] [x : R], 0 <= x -> (- x <= 0) * (- x <= x)*)

(* TODO: PR to MathComp *)
Lemma gerN {R : numDomainType} (x : R) : 0 <= x -> - x <= x.
Proof. by move=> x0; rewrite ge0_cp. Qed.

Section picard_from_cont.
Context {R : realType}.
Let U := R(* normedModType R*).
Variables (f : R -> U -> R) (d0 : {posnum R}).
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.
Local Notation d := d0%:num.

Local Notation V := (quot_contFunSegType (gerN (ge0 d0))).

Definition picard_from_cont
  (k : R) (lcf_x : {in `[- d, d], forall x, k.-lipschitz_B (f x)})
  (cf_y : {in B, forall y, {within `[-d, d], continuous f ^~ y}})
  (g : R -> R) : R -> R :=
match pselect (g @` `]- d, d[ `<=` interior B) with
| left imageg => @picard_from_cont' R u0 r%:num f g d0 imageg
| _ => cst 0
end.

End picard_from_cont.

(* second, we define picard_to_cont
   that takes a function continuous over a closed ball
   and returns a function continuous over a closed ball *)
Section picard_to_cont.
Context {R : realType}.
Let U := R.
Local Notation mu := lebesgue_measure.
(*Local Notation contFunBallType x := (contFunSegType (- x) x).*)
Variables (f : R -> U -> R) (d0 : {posnum R}) (k : R).
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.
Local Notation d := d0%:num.
Hypothesis k1 : 0 < k.
Hypothesis lip2 : {in `[- d, d], forall x, k.-lipschitz_B (f x)}.
Hypothesis cont1 : {in B, forall y, {within `[- d, d], continuous f ^~ y}}.

Local Notation picard_from_cont_not := (@picard_from_cont R f d0 u0 r k lip2 cont1).

Local Notation V := (quot_contFunSegType (gerN (ge0 d0))).
Lemma set_fun_picard_from_cont (g : V) :
  set_fun `[-d, d] setT (picard_from_cont_not g).
Proof.
  by [].
Qed.

HB.instance Definition _ (g : V) := @isFun.Build
  R R `[-d, d] setT (picard_from_cont_not g) (set_fun_picard_from_cont g).

Lemma continuous_picard_from_cont (g : V) :
  {within `[- d, d], continuous (picard_from_cont_not g)}.
Proof.
have := (@contFunSeg _ _ _ g).
rewrite /picard_from_cont.
case: pselect => //=.
  move => a cg.
  apply: contFunSeg.
  + exact: k1.
  + exact : lip2.
  + exact : cont1.
  + exact : cg.
move => _ _.
apply: continuous_subspaceT => z;apply: cvg_cst.
Qed.

HB.instance Definition _ (g : V) :=
  @isContFunSeg.Build R (- d) d
     (picard_from_cont_not g)
     (@continuous_picard_from_cont g).

Check fun g : V => picard_from_cont_not g : contFunSegType _ _.

Check fun g : V => (\pi_(V)%qT (picard_from_cont_not g )) : V.

Definition picard_to_cont (x : V) :=  \pi_V%qT (picard_from_cont_not x).

Definition restrictedV := [set f : V | f @` `]- d, d[ `<=` `]-d, d[ ].

Lemma set_fun_picard_to_cont :
  set_fun restrictedV restrictedV picard_to_cont.
Proof.
move=> x.
rewrite /restrictedV/= => xNdd _/= -[r0 r0Ndd] <-.
rewrite /picard_to_cont.
rewrite in_itv/=.
rewrite [X in _ < X < _](_ : _ =
       (picard_from_cont_not x) r0); last first.
  have /eqmod_on_itv : (repr (\pi_(V)%qT (picard_from_cont_not x)) =
       picard_from_cont_not x %[mod V])%qT.
    by rewrite reprK.
  move=> <-//.
  move/subset_itv_oo_cc : r0Ndd.
  by rewrite inE/=.
rewrite /picard_from_cont/=.
case: pselect => // {}xNdd.
rewrite /picard_from_cont'.
admit. (* NB: this is obviously not provable *)
Admitted.

Fail Check picard_to_cont : {fun [set: V] >-> [set: V]}.

HB.instance Definition _ :=
    @isFun.Build _ _ _ _ picard_to_cont set_fun_picard_to_cont.

Check picard_to_cont : {fun restrictedV >-> restrictedV}.
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
Let U := R.
Variable f : R -> U -> R.
Variable (d0 : {posnum R}).
Variable k : R.
Local Notation d := d0%:num.
Hypothesis k0 : 0 < k.
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[- d, d], forall x, k.-lipschitz_B (f x)}.
Hypothesis cont1 : {in B, forall y, {within `[- d, d], continuous f ^~ y}}.

Notation V := (quot_contFunSegType (gerN (ge0 d0))).

Notation Vr := (@restrictedV _ d0).

Definition contrac : {fun Vr >-> Vr} :=
  @picard_to_cont R f d0 k u0 r k0 lip2 cont1.

Lemma set_fun_picard : set_fun Vr Vr contrac.
Proof.
by [].
Qed.

HB.instance Definition _ :=
  @isFun.Build _ _ Vr Vr contrac set_fun_picard.

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
rewrite /=.
move=> -[/= g h _ (* True /\ True ?! *)].
rewrite /Num.norm/=.
rewrite /infty_norm.
rewrite /infty_norm0.
rewrite /contrac.
rewrite /picard_to_cont.
rewrite piE/=.
(*rewrite qnorm_piE.
rewrite /infty_norm0/=.
apply: sup_le_ub => //=.
  set u := _ \o _; exists (u d) => /=; exists d => //.
  by rewrite in_itv/= lexx gerN.
move=> _ /= [t tNdd <-].
rewrite /picard_from_cont/=.
case: pselect => /= Hg; last first.
  rewrite sub0r normrN.
  case: pselect => [|_]; last by rewrite normr0 mulr_ge0.
  rewrite /picard_from_cont'/= => hNdd.
  rewrite [in leRHS]/Num.norm/=.
  rewrite /infty_norm /infty_norm0 /=.
  Unset Printing Notations.
.by rewrite abse0.
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
by rewrite mulr_natl mulr2n lerD//.*)
Admitted.

End picard_to_cont_normedtype4.

Section picard_sketch.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
Local Notation contFunBallType x :=
  (@quot_contFunSegType R _ _ (gerN (ge0 x))).
Let U := R.

Variables (f : R -> U -> R) (d0 : {posnum R})(*NB: instead of [t0,t1]*)
  (k : R) (u0 : U) (r : {posnum R}).
Local Notation d := d0%:num.
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[- d, d], forall x : R, k.-lipschitz_B (f x)}.
Hypothesis cont1 : {in B, forall y, {within `[-d, d], continuous f ^~ y}}.
(*Variable y_ : R -> R.
Hypothesis y_init_t : y_ 0 = 0.*)

Hypothesis dtwok : d0%:num < (2 * k)^-1.

Definition tmp : is_contraction (contrac k0 lip2 cont1) :=
  (@is_contraction_picard_to_cont R f d0 k k0 u0 r lip2 cont1 dtwok).

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
