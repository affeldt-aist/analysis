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
From mathcomp Require Import common.
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

(* TODO(ishiguro): put elsewhere? *)
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

(* NB: attempt by Ishiguro-san to rewrite FTC2 with a notation *)
(*   for integral that can be swapped (int_a^b = - int_b^a) *)
(* TODO: maybe not needed right now *)

Notation "`[| x , y |]" := (setInterval (Interval (BLeft x) (BRight y))).
Notation "`]| x , y |[" := (setInterval (Interval (BRight x) (BLeft y))).

Section inteitv.
Local Open Scope ereal_scope.

Context {R : realType}.
Let mu := (@lebesgue_measure R).

(*
TODO restore
tinteitv (a b : R) f :=
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

(*
#[short(type="contFunSegType")]
HB.structure Definition ContFunSeg (R : realType) (a b : R) :=
  {f of isContinuous (subspace `[a, b]) R f & @Fun R R `[a, b] [set: R] f}.
(* Error: Structure subspace_topology_ContinuousFun contains the same mixins as ContFunSeg *)
*)

(* TODO: factory Lmodule is normed *)

(* NB(rei): was this just motivated by generic predicates such as rpredD?
or more generally by stability of "cont. over [a,b]"?
anyway, maybe not needed right now *)
Section cont_on_seg_sub.
Context {R : realType} {V : topologicalType}.
Variables a b : R.
Notation T := (continuousFunType `[a, b] [set: V]).

Section Sub.
Context (f : R -> V) (fP : f \in cont_on_seg a b).

Definition cont_on_seg_Sub_subproof := unsquash (set_mem fP).
#[local] HB.instance Definition _ := cont_on_seg_Sub_subproof.
Definition cont_on_seg_Sub : continuousFunType `[a, b] [set: V] :=
  {| ContinuousFun.sort := f; ContinuousFun.class := cont_on_seg_Sub_subproof |}.

End Sub.

Lemma cont_on_seg_rect (K : T -> Type) :
  (forall f (Pf : f \in cont_on_seg a b), K (cont_on_seg_Sub Pf)) ->
  forall u : T, K u.
Proof.
move=> Ksub [f Pf].
rewrite (_ : K _  = K (cont_on_seg_Sub (mem_set (squash Pf))))//.
rewrite /cont_on_seg_Sub /cont_on_seg_Sub_subproof /= mem_setK.
rewrite /unsquash; case : cid => // /= => x _.
congr (K (ContinuousFun.Pack _)).
move : Pf x => [[H1] [H2]] [[K1] [K2]].
by rewrite (Prop_irrelevance H1 K1) (Prop_irrelevance H2 K2).
Qed.

Lemma cont_on_seg_valP f (Pf : f \in cont_on_seg a b) :
  cont_on_seg_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ := isSub.Build _ _ T cont_on_seg_rect cont_on_seg_valP.

Lemma cont_on_seg_eqP (f g : continuousFunType `[a, b] [set: V]) :
  f = g <-> f =1 g.
Proof. by split=> [->//|fg]; exact/val_inj/funext. Qed.

(* commented out on [2025-12-26]
HB.instance Definition _ := [Choice of continuousFunType `[a, b] [set: R] by <:].
*)

End cont_on_seg_sub.

Module Rcont_on_seg_ring.
Section ring_instance.
Context {R : realType} (a b : R).

Lemma cont_on_seg_subring_closed : subring_closed (@cont_on_seg R R a b).
Proof.
split=> [|f g|f g]; rewrite !inE/=.
- apply: squash.
  do 2 split => //.
  exact: cst_continuous.
- move=> /unsquash cf /unsquash cg.
  apply: squash.
  pose f' : continuousFunType `[a, b] [set: R] := HB.pack f cf.
  pose g' : continuousFunType `[a, b] [set: R] := HB.pack g cg.
  rewrite [f]/(f' : _ -> _).
  rewrite [g]/(g' : _ -> _).
  move: {f g cf cg} f' g' => f g.
  have isfun_fg : @isFun (subspace `[a, b]) R `[a, b] [set: R] (f \- g).
    by constructor.
  have iscontfun_fg : isContinuous (subspace `[a, b]) R (f \- g).
    constructor => x.
    by apply: continuousB; exact: cts_fun.
  by split.
- move=> /unsquash cf /unsquash cg.
  apply: squash.
  pose f' : continuousFunType `[a, b] [set: R] := HB.pack f cf.
  pose g' : continuousFunType `[a, b] [set: R] := HB.pack g cg.
  rewrite [f]/(f' : _ -> _).
  rewrite [g]/(g' : _ -> _).
  move: {f g cf cg} f' g' => f g.
  have isfun_fg : @isFun (subspace `[a, b]) R `[a, b] [set: R] (f \- g).
    by constructor.
  have iscontfun_fg : isContinuous (subspace `[a, b]) R (f \* g).
    constructor => x.
    by apply: (@continuousM _ (subspace `[a, b])); exact: cts_fun.
  by split.
Qed.

HB.instance Definition _ := GRing.isSubringClosed.Build _
  (@cont_on_seg R R a b) cont_on_seg_subring_closed.

HB.instance Definition _ := [SubChoice_isSubComNzRing of
  continuousFunType `[a, b] [set: R] by <:].

HB.instance Definition _ := [SubChoice_isSubComNzRing of
  continuousFunType `[a, b] [set: R] by <:].

End ring_instance.
End Rcont_on_seg_ring.

Module Rcont_on_seg_lmodtype.
Import Rcont_on_seg_ring.
Section lmodtype_instances.
Context {R : realType} (a b : R).

HB.instance Definition _ := GRing.isZmodClosed.Build _ (@cont_on_seg R R a b)
  (cont_on_seg_zmod_closed a b).

HB.instance Definition _ :=
  [SubChoice_isSubZmodule of continuousFunType `[a, b] [set: R] by <:].

Check @continuousFunType _ R `[a, b] setT : zmodType.

Fail Check @continuousFunType _ R `[a, b] setT : lmodType _.

HB.instance Definition _ := GRing.isScaleClosed.Build _ _
  (cont_on_seg a b) (@contfun_scaler_closed R R a b).

HB.instance Definition _ :=
  [SubZmodule_isSubLmodule of continuousFunType `[a, b] [set: R] by <:].

Check @continuousFunType _ R `[a, b] setT : lmodType _.

End lmodtype_instances.
End Rcont_on_seg_lmodtype.

Module Rcont_on_seg.
Export Rcont_on_seg_ring Rcont_on_seg_lmodtype.
Section ideal_definition.
Context {R : realType} (a b : R) (ab : a <= b).

Local Notation T := (continuousFunType `[a, b] [set: R]).

#[using="ab"]
Definition ideal_itv : {pred T} := [pred f : T | f \_ `[a, b] == cst 0].

Lemma idealr_closed_itv : idealr_closed ideal_itv.
Proof.
split => /=.
- rewrite inE/=.
  apply/funext => x.
  by rewrite patchE; case: ifPn.
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

Fail Check ideal_itv : zmodClosed _.

HB.instance Definition _ := isIdealr.Build _ ideal_itv idealr_closed_itv.

Check ideal_itv : zmodClosed _.

End ideal_definition.

Section cont_on_seg_quotient.
Context {R : realType} (a b : R).
Hypothesis ab : a <= b.

Definition quot_continuousFunType := {ideal_quot (ideal_itv ab)}.

HB.instance Definition _ := NzRingQuotient.on quot_continuousFunType.

Definition quot_continuousFunType_to_fun (f : quot_continuousFunType) :
  (* NB(rei): was R -> R before 2025-12-26 *)
  subspace `[a, b] -> R := repr f.
Coercion quot_continuousFunType_to_fun : quot_continuousFunType >-> Funclass.

Local Open Scope quotient_scope.

Lemma eq_segP (f g : quot_continuousFunType) :
  reflect ({in `[a, b], f =1 g}) (f == g %[mod quot_continuousFunType]).
Proof.
apply/(iffP idP); rewrite eqmodE//=.
  rewrite /Quotient.equiv.
  rewrite inE => fgab0 x xab.
  move/(congr1 (fun z => z x)) : fgab0.
  by rewrite patchE xab => /eqP; rewrite subr_eq0/= => /eqP.
move=> abfg.
rewrite /Quotient.equiv inE; apply/funext => y.
rewrite patchE; case: ifPn => //= yab.
rewrite !fctE.
apply/eqP; rewrite subr_eq0; apply/eqP.
exact: abfg.
Qed.

End cont_on_seg_quotient.
End Rcont_on_seg.

Section zmodule_normed.
Context {R : realType} (a b : R) (ab : a <= b).

Import Rcont_on_seg.

Local Notation V := (quot_continuousFunType ab).

Definition infty_norm (f : V) := @infty_norm0 R R `[a, b] (repr f).

Local Notation norm := infty_norm.

Lemma cont_on_seg_norm0 (x : V) : b < a -> norm x = 0.
Proof.
move=> ba.
rewrite /norm /infty_norm0 [X in sup X](_ : _ = set0) ?sup0//.
rewrite -subset0 => /= f/= [r]; rewrite in_itv/= => /andP[ar rb] _.
by move: ba; rewrite ltNge (le_trans ar rb).
Qed.

Local Open Scope quotient_scope.

(* TODO: wait for quotient *)
Lemma contFunSeq_eq (f g : quot_continuousFunType ab) :
  f = g <-> {in `[a, b], repr f =1 repr g}.
Proof.
split=> [->//|fg].
Abort.

Let normr_repr_has_sup (x : V) :
  has_sup [set (normr \o repr x) x0 | x0 in `[a, b]].
Proof. by apply: normr_has_sup. Qed.

Lemma infty_norm_le  (g : continuousFunType `[a, b] [set: R]) (u : R) :
  {in `[a, b], forall x, `| g x | <= u} -> infty_norm0 g <= u.
Proof.
move=> abgu; rewrite /infty_norm0; apply: ge_sup.
  by exists (normr (g a)); exists a => //; rewrite /= in_itv/= lexx.
by move => _ [x xab] <-; rewrite abgu// inE.
Qed.

Lemma infty_norm_ge (g : continuousFunType `[a, b] [set: R]) x :
  x \in `[a, b] -> `|g x| <= infty_norm0 g.
Proof.
move => xab.
rewrite /infty_norm0 sup_upper_bound//=; first exact: normr_has_sup.
by exists x => //; rewrite inE in xab.
Qed.

Lemma eqmod_on_itv f g :
  f = g %[mod V] -> {in `[a,b], f =1 g}.
Proof.
move => /eqmodP + x xab.
rewrite /Quotient.equiv_equiv /Quotient.equiv /=.
rewrite /ideal_itv/= => /set_mem H.
apply subr0_eq.
rewrite -[RHS]/(cst 0 x) -H patchE; case : ifPn => //.
by rewrite xab.
Qed.

Lemma eval_mod_on_itv f x : x \in `[a,b] -> (\pi_V f : V) x = f x.
Proof. by move => xab; apply eqmod_on_itv => //; rewrite reprK. Qed.

Lemma infty_norm_itv_eq (f g : continuousFunType `[a, b] [set: R]) :
  {in `[a,b], f =1 g} -> infty_norm0 f = infty_norm0 g.
Proof.
move => abfg; rewrite /infty_norm0 /=; congr (sup _).
apply/seteqP; split; move => _ [ y ? <- ]; exists y => //=;
by rewrite abfg// inE.
Qed.

Lemma ler_infty_normD (x y : V) : norm (x + y) <= norm x + norm y :> R.
Proof.
rewrite /norm/= -sup_sumE//; last 2 first.
  exact: normr_repr_has_sup.
  exact: normr_repr_has_sup.
apply: sup_le.
- move=> A -[s sab] <-{A}.
  rewrite /down/=.
  exists (`|repr x s| + `|repr y s|); split.
    exists (`|repr x s|).
      by exists s.
    exists (`|repr y s|) => //.
    by exists s.
  suff  -> : (repr (x + y) s = repr x s + repr y s) by exact: ler_normD.
  suff /eqmod_on_itv ->: repr (x + y) = repr x + repr y %[mod V] =>//.
    by rewrite inE.
  by rewrite Quotient.pi_add !reprK.
- by apply normr_repr_has_sup.
- rewrite /has_sup; split.
  + exists ((normr \o repr x) a + (normr \o repr y) a)=> /=.
    exists ((normr \o repr x) a) => //; [exists a => //; rewrite in_itv/= lexx ab // | ].
    by exists ((normr \o repr y) a) => //; exists a => //; rewrite in_itv/= lexx ab.
  + rewrite /has_ubound.
    exists (sup [set (normr \o repr x) x0 | x0 in `[a, b]] +
       sup [set (normr \o repr y) x0 | x0 in `[a, b]]).
    apply ubP => _ [x0 xs] [y0 ys] <-.
    rewrite lerD// ub_le_sup//.
      exact: (normr_repr_has_sup x).2.
    exact: (normr_repr_has_sup y).2.
Qed.

Lemma infty_normr0_eq0 (x : V) : norm x = 0 -> x = 0.
Proof.
rewrite /norm/infty_norm0 /= => H.
rewrite -(reprK x) -(reprK 0).
apply/eqquotP.
rewrite /Quotient.equiv_equiv/Quotient.equiv/=.
rewrite /ideal_itv/=.
apply mem_set; rewrite /cst /=.
apply funext => x0 /=.
rewrite patchE.
case : ifPn => // /set_mem in_itv.
rewrite /GRing.opp/GRing.add /=.
have -> : {in `[a, b], repr (0 : V) =1
                      (0 : continuousFunType `[a, b] [set: R])} => //.
- apply /eqmod_on_itv.
  by rewrite reprK /GRing.zero /= /Quotient.zero /= -lock.
- rewrite subr0.
  apply /eqP;rewrite -normr_le0.
  have := (sup_upper_bound (normr_repr_has_sup x)).
  rewrite H /ubound /= => H0.
  apply H0.
  by exists x0.
- by rewrite inE.
Qed.

Local Lemma infty_norm0_eq0 :
  infty_norm0 (0 : continuousFunType `[a, b] [set: R]) = 0.
Proof.
rewrite /infty_norm0.
rewrite -(sup1 0).
congr sup.
apply eq_set => /= z ;apply propext; split => [[x _ <- ] | ->]; rewrite ?normr0 => //.
exists a; by [rewrite bound_itvE | rewrite normr0 ].
Qed.

Local Lemma infty_norm0rMn (x : continuousFunType `[a, b] [set: R]) n :
  infty_norm0 (x *+ n) = infty_norm0 x *+ n.
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
exact: normr_has_sup.
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
  by rewrite -normrN.
by rewrite normrN.
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
   continuousFunType where U satisfies
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
Variables (t0 t1 : R).
Hypothesis t01 : t0 < t1.
Variable u0 : R.
Variable r : {posnum R}.
Let B := closed_ball u0 r%:num.

Local Lemma imageg_closure (g : R -> R) : {within `[t0, t1], continuous g} ->
  g @` `]t0, t1[ `<=` interior B -> g @` `[t0, t1] `<=` B.
Proof.
move => cont_g imageg _ [] x /= + <-.
rewrite in_itv /= => /andP[+ +]/=.
have /continuous_within_itvP := cont_g.
move=> /(_ t01)[]/=.
move => gcont gcontl gcontr.
have closet01 :  closed `[t0, t1] by exact: interval_closed.
have h0 x0 : g x0 \in (interior B : set R) -> g x0 \in B.
  rewrite /B interior_closed_ballE//.
  rewrite closed_ball_itv//.
  rewrite ball_itv 2!inE.
  exact: subset_itv_oo_cc.
case: ltgtP => [hyd|_|<-] // => _.
  case: ltgtP => [hyd'|_|->] // => _.
  apply/set_mem/h0/mem_set/imageg => /=.
  exists x => //=; rewrite in_itv /= hyd hyd' //.
  apply: (@closed_cvg  _ _ (t1^'-) _ g B) => //=.
    exact: closed_ball_closed.
  near=>t.
  apply/set_mem/h0/mem_set/imageg => /=.
  exists t => //=.
  by rewrite !in_itv/=; apply/andP; split.
move => _.
apply: (@closed_cvg  _ _ (t0^'+) _ g B) => //=.
  exact: closed_ball_closed.
near=>t.
apply/set_mem/h0/mem_set/imageg; exists t => //=.
by rewrite !in_itv/=; apply/andP; split.
Unshelve. all: end_near. Qed.

(*Local Lemma imageg_closure' (g : continuousFunType t0 t1)
    (imageg : g @` `]t0, t1[ `<=` interior B) : g @` `[t0, t1] `<=` B.
Proof.
apply imageg_closure => //=.
by apply cont_on_seg.
Qed.*)

End intermediate_lemma.

Section lemmas_from_a_previous_tentative.
Context {R : realType}.
Variables (u0 : R) (r : {posnum R}).
Let B := closed_ball u0 r%:num.

Local Lemma ball_minr (x a b : R): subset (ball x (minr a b)) (ball x b).
Proof.
have [le_xy | lt_yx] := lerP a b => //.
rewrite /ball => /= x0 bx0.
exact/lt_le_trans/le_xy.
Qed.

Variable d0 : {posnum R}.
Local Notation d := d0%:num.

End lemmas_from_a_previous_tentative.

Section lip_implies_cont.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
Variables (f : R -> R -> R) (t0 t1 : R).
Hypothesis t01 : t0 < t1.
Variable k : R.
Hypothesis k1 : k > 0.
Variables (u0 : R) (r : {posnum R}).
Let B := closed_ball u0 r%:num.

Hypothesis lip2 : {in `[t0, t1]%R, forall x, k.-lipschitz_B (f x)}.

Lemma cont2 : {in `[t0, t1]%R, forall x, {within B, continuous f x}}.
Proof.
move=> x xt01.
rewrite [B]closed_ball_itv//.
apply/continuous_within_itvP; first by rewrite ltrD2l gtrN.
split.
- move=> y yt01.
  move: (xt01); have := @lip2 x => /[apply] kfx.
  rewrite /continuous_at.
  apply/cvgrPdist_le => /= e e0.
  near=> y'.
  move: kfx => /(_ (y, y'))/=.
    have By : B y.
      rewrite /B closed_ball_itv//=.
      exact: subset_itv_oo_cc yt01.
    have By' : B y'.
      rewrite /B closed_ball_itv//=.
      rewrite in_itv/=; apply/andP; split.
        near: y'.
        exists (y - (u0 - r%:num)).
          by move: yt01; rewrite in_itv/= -subr_gt0 => /andP[].
        move=> z/=.
        rewrite ltr_distlC.
        by rewrite opprB addrCA subrr addr0 => /andP[/ltW].
      near: y'.
      exists ((u0 + r%:num) - y).
        by move: yt01; rewrite in_itv/= -(subr_gt0 y) => /andP[].
      move=> z/=.
      rewrite ltr_distlC => /andP[_].
      by rewrite addrCA subrr addr0 => /ltW.
   move=> /(_ (conj By By')).
  move=> /le_trans; apply.
  rewrite -ler_pdivlMl// mulrC.
  near: y'.
  (* TODO(rei): investigate *)
  exists (e / k).
    by rewrite divr_gt0//.
  by move=> z/= => /ltW.
- apply/cvgrPdist_le => /= e e0.
  near=> y'.
  move: (xt01); have := @lip2 x => /[apply].
  move=> /(_ (u0 - r%:num, y'))/=.
    have Bu0r : B (u0 - r%:num).
      rewrite /B closed_ball_itv//=.
      by rewrite in_itv/= lexx/= lerD2l gerN.
    have By' : B y'.
      rewrite /B closed_ball_itv//=.
      rewrite in_itv/=; apply/andP; split => //.
      near: y'.
      exists r%:num => //=.
      move=> z/=.
      rewrite ltr_distlC.
      rewrite subrK => /andP[_ /ltW + _] => /le_trans; apply.
      by rewrite lerDl.
   move=> /(_ (conj Bu0r By')).
  move=> /le_trans; apply.
  rewrite -ler_pdivlMl// mulrC.
  near: y'.
  (* TODO(rei): investigate *)
  exists (e / k) => /=.
    by rewrite divr_gt0//.
  by move=> z/= => /ltW.
- apply/cvgrPdist_le => /= e e0.
  near=> y'.
  move: (xt01); have := @lip2 x => /[apply].
  move=> /(_ (y', u0 + r%:num))/=.
    have By' : B y'.
      rewrite /B closed_ball_itv//=.
      rewrite in_itv/=; apply/andP; split => //.
      near: y'.
      exists r%:num => //=.
      move=> z/=.
      rewrite ltr_distlC addrK => /andP[/ltW + _ _].
      rewrite lerBlDl => /le_trans; apply.
      by rewrite lerDr.
    have Bu0r : B (u0 + r%:num).
      rewrite /B closed_ball_itv//=.
      by rewrite in_itv/= lexx/= lerD2l andbT gerN.
  move=> /(_ (conj By' Bu0r)).
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
Variables (f : R -> R -> R) (t0 t1 : R).
Hypothesis t01 : t0 < t1.
Variable (u0 : R) (r : {posnum R}).

Variable (g : R -> R).
Hypothesis cg : {within `[t0, t1], continuous g}.

Let B := closed_ball u0 r%:num.

Variable k : R.
Hypothesis k0 : k > 0.
(* properties of the function f defining the differential equation: *)
(* k-lipschitz for all t *)
Hypothesis lip2 : {in `[t0, t1]%R, forall x, k.-lipschitz_B (f x)}.
(* within-continuous for all y *)
Hypothesis cont1 : {in B, forall y, {within `[t0, t1], continuous f ^~ y}}.


Local Lemma picard_from_cont'_isContinuousFunBuild_helper
    (imageg : g @` `[t0, t1] `<=` B) :
  f x (g x) @[x --> t0^'+] --> f t0 (g t0).
Proof.
apply/cvgrPdist_le => /= e e0.
have dd : t0 \in `[t0, t1]%R.
  by rewrite  in_itv/= lexx /= ltW.
have e20 : 0 < e / 2 by rewrite divr_gt0.
(* use continuity in first variable *)
have c1_ineq :  \forall t \near t0^'+,  `|f t0 (g t0) - f t (g t0)| <= (e/2).
  have : g t0 \in (B : set R).
   apply/mem_set.
   apply: imageg => /=.
   by exists t0 => //=.
  move /(cont1)/continuous_within_itvP => /(_ t01).
  move=> [_ + _].
  rewrite cvgrPdist_le /=.
  exact.
have gtd :  \forall t \near t0^'+, g t \in (B : set R).
  near=>t.
  apply/mem_set.
  apply: imageg => /=; exists t => //.
  rewrite in_itv/=; apply/andP; split => //.
  near: t.
  by apply: nbhs_right_le.
(* use continuity of g *)
have cg_ineq :  \forall t \near (t0)^'+,  `|(g (t0)) - (g t)| <= k^-1 *(e/2).
  have /continuous_within_itvP := cg.
  move/(_ t01) => [_ + _].
  move/cvgrPdist_le => /(_  (k^-1 * (e / 2)) ).
  apply.
  by rewrite mulr_gt0//invr_gt0.
(* use Lipschitz continuity *)
have c2_ineq :  \forall t \near (t0)^'+,  `|f t (g (t0)) - f t (g t)| <= (e/2).
  near=> t.
  have td' : t \in `[(t0), t1]%R.
    rewrite in_itv /=;apply /andP;split=>//.
    by rewrite ltW//.
  have gNdB: B (g (t0)).
    apply: imageg => //=.
    by exists (t0) => //=.
  have Bgt : B (g t).
    apply: imageg => //=.
    by exists (t) => //=.
  move: lip2 => /(_ _ td').
  move /(_ (g t0, g t)) => /=.
  move=> /(_ (conj gNdB Bgt)).
  move/le_trans; apply.
  rewrite -ler_pdivlMl //.
  by near:t.
near=>t.
rewrite -(subrKA (f t (g t0)) (f (t0) (g (t0)))).
rewrite (le_trans (ler_normD _ _))//.
rewrite (splitr e) lerD//;  by near:t.
Unshelve. all: end_near. Qed.

(* TODO: this proof is almost of copipe *)
Local Lemma picard_from_cont'_isContinuousFunBuild_helper_left
    (imageg : g @` `[t0, t1] `<=` B) :
  f x (g x) @[x --> t1^'-] --> f t1 (g t1).
Proof.
apply/cvgrPdist_le => /= e e0.
have dd : t1 \in `[t0, t1]%R.
  by rewrite in_itv/= lexx /= andbT ltW.
have e20 : 0 < e / 2 by rewrite divr_gt0.
(* use continuity in first variable *)
have c1_ineq :  \forall t \near t1^'-,  `|f t1 (g t1) - f t (g t1)| <= e / 2.
  have : g t1 \in (B : set R).
   apply/mem_set.
   apply: imageg => //=.
   by exists t1 => //.
  move /(cont1)/continuous_within_itvP => /(_ t01).
  move=> [_ _ +].
  rewrite cvgrPdist_le /=.
  exact.
have gtd :  \forall t \near t1^'-, g t \in (B : set R).
  near=>t.
  apply/mem_set.
  apply: imageg => /=; exists t => //.
  rewrite in_itv/=; apply/andP; split => //.
  near: t.
  by apply: nbhs_left_ge.
(* use continuity of g *)
have cg_ineq :  \forall t \near (t1)^'-,  `|(g (t1)) - (g t)| <= k^-1 *(e/2).
  have /continuous_within_itvP := cg.
  move/(_ t01) => [_ _ +].
  move/cvgrPdist_le => /(_  (k^-1 * (e / 2)) ).
  apply.
  by rewrite mulr_gt0//invr_gt0.
(* use Lipschitz continuity *)
have c2_ineq :  \forall t \near (t1)^'-,  `|f t (g (t1)) - f t (g t)| <= (e/2).
  near=> t.
  have td' : t \in `[(t0), t1]%R.
    rewrite in_itv /=;apply /andP;split=>//.
    by rewrite ltW//.
  have gNdB: B (g (t1)).
    apply: imageg => /=.
    by exists (t1) => //=.
  have Bgt : B (g t).
    apply: (imageg).
    by exists (t) => //=.
  move: lip2 => /(_ _  td').
  move /(_ (g t1, g t)) => /=.
  move=> /(_ (conj gNdB Bgt)).
  move/le_trans; apply.
  rewrite -ler_pdivlMl //.
  by near:t.
near=>t.
rewrite -(subrKA (f t (g t1)) (f (t1) (g (t1)))).
rewrite (le_trans (ler_normD _ _))//.
rewrite (splitr e) lerD//;  by near:t.
Unshelve. all: end_near. Qed.

End intermediate_lemma.

Definition picard_from_cont' {R : realType} (U := R)
  (u0 : U) (r : R)
  (B := closed_ball u0 r)
  (f : R -> U -> R) (g : R -> U)
    (t0 t1 : R)
    (imageg : g @` `[t0, t1] `<=` (*interior*) B) : R -> R :=
  fun t => u0 + (\int[lebesgue_measure]_(x in `[t0, t]) f x (g x))%R.

Lemma proveme {R : realType} (a b : R) (g : R -> R) :
  {within `[a, b], continuous g} ->
  {within `[a, b], continuous (g \o -%R)}.
Abort.

Section f_g_comp.
Context {R : realType}.
(*Variable U : normedModType R.*)
Let U := R.
Local Notation mu := lebesgue_measure.
Variables (f : R -> U -> R) (a b : R).
Hypothesis ab : a <= b.
Variables (u0 : U) (r : {posnum R}).

Let B : set R := closed_ball u0 r%:num.

Variable k : R.
Hypothesis k0 : k > 0.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (f x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous f ^~ y}}.

Variable g : R -> U.
Variable cg : {within `[a, b], continuous g}.
Hypothesis imageg : g @` `[a, b] `<=` B.

Lemma within_continuous_tmp :
  {within `[a, b], continuous fun x0 : R => f x0 (g x0)}.
Proof.
move: ab; rewrite le_eqVlt => /predU1P[<-| ab'].
  by rewrite set_itv1; exact: continuous_subspace1.
apply/continuous_within_itvP; [by [] | split].
- move=> x; rewrite in_itv/= => /andP[ndx dx].
  rewrite /continuous_at.
  pose f' := uncurry f.
  apply/cvgrPdist_le => /= e e0.
  have gxB : g x \in ((*interior*) B : set R).
    apply/mem_set/imageg => /=; exists x => //.
    by rewrite in_itv/= (ltW ndx) (ltW dx).
  have H : r%:num - `|g x - u0| >= 0.
    move: gxB.
    rewrite /B.
    rewrite !closed_ball_itv//.
    rewrite inE /=.
    rewrite in_itv/=/= => L.
    by rewrite subr_ge0 ler_distl.
  near=> t.
  rewrite /f'.
  rewrite -(subrKA (f t (g x)) (f x (g x))).
  rewrite (le_trans (ler_normD _ _))//.
  rewrite (splitr e) lerD//.
  + near: t.
    near_simpl.
    have /cont1 : g x \in B.
      apply/mem_set.
      apply/imageg => /=; exists x => //.
      by rewrite in_itv/= (ltW ndx) (ltW dx).
    move/continuous_within_itvP => /(_ ab').
    move=> [+ Htmp1 Htmp2].
    move/(_ x).
    rewrite /continuous_at.
    have e20 : 0 < e / 2 by rewrite divr_gt0.
    rewrite !in_itv/= ndx dx => /(_ isT).
    move/cvgrPdist_le => /(_ _ e20)[r0 /= r0_gt0 Br0].
    near=> t.
    apply: Br0 => //.
    rewrite -/(ball x r0 t).
    near: t.
    near_simpl.
    exact: (near_ball x _ r0_gt0).
  + have := @lip2 t.
    have t1dd : t \in `[a, b]%R.
      near: t.
      exists (Num.min (b - x) (x - a)) => /=.
        rewrite lt_min subr_gt0 dx/=.
        by rewrite subr_gt0.
      move=> z/=.
      rewrite lt_min => /andP[H1 H2].
      rewrite in_itv/=; apply/andP; split.
        move: H2.
        by rewrite ltr_distlC subKr => /andP[/ltW  ].
      move: H1.
      by rewrite ltr_distlC (addrC x (b-x)) subrK => /andP[_ /ltW].
    move/(_  t1dd).
    move/set_mem in gxB.
    have Bgt : B (g t).
      apply: imageg => /=.
      by exists t => //.
    move/(_ (g x, g t)) => /=.
    move/(_ (conj gxB Bgt)).
    move=> /le_trans; apply.
    rewrite -ler_pdivlMl//.
    near: t.
    move/continuous_within_itvP : cg => /(_ ab')[+ _ _] => /(_ x).
    rewrite in_itv/= ndx dx => /(_ isT).
    rewrite /continuous_at => /cvgrPdist_le.
    apply.
    by rewrite mulr_gt0 ?divr_gt0 ?invr_gt0//.
- by apply: (@picard_from_cont'_isContinuousFunBuild_helper R f a b ab' u0 r g _ _ k0) => //.
- by apply: (@picard_from_cont'_isContinuousFunBuild_helper_left R f a b ab' u0 r g _ _ k0) => //.
Unshelve. all: end_near. Qed.

End f_g_comp.

(* first, we define picard_from_cont
   that takes a function continuous over a closed ball *)
Section picard_from_cont'.
Context {R : realType}.
(*Variable U : normedModType R.*)
Let U := R.
Local Notation mu := lebesgue_measure.
Variables (f : R -> U -> R) (a b : R).
Hypothesis ab : a <= b.
Variables (u0 : U) (r : {posnum R}).

Let B : set R := closed_ball u0 r%:num.

Variable k : R.
Hypothesis k0 : k > 0.
(* properties of the function f defining the differential equation: *)
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (f x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous f ^~ y}}.

Variable g : R -> U (*contFunBallType d0*).
Variable cg : {within `[a, b], continuous g}.
Hypothesis imageg : g @` `[a, b] `<=` B.

Lemma set_fun_picard_from_cont' :
  {homo picard_from_cont' f imageg : x / `[a, b] x >-> [set: R] x}.
Proof. by []. Qed.

HB.instance Definition _ :=
  @isFun.Build (subspace `[a, b]) _ `[a, b] [set: R] (picard_from_cont' f imageg)
    (set_fun_picard_from_cont').

Lemma within_continuous_picard_from_cont' :
  {within `[a, b], continuous (picard_from_cont' f imageg)}.
Proof.
rewrite /picard_from_cont'.
suff: {within `[a, b], continuous (fun t => \int[mu]_(x0 in `[a, t]) f x0 (g x0))}.
  move=> abf x.
  apply: cvgD.
    exact: cvg_cst.
  exact: abf.
move=> /= x.
apply: parameterized_integral_continuous => //.
apply: continuous_compact_integrable; first exact: segment_compact.
move=> {x}.
exact: (within_continuous_tmp ab k0 lip2 cont1).
Qed.

HB.instance Definition _ := isContinuous.Build (subspace `[a, b]) R
  (picard_from_cont' f imageg : subspace _ -> R)
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
Let U := R(* normedModType R*).
Variables (f : R -> U -> R) (a b : R).
Variables (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.

Definition picard_from_cont
  (k : R) (lcf_x : {in `[a, b]%R, forall x, k.-lipschitz_B (f x)})
  (cf_y : {in B, forall y, {within `[a, b], continuous f ^~ y}})
  (g : R -> R) : R -> R :=
match pselect (g @` `[a, b] `<=` (*interior*) B) with
| left imageg => @picard_from_cont' R u0 r%:num f g a b imageg
| _ => cst 0
end.

End picard_from_cont.

Lemma sup_ge0 {R : realType} (A : set R) : (forall x, A x -> 0 <= x) -> 0 <= sup A.
Proof.
move=> Ax.
have [->|/set0P[a Aa]] := eqVneq A set0; first by rewrite sup0.
have [supA|supA] := pselect (has_sup A).
  rewrite (le_trans (Ax _ Aa))// ub_le_sup//.
  by case: supA.
by rewrite /sup supremum_out.
Qed.

Lemma lipschitzW {R : realType} {T U W : normedModType R} (A B : set T) C (f : T -> U -> W) k :
  A `<=` B -> {in B, forall x, k.-lipschitz_C (f x)} -> {in A, forall x, k.-lipschitz_C (f x)}.
Proof.
move=> AB H x xA.
apply: H.
by apply/mem_set/AB/set_mem.
Qed.
(* NB: why is in1_subset_itv so specialized?! *)

Lemma within_continuous_comp_norm {R : realType} a y (f : R -> R) :
  a <= y ->
  {within `[a, y], continuous fun x => f x} ->
  {within `[a, y], continuous fun x => `|f x|}.
Proof.
rewrite le_eqVlt => /predU1P[<-|ay].
  rewrite set_itv1 => _.
  exact: continuous_subspace1.
move/continuous_within_itvP => /(_ ay)[H1 H2 H3].
apply/continuous_within_itvP => //; split => //.
  move=> z zay.
  apply: continuous_comp => //.
    by apply: H1.
  exact: norm_continuous.
apply: cvg_comp.
  apply: H2.
  by apply: cvg_norm.
apply: cvg_comp.
apply: H3.
by apply: cvg_norm.
Qed.
(* TODO *)
Lemma integrable_norm d {T : measurableType d} {R : realType}
  (mu : {measure set T -> \bar R}) (D : set T) (f : T -> R) :
  mu.-integrable D (EFin \o f) ->
  mu.-integrable D (EFin \o (normr \o f)).
Proof.
move=> /integrableP[mf foo]; apply/integrableP; split.
  do 2 apply: measurableT_comp => //.
  exact/measurable_EFinP.
by under eq_integral do rewrite /= normr_id.
Qed.
(* second, we define picard_to_cont
   that takes a function continuous over a closed ball
   and returns a function continuous over a closed ball *)
Section picard_to_cont.
Context {R : realType}.
Let U := R.
Local Notation mu := lebesgue_measure.
Variables (f : R -> U -> R) (a b : R) (k : R).
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

(* Todo : rename *)

Lemma in_switch  (I : interval R) P : {in [set` I],forall x, P x} <-> {in I,forall x, P x}.
Proof.
  split => [h x xI| h x xI];apply h.
  by rewrite inE.
  by rewrite inE in xI.
Qed.

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

Local Notation picard_from_cont_not := (@picard_from_cont R f a (a + Delta) u0 r k lip2_Delta cont1_Delta).

Lemma Delta_gt0 : 0 < Delta.
Proof.
rewrite lt_min subr_gt0 ab/=.
rewrite lt_min mulr_gt0//=.
  by rewrite divr_gt0//.
rewrite invr_gt0//.
rewrite ltr_wpDr//.
  exact: hmax_ge0.
by rewrite mulr_gt0//.
Qed.

Let aaDelta : a < a + Delta.
Proof. by rewrite ltrDl Delta_gt0. Qed.

Import Rcont_on_seg.

Local Notation V := (quot_continuousFunType (ltW aaDelta)).

Definition restrictedV := [set f : V | f @` `[a, a + Delta] `<=` (*interior*) B ].

Lemma set_fun_picard_from_cont (g : V) :
  set_fun `[a, a + Delta] setT (picard_from_cont_not g).
Proof.
  by [].
Qed.

HB.instance Definition _ (g : V) := @isFun.Build
  (subspace `[a, a + Delta]) R
  `[a, a + Delta] setT (picard_from_cont_not g) (set_fun_picard_from_cont g).

Lemma continuous_picard_from_cont (g : V) :
  {within `[a, a + Delta], continuous (picard_from_cont_not g)}.
Proof.
have := (@cts_fun _ _ g).
rewrite /picard_from_cont.
case: pselect => //=.
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
Lemma integrable_comp (F : V) y:  y \in `[a, (a + Delta)]%R ->   [set F x | x in `[a, y]] `<=` closed_ball u0 r%:num -> mu.-integrable `[a, y] (EFin \o (fun t : R => f t (F t))).
Proof.
  move => yaaDelta ab0r.
  apply: continuous_compact_integrable.
    by apply: segment_compact.
   move: (yaaDelta); rewrite  in_itv/= => /andP[]. 
   move=> ay yaDelta.
   apply: (within_continuous_tmp ay k0).
  - apply/in_switch.
    move /in_switch : lip2_Delta.
    apply: lipschitzW.
    apply: subset_itvl.
    by rewrite bnd_simp.
  - rewrite -/B.
    move=> x xB.
    have := cont1_Delta xB.
    apply: continuous_subspaceW.
    apply: subset_itvl.
    by rewrite bnd_simp.
  - have := @cts_fun _ _ F.
    apply: continuous_subspaceW.
    apply: subset_itvl.
    by rewrite bnd_simp.
  - exact: ab0r.
Qed.

Lemma set_fun_picard_to_cont :
  set_fun restrictedV restrictedV picard_to_cont.
Proof.
move=> F.
rewrite /restrictedV/= => invariant _/= [y yaaDelta <-].
rewrite /picard_to_cont.
rewrite /B.
rewrite closed_ball_itv//=.
rewrite in_itv//=.
rewrite [X in _ <= X <= _](_ : _ = (picard_from_cont_not F) y); last first.
  have /eqmod_on_itv : (repr (\pi_(V)%qT (picard_from_cont_not F)) =
       picard_from_cont_not F %[mod V])%qT.
    by rewrite reprK.
  move=> <-//.
  have aDeltab : (a + Delta) <= b.
    by rewrite -lerBrDl ge_min lexx.
  by rewrite inE/=.
rewrite /picard_from_cont/=.
case: pselect => /= abu0r; last first.
  done.
rewrite /picard_from_cont'.
rewrite -ler_distl.
rewrite -addrA subrKC.
rewrite (le_trans (le_normr_Rintegral _ _))//=.
  rewrite /=.
  apply integrable_comp; first by done.
  apply: subset_trans abu0r. 
  apply: image_subset.
  apply: subset_itvl.
  rewrite bnd_simp.
  by move : yaaDelta;rewrite in_itv /= => /andP[].
have integrable2 :   mu.-integrable `[a, y] (EFin \o (fun x  => f x (F x))).
    apply integrable_comp => //=.
    apply: subset_trans abu0r.
    apply image_subset.
    apply: subset_itvl.
    rewrite bnd_simp.
    by move : yaaDelta;rewrite in_itv /= => /andP[].
have integrable1 :   mu.-integrable `[a, y]
    (fun x : g_sigma_algebraType (R.-ocitv).-measurable =>
     (`|f x (F x) - f x u0|%:E + `|f x u0|%:E)).
    rewrite integrableD //=.
    apply integrable_norm => /=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinD.
    rewrite integrableD //=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinN.
    rewrite integrableN //=.
    apply continuous_compact_integrable => //=.
    exact: segment_compact.
    apply /continuous_subspaceW/cont1_Delta.
    apply: subset_itvl.
    rewrite bnd_simp.
    by move : yaaDelta;rewrite in_itv /= => /andP[].
    rewrite /B inE.
    by apply closed_ballxx.
    apply integrable_norm => /=.
    apply continuous_compact_integrable => //=.
    exact: segment_compact.
    apply /continuous_subspaceW/cont1_Delta.
    apply: subset_itvl.
    rewrite bnd_simp.
    by move : yaaDelta;rewrite in_itv /= => /andP[].
    rewrite /B inE.
    by apply closed_ballxx.
rewrite (@le_trans _ _ (\int[mu]_(x in `[a, y]) (`|f x (F x) - f x u0| + `|f x u0|)))//.
  apply: le_Rintegral => //=.
  - apply integrable_norm => //=.
  - move=> x xay.
    rewrite (le_trans _ (ler_normD _ _))//.
    by rewrite subrK.
rewrite (@le_trans _ _ (\int[mu]_(x in `[a, y]) (k * `|F x - u0| + hmax)))//.
  apply: le_Rintegral => //=.
  - under [x in integrable _ _  x]eq_fun do rewrite EFinD.
    rewrite integrableD //=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinM.
    rewrite integrableMr //=.
    exact: bounded_cst.
    apply integrable_norm => //=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinB.
    rewrite integrableB //=.
    apply continuous_compact_integrable => //.
    exact: segment_compact.
    apply /continuous_subspaceW/cts_fun.
    apply: subset_itvl.
    rewrite bnd_simp.
    by move : yaaDelta;rewrite in_itv /= => /andP[].
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
      move/(_ (F x, u0)).
      apply.
      split => /=.
        apply: invariant => /=.
        exists x => //.
        move : xay.
        apply: subset_itvl.
        rewrite bnd_simp.
        by rewrite (itvP yaaDelta).
      by apply: closed_ballxx.
    rewrite /hmax.
    apply: ub_le_sup => /=.
      have [M [Mb1 Mb2]] : bounded_set [set `|f t u0| | t in `[a,b]].
        apply compact_bounded.
        apply continuous_compact.
        apply within_continuous_comp_norm.
        by rewrite ltW.
        by apply cont1;rewrite inE;apply: closed_ballxx.
        by apply segment_compact.
      exists (M+1).
      move => _ [x0 x0ab] <- /=.
      rewrite -normr_id.
      apply Mb2.
      by rewrite ltrDl.
      exists x0 => //.
    exists x => //.
    move: xay; rewrite !in_itv/= => /andP[] -> /=.
    move /le_trans.
    apply.
    move : yaaDelta.
    rewrite in_itv /= => /andP[].
    move => _ /le_trans;apply.
    by rewrite -lerBrDl /Delta ge_min lexx.
rewrite (@le_trans _ _ (\int[mu]_(x in `[a, y]) ((k * r%:num + hmax))))//.
  apply: le_Rintegral => //=.
  - under [x in integrable _ _  x]eq_fun do rewrite EFinD.
    rewrite integrableD //=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinM.
    rewrite integrableMr //=.
    exact: bounded_cst.
    apply integrable_norm => //=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinB.
    rewrite integrableB //=.
    apply continuous_compact_integrable => //.
    exact: segment_compact.
    apply /continuous_subspaceW/cts_fun.
    apply: subset_itvl.
    rewrite bnd_simp.
    by move : yaaDelta;rewrite in_itv /= => /andP[].
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
      rewrite closed_ball_itv//= in_itv/=.
      by rewrite ler_distl.
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
    by rewrite mulr_gt0//.
  exact: hmax_ge0.
rewrite 2!ge_min.
by rewrite mulrC lexx/= orbT.
Qed.

Lemma picard_from_cont_simpl g t :
  [set g x | x in `[a, (a + Delta)%E]] `<=` closed_ball u0 r%:num ->
  picard_from_cont_not g t = u0 + (\int[mu]_(x in `[a, t]) f x (g x))%R.
Proof.
  rewrite /picard_from_cont_not.
   case: pselect => [| // ] .
  by rewrite /picard_from_cont'.
Qed.
Lemma picard_to_cont_init g :
  [set g x | x in `[a, (a + Delta)%E]] `<=` closed_ball u0 r%:num ->
  picard_from_cont_not g a = u0.
Proof.
  move => h.
  rewrite picard_from_cont_simpl => //.
  by rewrite set_itv1 Rintegral_set1 addr0.
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

Section picard_to_cont_normedtype.
Context {R : realType} {r s : R} (rs : r <= s).
Local Notation mu := lebesgue_measure.
Import Rcont_on_seg.
Local Notation V := (quot_continuousFunType rs).

HB.instance Definition _ := PseudoMetric.copy V (pseudoMetric_normed V).
HB.instance Definition _ := isPointed.Build V 0.

End picard_to_cont_normedtype.

Section picard_to_cont_normedtype2.
Context {R : realType} {a b : R} (ab : a <= b).
Variables (f : R -> R -> R) (k : R).
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz (f x)}.
Hypothesis cont1 : {in `[a, b], forall y, {within `[a, b], continuous f ^~ y}}.
Import Rcont_on_seg.
Local Notation contFunBallType := (quot_continuousFunType ab).

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
Import Rcont_on_seg.
Notation V := (quot_continuousFunType rs).

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

Local Lemma repr_mult l (x : V) a :
  a \in `[r, s] -> repr (l *: x) a = l *: (repr x a).
Proof.
move=> ars.
have : repr (l *: x) = l *: repr x %[mod V] by case: piP.
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
- apply: ge_sup.
    exists (`|repr (l *: x) r|) => /=.
    exists r => //.
    by rewrite in_itv/= lexx/=.
  move=> _/= [a ars] <-.
  rewrite repr_mult; last by rewrite inE.
  rewrite normrZ ler_wpM2l//.
  apply: ub_le_sup.
    by apply @normr_has_sup.
  by exists a.
- rewrite -sup_mult => //; last by apply @normr_has_sup.
  apply sup_le; [ | | by apply @normr_has_sup].
  + move => _  [_ [x0 x0rs] <- <-].
    exists (normr l * (normr \o repr x) x0);split => //=;exists x0.
      by rewrite inE.
    rewrite repr_mult; last by rewrite inE.
    by rewrite normrZ.
  + exists (normr (l * x r)), (normr (repr x r)).
      exists r => //=.
      by rewrite bound_itvE.
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

Import Rcont_on_seg.
Notation V := (quot_continuousFunType (ltW (aaDelta_subproof f ab u0 r k0 rho))).
Notation Vr := (@restrictedV _ f a b k ab u0 r k0 rho).

HB.about cst.

Check @cst (subspace `[a, a + Delta f a b k u0 r rho]) R u0 : {fun `[a, a + Delta f a b k u0 r rho] >-> [set: R]}.

Check @cst (subspace `[a, a + Delta f a b k u0 r rho]) R u0 : continuousType (subspace `[a, a + Delta f a b k u0 r rho]) R.

Check @cst (subspace `[a, a + Delta f a b k u0 r rho]) R u0 : continuousFunType `[a, a + Delta f a b k u0 r rho] [set: R].

Lemma restrictedVball : Vr = @closed_ball R V
  (pi V (@cst (subspace `[a, a + Delta f a b k u0 r rho]) R u0)) r%:num.
Proof.
  rewrite closed_ballE => //.
  rewrite /Vr.
  apply eq_set => /= f' ;apply propext;split => h.
  - rewrite -(@reprK _ V f').
    rewrite /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
    rewrite qnorm_piE.
    apply infty_norm_le => /=.
    apply (ltW (aaDelta_subproof f ab u0 r k0 rho)).
    move => x adx.
    move /(_ (f' x)) : h.
    rewrite closed_ballE => //.
    apply.
    exists x => //.
    by rewrite inE in adx.
 -  move => _ [x xad] <-.
    rewrite closed_ballE => //.
    rewrite /closed_ball_ /=.
have -> :  (u0 - f' x) = ((pi V (cst u0)) - f' : V) x.
    by rewrite -(@reprK _ V f')  /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add !eval_mod_on_itv => //;rewrite inE.
    rewrite -(@reprK _ V f').
    rewrite /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
    rewrite eval_mod_on_itv;last by rewrite inE.
    rewrite -inE in xad.
    apply (le_trans (infty_norm_ge (ltW (aaDelta_subproof f ab u0 r k0 rho)) _ xad)).
    rewrite -(qnorm_piE (ltW (aaDelta_subproof f ab u0 r k0 rho))).
    by rewrite Quotient.pi_add Quotient.pi_opp reprK.
Qed.

Definition contrac : {fun Vr >-> Vr} :=
  @picard_to_cont R f a b k ab u0 r k0 lip2 cont1 rho.

Lemma set_fun_picard : set_fun Vr Vr contrac.
Proof.
by [].
Qed.

HB.instance Definition _ :=
  @isFun.Build _ _ Vr Vr contrac set_fun_picard.


(*Hypothesis dtwok : d0%:num < (2 * k)^-1.

Let twodk := (d0%:num * k) *+ 2.

Let twodk_ge0 : 0 <= twodk.
Proof. by rewrite /twodk mulrn_wge0// mulr_ge0// ltW. Qed.*)

Local Notation mu := (@lebesgue_measure _).

Lemma reprE (h : quot_continuousFunType (ltW (aaDelta_subproof f ab u0 r k0 rho))) x :
  (*x \in `[a, b] ->*) repr h x = h x.
Proof.
by [].
Qed.

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
rewrite qnorm_piE/=.
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
have integrable1 :  mu.-integrable `[a, t] (EFin \o(fun x0 => f x0 (x x0))).
  apply integrable_comp => //=.
  move => _ [x0 h] <-.
  apply: Hg => /=.
  exists x0 => //.
  apply /subset_itvl/h.
  rewrite bnd_simp.
  by move: tNdd; rewrite !in_itv/= => /andP[] .
have integrable2 :  mu.-integrable `[a, t] (EFin \o(fun x0 => f x0 (y x0))).
  apply integrable_comp => //=.
  move => _ [x0 h] <-.
  apply: Hg2 => /=.
  exists x0 => //.
  apply /subset_itvl/h.
  rewrite bnd_simp.
  by move: tNdd; rewrite !in_itv/= => /andP[] .
rewrite -RintegralB//=.
rewrite (le_trans (le_normr_Rintegral _ _))//=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinB.
    rewrite integrableB //=.
have integrable3 :   mu.-integrable `[a, t] (fun x0 => `|x x0 - y x0|%:E).
  apply integrable_norm => //=.
  under [x in integrable _ _  x]eq_fun do rewrite EFinB.
  rewrite integrableB //=.
  apply continuous_compact_integrable => //=.
  exact: segment_compact.
  apply /continuous_subspaceW/cts_fun.
  apply: subset_itvl.
  rewrite bnd_simp.
  by move : tNdd;rewrite in_itv /= => /andP[].
  apply continuous_compact_integrable => //=.
  exact: segment_compact.
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
    apply; split.
      apply: Vrx => /=.
      exists x0 => //.
      apply /subset_itvl/x0at.
      move: tNdd.
      by rewrite in_itv/= => /andP[Ndt].
    apply: Hg2 => /=.
    exists x0 => //.
    apply /subset_itvl/x0at.
    move: tNdd.
    by rewrite in_itv/= => /andP[Ndt].
  rewrite RintegralZl//=.
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
    apply (@eqmod_on_itv _  _ _ (ltW (aaDelta_subproof f ab u0 r k0 rho)) (repr x - repr y)) => //.
    by rewrite Quotient.pi_add Quotient.pi_opp !reprK //.
  apply: infty_norm_ge => //=.
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

Section completeness.
Context {R : realType}.
Variables  (a b : R).
Hypothesis ab : a <= b.

Import Rcont_on_seg.
Notation V := (quot_continuousFunType ab).

Check (V : pseudoMetricType R).
Check (V : normedModType R).

Lemma infty_norm_gt_V (f : V) e :
  `| f | <  e -> {in `[a, b], forall x : R, `|f x| < e}.
Proof.
rewrite -{1}(reprK f) qnorm_piE => h x xab.
exact/le_lt_trans/h/infty_norm_ge.
Qed.

Lemma infty_norm_le_V (f : V) e :
  {in `[a, b], forall x : R, `|f x| <= e} -> `| f | <=  e.
Proof.
move => h.
rewrite -(reprK f) qnorm_piE.
by apply infty_norm_le.
Qed.

Definition lim_fun (F : set_system V) (FF : ProperFilter F) (Fc : cauchy F) :
  subspace `[a, b] -> R :=
  fun t => lim (@^~t @ F).
Lemma lim_fun_is_fun (F : set_system V) (FF : ProperFilter F) (Fc : cauchy F) :
  @isFun (subspace `[a, b]) R `[a, b] [set: R] (@lim_fun F FF Fc).
Proof. by constructor. Qed.

HB.instance Definition _ F FF Fc := (@lim_fun_is_fun F FF Fc).

Lemma lim_fun_cvg_pt (F : set_system V) (FF: ProperFilter F) (Fc : cauchy F) :
  forall (e : R), e > 0 -> forall t, t \in `[a,b] ->
  \forall f \near F, `|lim_fun FF Fc t - (f : V) t| <= e.
Proof.
have /(_ _ _) /cauchy_cvg /cvg_app_entourageP cvF :
    forall t : R, t \in `[a,b] ->
      cauchy (fmap (fun (h : V) => h t) (fun x : set V => nbhs F (fun x0 : V => x x0))).
  move=> t tab A /= [e e0 ee]; rewrite near_simpl -near2E near_map2.
  apply : Fc.
  exists e => //.
  move => /= [f g].
  move /infty_norm_gt_V => h.
  apply ee => /=.
  have <- : (f - g : V) t = (f : V) t - (g : V) t.
    rewrite -(reprK f) -(reprK g)  /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
    by rewrite !eval_mod_on_itv.
  by apply h.
have  cvg_pt : forall (t : R),  t \in `[a,b] ->  x @[x --> fmap (fun h : V => h t) F] --> lim_fun FF Fc t.
  move => t tab.
  apply /cvg_entourageP.
  by apply cvF.
move => e e0 t tab.
move /(_ t tab) : cvg_pt.
move/cvgrPdist_le/(_ _ e0).
exact.
Qed.

Lemma lim_fun_cvg_uniform (F : set_system V) (FF: ProperFilter F) (Fc : cauchy F) :
  forall (e : R), e > 0 ->
  \forall f \near F, forall t, t \in `[a,b] -> `|lim_fun FF Fc t - (f : V) t| <= e.
Proof.
move => e e0.
have e20 : 0 < e/2 by rewrite divr_gt0.
have := (Fc _ (entourage_ball V (PosNum e20))).
move => [/= [ha hb] /= [n1 n2]] H.
near=>f.
move=>t tab.
near F => g.
rewrite -(subrKA (g t) (lim_fun FF Fc t)).
rewrite (le_trans (ler_normD _ _))//.
rewrite (splitr e) lerD//.
near:g.
by apply lim_fun_cvg_pt;rewrite // divr_gt0.
have c1 : ball f (e/2) g.
   apply (H (f,g)).
   split => //=.
   by near:f.
   by near:g.
   rewrite /ball /= in c1.
   rewrite /pseudoMetric_from_normedZmodType.ball /= in c1.
rewrite distrC.
have <- : (f - g : V) t = (f : V) t - (g : V) t.
  rewrite -(reprK f) -(reprK g)  /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
  by rewrite !eval_mod_on_itv.
  rewrite ltW //.
  by apply infty_norm_gt_V.
Unshelve. all: by end_near. Qed.

Lemma lim_fun_cont (F : set_system V) (FF : ProperFilter F) (Fc : cauchy F) :
  {within `[a, b], continuous (@lim_fun F FF Fc)}.
Proof.
move: ab; rewrite le_eqVlt => /predU1P[<-| ab'].
  by rewrite set_itv1; exact: continuous_subspace1.
have H : forall (e : R), e > 0 ->forall t, t \in `[a,b] -> \forall t' \near t, t' \in `[a,b] ->
    `|lim_fun FF Fc t - lim_fun FF Fc t'| <= e.
  move => e e0 t tab.
  near F => f.
  move /(continuous_within_itvP _ ab') : (@cts_fun _ _ f ) => [mc lc rc].
  move : (tab).
  rewrite -{1}setUitv1/=; last by rewrite bnd_simp ltW.
  rewrite -{1}setU1itv/=; last by rewrite bnd_simp.
  (* split t=a, t \in ]a,b[, t=b *)
  rewrite inE/= in_itv/= => -[[->|tab']|->].
  - near=> t' => t'ab.
    rewrite -(subrKA (f a) (lim_fun FF Fc a)).
    rewrite (le_trans (ler_normD _ _))//.
    rewrite (splitr e) lerD//.
      suff: forall t, t \in `[a,b] ->   `|lim_fun FF Fc t - f t| <= e / 2 by apply;rewrite inE /= in_itv/= lexx ltW //.
      near:f.
      by apply lim_fun_cvg_uniform;rewrite // divr_gt0 //.
    rewrite -(subrKA (f t') (f a)).
    rewrite (le_trans (ler_normD _ _))//.
    rewrite (splitr (e/2)) lerD//.
      move : t'ab.
      rewrite -{1}setU1itv/=; last by rewrite bnd_simp.
      rewrite inE/= in_itv/= => -[-> | ].
      rewrite subrr normr0 ltW //.
      do 2 rewrite divr_gt0 //.
      near:t'.
      move  /cvgrPdist_le : lc .
      move /( _ (e/ 2/ 2)) => [| e1 e10 eh].
      do 2 rewrite divr_gt0 //.
      exists e1 => //.
      move => x bx /andP [xa _].
      by apply eh.
    rewrite distrC.
    move : (t') t'ab.
    near:f.
    apply lim_fun_cvg_uniform; do 2 rewrite divr_gt0 //.
  - near=> t' => t'ab.
    rewrite -(subrKA (f t) (lim_fun FF Fc t)).
    rewrite (le_trans (ler_normD _ _))//.
    rewrite (splitr e) lerD//.
      move : (t) (tab).
      near:f.
      by apply lim_fun_cvg_uniform;rewrite // divr_gt0 //.
    rewrite -(subrKA (f t') (f t)).
    rewrite (le_trans (ler_normD _ _))//.
    rewrite (splitr (e/2)) lerD//.
      near:t'.
      move  /(_ _ tab'): mc.
      rewrite /continuous_at cvgrPdist_le /=.
      apply.
      do 2 rewrite divr_gt0 //.
    rewrite distrC.
    move : (t') t'ab.
    near:f.
    apply lim_fun_cvg_uniform; do 2 rewrite divr_gt0 //.
(* Todo: same as 1 *)
  - near=> t' => t'ab.
    rewrite -(subrKA (f b) (lim_fun FF Fc b)).
    rewrite (le_trans (ler_normD _ _))//.
    rewrite (splitr e) lerD//.
      suff: forall t, t \in `[a,b] ->   `|lim_fun FF Fc t - f t| <= e / 2 by apply;rewrite inE /= in_itv/= lexx ltW //.
      near:f.
      by apply lim_fun_cvg_uniform;rewrite // divr_gt0 //.
    rewrite -(subrKA (f t') (f b)).
    rewrite (le_trans (ler_normD _ _))//.
    rewrite (splitr (e/2)) lerD//.
      move : t'ab.
       rewrite -{1}setUitv1/=; last by rewrite bnd_simp ltW.
      rewrite inE/= in_itv/= => -[ | -> ];last first.
      rewrite subrr normr0 ltW //.
      do 2 rewrite divr_gt0 //.
      near:t'.
      move  /cvgrPdist_le : rc .
      move /( _ (e/ 2/ 2)) => [| e1 e10 eh].
      do 2 rewrite divr_gt0 //.
      exists e1 => //.
      move => x bx /andP [_ xb].
      by apply eh.
    rewrite distrC.
    move : (t') t'ab.
    near:f.
    by apply lim_fun_cvg_uniform; do 2 rewrite divr_gt0 //.
apply continuous_within_itvP => //; split.
- move => t tab.
  apply/cvgrPdist_le => /= e e0.
  near=>t'.
  have   : t' \in `[a,b].
    rewrite inE.
    apply subset_itv_oo_cc.
    near:t'.
    apply /at_right_in_segment.
    apply : open_itvcc_subset.
    apply: itv_open.
    by rewrite inE //.
  near:t'.
  apply: H => //.
  by rewrite inE; apply subset_itv_oo_cc.
- apply/cvgrPdist_le => /= e e0.
  near=>t'.
  have : t' \in `[a,b].
    rewrite inE /= in_itv/=.
    apply /andP;split;near:t'.
    by apply: nbhs_right_ge.
    by apply : nbhs_right_le.
  near:t'.
  apply : cvg_at_right_filter.
  apply cvg_id.
  apply: H => //.
  rewrite inE /= in_itv/= lexx ltW //.
apply/cvgrPdist_le => /= e e0.
near=>t'.
have : t' \in `[a,b].
  rewrite inE /= in_itv/=.
  apply /andP;split;near:t'.
  by apply: nbhs_left_ge.
  by apply : nbhs_left_le.
  near:t'.
  apply : cvg_at_left_filter.
  apply cvg_id.
  apply: H => //.
  rewrite inE /= in_itv/= lexx ltW //.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ F FF Fc :=
  isContinuous.Build (subspace `[a, b]) R (@lim_fun F FF Fc : subspace `[a, b] -> R) (@lim_fun_cont F FF Fc).

Fail Check (V : completeType).

Lemma cvg_V_entourageP  (F : set_system V) (FF : Filter F)
    (f : V) :
  F --> f <-> forall A, entourage A ->
              \forall g \near F, {in `[a, b], forall t : R, A (f t, (g : V) t)}.
Proof.
split => [/cvg_entourageP /= Ff A [eps eps0 /= H]|/=Ff].
   apply: (Ff [set fg : V*V| {in `[a, b], forall t : R, A (fg.1 t, fg.2 t)}]).
   exists eps => //.
   rewrite /pseudoMetric_from_normedZmodType.ball /=.
   move => /= x bx t tab.
   apply H => /=.
   have -> : ((x.1 : V) t - (x.2 : V) t = (x.1 - x.2 :V) t).
      rewrite -(reprK x.1) -(reprK x.2).
      rewrite /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
      by rewrite !eval_mod_on_itv.
   apply: infty_norm_gt_V => //.
apply/cvg_entourageP => /= A [e e0 sPA].
have e20 : 0 < e / 2 by rewrite divr_gt0.
have e2: (e / 2 < e).
   by rewrite ltr_pdivrMr// mulrC ltr_pMl //= ltrDr.
near=>g.
apply: sPA.
apply /le_lt_trans/e2.
apply infty_norm_le_V => /= .
move => t tab.
have -> : (f - g : V) t = f t - (g : V) t.
    rewrite -(reprK f) -(reprK g)  /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
    by rewrite !eval_mod_on_itv.
rewrite ltW //.
move : t tab.
near:g.
have := (Ff [set xy : R *R | ball xy.1 (PosNum e20)%:num xy.2]).
apply.
apply entourage_ball.
Unshelve. all: by end_near. Qed.

Lemma quot_cont_on_segType_cauchy_cvg :
  forall (F : set_system V), ProperFilter F -> cauchy F -> cvg F.
Proof.
move=> F FF Fc.
have /(_ _ _) /cauchy_cvg /cvg_app_entourageP cvF :
  forall t : R, t \in `[a,b] ->
    cauchy (fmap (fun (h : V) => h t) (fun x : set V => nbhs F (fun x0 : V => x x0))).
  move=> t tab A /= [e e0 ee]; rewrite near_simpl -near2E near_map2.
  apply : Fc.
  exists e => //.
  move => /= [f g].
  move /infty_norm_gt_V => h.
  apply ee => /=.
  have <- : (f - g : V) t = (f : V) t - (g : V) t.
    rewrite -(reprK f) -(reprK g)  /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
    by rewrite !eval_mod_on_itv.
  by apply h.
apply /cvg_ex.
exists ( pi V (@lim_fun F FF Fc : continuousFunType `[a, b] [set: R])).
apply /cvg_V_entourageP => /=.
move=> A /= entA.
near=>f.
move => t tab.
near F => g.
apply : (entourage_split (g t)) => //.

rewrite eval_mod_on_itv => //; first by near:g;apply: cvF.
move: (t) (tab); near: g; near: f; apply: nearP_dep; apply: Fc.
rewrite /nbhs /=.
have [e e0 ee] := (entourage_split_ent entA).
exists e => //.
move => [/= x y].
rewrite /pseudoMetric_from_normedZmodType.ball/=.
move /infty_norm_gt_V => h t tab.
apply ee => /=.
rewrite distrC.
have -> : ((x : V) t - (y : V) t = (x - y :V) t).
   rewrite -(reprK y) -(reprK x)  /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
   by rewrite !eval_mod_on_itv.
by apply: h.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ := Uniform_isComplete.Build V quot_cont_on_segType_cauchy_cvg.

Check (V : completeType).
End completeness.

Section picard_sketch.
Context {R : realType}.
Local Notation mu := lebesgue_measure.
Let U := R.

Variables (f : R -> U -> R) (a b : R) (k : R) (u0 : U) (r : {posnum R}).
Hypothesis ab : a < b.
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (f x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous f ^~ y}}.
Variable rho : {posnum R}.
Hypothesis rho1 : (rho%:num < 1).
(*Variable y_ : R -> R.
Hypothesis y_init_t : y_ 0 = 0.*)

(*Hypothesis dtwok : d0%:num < (2 * k)^-1.*)

Definition tmp : is_contraction (contrac ab k0 lip2 cont1 rho) :=
  (@is_contraction_picard_to_cont R f a b ab k k0 u0 r lip2 cont1 rho rho1).

Import Rcont_on_seg.
Let phi0 : quot_continuousFunType (ltW (aaDelta_subproof f ab u0 r k0 rho)) := 0. (* TODO: should be cst u0? *) (* 0 is init_y *)

Notation V := (quot_continuousFunType (ltW (aaDelta_subproof f ab u0 r k0 rho))).

Lemma Vr0 : (@restrictedV _ f a _ k _ u0 r k0 rho : set V) !=set0.
Proof.
exists (pi V (cst u0)).
move => _ [y x0] <-.
suff -> : quot_continuousFunType_to_fun  (\pi_(V)%qT (cst u0)) y = u0.
  by apply closed_ballxx.
rewrite /quot_continuousFunType_to_fun/=.
have /eqmod_on_itv : (repr (\pi_(V)%qT (cst u0)) = cst u0 %[mod V])%qT.
  by rewrite reprK.
apply.
by rewrite inE.
Qed.

(* Check (fun t =>lim  (@^~t @ F)). *)

(* apply/cvg_ex; exists (pi V (fun t => lim (@^~t @ F))). *)
(* Check lim. *)
(* Search cvg_to. *)
(* have /(_ _) /cauchy_cvg /cvg_app_entourageP cvF : cauchy (@^~_ @ F). *)

(*   move=> t A /= entA; rewrite near_simpl -near2E near_map2. *)
(*   near=>x. *)

(*   apply Fc. *)
(*   by apply: Fc; exists A. *)
(* apply/cvg_ex; exists (fun t => lim (@^~t @ F)). *)
(* apply/cvg_fct_entourageP => A entA; near=> f => t; near F => g. *)
(* apply: (entourage_split (g t)) => //; first by near: g; apply: cvF. *)
(* move: (t); near: g; near: f; apply: nearP_dep; apply: Fc. *)
(* by exists (split_ent A)^-1%relation => /=. *)
(* Unshelve. all: by end_near. Qed. *)
(* Admitted. *)

Notation Vr := (@restrictedV _ f a b k ab u0 r k0 rho).
Lemma closed_Vr : closed Vr.
Proof.
  rewrite restrictedVball.
  apply closed_ball_closed.
Qed.

Let phioo : quot_continuousFunType (ltW (aaDelta_subproof f ab u0 r k0 rho)) :=
  sval (cid2 (@banach_fixed_point R V Vr
  (@contrac _ f a b ab _ k0 u0 r lip2 cont1 rho)
  (@is_contraction_picard_to_cont _ f _ _ ab _ k0 u0 r lip2 cont1 rho rho1)
  closed_Vr
  Vr0)).

Let phiooE : phioo = (@contrac _ f a b ab _ k0 u0 r lip2 cont1 rho) phioo.
Proof.
rewrite {}/phioo.
by case: cid2.
Qed.

Lemma contrac_simpl g t : Vr g ->  t \in `[a, (a + Delta f a b k u0 r rho)%E] ->
  (@contrac _ f a b ab _ k0 u0 r lip2 cont1 rho) g t =
  u0 + (\int[mu]_(x in `[a, t]) f x (g x))%R.
Proof.
move => Vrg taad.
rewrite /contrac.
rewrite eval_mod_on_itv //.
by apply picard_from_cont_simpl.
Qed.


Lemma eq_on_itv_deriv  c d (g h : R -> R) :
  {in `]c,d[, g =1 h} -> {in `]c,d[, g^`() =1 h^`()}.
Proof.
  move => d1 x xcd.
  rewrite !derive1E.
  apply near_eq_derive => //.
  near=>  x0.
  apply d1.
  rewrite inE.
  near:x0.
  apply /near_in_itvoo.
  by rewrite -inE.
Unshelve. all: by end_near. Qed.

Theorem picard_lindelof_existence :
  phioo a = u0 /\
  {in `]a, a + Delta f a b k u0 r rho[, forall x, phioo^`() x = f x (phioo x)}.
Proof.
  have Vrphioo : Vr phioo.
    by apply (svalP (cid2 (banach_fixed_point (is_contraction_picard_to_cont ab k0 lip2 cont1 rho1) closed_Vr Vr0))).

  split.
  - rewrite phiooE.
    rewrite /contrac.
    rewrite eval_mod_on_itv; last by rewrite inE/= in_itv/= lexx (ltW (aaDelta_subproof f ab u0 r k0 rho)).
    rewrite /picard_from_cont /= picard_to_cont_init //.
  move => t tad.
  rewrite {1}phiooE.
  have altd : a < (a + Delta f a b k u0 r rho)%E by rewrite ltrDl Delta_gt0.
  suff -> :  (contrac ab k0 lip2 cont1 rho phioo)^`() t =  (fun x0 => (u0 + (\int[mu]_(x in `[a, x0]) f x (phioo x))%R))^`()  t.

    move : (tad).
    rewrite inE /= in_itv /= => /andP[ta taDelta].
    have Fint :  (mu.-integrable `[a, (a + Delta f a b k u0 r rho)%E] (EFin \o (fun x : R => f x (phioo x)))).
      apply integrable_comp => //.
      by rewrite   in_itv /= lexx ltW.
    have Fcont :  {for t, continuous (fun x0 : R => f x0 (phioo x0))}.
      rewrite inE in tad.
      apply: (within_continuous_continuous _ _ tad) => //.
      apply: (within_continuous_tmp _ k0 _ (u0 := u0) (r := r)).
      by rewrite ltW.
      exact: lip2_Delta.
      exact: cont1_Delta.
      exact: cts_fun.
      exact: Vrphioo.
    have [H1 H2] := @continuous_FTC1_closed _ (fun x => f x (phioo x)) a t _ taDelta Fint ta Fcont.
    rewrite derive1E deriveD /=;last 2 first.
    exact: derivable_cst.
    exact: H1.
    rewrite -!derive1E.
    rewrite H2.
    by rewrite derive1_cst add0r.
    rewrite /contrac/picard_to_cont/picard_from_cont.
    move : t tad.
    apply : eq_on_itv_deriv.
    move => t tad /=.
    rewrite -(@picard_from_cont_simpl _ _ a  b k _ r lip2 cont1 rho) //=.
    rewrite eval_mod_on_itv => //.
    by rewrite inE;apply: subset_itv_oo_cc;rewrite -inE.
Qed.

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
