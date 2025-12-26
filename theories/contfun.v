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

(* Todo: Check if they should be moved *)
Section GeneralStatements.


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
Lemma sup_le {R : realType} A (x : R) : has_sup A -> A x -> x <= sup A.
Proof.
  move=> supA Ax.
  have /sup_upper_bound := supA.
  by move/(_ x Ax).
Qed.

Lemma has_sup_Mn {R: realType} (A : set R) n: has_sup A -> has_sup [set x *+n | x in A ].
Proof.
  move => [-[] x Ax [y uby]].
  split; first by exists (x *+ n);exists x.
  exists (y *+ n).
  move => _ [y0 Ay0 <-] .
  rewrite lerMn2r.
  by apply /orP;right;apply uby.
Qed.

Lemma sup_Mn {R : realType} (A : set R) n: has_sup A -> sup [set x *+n | x in A ] = sup A *+ n.
Proof.
move => ex_sup.
elim: n.
rewrite !mulr0n -(sup1 0);congr (sup _).
apply eq_set => /= z ;apply propext; split => [[x _ <- ] | ->]; rewrite ?normr0 => //.
case : ex_sup => -[] x Ax _;by exists x.
move => n IH.
rewrite !mulrS.
rewrite -IH.
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
End GeneralStatements.

(* We define the type of functions that are continuous over a set *)
(* How does it relate to continuousFunType? *)
(* HB.mixin Record isContFunSeg (T U : topologicalType) (K : set T) (f : T -> U) := *)
(*   { contFunSeg : {within K, continuous f} }. *)

(* #[short(type="contFunSegType")] *)
(* HB.structure Definition ContFunSeg (T U : topologicalType) (K : set T) := *)
(*   {f of isContFunSeg T U K f & @Fun T U K [set: U] f}. *)


HB.instance Definition _ (T U : topologicalType) (K : set T)  := 
   gen_eqMixin (@continuousFunType T U K setT). 
HB.instance Definition _ (T U : topologicalType) (K : set T) := 
   gen_choiceMixin (@continuousFunType T U K setT). 

Section contfunseg_pred.
Context {U V : topologicalType}.
Variables (A : set U) (B : set V) .

Definition contfunseg : {pred U -> V}
  := mem [set f | squashed (@ContinuousFun U V A B f)].
Definition contfunseg_key : pred_key contfunseg. Proof. exact. Qed.
Canonical contfunseg_keyed := KeyedPred contfunseg_key.

End contfunseg_pred.
Section cont_to_contfun.

Context {U V : topologicalType} (A : set U) (f : U -> V).
Hypothesis fcont : {within A, continuous f}.

Local Lemma continuous_subproof : continuous (f : subspace A -> V).
Proof.
  apply fcont.
Qed.

Lemma f_is_fun : @isFun U V A setT f.
Proof. by constructor. Qed.

HB.instance Definition _ := f_is_fun.

HB.instance Definition _ :=
  @isContinuous.Build (subspace A) _ (f : subspace A -> V) fcont.
End cont_to_contfun.

Section contfun.
Context {U V : topologicalType}.
Variables (A : set U) (B : set V) .
Notation T := (continuousFunType A B).

Section Sub.
Context (f : U -> V) (fP : f \in contfunseg A B).

Definition contfunseg_Sub_subproof := unsquash (set_mem fP).
#[local] HB.instance Definition _ := contfunseg_Sub_subproof.
Definition contfunseg_Sub : continuousFunType A B :=
{| ContinuousFun.sort := f; ContinuousFun.class := contfunseg_Sub_subproof |}.

End Sub.

Lemma contfunseg_rect (F : T -> Type) :
  (forall f (Pf : f \in contfunseg A B), F (contfunseg_Sub Pf)) ->
  forall u : T, F u.
Proof.
move=> Ksub [f Pf].
rewrite (_ : F _  = F (contfunseg_Sub (mem_set (squash Pf))))//.
rewrite /contfunseg_Sub /contfunseg_Sub_subproof /= mem_setK.
rewrite /unsquash; case : cid => // /= => x _.
congr (F (ContinuousFun.Pack _)).
move : Pf x => [[H1] [H2]] [[?] [?]].
by rewrite (Prop_irrelevance H1) (Prop_irrelevance H2).
Qed.

Lemma contfunseg_valP f (Pf : f \in contfunseg A B) :
  contfunseg_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ := isSub.Build _ _ T contfunseg_rect contfunseg_valP.

Lemma contfunseg_eqP (f g : continuousFunType A B) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; exact/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of continuousFunType A B by <:].

(* Lemma cst_is_fun x : @isFun U V A setT (cst x). *)
(* Proof. by constructor.  Qed. *)
(* HB.instance Definition _ x := (cst_is_fun x). *)

(* Lemma cst_continuous_subspace (r : V) : *)
(*   {within A, continuous (@cst (subspace A) V r)}. *)
(* Proof. *)
(* apply: continuous_subspaceT. *)
(* exact: cst_continuous. *)
(* Qed. *)

(*  HB.instance Definition _ (x: V) :=  *)
(*    @isContinuous.Build (subspace A) _ (@cst (subspace A) V x) (@cst_continuous_subspace x).  *)

End contfun.

Lemma set_fun_cst T1 (T2 : Type) (A : set T1) c : set_fun A [set: T2] (cst c).
Proof. by []. Qed.

HB.instance Definition _ T1 (T2 : Type) (A : set T1) c :=
 @isFun.Build T1 T2 _ _ (cst c) (@set_fun_cst _ _ A c).

Section contfun_ring.
(* can this be generalized to V normedModType with ring structure??*)
Context {R : realType} (U : set R).

Lemma contfunseg_subring_closed : subring_closed (@contfunseg R R U setT ).
Proof.
split=> [|f g|f g]; rewrite !inE/=.
- apply: squash.
  split => //.
  apply: ContinuousFun.class => //.
  exact: cst_continuous.
- move=> /unsquash cf /unsquash cg.
  apply: squash.
  pose f' : continuousFunType U setT  := HB.pack f cf.
  pose g' : continuousFunType U setT  := HB.pack g cg.
  rewrite [f]/(f' : _ -> _).
  rewrite [g]/(g' : _ -> _).
  move: {f g cf cg} f' g' => f g.
  have isfun_fg : @isFun R R  U [set: R] (f \- g) by constructor.
  have iscontfun_fg : @isContinuous (subspace U) R (f \- g).
    constructor.
    move=> x.
    apply: continuousB; apply: cts_fun.
  by split.
- move=> /unsquash cf /unsquash cg.
  apply: squash.
  pose f' : continuousFunType U setT  := HB.pack f cf.
  pose g' : continuousFunType U setT  := HB.pack g cg.
  rewrite [f]/(f' : _ -> _).
  rewrite [g]/(g' : _ -> _).
  move: {f g cf cg} f' g' => f g.
  have isfun_fg : @isFun R R  U [set: R] (f \- g) by constructor.
  have iscontfun_fg : @isContinuous (subspace U) R (f \* g).
    constructor.
    move=> x.
    by apply: (@continuousM _ (subspace U)); exact: cts_fun.
  by split.
Qed.

HB.instance Definition _ := GRing.isSubringClosed.Build _
  (@contfunseg R R U setT) contfunseg_subring_closed.
HB.instance Definition _ := [SubChoice_isSubComRing of @continuousFunType R R U setT by <:].

Lemma contfun_scaler_closed : GRing.scaler_closed (@contfunseg R R U setT).
Proof.
move=> r f; rewrite 2!inE/=.
move/unsquash => [[_ cf]].
apply: squash.
split => //.
constructor.
move=> x.
apply: continuousZ.
  exact: cst_continuous.
apply: cts_fun.
by apply cf.
Qed.

HB.instance Definition _ := GRing.isScaleClosed.Build _ _
  (@contfunseg R R U setT) contfun_scaler_closed.

Fail Check @continuousFunType R R U setT : lmodType _.

HB.instance Definition _ :=
  [SubZmodule_isSubLmodule of @continuousFunType R R U setT by <:].

Check @continuousFunType R R U setT : lmodType _.
End contfun_ring.

Section contFun_seminorm.
Context {R : realType} (K : set R).
Hypothesis (nonemptyK : nonempty K) (compactK : compact K).

Local Notation T := (@continuousFunType R R K setT).

Definition infty_norm0 (f : {fun K >-> [set: R]}) :=
  sup ((Num.norm \o f) @` K).

(* todo *)
Lemma cont_within_cont_comp (f : R -> R) (g : T) : {in  g @` K, continuous f} ->
  {within K, continuous (f \o g)}.
Proof.
move => ctf.
rewrite continuous_subspace_in.
move => /= x Kx.
apply: continuous_comp; first by apply cts_fun.
apply ctf.
rewrite inE.
rewrite inE in Kx.
by exists x.
Qed.

Local Lemma compact_ubound  (A : set R) : compact A -> has_ubound A .
Proof.
  move /compact_bounded => [u [U1 /= U2]].
  exists (u+1).
  move => x Ax.
  apply: (le_trans (ler_norm x)).
  apply U2 => //; by rewrite ltrDl.
Qed.

Lemma normr_has_sup (x : T ) :
  has_sup [set (normr \o x) x0 | x0 in K].
Proof.
have [a Ka] := nonemptyK.
rewrite /has_sup; split.
  exists (`|x a|)=> /=.
  by exists a => //.
pose abs_x := normr \o x.
have cont_abs_x : {within K, continuous abs_x}.
  apply cont_within_cont_comp.
  move => z zK.
  exact: norm_continuous.
apply compact_ubound.
apply continuous_compact => //.
Qed.

Lemma infty_norm_le  (g : T)  (u : R) : {in K, forall x, `| g x | <= u} -> infty_norm0 g <= u.
Proof.
  move => h.
  apply sup_le_ub.
  have [a Ka] := nonemptyK.
  exists (normr (g a)); exists a => //.
  move => _ [x xab] <-.
  apply h.
  by rewrite inE.
Qed.

Lemma infty_norm_ge (g : T) x: x \in K -> `|g x| <= infty_norm0 g.  
Proof.
   move => h. 
   rewrite sup_upper_bound //=.
   exact: normr_has_sup.
   exists x => //.
   by rewrite inE in h.
Qed.

Lemma infty_norm_itv_eq (f g :  T):  {in K, f =1 g} -> infty_norm0 f = infty_norm0 g.
Proof.
move => inK.
rewrite /infty_norm0 /=;congr (sup _).
apply/seteqP; split; move => _ [ y ? <- ]; exists y; by rewrite //= inK // inE.
Qed.

Local Lemma infty_norm0_eq0 : infty_norm0 (0 : T) = 0.
Proof.
  rewrite /infty_norm0.
  rewrite -(sup1 0).
  f_equal.
  apply eq_set => /= z ;apply propext; split => [[x _ <- ] | ->]; rewrite ?normr0 => //.
  have [a Ka] := nonemptyK.
  exists a; by [ | rewrite normr0 ].
Qed.

Local Lemma infty_norm0rMn (x : T) n : infty_norm0 (x *+ n) = infty_norm0 x *+ n.
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
exact: (normr_has_sup x).
Qed.


Lemma infty_norm0N (x : T) : infty_norm0 (- x) = infty_norm0 x.
Proof.
  rewrite /infty_norm0.
  f_equal.
  apply eq_set => /= x0.
  apply propext;split => [[x1 in_itv] | [x1 in_itv]] H;exists x1 =>//.
  rewrite -normrN //.
  rewrite normrN //.
Qed.

End contFun_seminorm.
(*
Section ideal_definition.
Context {R : realType} (K : set R).
Hypothesis (nonemptyK : nonempty K).

Local Notation T := (@continuousFunType R R K setT).

#[using="nonemptyK"]
Definition ideal_K : {pred T} := [pred f : T | f \_ K == cst 0].

Lemma idealr_closed_K : idealr_closed ideal_K.
Proof.
split => /=.
- rewrite inE/=.
  apply/funext => x.
  rewrite patchE.
  by case: ifPn.
- rewrite inE/=.
  have [x Kx] := nonemptyK.
  apply/negP => /eqP /(congr1 (@^~ x))/=.
  rewrite patchE ifT//=.
    by apply/eqP; rewrite oner_eq0.
  by rewrite inE/=.
- move=> f u v.
  rewrite !inE => u0 v0.
  rewrite restrictD/= v0.
  rewrite restrictM u0.
  rewrite /GRing.mul_fun/= fctE.
  under eq_fun do rewrite mulr0.
  rewrite /GRing.add_fun.
  by under eq_fun do rewrite add0r.
Qed.

HB.instance Definition _ := isIdealr.Build _ ideal_K idealr_closed_K.

Check ideal_K : zmodClosed _.

End ideal_definition.
*)
(*
Section contFunSeg_quotient.
Context {R : realType} (K : set R).
Hypothesis (nonemptyK : nonempty K) (compactK : compact K).

Local Open Scope quotient_scope.
Definition quot_contFunType := {ideal_quot (@ideal_K R K nonemptyK)}.

HB.instance Definition _ := NzRingQuotient.on quot_contFunType.

About contfun_quot_contFunType__canonical__ring_quotient_NzRingQuotient.
Definition quot_contFunType_to_fun (f : quot_contFunType) : R -> R := repr f.
Coercion quot_contFunType_to_fun : quot_contFunType >-> Funclass.

Lemma cts_fun_quot (f : quot_contFunType): {within K, continuous f}.
Proof.
  apply: (@cts_fun _ _ (repr f)).
Qed.

 HB.instance Definition _ (f: quot_contFunType) :=  
   @isContinuous.Build (subspace K) _ _ (@cts_fun_quot f).
(* Lemma eq_segP (f g : quot_contFunType) : *)
(*   reflect ({in K, f =1 g}) (f == g %[mod quot_contFunType]). *)
(* Proof. *)
(* apply/(iffP idP); rewrite eqmodE//=. *)
(*   rewrite /Quotient.equiv. *)
(*   rewrite inE. *)
(*   move=> fgab0 x xab. *)
(*   move/(congr1 (fun z => z x)) : fgab0. *)
(*   by rewrite patchE xab => /eqP; rewrite subr_eq0/= => /eqP. *)
(* move=> abfg. *)
(* rewrite /Quotient.equiv inE; apply/funext => y. *)
(* rewrite patchE. *)
(* case: ifPn => //= yab. *)
(* rewrite !fctE. *)
(* apply/eqP; rewrite subr_eq0; apply/eqP. *)
(* exact: abfg. *)
(* Qed. *)

End contFunSeg_quotient.*)

(*
Section zmodule_normed.

Context {R : realType} (K : set R).
Hypothesis (nonemptyK : nonempty K) (compactK : compact K).

Local Notation V := (quot_contFunType nonemptyK).

Definition infty_norm (f : V) := infty_norm0 (repr f).

Local Notation norm := infty_norm.

Local Open Scope quotient_scope.



Let normr_repr_has_sup (x : V) :
  has_sup [set (normr \o repr x) x0 | x0 in K].
Proof. by apply normr_has_sup. Qed.


Lemma eqmod_on_itv f g :
  f = g %[mod V] -> {in K, f =1 g}.
Proof.
  move => /eqmodP + x xab.
  rewrite /Quotient.equiv_equiv /Quotient.equiv /= /ideal_K /=.
  move/set_mem =>  H.
  apply subr0_eq.
  rewrite -[RHS]/(cst 0 x) -H patchE; case : ifPn => //. 
  by rewrite xab.
Qed.


Lemma eval_mod_on_itv f x : x \in K -> (\pi_V f : V) x = f x.
Proof.
  move => xab.

  apply: (@eqmod_on_itv (repr (\pi_V f)) f) => //.
  by rewrite reprK.
Qed.


Lemma ler_infty_normD (x y : V) : norm (x + y) <= norm x + norm y :> R.
Proof.
  have [a Ka] := nonemptyK.
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
      exists (sup [set (normr \o repr x) x0 | x0 in K] + sup [set (normr \o repr y) x0 | x0 in K]).
      apply ubP => _ [x0 xs] [y0 ys] <-.
      apply lerD;apply sup_le => //.
Qed.

Lemma infty_normr0_eq0 (x : V) : norm x = 0 -> x = 0.
Proof.
  rewrite /norm/infty_norm0 /=.
  move => H.
  rewrite -(reprK x)  -(reprK 0).
  apply/eqquotP.
  rewrite /Quotient.equiv_equiv/Quotient.equiv/=/ ideal_K/=.
  apply mem_set; rewrite /cst /=.
  apply funext => x0 /=.
  rewrite patchE.
  case : ifPn => // /set_mem in_itv.
  rewrite /GRing.opp/GRing.add /=.
  have -> : ( {in K, repr (0 : V) =1 (0 : @continuousFunType R R K setT)}) => //.
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


Lemma infty_normrMn (x : V) n : norm (x *+ n) = norm x *+ n.
Proof.
  rewrite /norm.
  rewrite -infty_norm0rMn => //.
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
*)
