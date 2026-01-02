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

(* We define the type of functions that are continuous over a set *)
(*continuousFunType *)

HB.instance Definition _ (R : realType) (V : topologicalType) (A : set R) :=
  gen_eqMixin (continuousFunType A [set: V]).
HB.instance Definition _ (R : realType) (V : topologicalType) (A : set R) :=
  gen_choiceMixin (continuousFunType A [set: V]).

Section cont_on_seg_pred.
Context {R : realType} {V : topologicalType}.
Variables a b : R.

Definition cont_on_seg : {pred R -> V} :=
  mem [set f | squashed (@ContinuousFun R V `[a, b] [set: V] f)].
Definition cont_on_seg_key : pred_key cont_on_seg. Proof. exact. Qed.
Canonical cont_on_seg_keyed := KeyedPred cont_on_seg_key.

End cont_on_seg_pred.

(* Section cont_to_contfun. *)

(* Context {U V : topologicalType} (A : set U) (f : U -> V). *)
(* Hypothesis fcont : {within A, continuous f}. *)

(* Local Lemma continuous_subproof : continuous (f : subspace A -> V). *)
(* Proof. *)
(*   apply fcont. *)
(* Qed. *)

(* Lemma f_is_fun : @isFun U V A setT f. *)
(* Proof. by constructor. Qed. *)

(* HB.instance Definition _ := f_is_fun. *)

(* HB.instance Definition _ := *)
(*   @isContinuous.Build (subspace A) _ (f : subspace A -> V) fcont. *)
(* End cont_to_contfun. *)

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

Module Cont_on_seg.
Section lmodtype_instances.
Context {R : realType} {V : normedModType R} (a b : R).

Check V : zmodType.
Check V : topologicalType.

Lemma cont_on_seg_zmod_closed : zmod_closed (@cont_on_seg _ V a b).
Proof.
 split=> [|f g]; rewrite !inE/=.
- apply: squash.
  split => //.
  split => //.
  exact: cst_continuous.
- move=> /unsquash cf /unsquash cg.
  apply: squash.
  pose f' : @continuousFunType _ _ `[a, b] [set: V]  := HB.pack f cf.
  pose g' : @continuousFunType _ _ `[a, b] setT  := HB.pack g cg.
  rewrite [f]/(f' : _ -> _).
  rewrite [g]/(g' : _ -> _).
  move: {f g cf cg} f' g' => f g.
  have isfun_fg : @isFun _ V `[a, b] [set: V] (f \- g) by constructor.
  have iscontfun_fg : @isContinuous _ V (f \- g).
    constructor.
    move=> x.
    apply: continuousB;apply: cts_fun.
  by split.
Qed.

HB.instance Definition _ := GRing.isZmodClosed.Build _ _
  cont_on_seg_zmod_closed.

HB.instance Definition _ :=
  [SubChoice_isSubZmodule of continuousFunType `[a, b] [set: V] by <:].

Check continuousFunType `[a, b] [set: V] : zmodType.

Lemma contfun_scaler_closed : GRing.scaler_closed (@cont_on_seg R V a b).
Proof.
move=> r f; rewrite 2!inE/=.
move/unsquash => [[_ cf]].
apply: squash.
split => //.
constructor.
move=> x.
apply: continuousZ.
  exact: cst_continuous.
by case: cf; exact.
Qed.

HB.instance Definition _ := GRing.isScaleClosed.Build _ _
  (cont_on_seg a b) contfun_scaler_closed.

Fail Check @continuousFunType R V `[a, b] [set: V] : lmodType _.

HB.instance Definition _ :=
  [SubZmodule_isSubLmodule of continuousFunType `[a, b] [set: V] by <:].

Check continuousFunType `[a, b] [set: V] : lmodType _.

End lmodtype_instances.

Section submod_definition.
Context {R : realType} {V : normedModType R}.
Variables a b : R.

Local Notation T := (continuousFunType `[a, b] [set: V]).

(* point V does not need to be 0, so rewrite f\_K explicitly *)
Definition submod_itv (ab : a <= b) : {pred T} :=
  [pred f : T | patch 0 `[a, b] f == 0].

Lemma submod_closed_itv (ab : a <= b) : submod_closed (submod_itv ab).
Proof.
split => /=.
- rewrite inE/=.
  apply/funext => x.
  rewrite /patch.
  by case: ifPn => //.
- move => f u v.
  rewrite !inE => u0 v0.
  apply/funext => u1.
  rewrite /patch; case: ifPn => // u1ab.
  move: u0 v0; rewrite /patch.
  move=> /(congr1 (fun x => x u1)); rewrite u1ab => uu1.
  move=> /(congr1 (fun x => x u1)); rewrite u1ab => vu1.
  by rewrite -[LHS]/(f *: u u1 + v u1) uu1 vu1 addr0 scaler0.
Qed.

HB.instance Definition _ (ab : a <= b) :=
  GRing.isZmodClosed.Build _ _ (submod_closed_itv ab).

(*Check submod_itv : zmodClosed _.*)

End submod_definition.

Import Quotient.

Section cont_on_seg_quotient.
Context {R : realType} (a b : R).
Hypothesis ab : a <= b.

(*Definition eq_seg (f g : continuousFunType a b) := `[< {in `[a, b], f =1 g} >].

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

(*Definition quot_continuousFunType := {ideal_quot (ideal_itv ab)}.*)
Definition quot_continuousFunType := {quot (@submod_itv _ R _ _ ab)}.

HB.instance Definition _ := ZmodQuotient.on quot_continuousFunType.

About ode_quot_continuousFunType__canonical__ring_quotient_NzRingQuotient.

Definition quot_continuousFunType_to_fun (f : quot_continuousFunType) :
  (* NB(rei): was R -> R before 2025-12-26 *)
  subspace `[a, b] -> R := repr f.
Coercion quot_continuousFunType_to_fun : quot_continuousFunType >-> Funclass.

Lemma eq_segP (f g : quot_continuousFunType) :
  reflect ({in `[a, b], f =1 g}) (f == g %[mod quot_continuousFunType]).
Proof.
apply/(iffP idP); rewrite eqmodE//=.
  rewrite /Quotient.equiv.
  rewrite inE.
  move=> fgab0 x xab.
  move/(congr1 (fun z => z x)) : fgab0.
  by rewrite /patch xab => /eqP; rewrite subr_eq0/= => /eqP.
move=> abfg.
rewrite /Quotient.equiv inE; apply/funext => y.
rewrite patchE.
case: ifPn => //= yab.
rewrite !fctE.
apply/eqP; rewrite subr_eq0; apply/eqP.
exact: abfg.
Qed.

End cont_on_seg_quotient.
End Cont_on_seg.

Section contFun_seminorm.
Context {R : realType} {W : normedModType R}.
Variables a b : R.
Hypothesis ab : a <= b.
Let K := `[a, b].
Local Notation T := (continuousFunType K [set: W]).

Import Cont_on_seg.

Definition infty_norm0 (f : {fun K >-> [set: W]}) :=
  sup ((Num.norm \o f) @` K).

(* todo *)
Lemma cont_within_cont_comp (f : W -> R) (g : T) : {in  g @` K, continuous f} ->
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
have [c Kc] := seg_nonempty ab.
rewrite /has_sup; split.
  exists (`|x c|)=> /=.
  by exists c => //.
pose abs_x := normr \o x.
have cont_abs_x : {within K, continuous abs_x}.
  apply cont_within_cont_comp.
  move => z zK.
  exact: norm_continuous.
apply compact_ubound.
apply continuous_compact => //.
exact: segment_compact.
Qed.

Lemma infty_norm_le  (g : T)  (u : R) : {in K, forall x, `| g x | <= u} -> infty_norm0 g <= u.
Proof.
have [c Kc] := seg_nonempty ab.
  move => h; rewrite /infty_norm0; apply: ge_sup.
  by exists (normr (g c)); exists c => //; rewrite /= in_itv/= lexx.
  by move => _ [x xab] <-;apply h; rewrite inE.
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
  have [c Kc] := seg_nonempty ab.
  exists c; by [ | rewrite normr0 ].
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

Section zmodule_normed.
Context {R : realType} {W : normedModType R}.
Variables a b : R.
Hypothesis ab : a <= b.
Let K := `[a, b].

Import Cont_on_seg.

Local Notation V := (quot_continuousFunType ab).

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
  move/set_mem =>  H.
  apply subr0_eq.
  move/(congr1 (fun z => z x)) : H.
  by rewrite /patch xab.
Qed.

Lemma eval_mod_on_itv f x : x \in K -> (\pi_V f : V) x = f x.
Proof.
  move => xab.

  apply: (@eqmod_on_itv (repr (\pi_V f)) f) => //.
  by rewrite reprK.
Qed.

Lemma ler_infty_normD (x y : V) : norm (x + y) <= norm x + norm y :> R.
Proof.
  rewrite /norm/= -sup_sumE//; last 2 first.
  exact: normr_repr_has_sup.
  exact: normr_repr_has_sup.
  apply: sup_le.
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
      rewrite lerD// ub_le_sup//.
        exact: (normr_repr_has_sup x).2.
      exact: (normr_repr_has_sup y).2.
Qed.

Lemma infty_normr0_eq0 (x : V) : norm x = 0 -> x = 0.
Proof.
  rewrite /norm/infty_norm0 /=.
  move => H.
  rewrite -(reprK x)  -(reprK 0).
  apply/eqquotP.
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

Section V_normedtype.
Context {R : realType} {r s : R} (rs : r <= s).

Import Cont_on_seg.

Local Notation V := (quot_continuousFunType rs).

Fail Check (pseudoMetric_normed V) : normedModType R.
HB.instance Definition _ := PseudoMetric.copy V (pseudoMetric_normed V).
HB.instance Definition _ := isPointed.Build V 0.

Lemma is_normZmod_contFunBallType : NormedZmod_PseudoMetric_eq R V.
Proof.
by constructor.
Qed.

Fail Check V : pseudoMetricNormedZmodType R.

HB.instance Definition _ := is_normZmod_contFunBallType.

Check V : pseudoMetricNormedZmodType R.
Import Quotient.
Open Scope quotient_scope.
Definition cont_scale (k : R) (v : V) : V := \pi_V (k *: repr v).


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
  apply: ge_sup.
    exists (`|repr (l *: x) r|).
    rewrite /=.
    exists r => //.
    by rewrite in_itv/= lexx/=.
  move=> _/= [a ars] <-.
  rewrite repr_mult; last by rewrite inE.
  rewrite normrZ ler_wpM2l//.
  rewrite ub_le_sup//.
  by apply normr_has_sup.
  by exists a.
  rewrite -sup_mult => //; last first.
    by apply normr_has_sup.
  apply sup_le; [ | | by apply normr_has_sup].
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

HB.instance Definition _ := is_pmnormedZmod_contFunBallType.
End V_normedtype.

Section completeness.
Context {R : realType}.
Variables  (a b : R).
Hypothesis ab : a <= b.

Import Cont_on_seg.

Notation V := (quot_continuousFunType ab).

Check (V : pseudoMetricType R).
Check (V : normedModType R).

Lemma infty_norm_gt_V (f : V) e: `| f | <  e -> {in `[a, b], forall x : R, `|f x| < e}.
Proof.
   rewrite -{1}(reprK f).
   rewrite qnorm_piE => h.
   move => x xab.
   apply /le_lt_trans/h.
   by apply: infty_norm_ge => //.
Qed.

Lemma infty_norm_le_V (f : V) e:  {in `[a, b], forall x : R, `|f x| <= e} -> `| f | <=  e.
Proof.
   move => h.
   rewrite -(reprK f).
   rewrite qnorm_piE.
   by apply infty_norm_le => //.
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
apply.
Qed.

Lemma lim_fun_cvg_uniform (F : set_system V) (FF: ProperFilter F) (Fc : cauchy F) :
  forall (e : R), e > 0 -> \forall f \near F, forall t, t \in `[a,b] -> `|lim_fun FF Fc t - (f : V) t| <= e.
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
    apply infty_norm_gt_V => //.
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
apply continuous_within_itvP => //.
split.
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
      rewrite -(reprK x.1) -(reprK x.2)  /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
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
  have /(_ _ _) /cauchy_cvg /cvg_app_entourageP cvF :   forall t : R, t \in `[a,b] -> cauchy (fmap (fun (h : V) => h t) (fun x : set V => nbhs F (fun x0 : V => x x0))).
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

Definition cont_on_segN {R : realType} (t0 t1 : R) (t01 : t0 < t1)
  (g : R -> R) := g \o -%R.
Arguments cont_on_segN {R} _ _.

Section cont_on_segN.
Context {R : realType}.
Variables t0 t1 : R.
Hypothesis t01 : t0 < t1.

Let g'fun (g : continuousFunType `[t0, t1] [set: R]) :
  set_fun `[-t1, -t0] setT (cont_on_segN t0 t1 t01 g).
Proof. by constructor => x/=. Qed.

HB.instance Definition _ (g : continuousFunType `[t0, t1] [set: R]) :=
  @isFun.Build (subspace `[-t1, -t0]) R `[-t1, -t0] setT (cont_on_segN t0 t1 t01 g) (g'fun g).

(* TODO: should this be a lemma? about balls? *)

Let cg' (g : continuousFunType `[t0, t1] [set: R]) :
  {within `[- t1, - t0], continuous (cont_on_segN t0 t1 t01 g)}.
Proof.
apply/continuous_within_itvP.
  by rewrite ltrN2.
have /continuous_within_itvP[] := @cts_fun _ _ g.
  by [].
move=> cg gR gL; split.
- move=> x xdd; apply: continuous_comp; first exact: continuousN.
  by apply: cg; rewrite oppr_itvoo.
- by apply/cvg_at_leftNP; rewrite /cont_on_segN/= opprK.
- move/cvg_at_rightNP : gR.
  by rewrite /cont_on_segN/= opprK.
Qed.

HB.instance Definition _ (g : continuousFunType `[t0, t1] [set: R]) :=
  isContinuous.Build _ _ (cont_on_segN t0 t1 t01 g : subspace `[-t1, -t0] -> R) (@cg' g).

End cont_on_segN.


(* Section vector_contseg. *)

(* Context {R : realType}. *)
(* Variables  (a b : R). *)
(* Hypothesis ab : a <= b. *)

(* Notation V := (quot_contFunType (seg_nonempty ab) (@segment_compact R _ _)). *)

(* Definition Vn n := {ffun 'I_n -> V}. *)
(* Check V : normedZmodType R. *)
(* Check (V : pseudoMetricType R). *)
(* Check (V : normedModType R). *)
(* Check (Vn 2 : normedZmodType R). *)
(* Check (Vn 2 : pseudoMetricType R). *)
(*  Check (Vn 2 : completeType). *)
(* Fail Check (Vn 2 : normedModType R). *)
(* End vector_contseg. *)
(* (* not neeeded anymore *) *)
(* NB: merged to MathComp *)
(* Lemma gerN {R : numDomainType} (x : R) : 0 <= x -> - x <= x. *)
(* Proof. by move=> x0; rewrite ge0_cp. Qed. *)

(* Section lip_implies_cont. *)
(* Context {R : realType}. *)
(* Local Notation mu := lebesgue_measure. *)
(* Variables (f : R -> R -> R) (t0 t1 : R). *)
(* Hypothesis t01 : t0 < t1. *)
(* Variable k : R. *)
(* Hypothesis k1 : k > 0. *)
(* Variables (u0 : R) (r : {posnum R}). *)
(* Let B := closed_ball u0 r%:num. *)

(* Hypothesis lip2 : {in `[t0, t1]%R, forall x, k.-lipschitz_B (f x)}. *)

(* Lemma cont2 : {in `[t0, t1]%R, forall x, {within B, continuous f x}}. *)
(* Proof. *)
(* move=> x xt01. *)
(* rewrite [B]closed_ball_itv//. *)
(* apply/continuous_within_itvP; first by rewrite ltrD2l gtrN. *)
(* split. *)
(* - move=> y yt01. *)
(*   move: (xt01); have := @lip2 x => /[apply] kfx. *)
(*   rewrite /continuous_at. *)
(*   apply/cvgrPdist_le => /= e e0. *)
(*   near=> y'. *)
(*   move: kfx => /(_ (y, y'))/=. *)
(*     have By : B y. *)
(*       rewrite /B closed_ball_itv//=. *)
(*       exact: subset_itv_oo_cc yt01. *)
(*     have By' : B y'. *)
(*       rewrite /B closed_ball_itv//=. *)
(*       rewrite in_itv/=; apply/andP; split. *)
(*         near: y'. *)
(*         exists (y - (u0 - r%:num)). *)
(*           by move: yt01; rewrite in_itv/= -subr_gt0 => /andP[]. *)
(*         move=> z/=. *)
(*         rewrite ltr_distlC. *)
(*         by rewrite opprB addrCA subrr addr0 => /andP[/ltW]. *)
(*       near: y'. *)
(*       exists ((u0 + r%:num) - y). *)
(*         by move: yt01; rewrite in_itv/= -(subr_gt0 y) => /andP[]. *)
(*       move=> z/=. *)
(*       rewrite ltr_distlC => /andP[_]. *)
(*       by rewrite addrCA subrr addr0 => /ltW. *)
(*    move=> /(_ (conj By By')). *)
(*   move=> /le_trans; apply. *)
(*   rewrite -ler_pdivlMl// mulrC. *)
(*   near: y'. *)
(*   (* TODO(rei): investigate *) *)
(*   exists (e / k). *)
(*     by rewrite divr_gt0//. *)
(*   by move=> z/= => /ltW. *)
(* - apply/cvgrPdist_le => /= e e0. *)
(*   near=> y'. *)
(*   move: (xt01); have := @lip2 x => /[apply]. *)
(*   move=> /(_ (u0 - r%:num, y'))/=. *)
(*     have Bu0r : B (u0 - r%:num). *)
(*       rewrite /B closed_ball_itv//=. *)
(*       by rewrite in_itv/= lexx/= lerD2l gerN. *)
(*     have By' : B y'. *)
(*       rewrite /B closed_ball_itv//=. *)
(*       rewrite in_itv/=; apply/andP; split => //. *)
(*       near: y'. *)
(*       exists r%:num => //=. *)
(*       move=> z/=. *)
(*       rewrite ltr_distlC. *)
(*       rewrite subrK => /andP[_ /ltW + _] => /le_trans; apply. *)
(*       by rewrite lerDl. *)
(*    move=> /(_ (conj Bu0r By')). *)
(*   move=> /le_trans; apply. *)
(*   rewrite -ler_pdivlMl// mulrC. *)
(*   near: y'. *)
(*   (* TODO(rei): investigate *) *)
(*   exists (e / k) => /=. *)
(*     by rewrite divr_gt0//. *)
(*   by move=> z/= => /ltW. *)
(* - apply/cvgrPdist_le => /= e e0. *)
(*   near=> y'. *)
(*   move: (xt01); have := @lip2 x => /[apply]. *)
(*   move=> /(_ (y', u0 + r%:num))/=. *)
(*     have By' : B y'. *)
(*       rewrite /B closed_ball_itv//=. *)
(*       rewrite in_itv/=; apply/andP; split => //. *)
(*       near: y'. *)
(*       exists r%:num => //=. *)
(*       move=> z/=. *)
(*       rewrite ltr_distlC addrK => /andP[/ltW + _ _]. *)
(*       rewrite lerBlDl => /le_trans; apply. *)
(*       by rewrite lerDr. *)
(*     have Bu0r : B (u0 + r%:num). *)
(*       rewrite /B closed_ball_itv//=. *)
(*       by rewrite in_itv/= lexx/= lerD2l andbT gerN. *)
(*   move=> /(_ (conj By' Bu0r)). *)
(*   rewrite distrC. *)
(*   move=> /le_trans; apply. *)
(*   rewrite -ler_pdivlMl// mulrC. *)
(*   near: y'. *)
(*   (* TODO(rei): investigate *) *)
(*   exists (e / k) => /=. *)
(*     by rewrite divr_gt0//. *)
(*   move=> z/= => /ltW. *)
(*   by rewrite distrC. *)
(* Unshelve. all: end_near. Qed. *)

(* End lip_implies_cont. *)
