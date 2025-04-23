(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum archimedean.
From mathcomp Require Import matrix interval zmodp vector fieldext falgebra.
From mathcomp Require Import finmap.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import functions cardinality contra ereal reals.
From mathcomp Require Import interval_inference topology prodnormedzmodule tvs.
From mathcomp Require Import normedtype derive sequences real_interval.
From mathcomp Require Import function_spaces.
From mathcomp Require Import realfun.
From mathcomp Require Import rat.
From mathcomp Require Import pi_irrational. (* just for the rational definition *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Import numFieldNormedType.Exports.

(* NB: use {i01 R}? *)
Definition unit_itv {R : realType} : set R := `[0%R, 1%R].

Definition supnorm {R : realType} (f : R -> R) :=
  sup [set `| f s | | s in unit_itv].

Definition supnorm2 {R : realType} (f : R * R -> R) :=
  sup [set `| f s | | s in unit_itv `*` unit_itv].

Section lem25.
Context {R : realType}.

Definition lambda_prop (lambda : R) :=
  forall x1 x2 y1 y2 : rat,
    ratr x1 + lambda * ratr y1 = ratr x2 + lambda * ratr y2 ->
    x1 = x2 /\ y1 = y2.

Lemma mulrat_rat (x y : R) : x != 0 -> rational x -> rational (x * y) -> rational y.
Proof.
move=> /[swap].
move=> [n [d ->{x}]] nd0.
move=> [n' [d' ndy]].
exists (n' * d), (n * d').
rewrite !natrM invfM.
rewrite !mulrA mulrC !mulrA (mulrC d'%:R^-1) -ndy.
rewrite -mulrA mulrAC.
rewrite -[X in _ * X * _]invrK.
by rewrite invf_div mulfV ?mul1r//.
Qed.

Lemma lem25 : exists lambda : R, lambda_prop lambda.
Proof.
pose l := @trigo.pi R.
exists l => x1 x2 y1 y2.
move=> /eqP.
rewrite -subr_eq -addrA addrC eq_sym -subr_eq -mulrBr => xy12.
apply: contrapT => /not_andP[/eqP x12|/eqP y12].
  


Admitted.

End lem25.

Section kolmogorov_arnold_tuple.
Context {R : realType}.

Let I := @unit_itv R.

Definition Phi lambda (phi : 'rV[{uniform` I -> R}]_5) (i : 'I_5) xy :=
  (phi ord0 i) xy.1 + lambda * (phi ord0 i) xy.2.

Definition U_ lambda (f : {fun (I `*` I) >-> [set: R]})
    (phi : 'rV[{uniform` I -> R}]_5) :=
  exists g : R -> R, [/\ continuous g,
    (forall t, `|g t| <= 7^-1) &
    (forall x y, `|f (x, y) -
      \sum_(i < 5) g (Phi lambda phi i (x, y))| < 7 / 8)].

End kolmogorov_arnold_tuple.

Section lem31.
Context {R : realType}.
Let I := @unit_itv R.

Lemma lem31 (f : {fun (I `*` I) >-> [set: R]}) lambda :
  {within (I `*` I)%type, continuous f} ->
  supnorm2 f = 1 ->
  lambda_prop lambda ->
  open (U_ lambda f) /\ dense (U_ lambda f).
Proof.
Abort.

End lem31.

Section lem32.
Context {R : realType}.
Let I := @unit_itv R.

Lemma lem32 lambda : lambda_prop lambda ->
  exists phi : 'rV[{uniform` I -> R}]_5,
    forall f : {fun (I `*` I) >-> [set: R]},
      {within (I `*` I)%type, continuous f} ->
      exists g : R -> R, [/\ continuous g,
        (forall t, `|g t| <= t^-1 * supnorm2 f) &
        (supnorm2 (f \- \sum_(i < 5) (g \o Phi lambda phi i)) <
         (8 / 9) * supnorm2 f)].
Proof.
Abort.

End lem32.

Section thm41.
Context {R : realType}.

Let I := @unit_itv R.

Theorem thm41 : exists lambda : R,
  exists phi : 'rV[{uniform` I -> R}]_5,
    forall f : {fun (I `*` I) >-> [set: R]},
      {within (I `*` I)%type, continuous f} ->
        exists2 g : R -> R, continuous g &
          f = \sum_(i < 5) (g \o (Phi lambda phi i)) :> (R * R -> R).
Proof.
Abort.

End thm41.

Section thm42.
Context {R : realType}.

Let I := @unit_itv R.

Theorem thm42 n : (n >= 2)%N ->
  exists lambda : n.-tuple R,
    exists phi : 'rV[{uniform` I -> R}]_(n.*2.+1),
      (forall i, {within I, continuous (phi ord0 i)}) /\
      (forall i, {in I, increasing_fun (phi ord0 i)}) /\
      forall f : {fun [set: 'rV[I]_n] >-> [set: R]},
        {within [set: 'rV[I]_n], continuous f} ->
        exists g, continuous g /\
          forall t, f t = \sum_(i < n.*2.+1) g
            (\sum_(j < n) (tnth lambda j) * (phi ord0 i) (set_val (t ord0 j))).
Proof.
Abort.

End thm42.
