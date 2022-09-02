From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
Require Import mathcomp_extra boolp classical_sets signed functions cardinality.
Require Import reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure fsbigop numfun lebesgue_integral kernel prob_lang.

Set Implicit Arguments.
Implicit Types V : Set.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Require Import String ZArith.
Local Open Scope string.

Section v5.
Variable (R : realType).

Section def.

Inductive type :=
| ty_unit
| ty_bool
| ty_real
| ty_pair : type -> type -> type
| ty_prob : type -> type
.

(* Inductive type :=
| mty : mtype -> type
| ty_prob : mtype -> type
. *)

Inductive context :=
| empty
.

Inductive val : Type :=
(* | val_var : V -> val *)
| val_unit : val
| val_bool : bool -> val
| val_real : R -> val
(* | val_unif : val *)
| val_bernoulli : R -> val
with expD : Type :=
| exp_val : val -> expD 
| exp_if : expD -> expD -> expD -> expD
with expP : Type :=
| exp_sample : expD -> expP
| exp_score : expD -> expP
.

Coercion exp_val : val >-> expD.

Inductive wf_val (G : context) : val -> type -> Type :=
(* | wf_val_var {x} : wf_val G (val_var x) (G x) *)
| wf_val_unit : wf_val G val_unit ty_unit
| wf_val_bool b : wf_val G (val_bool b) ty_bool
| wf_val_real r : wf_val G (val_real r) ty_real
(* | wf_val_unif : wf_val G val_unif (ty_prob ty_real) *)
| wf_val_bernoulli r : wf_val G (val_bernoulli r) (ty_prob ty_bool)

with wf_expD (G : context) : expD -> type -> Type :=
| wf_exp_val {v T} : wf_val G v T -> wf_expD G v T
| wf_exp_if {e1 e2 e3 T} :
    wf_expD G e1 ty_bool -> wf_expD G e2 T -> wf_expD G e3 T ->
    wf_expD G (exp_if e1 e2 e3) T

with wf_expP (G : context) : expP -> type -> Type :=
| wf_exp_sample {e T} : 
  wf_expD G e (ty_prob T) -> wf_expP G (exp_sample e) T
.

End def.

Section interp.

Let mR := Real_sort__canonical__measure_Measurable R.
Let munit := Datatypes_unit__canonical__measure_Measurable.
Let mbool := Datatypes_bool__canonical__measure_Measurable.

Axiom prob_measurableType : forall (d : measure_display) (T : measurableType d) (R : realType), measurableType d.

Fixpoint interp_type (ty : type) : {d & measurableType d} :=
  match ty with
  | ty_unit => existT _ _ munit
  | ty_bool => existT _ _ mbool
  | ty_real => existT _ _ mR
    (* [the measurableType _ of \bar R] *)
  | ty_pair t1 t2 => 
    let: existT d1 A1 := interp_type t1 in 
    let: existT d2 A2 := interp_type t2 in
    existT _ _ [the measurableType _ of (A1 * A2)%type]
  | ty_prob t =>
    let: existT d A := interp_type t in
    existT _ _ (prob_measurableType A R)
    (* [the measurableType d of probability A R] *)
  end.

Definition interp_context (G : context) :=
  match G with
  | empty => unit
  end.

Fail Definition interp_wf_val {G a T} (wf : wf_val G a T) 
  : interp_context empty -> interp_type T :=
  match wf with
  | wf_val_unit => fun _ => tt
  | wf_val_bool b => fun _ => b
  | wf_val_real r => fun _ => r
  | wf_val_bernoulli r => fun _ => [the probability mbool R of bernoulli27 R]
  (* | _ => fun _ => tt *)
  end.

Fail Fixpoint interp_wf_expD {G a T} (wf : wf_expD G a T) 
  : interp_context empty -> interp_type T :=
  match wf with 
  | wf_exp_val _ _ w => interp_wf_val w
  | wf_exp_if _ _ _ T w1 w2 w3 => fun p => 
    if (interp_wf_expD w1 p) then (interp_wf_expD w2 p) else (interp_wf_expD w3 p)
  end.

(* Fixpoint interp_wf_expP {G a T} (wf : wf_expP G a T)
  : R.-sfker _ ~> interp_type T :=
  match wf with
  | wf_exp_sample _ _ w => sample (interp_wf_expD w tt)
  end. *)

Example wf1 := 
  wf_exp_val (wf_val_bool empty true).
Fail Example interp1 : interp_wf_expD wf1 = fun => true.
(* Proof. by []. Qed. *)
Example wf2 := 
  wf_exp_if (wf_exp_val (wf_val_bool empty true)) 
            (wf_exp_val (wf_val_real empty 0)) 
            (wf_exp_val (wf_val_real empty 1)).
Fail Example interp2 : interp_wf_expD wf2 = fun => 0 
    :> (interp_context empty -> \bar R).
(* Proof. by []. Qed. *)

End interp.

End v5.

Section dist_salgebra_instance.
Variables (d : measure_display) (T : measurableType d) (R : realType).

Definition mset (U : set T) (r : R) := [set mu : probability T R | mu U < r%:E].
Definition pset := 
  [set mset U r | r in `[0%R,1%R]%classic & U in @measurable d T].
Fail Definition sset := [the measurableType _ of salgebraType pset].

End dist_salgebra_instance.
(*
Section v4.
Variables (R : realType) (d : _) (mT : measurableType d).

Let mR := Real_sort__canonical__measure_Measurable R.
Let munit := Datatypes_unit__canonical__measure_Measurable.
Let mbool := Datatypes_bool__canonical__measure_Measurable.

Inductive type :=
| t_unit
| t_real
| t_bool
| t_P : type -> type
(* | t_arrow : type -> type -> type *)
.

Reserved Notation "[| T |]Type".

Check munit : measurableType _.
Check [the measurableType _ of \bar R] : measurableType _.

Fixpoint interp_type (T : type) : measurableType _ :=
  match T with
  | t_unit => munit
  | t_real => [the measurableType _ of \bar R]
  | t_bool => mbool 
  (* TODO: A -> B is measurable type ? *)
  (* | t_arrow A B => [the measurableType _ of [| A |]Type -> [| B |]Type] *)
  (* TODO : probability is measurable type ? *)
  (* | t_P t => [the measurableType _ of probability [the measurableType _ of [| T |]Type] R] *)
  | _ => [the measurableType _ of \bar R] 
  end
  where "[| T |]Type" := (interp_type T).

Definition variable := string.
Inductive context :=
| empty
| extend : context -> variable -> Type -> context
.

Inductive termB := True | False.

Inductive function := 
| f_const : R -> function
.

Inductive termD :=
| TT : termD
| Var : variable -> termD
| Const : R -> termD
| App : function -> termD -> termD
| Bernoulli : R -> termD
| Ifd : termD -> termD -> termD -> termD
.

Inductive termP :=
| Ret : termD -> termP
| Sample : termD -> termP
| Score : termD -> termP
| Letin : variable -> termP -> termP -> termP
| Ifp : termD -> termP -> termP -> termP
.

Reserved Notation "[| G |]context".
Fixpoint interp_context (G : context) : Type :=
  match G with
  | empty => unit
  | extend G x T => [| G |]context * T
  end
  where "[| G |]context" := (interp_context G).

Example context1 := extend empty "x" R.
Example context2 := extend context1 "y" R.

Compute [| context1 |]context.
Compute [| context2 |]context.

Fixpoint lookup (x : string) (G : context) : option _ :=
  match G with
  | empty => None
  | extend G' y T => if string_dec x y then Some T else lookup x G'
  end.

Inductive var : context -> string -> Type -> Type :=
| V1 : forall {G : context} {x : string} {t : Type}, var G x t
| VS : forall {G : context} {x} {A A'}, var G x A' -> var (extend G x A) x A'
.

Check Set : Type.
Reserved Notation "G |-d t ::: A" (at level 50).
Inductive program_d : context -> termD -> Type -> Type :=
(* | T_context : forall G x x' A A', G |-d (Var x) ::: A -> (extend G x' A') |-d (Var x) ::: A *)
| T_var     : forall G x A, lookup x G = Some A -> G |-d Var x ::: A
(* extend G x A |-d (Var x) ::: A *)
| T_app {G A B f t} : 
    G |-d f ::: (A -> B)%type -> G |-d t ::: A -> G |-d App f t ::: B 
| T_unit {G} : G |-d TT ::: [| t_unit |]Type
| T_ifd {G t u1 u2 B} : 
    G |-d t ::: [| t_bool |]Type -> G |-d u1 ::: B -> G |-d u2 ::: B -> 
    G |-d Ifd t u1 u2 ::: B
| T_bernoulli {G r} : G |-d Bernoulli r ::: probability mbool R
where "G |-d t ::: A" := (program_d G t A).

Reserved Notation "G |-p t ::: A" (at level 50). 
Inductive program_p : context -> termP -> Type -> Type :=
| T_return  : forall G t A, G |-d t ::: A -> G |-p Ret t ::: A
| T_sample  : forall G t A, G |-d t ::: probability mbool (* ? *) R -> G |-p Sample t ::: A
| T_score   : forall G t, G |-d t ::: R -> G |-p Score t ::: unit
| T_letin   : forall G x t u A B, 
    G |-p t ::: A -> (extend G x A) |-p u ::: B -> G |-p Letin x t u ::: B
| T_ifp     : forall G t u1 u2 A B, 
    G |-d t ::: A -> G |-p u1 ::: B -> G |-p u2 ::: B -> G |-p Ifp t u1 u2 ::: B
where "G |-p t ::: A" := (program_p G t A).

(* Example pgm1 := empty |-p Letin "x" (Score (Const 1)) (Ret (Var "x")) ::: t_unit.
Example _pgm1 : pgm1.
Proof. apply /T_letin.
apply /T_score. admit.
apply /T_return. admit.
Admitted. *)

Check tt : [| t_unit |]Type.

Fixpoint denote_d {G t A} (pgm : program_d G t A) 
  : [| G |]context -> A  (* TODO: measurable function *) := 
  match pgm with
  | T_unit _ => fun _ => tt
  | T_app _ _ _ _ _ f s => fun g => denote_d f g (denote_d s g)
  | T_ifd _ _ _ _ _ p1 p2 p3 => 
      fun p => if denote_d p1 p then denote_d p2 p else denote_d p3 p
  | T_var G' x t H => fun g => lookup x G
  | T_bernoulli _ r => fun _ => [the probability _ _ of bernoulli27 R] (* r *)
  end.

Example pgmd := @T_unit empty.
Compute denote_d pgmd.
Example denote_pgmd : denote_d pgmd tt = tt.
Proof. by []. Qed. 
Example pgmd2 := @T_bernoulli empty 1.
Example denote_pgmd2 : denote_d pgmd2 tt = [the probability _ _ of bernoulli27 R].
Proof. by []. Qed.  

Fixpoint denote_p {G t A} (pgm : program_p G t A)
  : R.-sfker _ ~> _ := 
  (* [the measurableType _ of [| G |]context] ~> [| A |]Type := *)
  match pgm with
  (* | T_return _ _ _ s => Return R (denote_d s _) *)
  (* | T_sample G t A p => sample (denote_d p _) *)
  | _ => sample [the probability _ _ of bernoulli27 R]
  end.

Example ex4 :
  empty |-p Letin "x" (Sample (Bernoulli (2 / 7)))
    (Ret (Var "x")) ::: R.
Proof. 
apply /T_letin.
Admitted.

Example k3d : empty |-d App (Const 3) TT ::: t_real.
Proof.
apply /T_app /T_unit.
Admitted.

Example k3p : empty |-p Score (App (Const 3) TT) ::: t_unit.
Proof.
apply /T_score /T_app /T_unit.
Admitted.

Example ex_p30 : 
  empty |-p Letin "x" (Sample (Bernoulli (1 / 2)))
    (Letin "r" (Ifp (Var "x") (Score (App (Const 4) TT)) (Score (App (Const 6) TT))) (Ret (Var "x"))) ::: t_real.
Proof.
apply /T_letin.
(* apply /T_sample /T_bernoulli.
apply /T_letin.
apply /T_ifp.
apply /T_var.
apply /T_score /T_app /T_unit.
apply /T_score /T_app /T_unit.
apply /T_return /T_context /T_var. *)
Admitted.

Inductive eval_termD : termD -> termD -> Prop :=
| E_var : forall x, eval_termD (Var x) (Var x)
.

(* Let mbool := Datatypes_bool__canonical__measure_Measurable.
Let munit := Datatypes_unit__canonical__measure_Measurable.
Definition eval_type (t : type) : Type :=
  match t with
  | t_unit => unit
  | t_real => R
  | t_P t_unit => probability munit R
  | t_P t_real => probability T (* R *) R
  | t_P _ => probability T R
  end. *)

End v4.
*)
Section v2.

Variable (R : realType).

Variable (d d' : measure_display) (T : measurableType d) (T' : measurableType d').
Definition Env := list (string * (R.-ker T ~> T')).
Definition empty_env : Env := [::].
Fixpoint env_get x (env : Env) : R.-ker T ~> T' :=
  match env with
  | [::] => [the kernel _ _ _ of @kernel_from_mzero _ _ R _ T]
  | (x', v) :: env' => if string_dec x x' then v else env_get x env'
  end.
Fixpoint env_set x v (env : Env) :=
  match env with
  | [::] => [:: (x, v)]
  | (x', v') :: env' => if string_dec x x' then (x,v)::env' else (x',v')::env_set x v env'
  end.

(* Definition env1 := set "x" 1 empty_env.
Definition env2 := set "y" 6%:R env1.
Compute get "x" env1.
Lemma _get2 : get "y" env2 = 6%:R.
Proof. by []. Qed. *)

Inductive Z := P | D.

(* Variables (d d': measure_display) (T : measurableType d) (T' : measurableType d'). *)

Inductive ExpD : Type :=
  (* | Const (r : R) *)
  (* | IfD (e1 : ExpD) (e2 e3 : ExpD) *)
  (* | Var : string -> ExpD *)
  | LamE : T -> ExpD -> ExpD
  | AppE : ExpD -> ExpD -> ExpD
  (* | Letin (x : string) (e1 : ExpP) (e2 : ExpD) *)
  .

Check Return R.

(* Example pgm1 := Const 1.
(* Example pgm2 :=  *)
Example eval1 : evalD pgm1 = fun=> 1%:R.
Proof. by []. Qed. *)

Inductive ExpP : Type :=
  | RetE (x : ExpD)
  (* | Samp (m : probability T' R) *)
  .

Variable (f : T -> T') (mf : measurable_fun setT f).

Check Return R mf.

Fixpoint evalP (e : ExpP) : R.-sfker _ ~> _ :=
  match e with 
  | RetE x => Return R mf
  (* | Samp m => [the sfinite_kernel T _ _ of kernel_probability m] *)
  end.

Fail Fixpoint evalD (env : Env) (e : ExpD) : R.-sfker _ ~> _ :=
  match e with 
  (* | Const n => [the sfinite_kernel _ _ _ of [the kernel _ _ _ of kn n] _ _] Const: return measurable fun. *)
  (* | If e1 e2 e3 => if e1 then (evalD env e2) else (evalD env e3)
  | Var x => get x env
  | Letin x e1 e2 => evalD (set x (evalP env e1) env) e2 *)
  end.

Fail Inductive ExpD : Type :=
  | Const (r : R)
  | Add (e1 e2 : ExpD)
  | If (e1 : bool) (e2 e3 : ExpD) (* If probabilistic *)
  | Var (x : string)
  | Letin (x : string) (e1 : ExpD) (e2 : ExpD)
  .

Fail Fixpoint eval (env : Env) (e : ExpD) : R :=
  match e with 
  | Const n => n (* Const: return measurable fun. *)
  | Add e1 e2 => eval env e1 + eval env e2
  | If e1 e2 e3 => if e1 then (eval env e2) else (eval env e3)
  | Var x => get x env
  | Letin x e1 e2 => eval (set x (eval env e1) env) e2
  end.

Fail Definition evalp (e : ExpP) : R.-sfker _ ~> _ :=
  match e with
  | RetE f mf => Return R mf
  | Samp m => [the sfinite_kernel T _ _ of kernel_probability m]
  end.
End v2.

Section eval.

Variables (R : realType).
Variables (d: measure_display) (T : measurableType d).

Let mR := Real_sort__canonical__measure_Measurable R.
Let munit := Datatypes_unit__canonical__measure_Measurable.
Let mbool := Datatypes_bool__canonical__measure_Measurable.

End eval.