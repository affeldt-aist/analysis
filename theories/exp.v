(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum.
From mathcomp Require Import matrix interval rat.
Require Import boolp reals ereal.
Require Import nsatz_realtype.
Require Import classical_sets posnum topology normedtype landau sequences.
Require Import derive realfun.

(******************************************************************************)
(*               Theory of exponential/logarithm functions                    *)
(*                                                                            *)
(* This file defines exponential and logarithm functions and develops their   *)
(* theory.                                                                    *)
(*                                                                            *)
(* Section TermDiff == Differentiability of series inspired by HOL-Light      *)
(*                     transc.ml                                              *)
(*        diffs f i == (i + 1) * f (i + 1)                                    *)
(*                                                                            *)
(*             ln x == the natural logarithm                                  *)
(*           a `^ x == exponential functions                                  *)
(*       riemannR a == sequence n |-> 1 / (n.+1) `^ a where a has a type of   *)
(*                     type realType                                          *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* TODO : backport to mathcomp *)
Lemma normr_nneg (R : numDomainType) (x : R) : `|x| \is Num.nneg.
Proof. by rewrite qualifE. Qed.
Hint Resolve normr_nneg : core.

Section continuous.
Variables (K : numFieldType) (U V : normedModType K).

Lemma continuous_shift (f : U -> V) u :
  {for u, continuous f} = {for 0, continuous (f \o shift u)}.
Proof. by rewrite [in RHS]forE /= add0r cvg_comp_shift add0r. Qed.

Lemma continuous_withinNshiftx (f : U -> V) u :
  f \o shift u @ 0^' --> f u <-> {for u, continuous f}.
Proof.
rewrite continuous_shift; split=> [cfu|].
  by apply/(continuous_withinNx _ _).2/(cvg_trans cfu); rewrite /= add0r.
by move/(continuous_withinNx _ _).1/cvg_trans; apply; rewrite /= add0r.
Qed.

End continuous.

Lemma derive1_comp (R : realFieldType) (f g : R -> R) x :
  derivable f x 1 -> derivable g (f x) 1 ->
  (g \o f)^`() x = g^`() (f x) * f^`() x.
Proof.
move=> /derivable1_diffP df /derivable1_diffP dg.
rewrite derive1E'; last exact/differentiable_comp.
rewrite diff_comp // !derive1E' //= -[X in 'd  _ _ X = _]mulr1.
by rewrite [LHS]linearZ mulrC.
Qed.

(******************************************************************************)
(* Multi-rule for fct                                                         *)
(******************************************************************************)

Lemma addrfunE [T : pointedType] [K : ringType] (f g : T -> K) :
  f + g = (fun x : T => f x + g x).
Proof. by []. Qed.

Lemma opprfunE [T : pointedType] [K : ringType] (f : T -> K) :
  - f = (fun x : T => - f x).
Proof. by []. Qed.

Lemma mulrfunE [T : pointedType] [K : ringType] (f g : T -> K) :
  f * g = (fun x : T => f x * g x).
Proof. by []. Qed.

Lemma scalrfunE [T : pointedType] [K : ringType] [L : lmodType K]
               k (f : T -> L) :
  k *: f = (fun x : T => k *: f x).
Proof. by []. Qed.

Lemma cstE [T T': Type] (x : T) : cst x = fun _: T' => x.
Proof. by []. Qed.

Lemma compE [T1 T2 T3 : Type] (f : T1 -> T2) (g : T2 -> T3) : 
  g \o f = fun x => g (f x).
Proof. by []. Qed.

Definition rcfE := 
 (cstE, compE, opprfunE, addrfunE, mulrfunE, scalrfunE, exprfunE).

Section is_derive_instances.
Variables (R : numFieldType) (V : normedModType R).

Lemma derivable_cst (x : V) : derivable (fun=> x) 0 1.
Proof. exact/derivable1_diffP/differentiable_cst. Qed.

Lemma derivable_id (x v : V) : derivable id x v.
Proof.
apply/derivable1P/derivableD.
  exact/derivable1_diffP/differentiableZl.
exact/derivable_cst.
Qed.

Global Instance is_derive_id (x v : V) : is_derive x v id v.
Proof.
apply: (DeriveDef (@derivable_id _ _)).
by rewrite deriveE// (@diff_lin _ _ _ [linear of idfun]).
Qed.

End is_derive_instances.

Section is_derive.

Variable R : realType.

(* Attempt to prove the diff of inverse *)

Lemma is_derive1_caratheodory (f : R -> R) (x a : R) :
  is_derive x 1 f a <->
  exists g, [/\ forall z, f z - f x = g z * (z - x),
        {for x, continuous g} & g x = a].
Proof.
split => [Hd|[g [fxE Cg gxE]]].
  exists (fun z => if z == x then a else (f(z) - f(x)) / (z - x)); split.
  - move=> z; case: eqP => [->|/eqP]; first by rewrite !subrr mulr0.
    by rewrite -subr_eq0 => /divfK->.
  - apply/continuous_withinNshiftx; rewrite eqxx /=.
    pose g1 h := (h^-1 *: ((f \o shift x) h%:A - f x)).
    have F1 : g1 @ 0^' --> a by case: Hd => H1 <-.
    apply: cvg_trans F1; apply: near_eq_cvg; rewrite /g1 !rcfE.
    near=> i.
    rewrite ifN; first by rewrite addrK mulrC /= [_%:A]mulr1.
    rewrite -subr_eq0 addrK.
    by near: i; rewrite near_withinE /= near_simpl; near=> x1.
  by rewrite eqxx.
suff Hf : h^-1 *: ((f \o shift x) h%:A - f x) @[h --> 0^'] --> a.
  have F1 : 'D_1 f x = a by apply: cvg_lim.
  rewrite -F1 in Hf.
    by constructor.
  have F1 :  (g \o shift x) y @[y --> 0^'] --> a.
  by rewrite -gxE; apply/continuous_withinNshiftx.
apply: cvg_trans F1; apply: near_eq_cvg.
near=> y.
rewrite /= fxE /= addrK [_%:A]mulr1.
suff yNZ : y != 0 by rewrite [RHS]mulrC mulfK.
by near: y; rewrite near_withinE /= near_simpl; near=> x1.
Grab Existential Variables. all: end_near. Qed.

Lemma is_derive_0_cst (f : R -> R) x y :
  (forall x, is_derive x 1 f 0) -> f x = f y.
Proof.
move=> Hd.
wlog xLy : x y / x <= y.
  by move=> H; case: (leP x y) => [/H |/ltW /H].
rewrite -(subKr (f y) (f x)).
case: (MVT xLy) => [x1 _|_ _].
  by apply/differentiable_continuous/derivable1_diffP.
by rewrite mul0r => ->; rewrite subr0.
Qed.

Global Instance is_derive1_comp (f g : R -> R) (x a b : R) :
  is_derive (g x) 1 f a -> is_derive x 1 g b ->
  is_derive x 1 (f \o g) (a * b).
Proof.
move=> [fgxv <-{a}] [gv <-{b}]; apply: (@DeriveDef _ _ _ _ _ (f \o g)).
  apply/derivable1_diffP/differentiable_comp; first exact/derivable1_diffP.
  by move/derivable1_diffP in fgxv.
by rewrite -derive1E (derive1_comp gv fgxv) 2!derive1E.
Qed.

Global Instance is_deriveV (f : R -> R) (x t v : R) :
  f x != 0 -> is_derive x v f t ->
  is_derive x v [fun y => (f y)^-1]  (- (f x) ^- 2 *: t).
Proof.
move=> fxNZ Df.
constructor; first by apply: derivableV => //; case: Df.
by rewrite deriveV //; case: Df => _ ->.
Qed.

Lemma is_derive_inverse (f g : R ->R) l x :
  {near x, cancel f g}  ->
  {near x, continuous f}  ->
  is_derive x 1 f l -> l != 0 -> is_derive (f x) 1 g l^-1.
Proof.
move=> fgK fC fD lNZ.
have /is_derive1_caratheodory [h [fE hC hxE]] := fD.
(* There should be something simpler *)
have gfxE :  g (f x) = x by have [d Hd]:= nbhs_ex fgK; apply: Hd.
pose g1 y := if y == f x then (h (g y))^-1
             else (g y - g (f x)) / (y - f x).
apply/is_derive1_caratheodory.
exists g1; split; first 2 last.
- by rewrite /g1 eqxx gfxE hxE.
- move=> z; rewrite /g1; case: eqP => [->|/eqP]; first by rewrite !subrr mulr0.
  by rewrite -subr_eq0 => /divfK.
have F1 : (h (g x))^-1 @[x --> f x] --> g1 (f x).
  rewrite /g1 eqxx; apply: continuousV; first by rewrite /= gfxE hxE.
  apply: continuous_comp; last by rewrite gfxE.
  by apply: nbhs_singleton (near_can_continuous _ _).
apply: cvg_sub0 F1.
apply/cvg_distP => eps eps_gt0 /=; rewrite !near_simpl /=.
near=> y; rewrite sub0r normrN !rcfE.
have fgyE : f (g y) = y by near: y; apply: near_continuous_can_sym.
rewrite /g1; case: eqP => [_|/eqP x1Dfx]; first by rewrite subrr normr0.
have -> : y - f x  = h (g y) * (g y - x) by rewrite -fE fgyE.
rewrite gfxE invfM mulrC divfK ?subrr ?normr0 // subr_eq0.
by apply: contra x1Dfx => /eqP<-; apply/eqP.
Grab Existential Variables. all: end_near. Qed.

(* Trick to trigger type class resolution *)
Lemma trigger_derive (f : R -> R) x x1 y1 :
  is_derive x 1 f x1 -> x1 = y1 -> is_derive x 1 f y1.
Proof. by move=> Hi <-. Qed.

End is_derive.


Section TermDiff.

Variable R : realType.

Fact is_cvg_series_Xn_inside_norm f (x z : R) :
  cvg (series (fun i =>    f i * x ^+ i)) -> `|z| < `|x| ->
  cvg (series (fun i => `|f i| * z ^+ i)).
Proof.
move=> Cx zLx.
have [K K_gt0 KP] := cvg_series_bounded Cx.
have F1 := cvg_series_cvg_0 Cx.
have F2 n : 0 <= K * `|z ^+ n| / `|x ^+ n|.
  by rewrite !mulr_ge0 ?invr_ge0 // ltW.
apply: normed_cvg.
apply: series_le_cvg F2 _ _ => [//=| /= n|].
  rewrite (_ : `|_ * _| = `|f n * x ^+ n| * `|z ^+ n| / `|x ^+ n|); last first.
    rewrite !normrM normr_id mulrAC mulfK // normr_eq0 expf_eq0 andbC.
    by case: ltrgt0P zLx; rewrite //= normr_lt0.
  do! (apply: ler_pmul || apply: mulr_ge0 || rewrite invr_ge0) => //.
  by apply: ltW.
have F : `|z / x| < 1.
  by rewrite normrM normfV ltr_pdivr_mulr ?mul1r // (le_lt_trans _ zLx).
rewrite (_ : (fun _ => _) = geometric K `|z / x|).
apply: is_cvg_geometric_series; first by rewrite normr_id.
apply/funext => i /=.
by rewrite normrM exprMn mulrA normfV !normrX exprVn.
Qed.

Fact is_cvg_series_Xn_inside f (x z : R) :
  cvg (series (fun i => f i * x ^+ i)) -> `|z| < `|x| ->
  cvg (series (fun i => f i * z ^+ i)).
Proof.
move=> Cx zLx.
apply: normed_cvg; rewrite /normed_series_of /=.
rewrite (_ : (fun _ => _) = (fun i : nat => `|f i| * `|z| ^+ i)); last first.
  by apply/funext => i; rewrite normrM normrX.
by apply: is_cvg_series_Xn_inside_norm Cx _; rewrite normr_id.
Qed.

Definition diffs (f : nat -> R) i := i.+1%:R * f i.+1.

Lemma diffsN (f : nat -> R) :  diffs (- f) = -(diffs f).
Proof. by apply/funext => i; rewrite /diffs /= -mulrN. Qed.

Lemma diffs_inv_fact :
  diffs (fun n => (n`!%:R)^-1) = (fun n => (n`!%:R)^-1 : R).
Proof.
by apply/funext => i; rewrite /diffs factS natrM invfM mulrA mulfV ?mul1r.
Qed.

Lemma diffs_sumE n f x :
  \sum_(0 <= i < n)  diffs f i * x ^+ i =
  (\sum_(0 <= i < n) i%:R * f i * x ^+ i.-1) + n%:R * f n * x ^+ n.-1.
Proof.
case: n => [|n]; first by rewrite !big_nil !mul0r add0r.
under eq_bigr do unfold diffs.
by rewrite big_nat_recr //= big_nat_recl //= !mul0r add0r.
Qed.

Lemma diffs_equiv f x :
  let s1 i := diffs f i * x ^+ i in
  let s2 i := i%:R * f i * x ^+ i.-1 in
  cvg (series s1) -> series s2 --> lim (series s1).
Proof.
move=> s1 s2 Cx; rewrite -[lim _]subr0 [X in X --> _]/series /=.
rewrite (_ : (fun n => _) =
    (fun n => \sum_(0 <= i < n) s1 i - n%:R * f n * x ^+ n.-1)); last first.
  by rewrite funeqE => n; rewrite diffs_sumE addrK.
by apply: cvgB => //; rewrite -cvg_shiftS; exact: cvg_series_cvg_0.
Qed.

Lemma is_cvg_diffs_equiv f x :
  let s1 i := diffs f i * x ^+ i in
  let s2 i := i%:R * f i * x ^+ i.-1 in cvg (series s1) -> cvg (series s2).
Proof.
move=> s1 s2 Cx; rewrite /s1 /s2 in Cx.
have F1 := diffs_equiv Cx.
by rewrite (cvg_lim _ (F1)).
Qed.

Let termdiffs_P1 m (z h : R) :
  \sum_(0 <= i < m) ((h + z) ^+ (m - i) * z ^+ i - z ^+ m) =
  \sum_(0 <= i < m) z ^+ i * ((h + z) ^+ (m - i) - z ^+ (m - i)).
Proof.
rewrite !big_mkord; apply: eq_bigr => i _.
by rewrite mulrDr mulrN -exprD mulrC addnC subnK // ltnW.
Qed.

Let termdiffs_P2 n (z h : R) :
  h != 0 ->
  ((h + z) ^+ n - (z ^+ n)) / h - n%:R * z ^+ n.-1 =
  h * \sum_(0 <= i < n.-1) z ^+ i *
      \sum_(0 <= j < n.-1 - i) (h + z) ^+ j * z ^+ (n.-2 - i - j).
Proof.
move=> hNZ; apply: (mulfI hNZ).
rewrite mulrBr mulrC divfK //.
case: n => [|n].
  by rewrite !expr0 !(mul0r, mulr0, subr0, subrr, big_geq).
rewrite subrXX addrK -mulrBr; congr (_ * _).
rewrite -(big_mkord xpredT (fun i : nat => (h + z) ^+ (n - i) * z ^+ i)).
rewrite big_nat_recr //= subnn expr0 -addrA -mulrBl.
rewrite  -add1n natrD opprD addrA subrr sub0r mulNr.
rewrite mulr_natl -[in X in _ *+ X](subn0 n) -sumr_const_nat -sumrB.
rewrite termdiffs_P1 mulr_sumr !big_mkord; apply: eq_bigr => i _.
rewrite mulrCA; congr (_ * _).
rewrite subrXX addrK big_nat_rev /= big_mkord.
congr (_ * _); apply: eq_bigr => k _.
by rewrite -!predn_sub subKn // -subnS.
Qed.

Let termdiffs_P3 (z h : R) n K :
  h != 0 -> `|z| <= K -> `|h + z| <= K ->
    `|((h +z) ^+ n - z ^+ n) / h - n%:R * z ^+ n.-1|
      <= n%:R * n.-1%:R * K ^+ n.-2 * `|h|.
Proof.
move=> hNZ zLK zhLk.
rewrite termdiffs_P2// normrM mulrC.
rewrite ler_pmul2r ?normr_gt0//.
rewrite (le_trans (ler_norm_sum _ _ _))//.
rewrite -mulrA mulrC -mulrA.
rewrite mulr_natl -[X in _ *+ X]subn0 -sumr_const_nat.
apply ler_sum_nat => i /=.
case: n => //= n ni.
rewrite normrM.
pose d := (n.-1 - i)%nat.
rewrite -[(n - i)%nat]prednK ?subn_gt0// predn_sub -/d.
rewrite -(subnK (_ : i <= n.-1)%nat) -/d; last first.
  by rewrite -ltnS prednK// (leq_ltn_trans _ ni).
rewrite addnC exprD mulrAC -mulrA.
apply: ler_pmul => //.
  by rewrite normrX ler_expn2r// qualifE (le_trans _ zLK).
apply: le_trans (_ : d.+1%:R * K ^+ d <= _); last first.
  rewrite ler_wpmul2r //; first by rewrite exprn_ge0 // (le_trans _ zLK).
  by rewrite ler_nat ltnS /d -subn1 -subnDA leq_subr.
rewrite (le_trans (ler_norm_sum _ _ _))//.
rewrite mulr_natl -[X in _ *+ X]subn0 -sumr_const_nat ler_sum_nat//= => j jd1.
rewrite -[in X in _ <= X](subnK (_ : j <= d)%nat) -1?ltnS // addnC exprD normrM.
by rewrite ler_pmul// ?normr_ge0// normrX ler_expn2r// qualifE (le_trans _ zLK).
Qed.

Lemma termdiffs (c : R^nat) K x :
  cvg (series (fun n => c n * K ^+ n)) ->
  cvg (series (fun n => diffs c n * K ^+ n)) ->
  cvg (series (fun n => diffs (diffs c) n * K ^+ n)) ->
  `|x| < `|K| ->
  is_derive x 1
    (fun x => lim (series (fun n => c n * x ^+ n)))
    (lim (series (fun n => diffs c n * x ^+ n))).
Proof.
move=> Ck CdK CddK xLK; set s := (fun n : nat => _).
set (f := fun x => _).
suff Hf :
  h^-1 *: (f (h + x) - f x) @[h --> 0^'] --> lim (series s).
  have F : f^`() x = lim (series s) by  apply: cvg_lim Hf.
  rewrite (_ : (fun h => h^-1 *: (f (h + x) - f x)) =
              (fun h => h^-1 *: (f (h%:A + x) - f x))) in Hf; last first.
    by apply/funext => i //=; rewrite [i%:A]mulr1.
  have Df : derivable f x 1 by rewrite /derivable (cvg_lim _ Hf).
  by constructor=> [//|]; rewrite -derive1E.
set sx := fun n : nat => c n * x ^+ n.
have Csx : cvg (series sx) by apply: is_cvg_series_Xn_inside Ck _.
pose shx h := fun n : nat => c n * (h + x) ^+ n.
suff Cc : lim (h^-1 *: (series (shx h - sx))) @[h --> 0^'] --> lim (series s).
  apply: cvg_sub0 Cc.
  apply/cvg_distP => eps eps_gt0 /=; rewrite !near_simpl /=.
  near=> h; rewrite sub0r normrN /=.
  apply: le_lt_trans eps_gt0.
  rewrite normr_le0 subr_eq0 -/sx -/(shx _); apply/eqP.
  have Cshx : cvg (series (shx h)).
    apply: is_cvg_series_Xn_inside Ck _.
    apply: le_lt_trans (ler_norm_add _ _) _.
    rewrite -(subrK  `|x| `|K|) ltr_add2r.
    near: h.
    apply/nbhs_ballP => /=; exists ((`|K| - `|x|) /2) => /=.
      by rewrite divr_gt0 // subr_gt0.
    move=> t; rewrite /ball /= sub0r normrN => H tNZ.
    apply: lt_le_trans H _.
    rewrite ler_pdivr_mulr // mulr2n mulrDr mulr1.
    by rewrite ler_paddr // subr_ge0 ltW.
  rewrite limZr; last by apply: is_cvg_seriesB.
  by rewrite lim_seriesB.
apply: cvg_zero => /=.
suff Cc :
  lim (series
       (fun n => c n * (((h + x) ^+ n - x ^+ n) / h - n%:R * x ^+ n.-1)))
   @[h --> 0^'] --> (0 : R).
  apply: cvg_sub0 Cc.
  apply/cvg_distP => eps eps_gt0 /=.
  rewrite !near_simpl /=.
  near=> h; rewrite sub0r normrN /=.
  apply: le_lt_trans eps_gt0.
  rewrite normr_le0 subr_eq0; apply/eqP.
  have Cs : cvg (series s) by apply: is_cvg_series_Xn_inside CdK _.
  have Cs1 := is_cvg_diffs_equiv Cs.
  have Fs1 := diffs_equiv Cs.
  set s1 := (fun i => _) in Cs1.
  have Cshx : cvg (series (shx h)).
    apply: is_cvg_series_Xn_inside Ck _.
    apply: le_lt_trans (ler_norm_add _ _) _.
    rewrite -(subrK  `|x| `|K|) ltr_add2r.
    near: h.
    apply/nbhs_ballP => /=; exists ((`|K| - `|x|) /2) => /=.
      by rewrite divr_gt0 // subr_gt0.
    move=> t; rewrite /ball /= sub0r normrN => H tNZ.
    apply: lt_le_trans H _.
    rewrite ler_pdivr_mulr // mulr2n mulrDr mulr1.
    by rewrite ler_paddr // subr_ge0 ltW.
  have C1 := is_cvg_seriesB Cshx Csx.
  have Ckf := @is_cvg_seriesZ _ _ h^-1 C1.
  have Cu :
   (series (h^-1 *: (shx h - sx)) - series s1) x0 @[x0 --> \oo] -->
    lim (series (h^-1 *: (shx h - sx))) - lim (series s).
    by apply: cvgB.
  set w := fun n : nat => _.
  have -> : w = h^-1 *: (shx h - sx)  - s1.
    apply: funext => i; rewrite !rcfE.
    rewrite /w /shx /sx /s1 /= mulrBr; congr (_ - _); last first.
      by rewrite mulrCA !mulrA.
    by rewrite -mulrBr [RHS]mulrCA [_^-1 * _]mulrC.
  rewrite [X in X h = _]/+%R /= [X in _ + X h = _]/-%R /=.
  have -> : series (h^-1 *: (shx h - sx) - s1) =
            series (h^-1 *: (shx h - sx)) - (series s1).
    by apply/funext => i; rewrite /series /= sumrB.
  have -> : h^-1 *: series (shx h - sx) = series (h^-1 *: (shx h - sx)).
    by apply/funext => i; rewrite /series /= -scaler_sumr.
  by apply/sym_equal/cvg_lim.
pose r := (`|x| + `|K|) / 2.
have xLr : `|x| < r by rewrite ltr_pdivl_mulr // mulr2n mulrDr mulr1 ltr_add2l.
have rLx : r < `|K| by rewrite ltr_pdivr_mulr // mulr2n mulrDr mulr1 ltr_add2r.
have r_gt0 : 0 < r by apply: le_lt_trans xLr.
have rNZ : r != 0by case: ltrgt0P r_gt0.
apply: (@lim_cvg_to_0_linear _
  (fun n => `|c n| * n%:R * (n.-1)%:R * r ^+ n.-2)
  (fun h n => c n * (((h + x) ^+ n - x ^+ n) / h -
                     n%:R * x ^+ n.-1))
  (r - `|x|)); first by rewrite subr_gt0.
- have : cvg (series (fun n => `|diffs (diffs c) n| * r ^+ n)).
    apply: is_cvg_series_Xn_inside_norm CddK _.
    by rewrite ger0_norm // ltW // (le_lt_trans _ xLr).
  have -> : (fun n => `|diffs (diffs c) n| * r ^+ n) =
            (fun n => diffs (diffs (fun m => `|c m|)) n * r ^+ n).
    apply/funext => i.
    by rewrite /diffs !normrM !mulrA ger0_norm // ger0_norm.
  move=> /is_cvg_diffs_equiv.
  rewrite /diffs.
  have -> :
         (fun n => n%:R * ((n.+1)%:R * `|c n.+1|) * r ^+ n.-1) =
         (fun n => diffs (fun m => (m.-1)%:R * `|c m| * r^-1) n * r ^+ n).
    apply/funext => n.
    rewrite /diffs /= mulrA.
    case: n => [|n /=]; first by rewrite !(mul0r, mulr0).
    rewrite [_%:R *_]mulrC !mulrA -[RHS]mulrA exprS.
    by rewrite [_^-1 * _]mulrA mulVf ?mul1r.
  move/is_cvg_diffs_equiv.
  have ->// : (fun n : nat => n%:R * (n.-1%:R * `|c n| / r) * r ^+ n.-1) =
              (fun n : nat => `|c n| * n%:R * n.-1%:R * r ^+ n.-2).
  apply/funext => [] [|[|i]]; rewrite ?(mul0r, mulr0) //=.
  rewrite mulrA -mulrA exprS [_^-1 * _]mulrA mulVf //.
  rewrite mul1r !mulrA; congr (_ * _).
  by rewrite mulrC mulrA.
move=> h /andP[h_gt0 hLrBx] n.
have hNZ : h != 0 by rewrite -normr_gt0.
rewrite normrM -!mulrA ler_wpmul2l //.
apply: le_trans (termdiffs_P3 _ hNZ (ltW xLr) _) _; last by rewrite !mulrA.
apply: le_trans (ler_norm_add _ _) _.
by rewrite -(subrK `|x| r) ler_add2r ltW.
Grab Existential Variables. all: end_near. Qed.

End TermDiff.

Section expR.

Variable R : realType.
Implicit Types x : R.

Lemma expR0 : expR 0 = 1 :> R.
Proof.
apply: lim_near_cst => //.
near=> m; rewrite -[m]prednK; last by near: m.
rewrite -addn1 series_addn series_exp_coeff0 big_add1 big1 ?addr0//.
by move=> i _; rewrite /exp_coeff /= expr0n mul0r.
Grab Existential Variables. all: end_near. Qed.

Lemma expR_ge1Dx x : 0 <= x -> 1 + x <= expR x.
Proof.
move=> x_gt0; rewrite /expR.
pose f (x : R) i := (i == 0%nat)%:R + x *+ (i == 1%nat).
have F n : (1 < n)%nat -> \sum_(0 <= i < n) (f x i) = 1 + x.
  move=> /subnK<-.
  by rewrite addn2 !big_nat_recl //= /f /= mulr1n !mulr0n big1 ?add0r ?addr0.
have -> : 1 + x = lim (series (f x)).
  by apply/sym_equal/lim_near_cst => //; near=> n; apply: F; near: n.
apply: ler_lim; first by apply: is_cvg_near_cst; near=> n; apply: F; near: n.
  exact: is_cvg_series_exp_coeff.
by near=> n; apply: ler_sum => [] [|[|i]] _;
  rewrite /f /exp_coeff /= !(mulr0n, mulr1n, expr0, expr1, divr1, addr0, add0r)
          // exp_coeff_ge0.
Grab Existential Variables. all: end_near. Qed.

Lemma exp_coeffE x :
  exp_coeff x = (fun n => (fun n => (n`!%:R)^-1) n * x ^+ n).
Proof. by apply/funext => i; rewrite /exp_coeff /= mulrC. Qed.

Import GRing.Theory.
Local Open Scope ring_scope.

Lemma expRE :
  expR = fun x => lim (series (fun n => (fun n => (n`!%:R)^-1) n * x ^+ n)).
Proof. by apply/funext => x; rewrite -exp_coeffE. Qed.

Global Instance is_derive_expR x : is_derive x 1 expR (expR x).
Proof.
pose s1 n := diffs (fun n => n`!%:R^-1) n * x ^+ n.
rewrite expRE /=.
rewrite (_ : (fun n => _) = s1); last first.
  by apply/funext => i; rewrite /s1 diffs_inv_fact.
apply: (@termdiffs _ _ (`|x| + 1)).
- rewrite -exp_coeffE; apply: is_cvg_series_exp_coeff.
- rewrite (_ : (fun n : nat => _) = exp_coeff (`|x| + 1)).
    by apply: is_cvg_series_exp_coeff.
  by apply/funext => i; rewrite diffs_inv_fact exp_coeffE.
- rewrite (_ : (fun n : nat => _) = exp_coeff (`|x| + 1)).
    by apply: is_cvg_series_exp_coeff.
  by apply/funext => i; rewrite !diffs_inv_fact exp_coeffE.
by rewrite ger0_norm ?addr_ge0 // addrC -subr_gt0 addrK.
Qed.

Lemma derivable_expR x : derivable expR x 1.
Proof. by apply: ex_derive; apply: is_derive_exp. Qed.

Lemma continuous_expR : continuous (@expR R).
Proof.
move=> x.
apply: differentiable_continuous.
by apply/derivable1_diffP/derivable_expR.
Qed.

Lemma expRxDyMexpx x y : expR (x + y) * expR (- x) = expR y.
Proof.
apply: etrans (_ : expR (0 + y) * expR (- 0) = _); last first.
  by rewrite add0r oppr0 expR0 mulr1.
apply: (@is_derive_0_cst _ (fun x => expR (x + y) * expR (- x))) => x1.
have -> : 0 = expR (x1 + y) * (expR (- x1) * (- 1)) +
              expR (- x1) * (expR (x1 + y) * (1 + 0)).
  by rewrite mulrN1 addr0 mulr1 mulrN addrC mulrC subrr.
apply: is_deriveM.
apply: is_derive1_comp.
apply: is_deriveN.
Qed.

Lemma expRxMexpNx_1 x : expR x * expR (- x) = 1.
Proof. by rewrite -[X in _ X * _ = _]addr0 expRxDyMexpx expR0. Qed.

Lemma pexpR_gt1 x : 0 < x -> 1 < expR x.
Proof.
move=> x_gt0.
apply: lt_le_trans (expR_ge1Dx (ltW x_gt0)).
by rewrite -subr_gt0 addrAC subrr add0r.
Qed.

Lemma expR_gt0 x : 0 < expR x.
Proof.
case: (ltrgt0P x) => [x_gt0|x_gt0|->].
- by apply: lt_trans (pexpR_gt1 x_gt0).
- have F : 0 < expR (- x) by apply: lt_trans (pexpR_gt1 _); rewrite ?oppr_gt0.
  by rewrite -(pmulr_lgt0 _ F) expRxMexpNx_1.
by rewrite expR0.
Qed.

Lemma expRN x : expR (- x) = (expR x)^-1.
Proof.
apply: (mulfI (lt0r_neq0 (expR_gt0 x))).
by rewrite expRxMexpNx_1 mulfV // (lt0r_neq0 (expR_gt0 x)).
Qed.

Lemma expRD x y : expR (x + y) = expR x * expR y.
Proof.
apply: (mulIf (lt0r_neq0 (expR_gt0 (- x)))).
rewrite expRxDyMexpx expRN [_ * expR y]mulrC mulfK //.
by case: ltrgt0P (expR_gt0 x).
Qed.

Lemma expRMm n x : expR (n%:R * x) = expR x ^+ n.
Proof.
elim: n x => [x|n IH x] /=; first by rewrite mul0r expr0 expR0.
by rewrite exprS -add1n natrD mulrDl mul1r expRD IH.
Qed.

Lemma expR_gt1 x:  (1 < expR x) = (0 < x).
Proof.
case: ltrgt0P => [x_gt0|xN|->]; first 2 last.
- by rewrite expR0.
- by rewrite (pexpR_gt1 x_gt0).
apply/idP/negP.
rewrite -[x]opprK expRN -leNgt invf_cp1 ?expR_gt0 //.
by rewrite ltW // pexpR_gt1 // lter_oppE.
Qed.

Lemma expR_lt1 x:  (expR x < 1) = (x < 0).
Proof.
case: ltrgt0P => [x_gt0|xN|->]; first 2 last.
- by rewrite expR0 //.
- by apply/idP/negP; rewrite -leNgt ltW // expR_gt1.
by rewrite -[x]opprK expRN invf_cp1 ?expR_gt0 // expR_gt1 lter_oppE.
Qed.

Lemma expRB x y : expR (x - y) = expR x / expR y.
Proof. by rewrite expRD expRN. Qed.

Lemma ltr_expR : {mono (@expR R) : x y / x < y}.
Proof.
move=> x y.
by  rewrite -[in LHS](subrK x y) expRD ltr_pmull ?expR_gt0 // expR_gt1 subr_gt0.
Qed.

Lemma ler_expR : {mono (@expR R) : x y / x <= y}.
Proof.
move=> x y.
case: (ltrgtP x y) => [xLy|yLx|<-].
- by rewrite ltW // ltr_expR.
- by rewrite leNgt ltr_expR yLx.
by rewrite lexx.
Qed.

Lemma expR_inj : injective (@expR R).
Proof.
move=> x y exE.
by have [] := (ltr_expR x y, ltr_expR y x); rewrite exE ltxx; case: ltrgtP.
Qed.

Lemma expR_total_gt1 x :
  1 <= x -> exists y, [/\ 0 <= y, 1 + y <= x & expR y = x].
Proof.
move=> x_ge1; have x_ge0 : 0 <= x by apply: le_trans x_ge1.
case: (@IVT _ (fun y => expR y - x) 0 x 0) => //.
- by move=> x1 x1Ix; apply: continuousB => // y1;
    [exact: continuous_expR|exact: cst_continuous].
- rewrite expR0; case: (ltrgtP (1- x) (expR x - x)) => [_| |].
  + rewrite subr_le0 x_ge1 subr_ge0.
    by apply: le_trans (expR_ge1Dx _); rewrite ?ler_addr.
  + by rewrite ltr_add2r expR_lt1 ltNge x_ge0.
  + rewrite subr_le0 x_ge1 => -> /=; rewrite subr_ge0.
    by apply: le_trans (expR_ge1Dx x_ge0); rewrite ler_addr.
- move=> x1 _ /eqP; rewrite subr_eq0 => /eqP x1_x.
  exists x1; split => //; first by rewrite -ler_expR expR0 x1_x.
  by rewrite -x1_x expR_ge1Dx // -ler_expR x1_x expR0.
Qed.

Lemma expR_total x : 0 < x -> exists y, expR y = x.
Proof.
case: (lerP 1 x) => [/expR_total_gt1[y [_ _ Hy]]|x_lt1 x_gt0].
  by exists y.
have /expR_total_gt1[y [H1y H2y H3y]] : 1 <= x^-1 by rewrite ltW // !invf_cp1.
by exists (-y); rewrite expRN H3y invrK.
Qed.

End expR.

Section Ln.

Variable R : realType.
Implicit Types x : R.

Notation exp := (@expR R).

Definition ln x : R := xget 0 [set y | exp y == x ].

Fact ln0 x : x <= 0 -> ln x = 0.
Proof.
rewrite /ln; case: xgetP => //= y _ /eqP yx x0.
by have := expR_gt0 y; rewrite yx => /(le_lt_trans x0); rewrite ltxx.
Qed.

Lemma expK : cancel exp ln.
Proof.
by move=> x; rewrite /ln; case: xgetP => [x1 _ /eqP/expR_inj //|/(_ x)[]/=].
Qed.

Lemma lnK : {in Num.pos, cancel ln exp}.
Proof.
move=> x; rewrite qualifE => x_gt0.
rewrite /ln; case: xgetP=> [x1 _ /eqP// |H].
by case: (expR_total x_gt0) => y /eqP Hy; case: (H y).
Qed.

Lemma lnK_eq x : (exp (ln x) == x) = (0 < x).
Proof.
apply/eqP/idP=> [<-|]; first exact: expR_gt0.
by move=> x0; rewrite lnK// in_itv/= x0.
Qed.

Lemma ln1 : ln 1 = 0.
Proof. by apply/expR_inj; rewrite lnK// ?expR0// qualifE. Qed.

Lemma lnM : {in Num.pos &, {morph ln : x y / x * y >-> x + y}}.
Proof.
move=> x y x0 y0; apply: expR_inj; rewrite expRD !lnK//.
by move: x0 y0; rewrite !qualifE; exact: mulr_gt0.
Qed.

Lemma ln_inj : {in Num.pos &, injective ln}.
Proof. by move=> x y /lnK {2}<- /lnK {2}<- ->. Qed.

Lemma lnV : {in Num.pos, {morph ln : x / x ^-1 >-> - x}}.
Proof.
move=> x x0; apply: expR_inj; rewrite lnK// ?expRN ?lnK//.
by move: x0; rewrite !qualifE invr_gt0.
Qed.

Lemma ln_div : {in Num.pos &, {morph ln : x y / x / y >-> x - y}}.
Proof.
move=> x y x0 y0; rewrite (lnM x0) ?lnV//.
by move: y0; rewrite !qualifE/= invr_gt0.
Qed.

Lemma ltr_ln : {in Num.pos &, {mono ln : x y / x < y}}.
Proof. by move=> x y x_gt0 y_gt0; rewrite -ltr_expR !lnK. Qed.

Lemma ler_ln : {in Num.pos &, {mono ln : x y / x <= y}}.
Proof. by move=> x y x_gt0 y_gt0; rewrite -ler_expR !lnK. Qed.

Lemma lnX n x : 0 < x -> ln(x ^+ n) = ln x *+ n.
Proof.
move=> x_gt0; elim: n => [|n ih] /=; first by rewrite expr0 ln1 mulr0n.
by rewrite !exprS lnM ?qualifE// ?exprn_gt0// mulrS ih.
Qed.

Lemma le_ln1Dx x : 0 <= x -> ln (1 + x) <= x.
Proof.
move=> x_ge0; rewrite -ler_expR lnK ?expR_ge1Dx //.
by apply: lt_le_trans (_ : 0 < 1) _; rewrite // ler_addl.
Qed.

Lemma ln_sublinear x : 0 < x -> ln x < x.
Proof.
move=> x_gt0; apply: lt_le_trans (_ : ln (1 + x) <= _).
  by rewrite -ltr_expR !lnK ?qualifE ?addr_gt0 // ltr_addr.
by rewrite -ler_expR lnK ?qualifE ?addr_gt0// expR_ge1Dx // ltW.
Qed.

Lemma ln_ge0 x : 1 <= x -> 0 <= ln x.
Proof.
by move=> x_ge1; rewrite -ler_expR expR0 lnK// qualifE (lt_le_trans _ x_ge1).
Qed.

Lemma ln_gt0 x : 1 < x -> 0 < ln x.
Proof.
by move=> x_gt1; rewrite -ltr_expR expR0 lnK // qualifE (lt_trans _ x_gt1).
Qed.

Lemma continuous_ln x : 0 < x -> {for x, continuous ln}.
Proof.
move=> x_gt0; rewrite -[x]lnK//.
apply: nbhs_singleton (near_can_continuous _ _); near=> z; first exact: expK.
by apply: continuous_expR.
Grab Existential Variables. all: end_near. Qed.

Global Instance is_derive1_ln (x : R) : 0 < x -> is_derive x 1 ln x^-1.
Proof.
move=> x_gt0; rewrite -[x]lnK//.
apply: (@is_derive_inverse R expR); first by near=> z; apply: expK.
  by near=>z; apply: continuous_expR.
by rewrite lnK // lt0r_neq0.
Grab Existential Variables. all: end_near. Qed.

End Ln.

Section ExpFun.
Variable R : realType.
Implicit Types a x : R.

Definition exp_fun a x := expR (x * ln a).

Local Notation "a `^ x" := (exp_fun a x).

Lemma exp_fun_gt0 a x : 0 < a `^ x. Proof. by rewrite expR_gt0. Qed.

Lemma exp_funr1 a : 0 < a -> a `^ 1 = a.
Proof. by move=> a0; rewrite /exp_fun mul1r lnK. Qed.

Lemma exp_funr0 a : 0 < a -> a `^ 0 = 1.
Proof. by move=> a0; rewrite /exp_fun mul0r expR0. Qed.

Lemma exp_fun1 : exp_fun 1 = fun=> 1.
Proof. by rewrite funeqE => x; rewrite /exp_fun ln1 mulr0 expR0. Qed.

Lemma ler_exp_fun a : 1 < a -> {homo exp_fun a : x y / x <= y}.
Proof. by move=> a1 x y xy; rewrite /exp_fun ler_expR ler_pmul2r // ln_gt0. Qed.

Lemma exp_funD a : 0 < a -> {morph exp_fun a : x y / x + y >-> x * y}.
Proof. by move=> a0 x y; rewrite [in LHS]/exp_fun mulrDl expRD. Qed.

Lemma exp_fun_inv a : 0 < a -> a `^ (-1) = a ^-1.
Proof.
move=> a0.
apply/(@mulrI _ a); first by rewrite unitfE gt_eqF.
rewrite -[X in X * _ = _](exp_funr1 a0) -exp_funD // subrr exp_funr0 //.
by rewrite divrr // unitfE gt_eqF.
Qed.

Lemma exp_fun_mulrn a n : 0 < a -> exp_fun a n%:R = a ^+ n.
Proof.
move=> a0; elim: n => [|n ih]; first by rewrite mulr0n expr0 exp_funr0.
by rewrite -addn1 natrD exp_funD // exprD ih exp_funr1.
Qed.

End ExpFun.
Notation "a `^ x" := (exp_fun a x).

Section riemannR_series.
Variable R : realType.
Implicit Types a : R.
Local Open Scope ring_scope.

Definition riemannR a : R ^nat := fun n => (n.+1%:R `^ a)^-1.
Arguments riemannR a n /.

Lemma riemannR_gt0 a i : 0 < a -> 0 < riemannR a i.
Proof. move=> ?; by rewrite /riemannR invr_gt0 exp_fun_gt0. Qed.

Lemma dvg_riemannR a : 0 < a <= 1 -> ~ cvg (series (riemannR a)).
Proof.
case/andP => a0; rewrite le_eqVlt => /orP[/eqP ->|a1].
  rewrite (_ : riemannR 1 = harmonic); first exact: dvg_harmonic.
  by rewrite funeqE => i /=; rewrite exp_funr1.
have : forall n, harmonic n <= riemannR a n.
  case=> /= [|n]; first by rewrite exp_fun1 invr1.
  rewrite -[X in _ <= X]div1r ler_pdivl_mulr ?exp_fun_gt0 // mulrC.
  rewrite ler_pdivr_mulr // mul1r -[X in _ <= X]exp_funr1 //.
  by rewrite (ler_exp_fun) // ?ltr1n // ltW.
move/(series_le_cvg harmonic_ge0 (fun i => ltW (riemannR_gt0 i a0))).
by move/contra_not; apply; exact: dvg_harmonic.
Qed.

End riemannR_series.
