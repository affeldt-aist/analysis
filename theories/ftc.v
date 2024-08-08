(* mathcomp analysis (c) 2023 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop .
Require Import signed reals ereal topology normedtype sequences real_interval.
Require Import esum measure lebesgue_measure numfun realfun lebesgue_integral.
Require Import derive charge.

(**md**************************************************************************)
(* # Fundamental Theorem of Calculus for the Lebesgue Integral                *)
(*                                                                            *)
(* NB: See CONTRIBUTING.md for an introduction to HB concepts and commands.   *)
(*                                                                            *)
(* This file provides a proof of the first fundamental theorem of calculus    *)
(* for the Lebesgue integral. We derive from this theorem a corollary to      *)
(* compute the definite integral of continuous functions.                     *)
(*                                                                            *)
(* parameterized_integral mu a x f := \int[mu]_(t \in `[a, x] f t)            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma continuous_locally_integrable {R : realType} (f : R -> R) :
  continuous f -> measurable_fun setT f -> locally_integrable setT f.
Proof.
move=> cf mf; split => //; first exact: openT.
move=> K _ cK.
have : {within K, continuous f} by exact: continuous_subspaceT.
by move=> /(continuous_compact_integrable cK)/=/integrableP[].
Qed.

Section FTC.
Context {R : realType}.
Notation mu := (@lebesgue_measure R).
Local Open Scope ereal_scope.
Implicit Types (f : R -> R) (a : itv_bound R).

Let FTC0 f a x :
  (forall y, mu.-integrable [set` Interval a (BRight y)] (EFin \o f)) ->
  locally_integrable setT f ->
  let F y := (\int[mu]_(t in [set` Interval a (BRight y)]) f t)%R in
  a < BRight x -> lebesgue_pt f x ->
    h^-1 *: (F (h + x) - F x) @[h --> 0%R^'] --> f x.
Proof.
move=> intf locf F ax fx.
apply: cvg_at_right_left_dnbhs.
- apply/cvg_at_rightP => d [d_gt0 d0].
  pose E x n := `[x, x + d n[%classic%R.
  have muE y n : mu (E y n) = (d n)%:E.
    rewrite /E lebesgue_measure_itv/= lte_fin ltrDl d_gt0.
    by rewrite -EFinD addrAC subrr add0r.
  have nice_E y : nicely_shrinking y (E y).
    split=> [n|]; first exact: measurable_itv.
    exists (2, (fun n => PosNum (d_gt0 n))); split => //= [n z|n].
      rewrite /E/= in_itv/= /ball/= ltr_distlC => /andP[yz ->].
      by rewrite (lt_le_trans _ yz)// ltrBlDr ltrDl.
    rewrite (lebesgue_measure_ball _ (ltW _))// -/mu muE -EFinM lee_fin.
    by rewrite mulr_natl.
  have ixdf n : \int[mu]_(t in [set` Interval a (BRight (x + d n))]) (f t)%:E -
                \int[mu]_(t in [set` Interval a (BRight x)]) (f t)%:E =
                \int[mu]_(y in E x n) (f y)%:E.
    rewrite -[in X in X - _]integral_itv_bndo_bndc//=; last first.
      by case: locf => + _ _; exact: measurable_funS.
    rewrite (@itv_bndbnd_setU _ _ _ (BLeft x))//=; last 2 first.
      by case: a ax F {intf} => [[|] a|[|]]// /ltW.
      by rewrite bnd_simp lerDl ltW.
    rewrite integral_setU_EFin//=.
    - rewrite addeAC -[X in _ - X]integral_itv_bndo_bndc//=; last first.
        by case: locf => + _ _; exact: measurable_funS.
      rewrite subee ?add0e//.
      apply: integral_fune_fin_num => //=.
      apply: integrableS (intf x) => //=.
      (* TODO: lemma *)
      move=> z/=.
      by rewrite !in_itv/= => /andP[-> /ltW].
    - by case: locf => + _ _; exact: measurable_funS.
    - apply/disj_setPRL => z/=.
      rewrite /E /= !in_itv/= => /andP[xz zxdn].
      move: a ax {F intf} => [[|] t/=|[_ /=|//]].
      - rewrite lte_fin => tx.
        by apply/negP; rewrite negb_and -leNgt xz orbT.
      - rewrite lte_fin => tx.
        by apply/negP; rewrite negb_and -!leNgt xz orbT.
      - by apply/negP; rewrite -leNgt.
  rewrite [f in f n @[n --> _] --> _](_ : _ =
      fun n => (d n)^-1 *: fine (\int[mu]_(t in E x n) (f t)%:E)); last first.
    apply/funext => n; congr (_ *: _); rewrite -fineB/=.
    by rewrite /= (addrC (d n) x) ixdf.
    by apply: integral_fune_fin_num => //=.
    by apply: integral_fune_fin_num => //=.
  have := nice_lebesgue_differentiation nice_E locf fx.
  rewrite {ixdf} -/mu.
  rewrite [g in g n @[n --> _] --> _ -> _](_ : _ =
      fun n => (d n)^-1%:E * \int[mu]_(y in E x n) (f y)%:E); last first.
    by apply/funext => n; rewrite muE.
  move/fine_cvgP => [_ /=].
  set g := _ \o _ => gf.
  set h := (f in f n @[n --> \oo] --> _).
  suff : g = h by move=> <-.
  apply/funext => n.
  rewrite /g /h /= fineM//.
  apply: integral_fune_fin_num => //; first exact: (nice_E _).1.
  apply: integrableS (intf (x + d n)) => //.
  exact: (nice_E _).1.
  rewrite /E.
  (* TODO: lemma *)
  move=> z/=.
  rewrite !in_itv/= => /andP[xz /ltW ->].
  rewrite andbT.
  have := lt_le_trans ax.
  move=> /(_ (BLeft z) xz).
  rewrite /=.
  destruct a => //=; destruct b => //=.
  by rewrite lte_fin => /ltW.
- apply/cvg_at_leftP => d [d_gt0 d0].
  have {}Nd_gt0 n : (0 < - d n)%R by rewrite ltrNr oppr0.
  pose E x n := `]x + d n, x]%classic%R.
  have muE y n : mu (E y n) = (- d n)%:E.
    rewrite /E lebesgue_measure_itv/= lte_fin -ltrBrDr.
    by rewrite ltrDl Nd_gt0 -EFinD opprD addrA subrr add0r.
  have nice_E y : nicely_shrinking y (E y).
    split=> [n|]; first exact: measurable_itv.
    exists (2, (fun n => PosNum (Nd_gt0 n))); split => //=.
      by rewrite -oppr0; exact: cvgN.
    move=> n z.
      rewrite /E/= in_itv/= /ball/= => /andP[yz zy].
      by rewrite ltr_distlC opprK yz /= (le_lt_trans zy)// ltrDl.
    move=> n.
    rewrite lebesgue_measure_ball//; last exact: ltW.
    by rewrite -/mu muE -EFinM lee_fin mulr_natl.
  have ixdf : {near \oo,
      (fun n => \int[mu]_(t in [set` Interval a (BRight (x + d n))]) (f t)%:E -
                \int[mu]_(t in [set` Interval a (BRight x)]) (f t)%:E) =1
      (fun n => - \int[mu]_(y in E x n) (f y)%:E)}.
    case: a ax intf {F}; last first.
      move=> [_ intf|//].
      apply: nearW => n.
      rewrite -[in LHS]integral_itv_bndo_bndc//=; last first.
        by case: locf => + _ _; exact: measurable_funS.
      rewrite -/mu -[LHS]oppeK; congr oppe.
      rewrite oppeB; last first.
        rewrite fin_num_adde_defl// fin_numN//.
        by apply: integral_fune_fin_num => //; exact: integrableS intf.
      rewrite addeC.
      rewrite (_ : `]-oo, x] = `]-oo, (x + d n)%R] `|` E x n)%classic; last first.
        by rewrite -itv_bndbnd_setU//= bnd_simp ler_wnDr// ltW.
      rewrite integral_setU_EFin//=.
      - rewrite addeAC.
        rewrite -[X in X - _]integral_itv_bndo_bndc//; last first.
          by case: locf => + _ _; exact: measurable_funS.
        rewrite subee ?add0e//.
        apply: integral_fune_fin_num => //=.
        apply: integrableS (intf (x + d n)) => //=.
        (* TODO: lemma *)
        by move=> z/=; rewrite !in_itv/= => /ltW.
      - exact: (nice_E _).1.
      - by case: locf => + _ _; exact: measurable_funS.
      - apply/disj_setPLR => z/=.
        rewrite /E /= !in_itv/= leNgt => xdnz.
        by apply/negP; rewrite negb_and xdnz.
    move=> b a ax intf.
    move/cvgrPdist_le : d0.
    move/(_ (x - a)%R); rewrite subr_gt0 => /(_ ax)[m _ /=] h.
    near=> n.
    have mn : (m <= n)%N by near: n; exists m.
    rewrite -[in X in X - _]integral_itv_bndo_bndc//=; last first.
      by case: locf => + _ _; exact: measurable_funS.
    rewrite -/mu -[LHS]oppeK; congr oppe.
    rewrite oppeB; last first.
      rewrite fin_num_adde_defl// fin_numN//.
      by apply: integral_fune_fin_num => //; exact: integrableS intf.
    rewrite addeC.
    rewrite (@itv_bndbnd_setU _ _ _ (BRight (x - - d n)%R))//; last 2 first.
      case: b in ax intf * => /=; rewrite bnd_simp.
        rewrite lerBrDl addrC -lerBrDl.
        by have := h _ mn; rewrite sub0r gtr0_norm.
      rewrite lerBrDl -lerBrDr.
      by have := h _ mn; rewrite sub0r gtr0_norm.
      by rewrite opprK bnd_simp -lerBrDl subrr ltW.
    rewrite integral_setU_EFin//=.
    - rewrite addeAC -[X in X - _]integral_itv_bndo_bndc//; last first.
        by case: locf => + _ _; exact: measurable_funS.
      rewrite opprK subee ?add0e//.
      apply: integral_fune_fin_num => //=.
      apply: integrableS (intf (x + d n)) => //.
      (* TODO: lemma *)
      move=> z/=.
      by rewrite !in_itv/= => /andP[->/= /ltW].
    - by case: locf => + _ _; exact: measurable_funS.
    - apply/disj_setPLR => z/=.
      rewrite /E /= !in_itv/= => /andP[az zxdn].
      by apply/negP; rewrite negb_and -leNgt zxdn.
  suff: ((d n)^-1 * - fine (\int[mu]_(y in E x n) (f y)%:E))%R
          @[n --> \oo] --> f x.
    apply: cvg_trans; apply: near_eq_cvg; near=> n;  congr (_ *: _).
    rewrite /F -fineN -fineB; last 2 first.
      by apply: integral_fune_fin_num => //; exact: integrableS intf.
      by apply: integral_fune_fin_num => //; exact: integrableS intf.
    by congr fine => /=; apply/esym; rewrite (addrC _ x); near: n.
  have := nice_lebesgue_differentiation nice_E locf fx.
  rewrite {ixdf} -/mu.
  move/fine_cvgP => [_ /=].
  set g := _ \o _ => gf.
  apply: cvg_trans gf.
  move: a ax intf {F} => [[t/=|t/=]|[|//]]; rewrite ?lte_fin => tx intf.
    move/cvgrPdist_le : d0 => /= /(_ (x - t)%R).
    rewrite subr_gt0 => /(_ tx)[k /= _] H.
    apply: near_eq_cvg; near=> n.
    rewrite /g /= fineM//=; last first.
      apply: integral_fune_fin_num => //; first exact: (nice_E _).1.
      rewrite /=.
      apply: integrableS (intf x)%R => //=.
        exact: (nice_E _).1.
      rewrite /E => y/=.
      rewrite !in_itv/= => /andP[xdny yx]; apply/andP; split => //.
      rewrite (le_trans _ (ltW xdny))//.
      rewrite -lerBlDl.
      rewrite -(opprK (_ - _)%R).
      rewrite lerNl opprB.
      have /= := H n.
      rewrite gtr0_norm ?sub0r//.
      apply.
      near: n.
      by exists k.
    by rewrite muE/= invrN mulNr -mulrN.
    move/cvgrPdist_le : d0 => /= /(_ (x - t)%R).
    rewrite subr_gt0 => /(_ tx)[k /= _] H.
    apply: near_eq_cvg; near=> n.
    rewrite /g /= fineM//=; last first.
      apply: integral_fune_fin_num => //; first exact: (nice_E _).1.
      rewrite /=.
      apply: integrableS (intf x)%R => //=.
        exact: (nice_E _).1.
      rewrite /E => y/=.
      rewrite !in_itv/= => /andP[xdny yx]; apply/andP; split => //.
      rewrite (le_lt_trans _ xdny)//.
      rewrite -lerBlDl.
      rewrite -(opprK (_ - _)%R).
      rewrite lerNl opprB.
      have /= := H n.
      rewrite gtr0_norm ?sub0r//.
      apply.
      near: n.
      by exists k.
    by rewrite muE/= invrN mulNr -mulrN.
  rewrite (@eq_cvg _ _ _ _ g)// => n.
  rewrite /g /= fineM//=; last first.
   apply: integral_fune_fin_num => //; first exact: (nice_E _).1.
   rewrite /=.
   apply: integrableS (intf x)%R => //=.
   exact: (nice_E _).1.
   by move=> z/=; rewrite /E/= !in_itv/= => /andP[].
  rewrite muE/=.
  rewrite invrN.
  rewrite mulNr.
  by rewrite mulrN.
Unshelve. all: by end_near. Qed.

(* NB: right-closed interval *)
Lemma FTC1_lebesgue_pt f a x : (forall y, mu.-integrable [set` Interval a (BRight y)] (EFin \o f)) ->
    locally_integrable [set: R] f(*mu.-integrable setT (EFin \o f)*) ->
  let F y := (\int[mu]_(t in [set` Interval a (BRight y)]) (f t))%R in
  a < BRight x -> lebesgue_pt f x ->
  derivable F x 1 /\ F^`() x = f x.
Proof.
move=> intf locf F ax fx; split; last first.
  apply/cvg_lim; [exact: Rhausdorff|].
  by apply: FTC0 => //=.
apply/cvg_ex; exists (f x).
have /= := FTC0 intf locf ax fx.
set g := (f in f n @[n --> _] --> _ -> _).
set h := (f in _ -> f n @[n --> _] --> _).
suff : g = h by move=> <-.
by apply/funext => y;rewrite /g /h /= [X in F (X + _)]mulr1.
Qed.

Corollary FTC1 f a : (forall y, mu.-integrable [set` Interval a (BRight y)] (EFin \o f)) ->
    locally_integrable [set: R] f(*mu.-integrable setT (EFin \o f) ->*) ->
  let F x := (\int[mu]_(t in [set` Interval a (BRight x)]) (f t))%R in
  {ae mu, forall x, a < BRight x -> derivable F x 1 /\ F^`() x = f x}.
Proof.
move=> intf locf F.
move: (locf).
move/lebesgue_differentiation.
apply: filterS; first exact: (ae_filter_ringOfSetsType mu).
by move=> i fi ai; apply: FTC1_lebesgue_pt => //; rewrite ltNyr.
Qed.

Corollary FTC1Ny f : (forall y, mu.-integrable [set` Interval -oo%O (BRight y)] (EFin \o f)) ->
    locally_integrable [set: R] f(*mu.-integrable setT (EFin \o f) ->*) ->
  let F x := (\int[mu]_(t in [set` `]-oo, x]]) (f t))%R in
  {ae mu, forall x, derivable F x 1 /\ F^`() x = f x}.
Proof.
move=> intf locf F; have := FTC1 intf locf.
apply: filterS; first exact: (ae_filter_ringOfSetsType mu).
by move=> r /=; apply; rewrite ltNyr.
Qed.

Lemma tmp (x : R) : \forall x0 \near nbhs 0^'+, (0 < x)%R -> (x0 <= x)%R.
Proof.
have [x0|x0] := leP x 0%R.
  by exists 1%R => //=.
exists x => //= z /=.
rewrite sub0r normrN => /[swap] z0.
by rewrite gtr0_norm// => /ltW.
Qed.

Corollary continuous_FTC1 f a x :  (forall y, mu.-integrable [set` Interval a (BRight y)] (EFin \o f)) ->
    locally_integrable [set: R] f(*mu.-integrable setT (EFin \o f) ->*) ->
  let F x := (\int[mu]_(t in [set` Interval a (BRight x)]) (f t))%R in
  a < BRight x -> {for x, continuous f} ->
  derivable F x 1 /\ F^`() x = f x.
Proof.
move=> fi locf F ax fx.
have lfx : lebesgue_pt f x.
destruct a; destruct b => //.
- near (0%R:R)^'+ => e; apply: (@continuous_lebesgue_pt _ _ _ (ball x e)).
  - exact: ball_open_nbhs.
  - exact: measurable_ball.
  - have /measurable_int/EFin_measurable_fun := fi (x + e)%R.
    apply: measurable_funS => //= z.
    rewrite ball_itv/=.
    rewrite !in_itv/= => /andP[xez zxe].
    rewrite (ltW zxe) andbT.
    move: ax => /=; rewrite lte_fin => sx.
    rewrite (le_trans _ (ltW xez))//.
    rewrite -lerBlDl.
    rewrite lerNr opprB.
    move: sx.
    rewrite -subr_gt0.
    near: e.
    by apply: tmp.
  - exact: fx.
- near (0%R:R)^'+ => e; apply: (@continuous_lebesgue_pt _ _ _ (ball x e)).
  - exact: ball_open_nbhs.
  - exact: measurable_ball.
  - have := fi (x + e)%R.
    move/measurable_int.
    move/EFin_measurable_fun.
    apply: measurable_funS => //.
    rewrite ball_itv => z.
    rewrite /= !in_itv/=.
    rewrite /ball/= => /andP[xez zxe].
    rewrite (ltW zxe) andbT.
    move: ax.
    rewrite /= lte_fin => sx.
    rewrite (le_lt_trans _ xez)//.
    rewrite -lerBlDl lerNr opprB.
    move: sx.
    rewrite -subr_gt0.
    near: e.
    exact: tmp.
  - exact: fx.
- near (0%R:R)^'+ => e; apply: (@continuous_lebesgue_pt _ _ _ (ball x e)).
  - exact: ball_open_nbhs.
  - exact: measurable_ball.
  - have := fi (x + e)%R.
    move/measurable_int.
    move/EFin_measurable_fun.
    apply: measurable_funS => //.
    rewrite ball_itv => z.
    rewrite /= !in_itv/=.
    rewrite /ball/= => /andP[xez zxe].
    exact/ltW.
  - exact: fx.
have /= /(_ ax lfx)/= [dfx f'xE] := @FTC1_lebesgue_pt f a x fi locf.
by split; [exact: dfx|rewrite f'xE].
Unshelve. all: by end_near. Qed.

End FTC.

Definition parameterized_integral {R : realType}
    (mu : {measure set (g_sigma_algebraType (R.-ocitv.-measurable)) -> \bar R})
    a x (f : R -> R) : R :=
  (\int[mu]_(t in `[a, x]) f t)%R.

Section parameterized_integral_continuous.
Context {R : realType}.
Notation mu := (@lebesgue_measure R).

Let int := (parameterized_integral mu).

Lemma parameterized_integral_near_left (a b : R) (e : R) (f : R -> R) :
  a < b -> 0 < e -> mu.-integrable `[a, b] (EFin \o f) ->
  \forall c \near a, a <= c -> `| int a c f | < e.
Proof.
move=> ab e0 intf.
have : mu.-integrable setT (EFin \o f \_ `[a, b]).
  by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setTI.
move=> /integral_normr_continuous /(_ _ e0)[d [d0 /=]] ifab.
near=> c => ac.
have /ifab : (mu `[a, c] < d%:E)%E.
  rewrite lebesgue_measure_itv/= lte_fin.
  case: ifPn => // {}ac; rewrite -EFinD lte_fin.
  by move: ac; near: c; exact: nbhs_right_ltDr.
move=> /(_ (measurable_itv _)) {ifab}.
apply: le_lt_trans.
have acbc : `[a, c] `<=` `[a, b].
  by apply: subset_itvl; rewrite bnd_simp; move: ac; near: c; exact: nbhs_le.
rewrite -lee_fin fineK; last first.
  apply: integral_fune_fin_num => //=.
  rewrite (_ : (fun _ => _) = abse \o ((EFin \o f) \_ `[a, b])); last first.
    by apply/funext => x /=; rewrite restrict_EFin.
  apply/integrable_abse/integrable_restrict => //=.
  by rewrite setIidl//; exact: integrableS intf.
rewrite [leRHS]integralEpatch//= [in leRHS]integralEpatch//=.
under [in leRHS]eq_integral.
  move=> /= x xac.
  rewrite -patch_setI setIid restrict_EFin/= restrict_normr/=.
  rewrite -patch_setI setIidl//.
  over.
rewrite /= [leRHS](_ : _ = \int[mu]_(x in `[a, c]) `| f x |%:E)%E; last first.
  rewrite [RHS]integralEpatch//=; apply: eq_integral => x xac/=.
  by rewrite restrict_EFin/= restrict_normr.
rewrite /int /parameterized_integral /=.
apply: (@le_trans _ _ ((\int[mu]_(t in `[a, c]) `|f t|))%:E).
  by apply: le_normr_integral => //; exact: integrableS intf.
set rhs : \bar R := leRHS.
have [->|rhsoo] := eqVneq rhs +oo%E; first by rewrite leey.
rewrite /rhs /Rintegral -/rhs.
rewrite fineK// fin_numE rhsoo andbT -ltNye (@lt_le_trans _ _ 0%E)//.
exact: integral_ge0.
Unshelve. all: by end_near. Qed.

Lemma parameterized_integral_cvg_left a b (f : R -> R) : a < b ->
  mu.-integrable `[a, b] (EFin \o f) ->
  int a x f @[x --> a] --> 0.
Proof.
move=> ab intf; pose fab := f \_ `[a, b].
have intfab : mu.-integrable `[a, b] (EFin \o fab).
  by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setIidr.
apply/cvgrPdist_le => /= e e0; rewrite near_simpl; near=> x.
rewrite {1}/int /parameterized_integral sub0r normrN.
have [|xa] := leP a x.
  move=> ax; apply/ltW; move: ax.
  by near: x; exact: (@parameterized_integral_near_left _ b).
by rewrite set_itv_ge ?Rintegral_set0 ?normr0 ?(ltW e0)// -leNgt bnd_simp.
Unshelve. all: by end_near. Qed.

Lemma parameterized_integral_cvg_at_left a b (f : R -> R) : a < b ->
  mu.-integrable `[a, b] (EFin \o f) ->
  int a x f @[x --> b^'-] --> int a b f.
Proof.
move=> ab intf; pose fab := f \_ `[a, b].
have /= int_normr_cont : forall e : R, 0 < e ->
    exists d : R, 0 < d /\
    forall A, measurable A -> (mu A < d%:E)%E -> \int[mu]_(x in A) `|fab x| < e.
  rewrite /= => e e0; apply: integral_normr_continuous => //=.
  by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setTI.
have intfab : mu.-integrable `[a, b] (EFin \o fab).
  by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setIidr.
rewrite /int /parameterized_integral; apply/cvgrPdist_le => /= e e0.
have [d [d0 /= {}int_normr_cont]] := int_normr_cont _ e0.
near=> x.
rewrite [in X in X - _](@itv_bndbnd_setU _ _ _ (BRight x))//;
  [|by rewrite bnd_simp ltW..].
rewrite Rintegral_setU_EFin//=; last 2 first.
  rewrite -itv_bndbnd_setU// ?bnd_simp; last 2 first.
    by near: x; exact: nbhs_left_ge.
    exact/ltW.
  apply/disj_set2P; rewrite -subset0 => z/=; rewrite !in_itv/= => -[/andP[_]].
  by rewrite leNgt => /negbTE ->.
have xbab : `]x, b] `<=` `[a, b].
  by apply: subset_itvr; rewrite bnd_simp; near: x; exact: nbhs_left_ge.
rewrite -addrAC subrr add0r (le_trans (le_normr_integral _ _))//.
  exact: integrableS intf.
rewrite [leLHS](_ : _ = (\int[mu]_(t in `]x, b]) normr (fab t)))//; last first.
  apply: eq_Rintegral => //= z; rewrite inE/= in_itv/= => /andP[xz zb].
  rewrite /fab patchE ifT// inE/= in_itv/= zb andbT (le_trans _ (ltW xz))//.
  by near: x; exact: nbhs_left_ge.
apply/ltW/int_normr_cont => //.
rewrite lebesgue_measure_itv/= lte_fin.
rewrite ifT// -EFinD lte_fin.
near: x; exists d => // z; rewrite /ball_/= => + zb.
by rewrite gtr0_norm// ?subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma parameterized_integral_continuous a b (f : R -> R) : a < b ->
  mu.-integrable `[a, b] (EFin \o f) ->
  {within `[a, b], continuous (fun x => int a x f)}.
Proof.
move=> ab intf; apply/(continuous_within_itvP _ ab); split; last first.
  split; last exact: parameterized_integral_cvg_at_left.
  apply/cvg_at_right_filter.
  rewrite {2}/int /parameterized_integral interval_set1 Rintegral_set1.
  exact: (parameterized_integral_cvg_left ab).
pose fab := f \_ `[a, b].
have /= int_normr_cont : forall e : R, 0 < e ->
    exists d : R, 0 < d /\
    forall A, measurable A -> (mu A < d%:E)%E -> \int[mu]_(x in A) `|fab x| < e.
  rewrite /= => e e0; apply: integral_normr_continuous => //=.
  by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setTI.
have intfab : mu.-integrable `[a, b] (EFin \o fab).
  by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setIidr.
rewrite /int /parameterized_integral => z; rewrite in_itv/= => /andP[az zb].
apply/cvgrPdist_le => /= e e0.
rewrite near_simpl.
have [d [d0 /= {}int_normr_cont]] := int_normr_cont _ e0.
near=> x.
have [xz|xz|->] := ltgtP x z; last by rewrite subrr normr0 ltW.
- have ax : a < x.
    move: xz; near: x.
    exists `|z - a| => /=; first by rewrite gtr0_norm ?subr_gt0.
    move=> y /= + yz.
    do 2 rewrite gtr0_norm ?subr_gt0//.
    rewrite ltrBlDr -ltrBlDl; apply: le_lt_trans.
    by rewrite opprB addrCA subrr addr0.
  rewrite Rintegral_itvB//; last 3 first.
    by apply: integrableS intf => //; apply: subset_itvl; exact: ltW.
    by rewrite bnd_simp ltW.
    exact: ltW.
  have xzab : `]x, z] `<=` `[a, b].
    by apply: subset_itvS; rewrite bnd_simp; exact/ltW.
  apply: (le_trans (le_normr_integral _ _)) => //; first exact: integrableS intf.
  rewrite -(setIidl xzab) Rintegral_mkcondr/=.
  under eq_Rintegral do rewrite restrict_normr.
  apply/ltW/int_normr_cont => //.
  rewrite lebesgue_measure_itv/= lte_fin xz -EFinD lte_fin ltrBlDl.
  move: xz; near: x.
  exists (d / 2); first by rewrite /= divr_gt0.
  move=> x/= /[swap] xz.
  rewrite gtr0_norm ?subr_gt0// ltrBlDl => /lt_le_trans; apply.
  by rewrite lerD2l ler_pdivrMr// ler_pMr// ler1n.
+ have ax : a < x by rewrite (lt_trans az).
  have xb : x < b.
    move: xz; near: x.
    exists `|b - z|; first by rewrite /= gtr0_norm ?subr_gt0.
    move=> y /= + yz.
    by rewrite ltr0_norm ?subr_lt0// gtr0_norm ?subr_gt0// opprB ltrBlDr subrK.
  rewrite -opprB normrN Rintegral_itvB ?bnd_simp; last 3 first.
    by apply: integrableS intf => //; apply: subset_itvl; exact: ltW.
    exact/ltW.
    exact/ltW.
  rewrite Rintegral_itv_obnd_cbnd//; last first.
    by apply: integrableS intf => //; apply: subset_itvS => //; exact/ltW.
  have zxab : `[z, x] `<=` `[a, b].
    by apply: subset_itvS; rewrite bnd_simp; exact/ltW.
  apply: (le_trans (le_normr_integral _ _)) => //; first exact: integrableS intf.
  rewrite -(setIidl zxab) Rintegral_mkcondr/=.
  under eq_Rintegral do rewrite restrict_normr.
  apply/ltW/int_normr_cont => //.
  rewrite lebesgue_measure_itv/= lte_fin xz -EFinD lte_fin ltrBlDl.
  move: xz; near: x.
  exists (d / 2); first by rewrite /= divr_gt0.
  move=> x/= /[swap] xz.
  rewrite ltr0_norm ?subr_lt0// opprB ltrBlDl => /lt_le_trans; apply.
  by rewrite lerD2l ler_pdivrMr// ler_pMr// ler1n.
Unshelve. all: by end_near. Qed.

End parameterized_integral_continuous.

Section corollary_FTC1.
Context {R : realType}.
Notation mu := lebesgue_measure.
Local Open Scope ereal_scope.
Implicit Types (f : R -> R) (a b : R).

Corollary within_continuous_FTC2 f F a b : (a < b)%R -> {within `[a, b], continuous f} ->
  derivable_oo_continuous_bnd F a b ->
  {in `]a, b[, F^`() =1 f} ->
  (\int[mu]_(x in `[a, b]) (f x)%:E = (F b)%:E - (F a)%:E)%E.
Proof.
move=> ab cf dF F'f.
pose fab := f \_ `[a, b].
pose G x : R := (\int[mu]_(t in `[a, x]) fab t)%R.
have iabf : mu.-integrable `[a, b] (EFin \o f).
  apply: continuous_compact_integrable; first exact: segment_compact.
  done.
have ifab : forall y : R, mu.-integrable `[a, y] (EFin \o fab).
  move=> y.
  rewrite -restrict_EFin; apply/integrable_restrict => //=.
  apply: integrableS iabf => //.
  exact: measurableI.
(*have ifab : mu.-integrable setT (EFin \o fab).
  by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setTI.*)
have locfab : locally_integrable [set: R] fab.
  split.
    move: iabf.
    move/(integrable_mkcond _ _).1 => /=.
    move=> /(_ (measurable_itv _)) /integrableP[+ _].
    by rewrite restrict_EFin => /EFin_measurable_fun.
   exact: openT.
  move=> K _ cK.
  under eq_integral.
    move=> x xK.
    rewrite /fab.
    rewrite -[_%:E]/((EFin \o (normr \o f \_ `[a, b])) x).
    rewrite -restrict_normr.
    rewrite -restrict_EFin.
    over.
  rewrite /=.
  rewrite -integral_mkcondr/=.
  move/integrableP : iabf => -[mabf].
  apply: le_lt_trans.
  apply: ge0_subset_integral => //=.
    apply: measurableI => //.
    by apply: compact_measurable.
  apply/EFin_measurable_fun => //=.
  apply/measurableT_comp => //.
  by apply/EFin_measurable_fun => //=.
have G'f : {in `]a, b[, forall x, G^`() x = fab x /\ derivable G x 1}.
  move=> x /[!in_itv]/= /andP[ax xb].
  have := @continuous_FTC1 _ _ (BLeft a) x ifab locfab.
  rewrite /= lte_fin => /(_ ax).
  have : {for x, continuous fab}.
    have : x \in `[a, b] by rewrite in_itv/= (ltW ax) (ltW xb).
    move: cf.
    move/(_ x).
    rewrite {1}/continuous_at => xf xab.

    rewrite /prop_for /continuous_at {2}/fab/= patchE.
    rewrite mem_set ?mulr1 /=; last by rewrite in_itv/= (ltW ax) (ltW xb).


    apply/cvgrPdist_lt => /= e e0.
    move/cvgrPdist_lt : xf => /(_ e e0) H.
    rewrite near_simpl; near=> z.
    rewrite /fab patchE ifT//; last first.
      rewrite inE.
      apply: subset_itv_oo_cc.
      near: z.
      apply: near_in_itv.
      by rewrite in_itv/= ax xb.
    near: z.
    red in H.
    red in H.
    simpl in H.
    red in H.
    simpl in H.
    red in H.
    rewrite ifT// in H; last first.
      by rewrite inE.
    red in H.
    simpl in H.
    red in H.
    red in H.
    simpl in H.
    red in H.
    simpl in H.
    red in H.
case: H => x0 /= x00 H.
near=> z.
apply: H => //=.
      rewrite inE.
      apply: subset_itv_oo_cc.
      near: z.
      apply: near_in_itv.
      by rewrite in_itv/= ax xb.
  by move=> /[swap] /[apply] -[].
have F'G'0 : {in `]a, b[, (F^`() - G^`() =1 cst 0)%R}.
  move=> x xab; rewrite !fctE (G'f x xab).1 /fab.
  by rewrite patchE mem_set/= ?F'f ?subrr//; exact: subset_itv_oo_cc.
have [k FGk] : exists k : R, {in `]a, b[, (F - G =1 cst k)%R}.
  have : {in `]a, b[ &, forall x y, (F x - G x = F y - G y)%R}.
    move=> x y xab yab.
    wlog xLy : x y xab yab / (x <= y)%R.
      move=> abFG; have [|/ltW] := leP x y; first exact: abFG.
      by move/abFG => /(_ yab xab).
    move: xLy; rewrite le_eqVlt => /predU1P[->//|xy].
    have [| |] := @MVT _ (F \- G)%R (F^`() - G^`())%R x y xy.
    - move=> z zxy; have zab : z \in `]a, b[.
        move: z zxy; apply: subset_itvW => //.
        + by move: xab; rewrite in_itv/= => /andP[/ltW].
        + by move: yab; rewrite in_itv/= => /andP[_ /ltW].
      have Fz1 : derivable F z 1.
        by case: dF => /= + _ _; apply; rewrite inE in zab.
      have Gz1 : derivable G z 1 by have [|] := G'f z.
      apply: DeriveDef.
      + by apply: derivableB; [exact: Fz1|exact: Gz1].
      + by rewrite deriveB -?derive1E; [by []|exact: Fz1|exact: Gz1].
    - apply: derivable_within_continuous => z zxy.
      apply: derivableB.
      + case: dF => /= + _ _; apply.
        rewrite in_itv/=; move: zxy; rewrite in_itv/= => /andP[xz zy].
        rewrite (lt_le_trans _ xz)/= ?(le_lt_trans zy)//=.
        * by move: yab; rewrite in_itv/= => /andP[].
        * by move: xab; rewrite in_itv/= => /andP[].
      + apply: (G'f _ _).2; rewrite in_itv/=; apply/andP; split.
        * move: zxy; rewrite in_itv/= => /andP[+ _]; apply: lt_le_trans.
          by move: xab; rewrite in_itv/= => /andP[].
        * move: zxy; rewrite in_itv/= => /andP[_]; move=> /le_lt_trans; apply.
          by move: yab; rewrite in_itv/= => /andP[].
    - move=> z zxy; rewrite F'G'0.
        by rewrite /cst/= mul0r => /eqP; rewrite subr_eq0 => /eqP.
      rewrite !in_itv/=; move: zxy; rewrite in_itv/= => /andP[xz zy].
      rewrite (le_lt_trans _ xz)//= ?(lt_le_trans zy)//=.
      * by move: yab; rewrite in_itv/= => /andP[_ /ltW].
      * by move: xab; rewrite in_itv/= => /andP[/ltW].
  move=> H; pose c := (a + b) / 2.
  exists (F c - G c)%R => u /(H u c); apply.
  by rewrite in_itv/= midf_lt//= midf_lt.
have [c GFc] : exists c : R, forall x, x \in `]a, b[ -> (F x - G x)%R = c.
  by exists k => x xab; rewrite -[k]/(cst k x) -(FGk x xab).
have Ga0 : G a = 0%R by rewrite /G interval_set1// Rintegral_set1.
case: (dF) => _ Fa Fb.
have GacFa : G x @[x --> a^'+] --> (- c + F a)%R.
  have Fap : Filter a^'+ by exact: at_right_proper_filter.
  have GFac : (G x - F x)%R @[x --> a^'+] --> (- c)%R.
    apply/cvgrPdist_le => /= e e0; near=> t.
    rewrite opprB GFc; last by rewrite in_itv/=; apply/andP.
    by rewrite addrC subrr normr0 ltW.
  have := @cvgD _ _ _ _ Fap _ _ _ _ GFac Fa.
  rewrite (_ : (G \- F)%R + F = G)//.
  by apply/funext => x/=; rewrite subrK.
have GbcFb : G x @[x --> b^'-] --> (- c + F b)%R.
  have Fbn : Filter b^'- by exact: at_left_proper_filter.
  have GFbc : (G x - F x)%R @[x --> b^'-] --> (- c)%R.
    apply/cvgrPdist_le => /= e e0; near=> t.
    rewrite opprB GFc; last by rewrite in_itv/=; apply/andP.
    by rewrite addrC subrr normr0 ltW.
  have := @cvgD _ _ _ _ Fbn _ _ _ _ GFbc Fb.
  rewrite (_ : (G \- F)%R + F = G)//.
  by apply/funext => x/=; rewrite subrK.
have contF : {within `[a, b], continuous F}.
  apply/(continuous_within_itvP _ ab); split; last exact: (conj Fa Fb).
  move=> z zab.
  apply/differentiable_continuous/derivable1_diffP.
  by case: dF => /= dF _ _; apply: dF.
have iabfab : mu.-integrable `[a, b] (EFin \o fab).
  by rewrite -restrict_EFin; apply/integrable_restrict => //; rewrite setIidr.
have Ga : G x @[x --> a^'+] --> G a.
   have := parameterized_integral_cvg_left ab iabfab.
   rewrite (_ : 0 = G a)%R.
     by move=> /left_right_continuousP[].
   by rewrite /G interval_set1 Rintegral_set1.
have Gb : G x @[x --> b^'-] --> G b.
  exact: (parameterized_integral_cvg_at_left ab iabfab).
have cE : c = F a.
  apply/eqP; rewrite -(opprK c) eq_sym -addr_eq0 addrC.
  by have := cvg_unique _ GacFa Ga; rewrite Ga0 => ->.
have GbFbc : G b = (F b - c)%R.
  by have := cvg_unique _ GbcFb Gb; rewrite addrC => ->.
rewrite -EFinB -cE -GbFbc /G /Rintegral/= fineK//.
  rewrite integralEpatch//=.
  by under eq_integral do rewrite restrict_EFin.
exact: integral_fune_fin_num.
Unshelve. all: by end_near. Qed.

Corollary continuous_FTC2 f F a b : (a < b)%R -> {in `[a, b], continuous f} ->
  derivable_oo_continuous_bnd F a b ->
  {in `]a, b[, F^`() =1 f} ->
  (\int[mu]_(x in `[a, b]) (f x)%:E = (F b)%:E - (F a)%:E)%E.
Proof.
move=> ab cf dF F'f.
apply: within_continuous_FTC2 => //.
exact/continuous_subspace_itv.
Qed.

End corollary_FTC1.
