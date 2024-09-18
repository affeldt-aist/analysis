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

(* TODO: move to normedtype.v? *)
Lemma nbhs_right_lt_lt {R : realType} (x y : R) :
  (y < x)%R -> \forall z \near nbhs y^'+, (z < x)%R.
Proof.
move=> yx.
exists (x - y)%R => /=; first by rewrite subr_gt0.
move=> z/= /[swap] yz.
by rewrite ltr0_norm ?subr_lt0// opprB ltrBlDl addrC subrK.
Qed.

(* TODO: move to normedtype.v? *)
Lemma nbhs_right_lt_le {R : realType} (x y : R) :
  (y < x)%R -> \forall z \near nbhs y^'+, (z <= x)%R.
Proof.
by move=> yx; near=> z; apply/ltW; near: z; exact: nbhs_right_lt_lt.
Unshelve. all: by end_near. Qed.

(* TODO: move to normedtype.v? *)
Lemma cvg_patch {R : realType} (f : R -> R^o) (a b : R) (x : R) : (a < b)%R ->
  x \in `]a, b[ ->
  f @ (x : subspace `[a, b]) --> f x ->
  (f \_ `[a, b] x) @[x --> x] --> f x.
Proof.
move=> ab xab xf; apply/cvgrPdist_lt => /= e e0.
move/cvgrPdist_lt : xf => /(_ e e0) xf.
rewrite near_simpl; near=> z.
rewrite patchE ifT//; last first.
  rewrite inE; apply: subset_itv_oo_cc.
  by near: z; exact: near_in_itv.
near: z.
rewrite /prop_near1 /nbhs/= /nbhs_subspace ifT// in xf; last first.
  by rewrite inE/=; exact: subset_itv_oo_cc xab.
case: xf => x0 /= x00 xf.
near=> z.
apply: xf => //=.
rewrite inE; apply: subset_itv_oo_cc.
by near: z; exact: near_in_itv.
Unshelve. all: by end_near. Qed.

Section FTC.
Context {R : realType}.
Notation mu := (@lebesgue_measure R).
Local Open Scope ereal_scope.
Implicit Types (f : R -> R) (a : itv_bound R).

Let integrable_locally f (A : set R) : measurable A ->
  mu.-integrable A (EFin \o f) -> locally_integrable [set: R] (f \_ A).
Proof.
move=> mA intf; split.
- move/integrableP : intf => [mf _].
  by apply/(measurable_restrictT _ _).1 => //; exact/EFin_measurable_fun.
- exact: openT.
- move=> K _ cK.
  move/integrableP : intf => [mf].
  rewrite integral_mkcond/=.
  under eq_integral do rewrite restrict_EFin restrict_normr.
  apply: le_lt_trans.
  apply: ge0_subset_integral => //=; first exact: compact_measurable.
  apply/EFin_measurable_fun/measurableT_comp/EFin_measurable_fun => //=.
  move/(measurable_restrictT _ _).1 : mf => /=.
  by rewrite restrict_EFin; exact.
Qed.

Let FTC0 f a : mu.-integrable setT (EFin \o f) ->
  let F x := (\int[mu]_(t in [set` Interval a (BRight x)]) f t)%R in
  forall x, a < BRight x -> lebesgue_pt f x ->
    h^-1 *: (F (h + x) - F x) @[h --> 0%R^'] --> f x.
Proof.
move=> intf F x ax fx.
have locf : locally_integrable setT f.
  by apply: open_integrable_locally => //; exact: openT.
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
      by case: a ax F => [[|] a|[|]]// /ltW.
      by rewrite bnd_simp lerDl ltW.
    rewrite integral_setU_EFin//=.
    - rewrite addeAC -[X in _ - X]integral_itv_bndo_bndc//=; last first.
        by case: locf => + _ _; exact: measurable_funS.
      rewrite subee ?add0e//.
      by apply: integral_fune_fin_num => //; exact: integrableS intf.
    - by case: locf => + _ _; exact: measurable_funS.
    - apply/disj_setPRL => z/=.
      rewrite /E /= !in_itv/= => /andP[xz zxdn].
      move: a ax {F} => [[|] t/=|[_ /=|//]].
      - rewrite lte_fin => tx.
        by apply/negP; rewrite negb_and -leNgt xz orbT.
      - rewrite lte_fin => tx.
        by apply/negP; rewrite negb_and -!leNgt xz orbT.
      - by apply/negP; rewrite -leNgt.
  rewrite [f in f n @[n --> _] --> _](_ : _ =
      fun n => (d n)^-1 *: fine (\int[mu]_(t in E x n) (f t)%:E)); last first.
    apply/funext => n; congr (_ *: _); rewrite -fineB/=.
    by rewrite /= (addrC (d n) x) ixdf.
    by apply: integral_fune_fin_num => //; exact: integrableS intf.
    by apply: integral_fune_fin_num => //; exact: integrableS intf.
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
  by apply: integrableS intf => //; exact: (nice_E _).1.
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
    case: a ax {F}; last first.
      move=> [_|//].
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
        by apply: integral_fune_fin_num => //; exact: integrableS intf.
      - exact: (nice_E _).1.
      - by case: locf => + _ _; exact: measurable_funS.
      - apply/disj_setPLR => z/=.
        rewrite /E /= !in_itv/= leNgt => xdnz.
        by apply/negP; rewrite negb_and xdnz.
    move=> b a ax.
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
      case: b in ax * => /=; rewrite bnd_simp.
        rewrite lerBrDl addrC -lerBrDl.
        by have := h _ mn; rewrite sub0r gtr0_norm.
      rewrite lerBrDl -lerBrDr.
      by have := h _ mn; rewrite sub0r gtr0_norm.
      by rewrite opprK bnd_simp -lerBrDl subrr ltW.
    rewrite integral_setU_EFin//=.
    - rewrite addeAC -[X in X - _]integral_itv_bndo_bndc//; last first.
        by case: locf => + _ _; exact: measurable_funS.
      rewrite opprK subee ?add0e//.
      by apply: integral_fune_fin_num => //; exact: integrableS intf.
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
  rewrite (@eq_cvg _ _ _ _ g)// => n.
  rewrite /g /= fineM//=; last first.
    apply: integral_fune_fin_num => //; first exact: (nice_E _).1.
    by apply: integrableS intf => //; exact: (nice_E _).1.
  by rewrite muE/= invrN mulNr -mulrN.
Unshelve. all: by end_near. Qed.

Let FTC0_restrict f a x (u : R) : (x < u)%R ->
  mu.-integrable [set` Interval a (BRight u)] (EFin \o f) ->
  let F y := (\int[mu]_(t in [set` Interval a (BRight y)]) f t)%R in
  a < BRight x -> lebesgue_pt f x ->
  h^-1 *: (F (h + x) - F x) @[h --> 0%R^'] --> f x.
Proof.
move=> xu + F ax fx.
rewrite integrable_mkcond//= (restrict_EFin f) => intf.
have /(@FTC0 _ _ intf _ ax) : lebesgue_pt (f \_ [set` Interval a (BRight u)]) x.
  exact: lebesgue_pt_restrict.
rewrite patchE mem_set; last first.
  rewrite /= in_itv/= (ltW xu) andbT.
  by move: a ax {F intf} => [[a|]|[]]//=; rewrite lte_fin => /ltW.
apply: cvg_trans; apply: near_eq_cvg; near=> r; congr (_ *: (_ - _)).
- apply: eq_Rintegral => y yaxr; rewrite patchE mem_set//=.
  move: yaxr; rewrite /= !in_itv/= inE/= in_itv/= => /andP[->/=].
  move=> /le_trans; apply; rewrite -lerBrDr.
  have [r0|r0] := leP r 0%R; first by rewrite (le_trans r0)// subr_ge0 ltW.
  by rewrite -(gtr0_norm r0); near: r; apply: dnbhs0_le; rewrite subr_gt0.
- apply: eq_Rintegral => y yaxr; rewrite patchE mem_set//=.
  move: yaxr => /=; rewrite !in_itv/= inE/= in_itv/= => /andP[->/=].
  by move=> /le_trans; apply; exact/ltW.
Unshelve. all: by end_near. Qed.

(* NB: right-closed interval *)
Lemma FTC1_lebesgue_pt f a x (u : R) : (x < u)%R ->
  mu.-integrable [set` Interval a (BRight u)] (EFin \o f) ->
  let F y := (\int[mu]_(t in [set` Interval a (BRight y)]) (f t))%R in
  a < BRight x -> lebesgue_pt f x ->
  derivable F x 1 /\ F^`() x = f x.
Proof.
move=> xu intf F ax fx; split; last first.
  by apply/cvg_lim; [exact: Rhausdorff|exact: (@FTC0_restrict _ _ _ u)].
apply/cvg_ex; exists (f x).
have /= := FTC0_restrict xu intf ax fx.
set g := (f in f n @[n --> _] --> _ -> _).
set h := (f in _ -> f n @[n --> _] --> _).
suff : g = h by move=> <-.
by apply/funext => y;rewrite /g /h /= [X in F (X + _)]mulr1.
Qed.

Corollary FTC1 f a :
  (forall y, mu.-integrable [set` Interval a (BRight y)] (EFin \o f)) ->
  locally_integrable [set: R] f ->
  let F x := (\int[mu]_(t in [set` Interval a (BRight x)]) (f t))%R in
  {ae mu, forall x, a < BRight x -> derivable F x 1 /\ F^`() x = f x}.
Proof.
move=> intf locf F; move: (locf) => /lebesgue_differentiation.
apply: filterS; first exact: (ae_filter_ringOfSetsType mu).
move=> i fi ai.
by apply: (@FTC1_lebesgue_pt _ _ _ (i + 1)%R) => //; rewrite ltrDl.
Qed.

Corollary FTC1Ny f :
  (forall y, mu.-integrable `]-oo, y] (EFin \o f)) ->
  locally_integrable [set: R] f ->
  let F x := (\int[mu]_(t in [set` `]-oo, x]]) (f t))%R in
  {ae mu, forall x, derivable F x 1 /\ F^`() x = f x}.
Proof.
move=> intf locf F; have := FTC1 intf locf.
apply: filterS; first exact: (ae_filter_ringOfSetsType mu).
by move=> r /=; apply; rewrite ltNyr.
Qed.

Let itv_continuous_lebesgue_pt f a x (u : R) : (x < u)%R ->
  measurable_fun [set` Interval a (BRight u)] f ->
  a < BRight x ->
  {for x, continuous f} -> lebesgue_pt f x.
Proof.
move=> xu fi + fx.
move: a fi => [b a fi /[1!(@lte_fin R)] ax|[|//] fi _].
- near (0%R:R)^'+ => e; apply: (@continuous_lebesgue_pt _ _ _ (ball x e)) => //.
  + exact: ball_open_nbhs.
  + exact: measurable_ball.
  + apply: measurable_funS fi => //; rewrite ball_itv.
    apply: (@subset_trans _ `](x - e)%R, u]) => //.
      apply: subset_itvl; rewrite bnd_simp -lerBrDl.
      by near: e; apply: nbhs_right_ltW; rewrite subr_gt0.
    apply: subset_itvr; rewrite bnd_simp lerBrDr -lerBrDl.
    by near: e; apply: nbhs_right_ltW; rewrite subr_gt0.
- near (0%R:R)^'+ => e; apply: (@continuous_lebesgue_pt _ _ _ (ball x e)) => //.
  + exact: ball_open_nbhs.
  + exact: measurable_ball.
  + apply: measurable_funS fi => //; rewrite ball_itv.
    apply: (@subset_trans _ `](x - e)%R, u]) => //.
      apply: subset_itvl; rewrite bnd_simp -lerBrDl.
      by near: e; apply: nbhs_right_ltW; rewrite subr_gt0.
    exact: subset_itvr.
Unshelve. all: by end_near. Qed.

Corollary continuous_FTC1 f a x (u : R) : (x < u)%R ->
  mu.-integrable [set` Interval a (BRight u)] (EFin \o f) ->
  let F x := (\int[mu]_(t in [set` Interval a (BRight x)]) (f t))%R in
  a < BRight x -> {for x, continuous f} ->
  derivable F x 1 /\ F^`() x = f x.
Proof.
move=> xu fi F ax fx; suff lfx : lebesgue_pt f x.
  have /(_ ax lfx)[dfx f'xE] := @FTC1_lebesgue_pt _ a _ _ xu fi.
  by split; [exact: dfx|rewrite f'xE].
apply: itv_continuous_lebesgue_pt xu _ ax fx.
by move/integrableP : fi => -[/EFin_measurable_fun].
Qed.

Corollary continuous_FTC1_closed f (a x : R) (u : R) : (x < u)%R ->
  mu.-integrable `[a, u] (EFin \o f) ->
  let F x := (\int[mu]_(t in [set` `[a, x]]) (f t))%R in
  (a < x)%R -> {for x, continuous f} ->
  derivable F x 1 /\ F^`() x = f x.
Proof. by move=> xu locf F ax fx; exact: (@continuous_FTC1 _ _ _ u). Qed.

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
move=> ab intf; apply/(continuous_within_itvP _ ab); split; first last.
  exact: parameterized_integral_cvg_at_left.
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
    by apply: subset_itvScc; rewrite bnd_simp; exact/ltW.
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
    by apply: integrableS intf => //; apply: subset_itvScc => //; exact/ltW.
  have zxab : `[z, x] `<=` `[a, b].
    by apply: subset_itvScc; rewrite bnd_simp; exact/ltW.
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

(* TODO: move? *)
Let within_continuous_restrict f a b : (a < b)%R ->
  {within `[a, b], continuous f} -> {in `]a, b[, continuous (f \_ `[a, b])}.
Proof.
move=> ab + x xab; move=> /(_ x).
rewrite {1}/continuous_at => xf.
rewrite /prop_for /continuous_at  patchE.
rewrite mem_set ?mulr1 /=; last exact: subset_itv_oo_cc.
exact: cvg_patch.
Qed.

Corollary continuous_FTC2 f F a b : (a < b)%R ->
  {within `[a, b], continuous f} ->
  derivable_oo_continuous_bnd F a b ->
  {in `]a, b[, F^`() =1 f} ->
  (\int[mu]_(x in `[a, b]) (f x)%:E = (F b)%:E - (F a)%:E)%E.
Proof.
move=> ab cf dF F'f.
pose fab := f \_ `[a, b].
pose G x : R := (\int[mu]_(t in `[a, x]) fab t)%R.
have iabf : mu.-integrable `[a, b] (EFin \o f).
  by apply: continuous_compact_integrable => //; exact: segment_compact.
have G'f : {in `]a, b[, forall x, G^`() x = fab x /\ derivable G x 1}.
  move=> x /[!in_itv]/= /andP[ax xb].
  have ifab : mu.-integrable `[a, b] (EFin \o fab).
    by rewrite -restrict_EFin; apply/integrable_restrict => //=; rewrite setIid.
  have cfab : {for x, continuous fab}.
    by apply: within_continuous_restrict => //; rewrite in_itv/= ax xb.
  by have [] := continuous_FTC1_closed xb ifab ax cfab.
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
        apply: subset_itvSoo zxy => //.
        by move: xab; rewrite in_itv/= => /andP[].
        by move: yab; rewrite in_itv/= => /andP[].
      + apply: (G'f _ _).2; apply: subset_itvSoo zxy => //.
        by move: xab; rewrite in_itv/= => /andP[].
        by move: yab; rewrite in_itv/= => /andP[].
    - move=> z zxy; rewrite F'G'0.
        by rewrite /cst/= mul0r => /eqP; rewrite subr_eq0 => /eqP.
      apply: subset_itvSoo zxy => //=; rewrite bnd_simp.
      * by move: xab; rewrite in_itv/= => /andP[/ltW].
      * by move: yab; rewrite in_itv/= => /andP[_ /ltW].
  move=> H; pose c := (a + b) / 2.
  exists (F c - G c)%R => u /(H u c); apply.
  by rewrite in_itv/= midf_lt//= midf_lt.
have [c GFc] : exists c : R, forall x, x \in `]a, b[ -> (F x - G x)%R = c.
  by exists k => x xab; rewrite -[k]/(cst k x) -(FGk x xab).
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
  apply/(continuous_within_itvP _ ab); split => //.
  move=> z zab; apply/differentiable_continuous/derivable1_diffP.
  by case: dF => /= + _ _; exact.
have iabfab : mu.-integrable `[a, b] (EFin \o fab).
  by rewrite -restrict_EFin; apply/integrable_restrict => //; rewrite setIidr.
have Ga : G x @[x --> a^'+] --> G a.
   have := parameterized_integral_cvg_left ab iabfab.
   rewrite (_ : 0 = G a)%R.
     by move=> /left_right_continuousP[].
   by rewrite /G interval_set1 Rintegral_set1.
have Gb : G x @[x --> b^'-] --> G b.
  exact: (parameterized_integral_cvg_at_left ab iabfab).
have Ga0 : G a = 0%R by rewrite /G interval_set1// Rintegral_set1.
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

End corollary_FTC1.

Section integration_by_parts.
Context {R : realType}.
Notation mu := lebesgue_measure.
Local Open Scope ereal_scope.
Implicit Types (F G f g : R -> R) (a b : R).

Lemma integration_by_parts F G f g a b : (a < b)%R ->
    {within `[a, b], continuous f} ->
    derivable_oo_continuous_bnd F a b ->
    {in `]a, b[, F^`() =1 f} ->
    {within `[a, b], continuous g} ->
    derivable_oo_continuous_bnd G a b ->
    {in `]a, b[, G^`() =1 g} ->
  \int[mu]_(x in `[a, b]) (F x * g x)%:E = (F b * G b - F a * G a)%:E -
  \int[mu]_(x in `[a, b]) (f x * G x)%:E.
Proof.
move=> ab cf Fab Ff cg Gab Gg.
have cfg : {within `[a, b], continuous (f * G + F * g)%R}.
  apply/subspace_continuousP => x abx; apply: cvgD.
  - apply: cvgM.
    + by move/subspace_continuousP : cf; exact.
    + have := derivable_oo_continuous_bnd_within Gab.
      by move/subspace_continuousP; exact.
  - apply: cvgM.
    + have := derivable_oo_continuous_bnd_within Fab.
      by move/subspace_continuousP; exact.
    + by move/subspace_continuousP : cg; exact.
have FGab : derivable_oo_continuous_bnd (F * G)%R a b.
  move: Fab Gab => /= [abF FFa FFb] [abG GGa GGb];split; [|exact:cvgM..].
  by move=> z zab; apply: derivableM; [exact: abF|exact: abG].
have FGfg : {in `]a, b[, (F * G)^`() =1 f * G + F * g}%R.
  move: Fab Gab => /= [abF FFa FFb] [abG GGa GGb] z zba.
  rewrite derive1E deriveM; [|exact: abF|exact: abG].
  by rewrite -derive1E Gg// -derive1E Ff// addrC (mulrC f).
have := continuous_FTC2 ab cfg FGab FGfg; rewrite -EFinB => <-.
under [X in _ = X - _]eq_integral do rewrite EFinD.
have ? : mu.-integrable `[a, b] (fun x => ((f * G) x)%:E).
  apply: continuous_compact_integrable => //; first exact: segment_compact.
  apply/subspace_continuousP => x abx; apply: cvgM.
  + by move/subspace_continuousP : cf; exact.
  + have := derivable_oo_continuous_bnd_within Gab.
    by move/subspace_continuousP; exact.
rewrite /= integralD//=.
- by rewrite addeAC subee ?add0e// integral_fune_fin_num.
- apply: continuous_compact_integrable => //; first exact: segment_compact.
  apply/subspace_continuousP => x abx;apply: cvgM.
  + have := derivable_oo_continuous_bnd_within Fab.
    by move/subspace_continuousP; exact.
  + by move/subspace_continuousP : cg; exact.
Qed.

End integration_by_parts.

Section Rintegration_by_parts.
Context {R : realType}.
Notation mu := lebesgue_measure.
Implicit Types (F G f g : R -> R) (a b : R).

Lemma Rintegration_by_parts F G f g a b :
    (a < b)%R ->
    {within `[a, b], continuous f} ->
    derivable_oo_continuous_bnd F a b ->
    {in `]a, b[, F^`() =1 f} ->
    {within `[a, b], continuous g} ->
    derivable_oo_continuous_bnd G a b ->
    {in `]a, b[, G^`() =1 g} ->
  \int[mu]_(x in `[a, b]) (F x * g x) = (F b * G b - F a * G a) -
  \int[mu]_(x in `[a, b]) (f x * G x).
Proof.
move=> ab cf Fab Ff cg Gab Gg.
rewrite [in LHS]/Rintegral (@integration_by_parts R F G f g)// fineB//.
suff: mu.-integrable `[a, b] (fun x => (f x * G x)%:E).
  move=> /integrableP[? abfG]; apply: fin_real.
  rewrite (_ : -oo = - +oo)%E// -lte_absl.
  by apply: le_lt_trans abfG; exact: le_abse_integral.
apply: continuous_compact_integrable.
  exact: segment_compact.
move=> /= z; apply: continuousM; [exact: cf|].
exact: (derivable_oo_continuous_bnd_within Gab).
Qed.

End Rintegration_by_parts.

Section at_left_right.
Variable R : numFieldType.

(* TODO: check duplicate *)
Lemma nbhs_left_ltBl (x e : R) : 0 < e -> \forall y \near x^'-, x - y < e.
Proof.
move=> e0; near=> y; rewrite -ltrBrDl ltrNl opprB; near: y.
by apply: nbhs_left_gt; rewrite ltrBlDr ltrDl.
Unshelve. all: by end_near. Qed.

End at_left_right.

(* TODO: check duplicate *)
Lemma within_continuous_continuous {R : realType} a b (f : R -> R) x : (a < b)%R ->
  {within `[a, b], continuous f} -> x \in `]a, b[ -> {for x, continuous f}.
Proof.
by move=> ab /continuous_within_itvP-/(_ ab)[+ _] /[swap] xab cf; exact.
Qed.

Section integration_by_substitution_preliminaries.
Context {R : realType}.
Notation mu := lebesgue_measure.
Implicit Types (F G f : R -> R) (a b : R).

Lemma increasing_image_oo F (a b : R) : (a < b)%R ->
  {in `[a, b] &, {homo F : x y / (x < y)%R}} ->
  F @` `]a, b[ `<=` `]F a, F b[.
Proof.
move=> ab iF ? [x /= xab <-].
move: xab; rewrite !in_itv/= => /andP[ax xb].
by apply/andP; split; apply: iF; rewrite // in_itv/= ?lexx !ltW.
Qed.

Lemma decreasing_image_oo F (a b : R) : (a < b)%R ->
  {in `[a, b] &, {homo F : x y /~ (x < y)%R}} ->
  F @` `]a, b[ `<=` `]F b, F a[.
Proof.
move=> ab iF ? [x /= xab <-].
move: xab; rewrite !in_itv/= => /andP[ax xb].
by apply/andP; split; apply: iF; rewrite // in_itv/= ?lexx !ltW.
Qed.

Lemma increasing_cvg_at_right_comp F G a b (l : R) : (a < b)%R ->
  {in `[a, b[ &, {homo F : x y / (x < y)%R}} ->
  F x @[x --> a^'+] --> F a ->
  G x @[x --> (F a)^'+] --> l ->
  (G \o F) x @[x --> a^'+] --> l.
Proof.
move=> ab incrF cFa GFa.
(* take arbitrary e > 0, find d s.t. `| G (F (a + d))) - G (F a)| < e *)
apply/cvgrPdist_le => /= e e0.
(* for this e,
   there exists d s.t. `| G (F a + d) - G (F a)| < e by continuity of G *)
have/cvgrPdist_le /(_ e e0) [d /= d0 {}GFa] := GFa.
(* for this d,
   there exists d' s.t. forall r, `| r - a | < d' implies F (a + d') - F a < d
   by continuity of F at a *)
(* apply a lemma for take r := (a + d') from `[a, b] *)
have := cvg_at_right_within cFa.
move=> /cvgrPdist_lt/(_ _ d0)[d' /= d'0 {}cFa].
near=> t.
apply: GFa; last by apply: incrF; rewrite //in_itv/= ?lexx//; apply/andP; split.
apply: cFa => //=.
rewrite ltr0_norm// ?subr_lt0// opprB.
by near: t; exact: nbhs_right_ltDr.
Unshelve. all: end_near. Qed.

Lemma increasing_cvg_at_left_comp F G a b (l : R) : (a < b)%R ->
  {in `]a, b] &, {homo F : x y / (x < y)%R}} ->
  F x @[x --> b^'-] --> F b ->
  G x @[x --> (F b)^'-] --> l ->
  (G \o F) x @[x --> b^'-] --> l.
Proof.
move=> ab incrF cFb GFb.
apply/cvgrPdist_le => /= e e0.
have/cvgrPdist_le /(_ e e0) [d /= d0 {}GFb] := GFb.
have := cvg_at_left_within cFb.
move/cvgrPdist_lt/(_ _ d0) => [d' /= d'0 {}cFb].
near=> t.
apply: GFb; last by apply: incrF; rewrite //in_itv/= ?lexx//; apply/andP; split.
apply: cFb => //=.
rewrite gtr0_norm// ?subr_gt0//.
by near: t; exact: nbhs_left_ltBl.
Unshelve. all: end_near. Qed.

Lemma decreasing_cvg_at_right_comp F G a b (l : R) : (a < b)%R ->
  {in `[a, b[ &, {homo F : x y /~ (x < y)%R}} ->
  F x @[x --> a^'+] --> F a ->
  G x @[x --> (F a)^'-] --> l ->
  (G \o F) x @[x --> a^'+] --> l.
Proof.
move=> ab decrF cFa GFa.
apply/cvgrPdist_le => /= e e0.
have/cvgrPdist_le /(_ e e0) [d' /= d'0 {}GFa] := GFa.
have := cvg_at_right_within cFa.
move/cvgrPdist_lt/(_ _ d'0) => [d'' /= d''0 {}cFa].
near=> t.
apply: GFa; last by apply: decrF; rewrite //in_itv/= ?lexx//; apply/andP; split.
apply: cFa => //=.
rewrite ltr0_norm// ?subr_lt0// opprB.
by near: t; exact: nbhs_right_ltDr.
Unshelve. all: end_near. Qed.

Lemma decreasing_cvg_at_left_comp F G a b (l : R) : (a < b)%R ->
  {in `]a, b] &, {homo F : x y /~ (x < y)%R}} ->
  F x @[x --> b^'-] --> F b ->
  G x @[x --> (F b)^'+] --> l ->
  (G \o F) x @[x --> b^'-] --> l.
Proof.
move=> ab decrF cFb GFb.
apply/cvgrPdist_le => /= e e0.
have/cvgrPdist_le /(_ e e0) [d' /= d'0 {}GFb] := GFb.
have := cvg_at_left_within cFb. (* different point from gt0 version *)
move/cvgrPdist_lt/(_ _ d'0) => [d'' /= d''0 {}cFb].
near=> t.
apply: GFb; last by apply: decrF; rewrite //in_itv/= ?lexx//; apply/andP; split.
apply: cFb => //=.
rewrite gtr0_norm// ?subr_gt0//.
by near: t; exact: nbhs_left_ltBl.
Unshelve. all: end_near. Qed.

End integration_by_substitution_preliminaries.

Section integration_by_substitution.
Local Open Scope ereal_scope.
Context {R : realType}.
Notation mu := lebesgue_measure.
Implicit Types (F G f : R -> R) (a b : R).

Lemma increasing_change F G a b : (a < b)%R ->
  {in `[a, b] &, {homo F : x y / (x < y)%R}} ->
  {within `[a, b], continuous F^`()} ->
  derivable_oo_continuous_bnd F a b ->
  {within `[F a, F b], continuous G} ->
  \int[mu]_(x in `[F a, F b]) (G x)%:E =
  \int[mu]_(x in `[a, b]) (((G \o F) * F^`()) x)%:E.
Proof.
set f : R -> R := F^`().
move=> ab incrF cf dcbF cG.
have FaFb : (F a < F b)%R by apply: incrF; rewrite //= in_itv/= (ltW ab) lexx.
pose PG x := parameterized_integral mu (F a) x G.
have intGFb : mu.-integrable `[(F a), (F b)] (EFin \o G).
  by apply: continuous_compact_integrable => //; exact: segment_compact.
set H := PG \o F.
set h : R -> R := ((G \o F) * f)%R.
have dcbPG : derivable_oo_continuous_bnd PG (F a) (F b).
  have [/= dF rF lF] := dcbF.
  split => /=.
  - move=> x xFaFb /=.
    have xFb : (x < F b)%R by move: xFaFb; rewrite in_itv/= => /andP[].
    apply: (continuous_FTC1 xFb intGFb _ _).1 => /=.
      by move: (xFaFb); rewrite lte_fin in_itv/= => /andP[].
    exact: (within_continuous_continuous _ _ xFaFb).
  - have := parameterized_integral_continuous FaFb intGFb.
    by move=> /(continuous_within_itvP _ FaFb)[].
  - exact: parameterized_integral_cvg_at_left.
have dPGE : {in `](F a), (F b)[, PG^`() =1 G}.
  move=> x xFaFb.
  have xFb : (x < F b)%R by move: xFaFb; rewrite in_itv/= => /andP[].
  apply: (continuous_FTC1 xFb intGFb _ _).2 => //=.
    by move: (xFaFb); rewrite lte_fin in_itv/= => /andP[].
  exact: (within_continuous_continuous _ _ xFaFb).
move/continuous_within_itvP : (cG) => /(_ FaFb)[incG GFa GFb].
have : {within `[a, b], continuous F} :=
  derivable_oo_continuous_bnd_within dcbF.
move/continuous_within_itvP => /(_ ab)[incF cFa cFb].
have ch : {within `[a, b], continuous h}.
  apply/(continuous_within_itvP _ ab); split.
  - move=> /= x xab.
    apply: continuousM; last first.
      by move/(continuous_within_itvP _ ab) : cf => [+ _ _]; exact.
    apply: continuous_comp; first exact: incF.
    by apply: incG; exact: increasing_image_oo.
  - apply: cvgM.
      apply: (increasing_cvg_at_right_comp ab) => //x y xab yab.
      by apply: incrF; apply: subset_itv_co_cc.
    by move /(continuous_within_itvP _ ab) : cf => [].
  - apply: cvgM.
      apply: (increasing_cvg_at_left_comp ab) => //x y xab yab.
      by apply: incrF; apply: subset_itv_oc_cc.
    by move /(continuous_within_itvP _ ab) : cf => [].
have dcbH : derivable_oo_continuous_bnd H a b.
  have := derivable_oo_continuous_bnd_within dcbPG.
  move=> /(continuous_within_itvP _ FaFb)[_ PGFa PGFb].
  split => /=.
  - move=> x xab.
    apply/derivable1_diffP.
    apply: differentiable_comp; apply/derivable1_diffP.
      by have [+ _ _] := dcbF; apply.
    have [+ _ _] := dcbPG.
    by apply; exact: increasing_image_oo.
  - apply/cvgrPdist_le => /= e e0.
    have/cvgrPdist_le /(_ e e0) [d /= d0 {}PGFa] := PGFa.
    have := cvg_at_right_within cFa.
    move/cvgrPdist_lt/(_ _ d0) => [d' /= d'0 {}cFa].
    near=> t.
    apply: PGFa; last by apply: incrF; rewrite //in_itv/= ?lexx !ltW.
    apply: cFa => //=.
    rewrite ltr0_norm// ?subr_lt0// opprB.
    by near: t; exact: nbhs_right_ltDr.
  - apply/cvgrPdist_le => /= e e0.
    have/cvgrPdist_le /(_ e e0) [d /= d0 {}PGFb] := PGFb.
    have := cvg_at_left_within cFb.
    move/cvgrPdist_lt/(_ _ d0) => [d' /= d'0 {}cFb].
    near=> t.
    apply: (PGFb); last by apply: incrF; rewrite //in_itv/= ?lexx !ltW.
    apply: cFb => //=.
    rewrite gtr0_norm// ?subr_gt0//.
    by near: t; exact: nbhs_left_ltBl.
have ? : {in `]a, b[, H^`() =1 h}.
  move=> x xab; rewrite derive1_comp.
  - by rewrite dPGE//; exact: increasing_image_oo.
  - by have [+ _ _] := dcbF; apply.
  - by have [+ _ _] := dcbPG; apply; exact: increasing_image_oo.
rewrite (continuous_FTC2 FaFb cG dcbPG dPGE).
by rewrite (continuous_FTC2 ab ch dcbH).
Unshelve. all: end_near. Qed.

Lemma decreasing_change F G a b :
    (a < b)%R ->
    {in `[a, b]&, {homo F : x y /~ (x < y)%R}} ->
    {within `[a, b], continuous F^`()} ->
    derivable_oo_continuous_bnd F a b ->
    {within `[F b, F a], continuous G} ->
  \int[mu]_(x in `[F b, F a]) (G x)%:E =
  \int[mu]_(x in `[a, b]) (((G \o F) * - (F^`() : R -> R)) x)%:E.
Proof.
set f : R -> R := F^`().
move=> ab decrF cf dcbF cG.
have FbFa : (F b < F a)%R by apply: decrF; rewrite //in_itv/= (ltW ab) lexx.
pose PG x := parameterized_integral mu (F b) x G.
have intGFa : mu.-integrable `[(F b), (F a)] (EFin \o G).
  by apply: continuous_compact_integrable => //; exact: segment_compact.
set H := PG \o F.
set h : R -> R := ((G \o F) * (- f))%R.
have dcbPG : derivable_oo_continuous_bnd PG (F b) (F a).
  have [dF rF lF] := dcbF.
  split.
  - move=> x xFbFa /=.
    have xFa : (x < F a)%R by move: xFbFa; rewrite in_itv/= => /andP[].
    apply: (continuous_FTC1 xFa intGFa _ _).1 => //=.
      by move: (xFbFa); rewrite lte_fin in_itv/= => /andP[].
    exact: (within_continuous_continuous _ _ xFbFa).
  - move: intGFa.
    move/(parameterized_integral_continuous FbFa).
    by move/(continuous_within_itvP _ FbFa) => [_ + _].
  - exact: parameterized_integral_cvg_at_left.
have dPGE : {in `](F b), (F a)[, PG^`() =1 G}.
  move=> x xFbFa.
  have xFa : (x < F a)%R by move: xFbFa; rewrite in_itv/= => /andP[].
  apply: (continuous_FTC1 xFa intGFa _ _).2 => //=.
    by move: (xFbFa); rewrite lte_fin in_itv/= => /andP[].
  exact: (within_continuous_continuous _ _ xFbFa).
move/continuous_within_itvP : (cG) => /(_ FbFa)[in_cG GFb GFa].
have := derivable_oo_continuous_bnd_within dcbF.
move=> /continuous_within_itvP => /(_ ab)[in_cF cFa cFb].
have cNh : {within `[a, b], continuous (- h)%R}.
  apply/(continuous_within_itvP _ ab); split.
  - move=> /= x xab; apply: continuousN.
    apply: continuousM; last first.
      apply: continuousN.
      move/(continuous_within_itvP _ ab) : cf => [+ _ _].
      exact.
    apply: continuous_comp.
      exact: in_cF.
    by apply: in_cG; exact: decreasing_image_oo.
  - apply: cvgN; apply: cvgM.
      apply: (decreasing_cvg_at_right_comp ab) => //x y xab yab.
      by apply: decrF; apply: subset_itv_co_cc.
    apply: (@cvgN _ _ _ _ _ f (f a)).
    by move /(continuous_within_itvP _ ab) : cf => [].
  - apply: cvgN; apply: cvgM.
      apply: (decreasing_cvg_at_left_comp ab) => //x y xab yab.
      by apply: decrF; apply: subset_itv_oc_cc.
    apply: (@cvgN _ _ _ _ _ f (f b)).
    by move /(continuous_within_itvP _ ab) : cf => [].
have dcbH : derivable_oo_continuous_bnd H a b.
  have := derivable_oo_continuous_bnd_within dcbPG.
  move=> /(continuous_within_itvP _ FbFa)[_ PGFb PGFa].
  split => /=.
  - move=> x xab.
    apply/derivable1_diffP.
    apply: differentiable_comp; apply/derivable1_diffP.
      by have [+ _ _] := dcbF; apply.
    have [dPG ? ?] := dcbPG.
    by apply: dPG; exact: decreasing_image_oo.
  - apply/cvgrPdist_le => /= e e0.
    have/cvgrPdist_le /(_ e e0) [d' /= d'0 {}PGFa] := PGFa.
    have := cvg_at_right_within cFa.
    move/cvgrPdist_lt/(_ _ d'0) => [d'' /= d''0 {}cFa].
    near=> t.
    apply: PGFa; last by apply: decrF; rewrite //in_itv/= ?lexx !ltW.
    apply: cFa => //=.
    rewrite ltr0_norm// ?subr_lt0// opprB.
    by near: t; exact: nbhs_right_ltDr.
  - apply/cvgrPdist_le => /= e e0.
    have/cvgrPdist_le /(_ e e0) [d' /= d'0 {}PGFb] := PGFb.
    have := cvg_at_left_within cFb.
    move/cvgrPdist_lt/(_ _ d'0) => [d'' /= d''0 {}cFb].
    near=> t.
    apply: (PGFb); last by apply: decrF; rewrite //in_itv/= ?lexx !ltW.
    apply: cFb => //=.
    rewrite gtr0_norm// ?subr_gt0//.
    by near: t; exact: nbhs_left_ltBl.
have dHE : {in `]a, b[, H^`() =1 (- h)%R}. (* difference from gt0 version *)
  move=> x xab; rewrite derive1_comp.
  - rewrite dPGE//; first by rewrite /h mulrN opprK//.
    exact: decreasing_image_oo.
  - by have [+ _ _] := dcbF; apply.
  - by have [+ _ _] := dcbPG; apply; exact: decreasing_image_oo.
rewrite (continuous_FTC2 FbFa cG dcbPG dPGE).
under eq_integral do rewrite -(opprK (h _)) EFinN.
rewrite integralN/=; last first.
  apply: integrable_add_def => //.
  apply: continuous_compact_integrable => //.
  exact: segment_compact.
by rewrite (continuous_FTC2 ab cNh dcbH dHE) oppeB// EFinN addeC.
Unshelve. all: end_near. Qed.

End integration_by_substitution.
