From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import all_ssreflect interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality.
From mathcomp Require Import reals ereal topology normedtype.
From mathcomp Require Import sequences measure lebesgue_measure realfun.
From mathcomp Require Import borel_hierarchy absolute_continuity.
From mathcomp Require Import banach_zarecki_lemma2.

(**md**************************************************************************)
(* # Banach–Zarecki Theorem (lemma 3)                                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma cvg_half {R : realType} : (2^-1 ^+ x) @[x --> \oo] --> (0 : R).
Proof.
rewrite (_:(fun n => (2^-1 ^+ n)) = (fun n => geometric 1 2^-1 n)); last first.
   apply: funext => n.
   by rewrite /geometric/= mul1r.
apply: cvg_geometric.
rewrite ger0_norm// invf_lt1//.
exact: ltr1n.
Qed.

Section lemma3.
Context {R : realType}.
Variables a b : R.
Hypothesis ab : a < b.

Local Notation mu := (@completed_lebesgue_measure R).

(* lemma3 (easy direction) *)
Lemma Lusin_image_measure0 (f : R -> R) :
  {within `[a, b], continuous f} ->
  {in `[a, b] &, {homo f : x y / x <= y}} ->
  lusinN `[a, b] f ->
  forall Z : set R, [/\ Z `<=` `[a, b]%classic,
      compact Z &
      mu Z = 0] ->
      mu (f @` Z) = 0.
Proof.
move=> cf ndf lusinNf Z [Zab cZ muZ0].
have /= mZ : (wlength idfun)^*%mu.-cara.-measurable Z.
  by apply: sub_caratheodory; exact: compact_measurable.
exact: (lusinNf Z Zab mZ muZ0).
Qed.

(* duplicate of outer_Gdelta ? *)
Lemma lebesgue_measure_Gdelta_approx (Z : set R) : ((wlength idfun)^*%mu Z < +oo)%E ->
  exists U : nat -> set R, [/\ (forall k, Z `<=` U k), (forall k, open (U k)) &
  ((wlength idfun)^*%mu Z = (wlength idfun)^*%mu (\bigcap_k U k))].
Proof.
move=> Zoo.
pose delta0 k := 2^-1 ^+ k :> R.
have delta_ge0 k : 0 < delta0 k.
  apply: exprn_gt0.
  by rewrite invr_gt0.
have mUfin : ereal_inf [set mu U | U in [set U | open U /\ Z `<=` U]] \is a fin_num.
  by rewrite -lebesgue_regularity_outer_inf ge0_fin_numE.
have := fun k => (@exists2P _ _ _).1
    (@lb_ereal_inf_adherent _ [set mu U | U in [set U | open U /\ Z `<=` U]]
      (delta0 k) (delta_ge0 k) mUfin).
move/(@choice _ _ (fun k x => [set mu U | U in [set U | open U /\ Z `<=` U]] x /\
     (x < ereal_inf [set mu U | U in [set U | open U /\ Z `<=` U]] +
      (delta0 k)%:E)%E)).
move=> [e_] /all_and2[/= + einf].
under [X in X -> _]eq_forall do rewrite exists2E.
move=> /choice[U_].
move=> /all_and2[/all_and2[oU ZU] mUe].
pose V_ := fun n => \bigcap_(i < n.+1) U_ i.
exists V_; split.
    move=> n.
    exact: sub_bigcap => i _.
  move=> n.
  exact: bigcap_open.
rewrite [X in _ = _ X](_:_= \bigcap_i U_ i); last first.
  rewrite eqEsubset; split.
    move=> x Hx n _.
    by apply: (Hx n.+1) => /=.
  move=> x Hx n _ k /= kn.
  exact: Hx.
have V0oo : (mu (V_ 0%N) < +oo)%E.
  rewrite /V_ bigcap1.
  rewrite (mUe 0%N).
  apply: (lt_trans (einf 0%N)).
  apply: lte_add_pinfty; last by exact: ltry.
  by rewrite -lebesgue_regularity_outer_inf.
have mV i : measurable (V_ i).
    apply: bigcap_measurable.
    by exists 0%N.
  move=> k /= _.
  by exact: open_measurable.
have mIV : measurable (\bigcap_i V_ i) by exact: bigcap_measurable.
have niV :{homo V_ : n m / (n <= m)%N >-> (m <= n)%O}.
  apply/nonincreasing_seqP => n.
  rewrite /V_ !bigcap_mkord.
  rewrite big_ord_recr/= subsetEset.
  exact: subIsetl.
have pVE n : \bigcap_(i < n) V_ i = \bigcap_(i < n) U_ i.
  case: n.
    by rewrite eqEsubset; split.
  move=> //n.
  rewrite eqEsubset; split.
    move=> x Vx.
    move=> k/= kn.
    by apply: (Vx k) => /=.
  move=> x HU k /= kn m /= mk.
  apply: (HU m) => /=.
  exact: leq_trans _ kn.
have VE : \bigcap_i V_ i = \bigcap_i U_ i.
  rewrite eqEsubset; split.
    move=> x HV n _.
    apply: (HV n) => //.
    by rewrite IIS; right.
  move=> x HU n _ k /= kn.
  exact: (HU k).
rewrite -VE.
apply: esym.
have /cvg_lim VIV:= @nonincreasing_cvg_mu _ _ _ lebesgue_measure V_ V0oo mV mIV niV.
rewrite -[LHS]VIV//.
apply: cvg_lim => //.
apply: (@squeeze_cvge _ _ _ _ (cst (mu Z)) _ (fun n => (mu Z + (delta0 n)%:E)%E)).
- apply: nearW => n/=; apply/andP; split.
    apply: le_outer_measure.
    move=> x Zx k/= _.
    exact: ZU.
  apply: (@le_trans _ _ (mu (U_ n))).
    apply: le_outer_measure.
    by apply: bigcap_inf => /=.
  rewrite mUe completed_lebesgue_measureE lebesgue_regularity_outer_inf ltW//.
  by apply: einf.
- exact: cvg_cst.
- rewrite -(adde0 ((wlength _)^*%mu Z)).
  apply: cvgeD.
  + exact: fin_num_adde_defl.
  + exact: cvg_cst.
  + apply: cvg_EFin; first exact: nearW.
    exact: cvg_half.
Qed.

Lemma continuous_increasing_set_bij (f : R -> R) :
  {within `[a, b], continuous f} ->
  {in `[a, b] &, {homo f : x y / x < y}} ->
  set_bij `[a, b] `[f a, f b] f.
Proof.
move=> cf incf.
split.
- move=> x/=; rewrite 2!in_itv/= => /andP[ax xb]; apply/andP; split.
  + move: ax; rewrite le_eqVlt => /predU1P[-> //|ax].
    apply/ltW/incf; rewrite ?in_itv//=.
    * by rewrite lexx (ltW ab).
    * by rewrite xb andbT ltW.
  + move: xb; rewrite le_eqVlt => /predU1P[-> //|xb].
    apply/ltW/incf; rewrite ?in_itv//=.
    * by rewrite ax/= ltW.
    * by rewrite lexx (ltW ab).
- move=> x y; rewrite 2!inE/= 2!in_itv/= => /andP[ax xb]/andP[ay yb].
  move/eqP; rewrite eq_le => /andP[fxy fyx].
  apply/notP => /eqP.
  rewrite neq_lt => /orP[xy|yx].
  + move: fyx => /notP; apply.
    apply/negP; rewrite lt_geF//.
    apply: incf; rewrite ?in_itv//=.
    * by rewrite ax xb.
    * by rewrite ay yb.
  + move: fxy => /notP; apply.
    apply/negP; rewrite lt_geF//.
    apply: incf; rewrite ?in_itv//=.
    * by rewrite ay yb.
    * by rewrite ax xb.
- apply: segment_continuous_le_surjective => //.
  + exact: ltW.
  + by apply/ltW/incf; rewrite //?boundl_in_itv ?boundr_in_itv bnd_simp/= ltW.
Qed.

Lemma continuous_increasing_image_itv (f : R -> R) :
  {within `[a, b], continuous f} ->
  {in `[a, b] &, {homo f : x y / x < y}} ->
  f @` `[a, b] = `[f a, f b]%classic.
Proof.
move=> cf incf.
rewrite eqEsubset; split.
  apply: set_bij_sub.
  exact: continuous_increasing_set_bij.
rewrite -surjE.
apply: set_bij_surj.
exact: continuous_increasing_set_bij.
Qed.

Lemma GdeltaIr (U S : set R) :
  open U ->
  Gdelta S ->
  Gdelta (U `&` S).
Proof.
move=> oU [V_ oV {S}->].
exists (fun n => if n == 0 then U else (V_ n.-1)).
- by case.
- rewrite [RHS](bigcap_splitn 1)/=; congr setI.
  by rewrite big_ord1/=.
Qed.

Lemma GdeltaIl (U S : set R) :
  open U ->
  Gdelta S ->
  Gdelta (S `&` U).
Proof. by move=> oU GS; rewrite setIC; exact: GdeltaIr. Qed.

Let measurable_image_setI_set1 (f : R -> R) (A : set R) (x : R) :
  measurable (f @` (A `&` [set x])).
Proof.
rewrite setI1; case: ifP; rewrite ?image_set0// image_set1 => _.
exact: measurable_set1.
Qed.

Let measurable_setD1 (A : set R) (x : R) :
  measurable A -> measurable (A `\ x).
Proof.
move=> mA.
rewrite setDE.
apply: measurableI => //.
apply: measurableC.
exact: measurable_set1.
Qed.

Let image_setD1 (f : R -> R) (A : set R) (x : R) :
(forall a, (A `\ x) a -> f a != f x) ->
  f @` (A `\ x) = (f @` A) `\ f x.
Proof.
move=> H.
rewrite eqEsubset; split.
  move=> _ [z [Az /= zx] <-]; split; first by exists z.
  apply/eqP; exact: H.
move=> _ [[z Az <-] /= fzx].
exists z => //; split => //.
move=> zx; apply: fzx.
by f_equal.
Qed.

Let not_image_setD1 (f : R -> R) (A : set R) (x : R) :
 ~ (forall a, (A `\ x) a -> f a != f x) ->
  f @` (A `\ x) = (f @` A).
Proof.
move=> H.
rewrite eqEsubset; split.
  apply: image_subset.
  exact: subDsetl.
have [Ax|nAx] := pselect (A x); last by rewrite not_setD1.
rewrite -{1}(setD1K Ax).
move=> y [z + <-].
case.
  move->.
  move: H.
  move/existsNP => [t].
  move/not_implyP => [[At /= tx]].
  move/negP/negPn/eqP => ftx.
  by exists t.
move=> [Az /= zx].
by exists z.
Qed.

Let measurable_image_setD1 (f : R -> R) (A : set R) (x : R) :
  measurable (f @` A) ->
  measurable (f @` (A `\ x)).
Proof.
move=> mfA.
have [Ax|nAx] := pselect (forall a, (A `\ x) a -> f a != f x).
  by rewrite image_setD1//; apply: measurableD.
by rewrite not_image_setD1.
Qed.

Let measure0_image_setI_set1 (f : R -> R) (A : set R) (x : R) :
  mu (f @` (A `&` [set x])) = 0.
Proof.
rewrite setI1; case: ifP; rewrite ?image_set0// image_set1 => _.
exact: lebesgue_measure_set1.
Qed.

Let measure0_setI_set1 (A : set R) (x : R) :
  mu (A `&` [set x]) = 0.
Proof.
rewrite setI1; case: ifP => //.
by rewrite completed_lebesgue_measureE lebesgue_measure_set1.
Qed.

(* generalize? *)
Let measure_image_setD_set1 (f : R -> R) (A : set R) (x : R) :
  mu (f @` (A `\ x)) = mu (f @` A).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: le_outer_measure.
  rewrite setDE.
  apply: (subset_trans sub_image_setI).
  exact: subIsetl.
rewrite -{1}(setUIDK A [set x]).
rewrite image_setU.
apply: (le_trans (outer_measureU2 _ _ _)) => /=.
have := measure0_image_setI_set1 f A x.
rewrite completed_lebesgue_measureE.
rewrite /lebesgue_measure/lebesgue_stieltjes_measure/measure_extension.
by move->; rewrite add0r.
Qed.

(* testing strict increasing version *)
Lemma image_measure0_Lusin_increasing (F : R -> R) :
  {within `[a, b], continuous F} ->
  {in `[a, b] &, {homo F : x y / x < y}} ->
  (forall Z : set R, Z `<=` `[a, b]%classic ->
      compact Z ->
      mu Z = 0 ->
      mu (F @` Z) = 0) ->
  lusinN `[a, b] F.
Proof.
move=> cF incF lusinN'.
apply: contrapT.
move=> /existsNP[Z]/not_implyP[Zab/=] /not_implyP[mZ] /not_implyP[muZ0].
move=> /eqP; rewrite neq_lt ltNge measure_ge0/= => muFZ0.
have Zoo : (mu Z < +oo)%E.
  apply: (@le_lt_trans _ _ (mu `[a, b])); first exact: le_outer_measure.
  rewrite completed_lebesgue_measureE.
  by rewrite lebesgue_measure_itv/= lte_fin ab -EFinD ltry.
have [U_ [ZU oU mZIU]] := lebesgue_measure_Gdelta_approx Zoo.
set Z1 := `]a, b[ `&` \bigcap_n U_ n.
have muZ10 : mu Z1 = 0.
  apply/eqP; rewrite -measure_le0/= -muZ0.
  rewrite completed_lebesgue_measureE.
  rewrite /lebesgue_measure/lebesgue_stieltjes_measure/measure_extension mZIU.
  apply: le_outer_measure.
  exact: subIsetr.
have Z1ab : Z1 `<=` `]a, b[ by exact: subIsetl.
have Z1oo : (mu (F @` Z1) < +oo)%E.
  apply: (@le_lt_trans _ _ (mu (F @` `[a, b]))).
    apply: le_outer_measure.
    apply: image_subset.
    apply: (subset_trans Z1ab).
    exact: subset_itv_oo_cc.
  rewrite continuous_increasing_image_itv//.
  rewrite completed_lebesgue_measure_itv lte_fin incF// -?EFinB ?ltry//.
    by rewrite boundl_in_itv/= bnd_simp ltW.
  by rewrite boundr_in_itv bnd_simp ltW.
have gZ1 : Gdelta Z1.
  apply: GdeltaIr => //.
  by exists U_.
(* using lemma2 *)
have mFZ1 : measurable (F @` Z1).
  apply: measurable_image_Gdelta_set_nondecreasing_fun Z1ab gZ1 => //.
  by move=> ? ? ? ?; rewrite le_eqVlt => /predU1P[->//|xy]; exact/ltW/incF.
have ZZ1 : Z `\ a `\ b `<=` Z1.
  rewrite subsetI; split.
  - rewrite -(setIidr Zab).
    rewrite -setU1itv ?bnd_simp ?ltW//.
    rewrite setIUl setDUl.
    rewrite setIC -setIDA setDv setI0 set0U.
    rewrite -setUitv1 ?bnd_simp ?ltW//.
    rewrite setIUl 2!setDUl -2!setIDA.
    rewrite -setIDA (setIC [set b]) -setIDA setDv setI0 setU0.
    exact: subIsetl.
  - apply: sub_bigcap => n _.
    apply: subset_trans (ZU n).
    rewrite setDDl.
    exact: subDsetl.
have FZ1oo : (mu (F @` Z1) < +oo)%E.
  apply: (@le_lt_trans _ _ (mu (F @` `]a, b[))).
    apply: le_outer_measure.
    exact: image_subset.
  apply: (@le_lt_trans _ _ (mu `[F a, F b])).
    apply: le_outer_measure.
    rewrite -continuous_increasing_image_itv => //.
    apply: image_subset.
    exact: subset_itv_oo_cc.
  rewrite completed_lebesgue_measure_itv.
  by case: ifP=> //; rewrite -EFinB ltry.
have FZ10 : (0 < mu (F @` Z1))%E.
  apply: (@lt_le_trans _ _ (mu (F @` (Z `\ a `\ b)))).
    by rewrite 2!measure_image_setD_set1.
  apply: le_outer_measure.
  exact: image_subset.
set e := fine (mu (F @` Z1)) / 2.
have e0 : 0 < e by rewrite divr_gt0 ?fine_gt0 ?FZ1oo ?FZ10.
have [K [cK KFZ1 Z1Ke]] := lebesgue_regularity_inner mFZ1 FZ1oo e0.
set K1 := `[a, b] `&` F @^-1` K.
have K1K : F @` K1 = K.
  rewrite eqEsubset; split.
    apply: (subset_trans sub_image_setI).
    apply: subIset; right.
    exact: image_preimage_subset.
  move=> r Kr/=.
  pose L := `[a, b] `&` preimage F [set r].
  have L0 : L !=set0.
    have [] := @IVT _ _ _ _ r (ltW ab) cF.
      have Fab : F a < F b.
        apply: incF => //.
        - by rewrite boundl_in_itv bnd_simp ltW.
        - by rewrite boundr_in_itv bnd_simp ltW.
      rewrite minElt Fab.
      rewrite maxElt Fab.
      move: Kr => /KFZ1[t [/= tab _] <-].
      rewrite 2?ltW ?incF//.
      - exact: subset_itv_oo_cc.
      - by rewrite boundr_in_itv ?bnd_simp ?ltW.
      - by move: tab; rewrite in_itv/= => /andP[].
      - by rewrite boundl_in_itv ?bnd_simp ?ltW.
      - exact: subset_itv_oo_cc.
      - by move: tab; rewrite in_itv/= => /andP[].
    by move=> x xab; rewrite /L; move <-; exists x.
  move: (L0) => [r'] /[dup] Lr'.
  rewrite /L/= => [[r'ab Fr'r]].
  exists r' => //.
  rewrite /K1/=; split => //.
  by rewrite Fr'r.
have : (0 < mu (F @` K1))%E.
  rewrite K1K.
  have := Z1Ke.
  rewrite measureD//; last exact: compact_measurable.
  rewrite setIidr//.
  rewrite lteBlDl; last first.
    rewrite ge0_fin_numE//.
    apply: le_lt_trans FZ1oo.
    exact: le_outer_measure.
  rewrite -lteBlDr//.
  rewrite completed_lebesgue_measureE.
  apply: le_lt_trans.
  rewrite sube_ge0// /e EFinM fineK; last by rewrite ge0_fin_numE.
  rewrite muleC gee_pMl//.
  rewrite lee_fin invf_le1//.
  by rewrite -[leLHS](mulr1n 1) ler_nat.
apply/negP.
rewrite -leNgt.
rewrite measure_le0/=.
apply/eqP.
apply: lusinN'.
- exact: subIsetl.
- rewrite /K1 setIC.
  rewrite -(setIid `[a, b]%classic) setICA.
  apply: compact_closedI => //; first exact: segment_compact.
  rewrite closed_setIS; last exact: interval_closed.
  apply: (continuous_closedP _).1 => //.
  exact: compact_closed.
- apply/eqP; rewrite -measure_le0/= -muZ10.
  have bijF := continuous_increasing_set_bij cF incF.
  have [F' FF'] := pPbij bijF.
  rewrite /K1 FF' -inv_sub_image; last first.
    apply: (subset_trans KFZ1).
    rewrite -continuous_increasing_image_itv//.
    apply: image_subset.
    apply: (subset_trans Z1ab).
    exact: subset_itv_oo_cc.
  apply: le_outer_measure.
  rewrite image_sub.
  apply: subset_trans (@inv_image_sub _ _ _ _ _ Z1 _) => /=; last first.
    apply: (subset_trans Z1ab).
    exact: subset_itv_oo_cc.
  rewrite invV.
  by move=> ? ?/=; rewrite -FF'; exact: KFZ1.
Abort.

  (* Lemma open_subset_itvoocc S : open S -> S `<=` `[a, b] -> S `<=` `]a, b[. *)
  (*   move=> oS Sab. *)
  (*   apply: (@subset_trans _ [set` Rhull S]). *)
  (*     exact: sub_Rhull. *)
  (*     (* lemma? *) *)
  (*   have itv_closure_subset : {in (@is_interval R) : set (set R) &, {mono closure : i j / i `<=` j}}. *)
  (*     move=> i j itvi itvj. *)
  (*     rewrite propeqE; split. *)
  (*       admit. *)
  (*     exact: closure_subset. *)
  (*   rewrite -itv_closure_subset; last 2 first. *)
  (*       admit. *)
  (*     admit. *)
  (*   rewrite closure_itvoo //. *)
  (*   (* lemma? *) *)
  (*   have closurer_subset X (x y : R) : X `<=` `[x, y] -> closure X `<=` `[x, y]. *)
  (*     admit. *)
  (*   apply: closurer_subset. *)
  (*   (* lemma? *) *)
  (*   have sub_Rhullr (i : interval R) : S `<=` [set` i] -> [set` Rhull S] `<=` [set` i]. *)
  (*     admit. *)
  (*   by apply: sub_Rhullr. *)

Section main_lemma.

Arguments open : clear implicits.
Arguments closed : clear implicits.
Arguments compact : clear implicits.
Arguments continuous_at : clear implicits.

(* lemma3 (converse) *)
(* NB: 1. In Hypothesis, "F is increasing" means nondecreasing or not?        *)
(*     2. In wlog step, "Gdelta-type" means Gdelta set?                       *)
(*        Then, can we obtain Z1 as (closure Z)?                              *)
(*     3. In Hypothesis and proof, when Gdelta-type doesn't means Gdelta set, *)
(*        "compact" means precompact, as compactness in `[a, b]?              *)
Lemma image_measure0_Lusin_nondecreasing (F : R -> R) :
  {within `[a, b], continuous F} ->
  (* increasing means nondecreasing or not? *)
  {in `[a, b] &, {homo F : x y / x <= y}} ->
  (forall Z : set R, Z `<=` `[a, b]%classic ->
      compact R Z ->
      mu Z = 0 ->
      mu (F @` Z) = 0) ->
  lusinN `[a, b] F.
Proof.
move=> cF ndF HZ.
(* Suppose on the contrary that F \notin (N) on `[a, b] *)
apply: contrapT.
(*Then there exists ... *)
move=> /existsNP[Z]/not_implyP[Zab/=] /not_implyP[mZ] /not_implyP[muZ0].
move=> /eqP; rewrite neq_lt ltNge measure_ge0/= => muFZ0.
have Zoo : (mu Z < +oo)%E.
  apply: (@le_lt_trans _ _ (mu `[a, b])); first exact: le_outer_measure.
  rewrite completed_lebesgue_measureE.
  by rewrite lebesgue_measure_itv/= lte_fin ab -EFinD ltry.
(* wlog (we should read Z1 as Z in paper) *)
have [U_ [ZU oU mZIU]] := lebesgue_measure_Gdelta_approx Zoo.
set Z1 := `]a, b[ `&` \bigcap_n U_ n.
have muZ10 : mu Z1 = 0.
  apply/eqP; rewrite -measure_le0/= -muZ0.
  rewrite completed_lebesgue_measureE.
  rewrite /lebesgue_measure/lebesgue_stieltjes_measure/measure_extension mZIU.
  apply: le_outer_measure.
  exact: subIsetr.
have gZ1 : Gdelta Z1.
 exists (fun n => `]a, b[ `&` U_ n).
   by move=> n; apply: openI.
  by rewrite bigcapIr.
have Z1ab : Z1 `<=` `]a, b[.
  exact: subIsetl.
have mFZ1 : measurable (F @` Z1).
  exact: measurable_image_Gdelta_set_nondecreasing_fun Z1ab gZ1.
have FZ1oo : (mu (F @` Z1) < +oo)%E.
  apply: (@le_lt_trans _ _ (mu (F @` `]a, b[))).
    apply: le_outer_measure.
    exact: image_subset.
  apply: (@le_lt_trans _ _ (mu `[F a, F b])).
    apply: le_outer_measure.
    apply: continuous_nondecreasing_image_itvoo => //.
    by move=> ? ? ? ?; apply: ndF; exact: subset_itv_oo_cc.
  rewrite completed_lebesgue_measure_itv.
  by case: ifP=> //; rewrite -EFinB ltry.
have ZabZ1 : Z `\ a `\ b `<=` Z1.
  rewrite subsetI; split.
  - rewrite -(setIidr Zab).
    rewrite -setU1itv ?bnd_simp ?ltW//.
    rewrite setIUl setDUl.
    rewrite setIC -setIDA setDv setI0 set0U.
    rewrite -setUitv1 ?bnd_simp ?ltW//.
    rewrite setIUl 2!setDUl -2!setIDA.
    rewrite -setIDA (setIC [set b]) -setIDA setDv setI0 setU0.
    exact: subIsetl.
  - apply: sub_bigcap => n _.
    apply: subset_trans (ZU n).
    rewrite setDDl.
    exact: subDsetl.
have FZ10 : (0 < mu (F @` Z1))%E.
  apply: (@lt_le_trans _ _ (mu (F @` (Z `\ a `\ b)))).
    by rewrite 2!measure_image_setD_set1.
  apply: le_outer_measure.
  exact: image_subset.
set e := fine (mu (F @` Z1)) / 2.
have e0 : 0 < e by rewrite divr_gt0 ?fine_gt0 ?FZ1oo ?FZ10.
set FZ1' := ((F @` Z1) `\` preimages_gt1 `[a, b] [set: R] F).
set e' := fine (mu FZ1') / 2.
have mpreF0 : mu ([set F x | x in Z1] `&` preimages_gt1 `[a, b] [set: R] F) = 0.
  apply: countable_lebesgue_measure0.
  apply: (@sub_countable _ _ _ (preimages_gt1 `[a, b] [set: R] F)).
    apply: subset_card_le.
    exact: subIsetr.
  exact: is_countable_preimages_gt1_nondecreasing_fun.
have e'0 : 0 < e'.
  rewrite /e' measureD//=; last 2 first.
  - exact: sub_caratheodory.
  - apply: sub_caratheodory.
    apply: countable_measurable => //.
    exact: is_countable_preimages_gt1_nondecreasing_fun.
  rewrite mpreF0 sube0.
  exact: e0.
have FZ1'oo : (mu FZ1' < +oo)%E.
  apply: le_lt_trans FZ1oo.
  apply: le_outer_measure.
  exact: subIsetl.
have mFZ1' : measurable FZ1'.
  apply: measurableI => //.
  apply: measurableC.
  apply: countable_measurable => //.
  exact: is_countable_preimages_gt1_nondecreasing_fun.
have [K [cK KFZ1' FZ1'Ke']] := lebesgue_regularity_inner mFZ1' FZ1'oo e'0.
set K1 := `[a, b] `&` F @^-1` K.
have K1K : F @` K1 = K.
  rewrite eqEsubset; split.
    apply: (subset_trans sub_image_setI).
    apply: subIset; right.
    exact: image_preimage_subset.
  move=> r Kr/=.
  pose L := `[a, b] `&` preimage F [set r].
  have L0 : L !=set0.
    have [] := @IVT _ _ _ _ r (ltW ab) cF.
      have Fab : F a <= F b.
        apply: ndF => //.
        - by rewrite boundl_in_itv bnd_simp ltW.
        - by rewrite boundr_in_itv bnd_simp ltW.
        - exact: ltW.
      rewrite minEle Fab.
      rewrite maxEle Fab.
      move: Kr=> /KFZ1'.
      case=> -[t [/= tab _] <-] _.
      rewrite 2?ndF//.
      - exact: subset_itv_oo_cc.
      - by rewrite boundr_in_itv ?bnd_simp ?ltW.
      - by apply/ltW; move: tab; rewrite in_itv/= => /andP[].
      - by rewrite boundl_in_itv ?bnd_simp ?ltW.
      - exact: subset_itv_oo_cc.
      - by apply/ltW; move: tab; rewrite in_itv/= => /andP[].
    by move=> x xab; rewrite /L; move <-; exists x.
  move: (L0) => [r'] /[dup] Lr'.
  rewrite /L/= => [[r'ab Fr'r]].
  exists r' => //.
  rewrite /K1/=; split => //.
  by rewrite Fr'r.
have : (0 < mu (F @` K1))%E.
  rewrite K1K.
  have := FZ1'Ke'.
  rewrite measureD//; last exact: compact_measurable.
  rewrite setIidr//.
  rewrite lteBlDl; last first.
    rewrite ge0_fin_numE//.
    apply: le_lt_trans FZ1'oo.
    exact: le_outer_measure.
  rewrite -lteBlDr//.
  rewrite completed_lebesgue_measureE.
  apply: le_lt_trans.
  rewrite sube_ge0// /e EFinM fineK; last by rewrite ge0_fin_numE.
  rewrite muleC gee_pMl//.
  rewrite lee_fin invf_le1//.
  by rewrite -[leLHS](mulr1n 1) ler_nat.
apply/negP.
rewrite -leNgt.
rewrite measure_le0/=.
apply/eqP.
apply: HZ.
- exact: subIsetl.
- rewrite /K1 setIC -(setIid `[a, b]%classic) setICA.
  apply: compact_closedI; first exact: segment_compact.
  rewrite closed_setIS; last exact: itv_closed.
  apply: ((@continuous_closedP (subspace `[a, b]) _ F).1 cF).
  exact: compact_closed cK.
- apply/eqP; rewrite -measure_le0/=.
  rewrite -muZ10.
  apply: le_outer_measure.
  apply: (@subset_trans _ (`[a, b] `&` F @^-1` FZ1')).
    apply: setIS.
    exact: preimage_subset.
  rewrite /FZ1' setDE.
  rewrite [X in X `<=` _](_: _
    = Z1 `\` (F @^-1` preimages_gt1 `[a, b] [set: R] F)); last first.
    rewrite eqEsubset; split.
    - move=> x/= [xab [[x' Z1x' Fx'Fx ]]].
      (* lemma? *)
      rewrite /preimages_gt1.
      rewrite not_andE notE orNp => /(_ Logic.I) sub1Fx.
      split => //.
      rewrite (sub1Fx x x')//.
      split => //.
      rewrite /=.
      apply: subset_itv_oo_cc.
      exact: Z1ab.
    - move=> x/= [Z1x].
      (* lemma? *)
      rewrite /preimages_gt1.
      rewrite not_andE notE orNp => /(_ Logic.I) sub1Fx.
      split => //.
        apply: subset_itv_oo_cc.
        exact: Z1ab.
      split => //.
      by exists x.
  exact: subDsetl.
Qed.

End main_lemma.

End lemma3.
