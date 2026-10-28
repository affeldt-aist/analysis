From HB Require Import structures.
From mathcomp Require Import boot order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean.
From mathcomp Require Import unstable.
From mathcomp Require Import boolp contra classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype derive.
From mathcomp Require Import sequences measure numfun realfun.
From mathcomp Require Import bz_mathcomp_extra.
From mathcomp Require Import absolute_continuity merge_extra mesh
  variation_extra oscillation.

(* only for right_continuous and right_continuousW *)
From mathcomp Require Import lebesgue_measure.

(**md**************************************************************************)
(* # Banach–Zarecki Theorem (lemma 5)                                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.


(*
  transitive leT -> irreflexive leT -> forall [s : seq T], sorted leT s -> uniq s
lt_sorted_uniq_le:
  forall {disp : Order.disp_t} {T : porderType disp} (s : seq T),
  uniq s -> sorted <%O s = sorted <=%O s
*)

Section merge_lt_seq_lemmas.
Context {R : realDomainType}.
Implicit Types (l s : seq R).

Lemma merge_lt_seq0r s : merge_lt_seq [::] s = s.
Proof.
elim: s => //= a s IH; by rewrite IH.
Qed.

End merge_lt_seq_lemmas.

Section itv_partition_order.
Context {d} {T : orderType d}.
Implicit Types (a b x : T) (s : seq T).

Lemma lt_merge_min s x : all (<%O x) s -> merge <%O s [:: x] = x :: s.
Proof.
case: s => // s0 s1 /= /andP[xs0 xs1].
by rewrite ltNge (ltW xs0)/=.
Qed.

Lemma merge1_max r s x :
   all (r ^~ x) s ->
   merge r s [:: x] = rcons s x.
Proof.
elim: s x => // s0 s1 /= ih x s0s1.
destruct s1 as [|s1 s2].
  by move/andP: s0s1 => [-> _].
case: ifPn.
  rewrite ih//.
  by have/andP[] := s0s1.
move/negP.
by have/andP[] := s0s1.
Qed.

End itv_partition_order.

(* if the new point falls into the interval between x_k and x_{k+1}, the
  increase in the sum V due to this point is not greater than twice the
  oscillation w_k of the function f(x) on the segment [x_k, x_{k+1}] *)
Section twice.
Context {R : realType}.
Implicit Types (a b : R) (f : R -> R).
Implicit Types (s : seq R) (x : R).

Lemma itvcc_max_sup a b f : a <= b ->
  {within `[a, b], continuous f} ->
  forall c, c \in `[a, b] ->
   (f c = sup (f @` `[a, b]) <-> (forall x, x \in `[a, b] -> f x <= f c)).
Proof.
move=> ab cf c cab; split => H.
- have [d dab dmax] := EVT_max ab cf.
  move=> x /dmax.
  move/le_trans; apply.
  rewrite H.
  apply: ub_le_sup; last by exists d.
  exists (f d) => _/=[y yab <-].
  exact: dmax.
- apply/eqP; rewrite eq_le; apply/andP; split.
    apply: ub_le_sup => //.
    by exists (f c) => _/=[? ? <-]; exact: H.
  apply: ge_sup; first by exists (f c).
  move=> _/=[? ? <-]; exact: H.
Qed.

Lemma itvcc_min_inf a b f : a <= b ->
  {within `[a, b], continuous f} ->
  forall c, c \in `[a, b] ->
   (f c = inf (f @` `[a, b]) <-> (forall x, x \in `[a, b] -> f c <= f x)).
Proof.
Abort.

Lemma continuous_oscillationE (a b : R) (f : R -> R) :
a < b ->
{within `[a, b], continuous f} ->
exists s : R * R,
  [/\ s.1 != s.2,
  s.1 \in `[a, b], s.2 \in `[a, b],
  (forall t, t \in `[a, b] -> f s.2 <= f t <= f s.1) &
  `|f s.1 - f s.2|%:E = oscillation f `[a, b]].
Proof.
move=> ab cf.
have [d' dab maxd] := EVT_max (ltW ab) cf.
have [e' eab mine] := EVT_min (ltW ab) cf.
have fcst : (f d' = f e') = {in `[a, b], f =1 cst (f a)}.
  apply/propext; split.
  - move=> fdfe x xab.
    apply/eqP; rewrite eq_le; apply/andP; split.
      apply: (le_trans (maxd x xab)).
      rewrite fdfe; apply: mine.
      by rewrite boundl_in_itv bnd_simp/= ltW.
    apply: (le_trans _ (mine x xab)).
    rewrite -fdfe; apply: maxd.
    by rewrite boundl_in_itv bnd_simp/= ltW.
  by move=> H; rewrite H//; apply/esym; rewrite H.
(*
pose e := if f d' == f e' then (a + 2 * b) / 3 else e'.
pose d := if f d' == f e' then (2 * a + b) / 3 else d'.
*)
pose e := if f d' == f e' then a else e'.
pose d := if f d' == f e' then b else d'.

have neq_ed : d != e.
  rewrite /e/d; case: ifPn => [_|H].
    by rewrite neq_lt; apply/orP; right.
(* by right; rewrite ltr_pM2r// 2!mulr_natl 2!mulr2n -addrA [ltRHS]addrCA ltrD2r. *)
  apply/negP; move/eqP => ed.
  have := fcst.
  rewrite propeqE => -[_ /contra_not]; apply.
    exact/eqP.
  by rewrite -fcst ed.
exists (d, e); split => //=.
- move: dab; rewrite in_itv/= => /andP[ae eb].
  by rewrite /d in_itv/=; apply/andP; split; case: ifP => //; rewrite ltW.
- move: eab; rewrite in_itv/= => /andP[ae eb].
  by rewrite /e in_itv/=; apply/andP; split; case: ifP => //; rewrite ltW.
- move=> t tab.
  apply/andP; split; rewrite /d/e; case: ifP => [|_].
  + move/eqP; rewrite fcst => H.
    rewrite H; first by rewrite boundl_in_itv/= bnd_simp ltW.
    by rewrite [leRHS]H.
  + exact: mine.
  + move/eqP; rewrite fcst => H.
    rewrite [leRHS]H; first by rewrite boundr_in_itv/= bnd_simp ltW.
    by rewrite H.
  + exact: maxd.
- rewrite /oscillation ifN.
  by apply/neitvP => /=; rewrite bnd_simp ltW.
Abort.


End twice.

Section lt_merge_lemmas.
Context {R : realType}.
Implicit Types (s t r : seq R) (x : R).

Local Notation sorted := (@sorted R <%R).
Local Notation path := (@path R <%R).
Local Notation merge := (@merge R <%R).

Definition udmerge s t := (undup (merge s t)).

Let lt_pathNmem x s : path x s -> x \notin s.
Proof.
move/lt_path_min/allP => ltxs.
apply/negP => xs.
have := ltxs x xs.
by rewrite ltxx.
Qed.

Lemma merge_cons s t x :
  path x t -> merge s (x :: t) = merge (merge s [:: x]) t.
Proof.
move=> xt.
elim: s x t xt => [x t xt|s0 s1 ih x t xt].
  by rewrite /= merger_cons// order_path_min//; exact: lt_trans.
rewrite /=.
rewrite -/(merge (s0 :: s1) t).
case: ifPn => [s0x|].
  rewrite merger_cons//.
    rewrite order_path_min//.
      exact: lt_trans.
    apply: path_le xt => //.
    exact: lt_trans.
  by rewrite ih.
rewrite -leNgt => xs0.
case: t xt xs0 => [//|t0 t1 xt xs0].
rewrite /=.
rewrite -/(merge (s0 :: s1) t1).
rewrite -/(merge (x :: s0 :: s1) t1).
case: ifPn => [s0t0|].
  by rewrite (le_lt_trans xs0).
rewrite -leNgt => t0s0.
by move: xt => /= /andP[->].
Qed.

End lt_merge_lemmas.

Section variation_merge_omega_max.
Context {R : realType}.
Variables (a b : R) (f : R -> R).
Hypothesis ab : a < b.
Hypothesis cf : {within `[a, b], continuous f}.
Implicit Types (s : seq R) (x : R).

Lemma variation_merge1_omega_max s : itv_partition a b s ->
  forall x, x \in `[a, b] ->
    ((variation a b f (merge <%R s [:: x]))%:E <=
       (variation a b f s)%:E + 2 * omega_max a s f)%E.
Proof.
move=> abs.
case: (abs) => pas lsb x.
have [xs|xs] := boolP (x \in s).
  move=> _.
  rewrite in_variation_merge1// leeDl// mule_ge0// omega_max_ge0//.
  rewrite -size_eq0 -lt0n.
  by move: xs; rewrite -index_mem; exact: leq_trans.
rewrite in_itv/= => /andP[].
rewrite le_eqVlt => /predU1P[ax|ax].
  rewrite le_eqVlt => /predU1P[xb|xb].
    by move: ab; rewrite ax xb ltxx.
  subst x.
  rewrite lt_merge_min.
   by move/order_path_min : pas => /(_ lt_trans).
   rewrite variationxx leeDl// mule_ge0// omega_max_ge0//.
   destruct s => //.
   move/eqP : lsb xb => /= ->.
   by rewrite ltxx.
rewrite le_eqVlt => /predU1P[xb|xb].
  subst x.
  have bs := last_mem_itv_partition abs ab.
  by move/negP in xs.
have := @variation_merge1_oscillation R a b f s cf abs x.
rewrite in_itv/= ax xb => /(_ isT xs).
have := @itv_partition_notin_inbetween _ a b s x abs xs.
rewrite ax xb => /(_ isT)[k ks xk].
move/(_ k ks xk)/le_trans; apply.
rewrite leeD2l//.
rewrite lee_pmul ?oscillation_ge0//.
rewrite /omega_max.
rewrite (set_nth_default 0 b)/=.
  by rewrite (leq_trans ks).
rewrite (set_nth_default 0 b)//=.
pose h := fun k => oscillation f `[(a :: s)`_k, s`_k].
apply: (le_bigmax_seq -oo%E k xpredT h) => //.
by rewrite mem_index_iota ks.
Qed.

End variation_merge_omega_max.

Section variation_merge.
Context {R : realType}.
Implicit Type (f : R -> R).
Implicit Types (s : seq R) (x : R).

Lemma merge_filter_undup_alter (s t : seq R) :
  sorted <%R t ->  sorted <%R s ->
  merge <%R s [seq x <- t | [pred x | x \notin s] x] = undup (merge <%R s t).
Proof.
elim: t s => //=.
  move=> s _.
  rewrite merge0r => sorteds.
  rewrite undup_id//.
  apply: sorted_uniq sorteds.
  exact: lt_trans.
  exact: ltxx.
move=> t0 t1 ih s.
elim: s t0 t1 ih => [t0 t1 ih t0t1 /= _|].
  rewrite ifN//.
    move/order_path_min : t0t1 => /(_ lt_trans)/allP t0t1.
    apply/negP => /t0t1.
    by rewrite ltxx.
  rewrite filter_predT undup_id//.
  move/path_sorted : t0t1 => /sorted_uniq; apply.
  exact: lt_trans.
  exact: ltxx.
move=> s0 s1 ih' t0 t1 ih t0t1 sorted_s.
rewrite inE negb_or.
case: ifPn.
  move=> /andP[t0s0 t0s1].
  rewrite /= -!/(merge <%R (s0 :: s1) _).
  have [{}t0s0|] := ltP s0 t0.
    rewrite /=.
    rewrite ifN.
      rewrite mem_merge mem_cat negb_or inE negb_or lt_eqF//=.
      apply/andP; split.
        move: sorted_s => /= => /order_path_min => /(_ lt_trans)/allP H.
        apply/negP => /H.
        by rewrite ltxx.
      move: t0t1 => /= => /order_path_min => /(_ lt_trans)/allP H.
      apply/negP => /H.
      by rewrite ltNge (ltW t0s0).
    congr cons.
    rewrite -ih'//.
    move: sorted_s => /=.
    exact: path_sorted.
    rewrite t0s1//.
    congr merge.
    congr cons.
    apply: eq_in_filter => y yt1.
    rewrite inE negb_or.
    rewrite andb_idl// => ys1.
    move: t0t1 => /= /order_path_min => /(_ lt_trans)/allP => /(_ _ yt1).
    move=> /(lt_trans t0s0) ?.
    by rewrite gt_eqF//.
    rewrite le_eqVlt (negbTE t0s0)/= => {}t0s0.
    rewrite ifN.
      rewrite mem_merge mem_cat !inE !negb_or lt_eqF//=.
    apply/andP; split.
      move: sorted_s => /= => /order_path_min => /(_ lt_trans)/allP H.
      apply/negP => /H.
      by rewrite ltNge (ltW t0s0).
    move: t0t1 => /= => /order_path_min => /(_ lt_trans)/allP H.
    apply/negP => /H.
    by rewrite ltxx.
    congr cons.
    apply: ih => //.
    move: t0t1 => /=.
    by move/path_sorted.
rewrite negb_and !negbK => /predU1P[?|].
  subst t0.
  rewrite /=.
  rewrite /= -!/(merge <%R (s0 :: s1) _).
  rewrite ltxx/= ifT.
    by rewrite mem_merge !inE eqxx.
  rewrite ih//.
  move: t0t1 => /=.
  by apply: path_sorted.
move=> t0s1.
rewrite /= -!/(merge <%R (s0 :: s1) _).
rewrite ifT.
  move: sorted_s => /= => /order_path_min => /(_ lt_trans)/allP.
  by apply.
rewrite /=.
rewrite ifN.
  rewrite mem_merge mem_cat negb_or !inE negb_or.
  apply/and3P; split.
  move: sorted_s => /= => /order_path_min => /(_ lt_trans)/allP H.
  apply/negP => /H.
  by rewrite ltxx.
  rewrite lt_eqF//.
  move: sorted_s => /= => /order_path_min => /(_ lt_trans)/allP.
  exact.
  apply/negP => H.
  move: t0t1 => /order_path_min => /(_ lt_trans)/allP => /(_ _ H) t0s0.
  move: sorted_s => /= => /order_path_min => /(_ lt_trans)/allP => /(_ _ t0s1).
  by rewrite ltNge (ltW t0s0).
rewrite ih//.
  by move: t0t1 => /=; exact: path_sorted.
  transitivity (s0 :: undup (merge <%R s1 t1)).
    rewrite merger_cons//=; last first.
      rewrite mem_merge mem_cat ifN//.
      rewrite negb_or; apply/andP; split.
        move: sorted_s => /= /order_path_min => /(_ lt_trans)/allP H.
        apply/negP => /H.
        by rewrite ltxx.
      move: t0t1 => /= /order_path_min => /(_ lt_trans)/allP H.
      apply/negP => /H => t0s0.
      move: sorted_s => /= /order_path_min => /(_ lt_trans)/allP.
      move/(_ _ t0s1).
      by rewrite ltNge (ltW t0s0).
    apply/allP => x xt1.
    move: sorted_s => /= /order_path_min => /(_ lt_trans)/allP.
    move/(_ _ t0s1) => /lt_le_trans; apply.
    move: t0t1 => /= /order_path_min => /(_ lt_trans)/allP /(_ _ xt1).
    by move/ltW.
congr cons.
rewrite -ih//.
by move: t0t1 => /=; apply: path_sorted.
by move: sorted_s => /=; apply: path_sorted.
rewrite -ih'//.
by move: sorted_s => /=; apply: path_sorted.
rewrite t0s1//=.
Qed.

(* TODO: generalize *)
Lemma lt_merge_lrcons (s t : seq R) (b : R) :
   all (<=%R ^~ b) t -> merge <%R (rcons s b) t = rcons (merge <%R s t) b.
Proof.
elim: t s b; first by move=> ? ?; rewrite 2!merge0r.
move=> + + + s; elim: s => [t0 t1 IH b|s0 s1 IHs t0 t1 IHt b].
  rewrite [all _ _]/= [rcons _ _]/= [merge _ [::] _]/= => /andP[t0b t1b].
  rewrite merge_step ifN; first by rewrite -leNgt.
  have -> : [:: b] = rcons [::] b by []; by rewrite IH.
rewrite [all _ _]/= => /andP[t0b t1b].
rewrite rcons_cons 2!merge_step.
case: ifPn; by [rewrite IHs//= t0b t1b|rewrite -rcons_cons IHt].
Qed.

Lemma all_ge_merge1r (t : seq R) (b : R) :
all (<=%R ^~ b) t -> merge <=%R t [:: b] = rcons t b.
Proof.
elim: t => //.
move=> t0 t1 IH /=/andP[t0b t1b]/=.
by rewrite ifT ?IH.
Qed.

Lemma all_gt_merge1r (t : seq R) (b : R) :
all (<%R ^~ b) t -> merge <%R t [:: b] = rcons t b.
Proof.
elim: t => //.
move=> t0 t1 IH /=/andP[t0b t1b]/=.
by rewrite ifT ?IH.
Qed.

(* TODO: generalize *)
Lemma merge_rcons_step (s0: seq R) (s1 : R) (t0 : seq R) (t1 : R) :
  sorted <=%R (rcons s0 s1) -> sorted <=%R (rcons t0 t1) ->
  merge <%R (rcons s0 s1) (rcons t0 t1) =
  if s1 < t1 then (merge <%R (rcons s0 s1) t0) ++ [:: t1]
             else (merge <%R s0 (rcons t0 t1)) ++ [:: s1].
Proof.
elim/last_ind : t0 s0 => //=.
  move=> s0 // ss0 _.
  case: ifPn => [s1t1|].
  - rewrite merge0r.
    rewrite merge_ltEle//.
    rewrite all_ge_merge1r//; last by rewrite cats1.
    apply/allP => x.
    rewrite mem_rcons in_cons => /predU1P[->|xs0]; first exact: ltW.
    apply/ltW/(le_lt_trans _ s1t1).
    have := ss0.
    rewrite sorted_rconsE/=; first exact: le_trans.
    by move/andP => [_ /allP]; exact.
  - rewrite -leNgt le_eqVlt => /predU1P[t1s1|t1s1].
      subst t1.
      rewrite 2?merge_ltEle//.
        rewrite le_sorted_rconsE in ss0.
        by have/andP[] := ss0.
      rewrite 2?allrel_merge ?cats1//; last first.
        rewrite allrel1r; apply/allP => x xs0.
        by have := ss0; rewrite le_sorted_rconsE => /andP[_ /allP]; exact.
      rewrite allrel1r; apply/allP => x.
      rewrite mem_rcons in_cons => /predU1P[->//|].
      by have := ss0; rewrite le_sorted_rconsE => /andP[_ /allP]; exact.
    rewrite cats1.
    admit.
Abort.

End variation_merge.

Lemma mem_interval_le (R : realDomainType) (x y a b : R) :
  x \in `[a, b] -> y \in `[a, b] -> `|x - y| <= `|a - b|.
Proof.
rewrite !in_itv/= => /andP[ax xb] /andP[ay yb].
rewrite (@ler0_norm _ (a - b)); first by rewrite subr_le0 (le_trans ax).
rewrite opprB.
have [xy|yx] := leP x y.
  by rewrite ler0_norm ?subr_le0// opprB lerB.
by rewrite gtr0_norm ?subr_gt0// lerB.
Qed.

Section ene5.
Context {R : realType} (a b : R) (f : R -> R).
Hypothesis (ab : a < b).
Hypothesis cf : {within `[a, b], continuous f}.
Implicit Types (s : seq R) (x : R).

Lemma le_sorted_lt_sorted_undup (s : seq R) :
  sorted <=%R s -> sorted <%R (undup s).
Proof.
move=> ss.
rewrite lt_sorted_uniq_le; apply/andP; split; first exact: undup_uniq.
apply: undup_sorted => //.
exact: le_trans.
Qed.

Lemma mesh_variation (A : R) :
  (0 <= A%:E < total_variation a b f)%E ->
  exists2 delta, 0 < delta &
    (forall p, itv_partition a b p -> mesh a p < delta ->
      A < variation a b f p).
Proof.
rewrite lee_fin => /andP[A0].
move/ereal_sup_gt => [_ /=[Vstar [xstar dxstar vVstar] <-]].
rewrite lte_fin => AVstar.
have /unif_continuousP/= : @unif_continuous (subspace `[a, b]) R f.
  by apply/heine_cantor_subspace => //; exact: segment_compact.
pose m := size xstar.
have mE : m = size xstar by [].
pose eps := (Vstar - A) / (4 * m)%:R.
have epsE : eps = (Vstar - A) / (4 * m)%:R by [].
have eps0 : 0 < eps.
  rewrite divr_gt0//; first by rewrite subr_gt0.
  rewrite natrM mulr_gt0// ltr0n mE.
  exact: (itv_partitionNnil ab dxstar).
move/(_ _ eps0) => [d d0 unifcf].
exists d => // sI dsI abpd. (* NB: sI is (I) in Natanson *)
apply: (@lt_le_trans _ _ ((Vstar + A) / 2)).
  rewrite ltr_pdivlMr//.
  rewrite -ltrBlDr -{2}(mulr1 A) -mulrBr.
  by rewrite -{2}(mulr1n 1) -natrB// subSnn mulr1.
pose V0 : R := variation a b f (merge <%R sI xstar).
have sxstar : sorted <=%R xstar by have [/path_sorted/sorted_ltW] := dxstar.
have ssI : sorted <=%R sI by have [/path_sorted/sorted_ltW] := dsI.
apply: (@le_trans _ _ (V0 - (Vstar - A) / 2)).
  rewrite [leRHS](_ : _ = V0 - Vstar + (Vstar + A) / 2).
    rewrite -[in LHS](@subrK _ Vstar V0) -(addrA (V0 - Vstar)); congr +%R.
    rewrite -mulNr opprD opprK 2!mulrDl addrA; congr +%R.
    rewrite -{1}(@mulfK _ 2 _ Vstar)// mulrDr mulr1.
    by rewrite mulrDl mulNr addrK.
  rewrite lerDr subr_ge0 -vVstar.
  rewrite sorted_variation_subseq//.
    by rewrite merge_ltEle// merge_sorted//; exact: le_total.
  rewrite (subseq_merger _ lt_trans)//.
  exact: itv_partition_sorted dxstar.
rewrite lerBlDr -lee_fin EFinD.
have sltxstar : sorted <%R xstar by have [/path_sorted] := dxstar.
have V0E : V0 = variation a b f (merge <%R sI xstar) by [].
(* NB: not a genuine induction because we do not use the inductive hypothesis generated *)
elim/last_ind : xstar dxstar vVstar m mE eps epsE eps0 unifcf V0 sxstar V0E sltxstar.
  by move/(itv_partitionNnil ab).
move=> xstar0 xstar1 _.
pose X' := rcons xstar0 xstar1.
have X'E : X' = rcons xstar0 xstar1 by [].
move=> dxstar vVstar m mE eps epsE eps0 unifcf V0 sleX' V0E sltxstar.
have xstar0ab x : x \in xstar0 -> x \in `]a, b[.
  by move=> ?; exact: (itv_partition_head_in_itv dxstar).
have sxstar0 : sorted <%R xstar0.
  by have[/= + _] := dxstar; rewrite rcons_path => /andP[/path_sorted].
have xstar1E : xstar1 = b by have [_] := dxstar; rewrite last_rcons => /eqP ->.
rewrite V0E.
have [_ /eqP pb] := dsI.
(* TODO: this step looks a bit long for what it is *)
rewrite [X in (X%:E <= _)%E](_ : _ = variation a b f (merge <%R sI xstar0)).
  rewrite variation_undup//.
  - rewrite merge_ltEle//.
    apply: merge_path; first exact: le_total.
    + by have [/path_ltW] := dsI.
    + by have [/path_ltW] := dxstar.
  - rewrite (@itv_partition_last_merge _ _ b)//.
      exact: ltW.
    move=> x; rewrite mem_rcons inE => /predU1P[->|].
      by rewrite xstar1E !in_itv/= lexx andbT.
    by move/xstar0ab; exact: subset_itv_oo_oc.
  rewrite [RHS]variation_undup//.
  - rewrite merge_ltEle//; first exact: sorted_ltW.
    apply: merge_path; first exact: le_total.
    + by have [/path_ltW] := dsI.
    + have [/path_ltW] := dxstar.
      by rewrite rcons_path => /andP[].
  - rewrite (@itv_partition_last_merge _ _  _ (ltW ab))//.
    by move=> x /xstar0ab; exact: subset_itv_oo_oc.
  congr (variation a b f).
  apply: lt_sorted_eq => //.
  - apply: le_sorted_lt_sorted_undup.
    rewrite merge_ltEle//.
    by apply: merge_sorted => //; exact: le_total.
  - apply: le_sorted_lt_sorted_undup.
    have ? : sorted <=%R xstar0.
      by have := sleX'; rewrite le_sorted_rconsE => /andP[].
    rewrite merge_ltEle//.
    by apply: merge_sorted => //; exact: le_total.
  have sltsI : sorted <%R sI by exact: itv_partition_sorted dsI.
  rewrite -2?merge_filter_undup//.
  rewrite filter_rcons ifN//.
  rewrite negbK.
  have [_ /eqP] := dxstar; rewrite last_rcons => ->.
  exact: last_mem_itv_partition dsI ab.
have := @variation_merge _ f a b ab sI xstar0 cf dsI sxstar0 xstar0ab.
move/le_trans; apply; apply: leeD2l.
case: xstar0 mE X' X'E dxstar vVstar sleX' V0E sltxstar xstar0ab sxstar0 => //=.
  by move=> _ _ _ _ _ _ _ _; rewrite 2!mul0e lee_fin divr_ge0// subr_ge0 ltW.
move=> X'00 X'01 mE X' X'E partX' X'V' sleX' V0E sorted_X' X'0ab sX'0.
rewrite -lee_pdivlMl.
  by rewrite mulr_gt0.
rewrite (_ : (Vstar - A) / 2 = (m%:R * 2) * eps).
  rewrite epsE.
  rewrite (_ : 4 = 2 * 2)%N//.
  rewrite mulnAC 2!natrM.
  rewrite 2!invfM 2!mulrA.
  congr *%R.
  rewrite mulrA.
  rewrite -(mulrA m%:R 2).
  rewrite -(mulrA m%:R (2 * (Vstar - A))).
  rewrite mulrC.
  rewrite (mulrA m%:R^-1).
  rewrite mulVf ?mul1r.
    by rewrite gt_eqF// ltr0n mE.
  by rewrite mulrAC divff// mul1r.
rewrite /omega_max.
rewrite big_nat_cond.
apply: bigmax_le; first by rewrite leNye.
move=> n.
rewrite leq0n/= andbT => np.
rewrite /oscillation/=.
rewrite -image_comp.
have : compact (f @` `[(a :: sI)`_n, sI`_n]).
  apply: continuous_compact; last exact: segment_compact.
  apply: continuous_subspaceW cf.
  apply: subset_itv; rewrite bnd_simp//.
    case: n => //= ? in np *.
    rewrite (set_nth_default b 0) ?(leq_trans _ np)//.
    exact/ltW/(itv_partition_gt_lb _ dsI).
  exact: (itv_partition_le_ub _ dsI).
rewrite Rcompact_boundE/= => -[cimg ubimg lbimg].
have nonempty_img : [set f x | x in `[(a :: sI)`_n, sI`_n]] !=set0.
  exists (f ((a :: sI)`_n)),  ((a :: sI)`_n) => //=.
  rewrite boundl_in_itv/= bnd_simp.
  apply/ltW/pathP => //.
  by have [] := dsI.
rewrite ereal_sup_EFin// ereal_inf_EFin//.
rewrite ifN.
  move/set0P : nonempty_img; apply: contra_neq => ->.
  by rewrite image_set0.
rewrite -EFinB lee_fin.
have : forall x y, x \in `[(a :: sI)`_n, sI`_n] ->
    y \in `[(a :: sI)`_n, sI`_n] -> `|f x - f y| < eps.
  move=> x y Hx Hy.
  have @x' : subspace `[a, b] by exact: x.
  have @y' : subspace `[a, b] by exact: y.
  have := unifcf (x', y').
  rewrite /=/ball/=.
  apply.
  rewrite /subspace_ball.
  rewrite ifT.
    rewrite inE/=.
    apply: subset_itv Hx; rewrite bnd_simp.
      case: n cimg ubimg lbimg nonempty_img Hy => //=n _ _ _ _ _ in np *.
      rewrite (set_nth_default b 0) ?(leq_trans _ np)//.
      exact/ltW/(itv_partition_gt_lb _ dsI).
    exact: (itv_partition_le_ub _ dsI).
  rewrite /=; split.
    apply: subset_itv Hy; rewrite bnd_simp.
      case: n cimg ubimg lbimg nonempty_img Hx => //=n _ _ _ _ _ in np *.
      rewrite (set_nth_default b 0) ?(leq_trans _ np)//.
      exact/ltW/(itv_partition_gt_lb _ dsI).
    exact: (itv_partition_le_ub _ dsI).
  rewrite /ball/=.
  apply: (@le_lt_trans _ _ `|sI`_n - (a :: sI)`_n|).
    rewrite [in leRHS]distrC.
    exact: mem_interval_le.
  apply: le_lt_trans abpd.
  apply: (@le_trans _ _ (\big[maxr/0]_(0 <= i < size sI)
      `|sI`_i - (a :: sI)`_i|)); last first.
    by rewrite /mesh/= -bigmaxr_morph.
  apply: (le_bigmax_seq _ _ _ (fun=> _)) => //.
  by rewrite mem_index_iota leq0n.
move=> H.
rewrite lerBlDl; apply: ge_sup => //.
move=> _/= [x px <-].
rewrite -lerBlDr.
apply: lb_le_inf => // _/=[x' px' <-].
rewrite lerBlDr -lerBlDl.
apply: (@le_trans _ _ `|f x - f x'|); first exact: ler_norm.
rewrite 2!mulrA -[leLHS]mul1r.
  apply: ler_pM => //.
  rewrite -mulrA mulrC.
  rewrite -mulf_div divff// mulr1.
  rewrite ler_pdivlMr// mul1r mE.
  by rewrite ler_nat size_rcons.
exact/ltW/H.
Qed.

Definition variations_with_max a b f l : set R :=
   [set r| exists s, [/\ r = variation a b f s,
 itv_partition a b s & (mesh a s <= l)%R]].

Local Definition lambda_partition (a b : R) (lambda : R) :=
  let n := `|ceil ((b - a) / lambda)|%N in
  [seq (a + (b - a) * i.+1%:R / n%:R) | i <- iota 0 n].

Lemma mesh_lambda x :
  mesh a (lambda_partition a b x) =
     (b - a) / `|ceil ((b - a) / x)|%N%:R.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite /mesh/=.
  (* apply: bigmax_le. *)
  admit.
Abort.

Lemma itv_partition_lambda x : itv_partition a b (lambda_partition a b x).
Proof.
Abort.

Let divr_ceil_le x : (b - a) / `|ceil ((b - a) / x)|%:R <= x.
Proof.
Abort.

Lemma variations_with_max_lambda x :
   variations_with_max a b f x (variation a b f (lambda_partition a b x)).
Proof.
Abort.
(*
exists (lambda_partition a b x); split => //; first exact: itv_partition_lambda.
rewrite itv_partition_max_lambda.
exact: divr_ceil_le.
Qed.
*)
Lemma total_variation_ex :
  bounded_variation a b f ->
  exists2 p, itv_partition a b p &
       (variation a b f p)%:E = total_variation a b f.
Proof.
Abort.

Lemma variation_with_max0E :
  \forall l \near 0^'+,
  variations_with_max a b f l =
  variations a b f.
Proof.
near=> l.
rewrite eqEsubset; split => A; first by move=> [p [-> pabp _]]; exists p.
move=> [p pabp <-]; exists p; split => //.
apply/eqP; rewrite eq_le; apply/andP; split.
rewrite /total_variation.
Abort.

Definition variations_with_restr a b f l : set R :=
   [set r| exists s, [/\ r = variation a b f s,
 itv_partition a b s & (l <= mesh a s)%R]].

Lemma variation_with_restr0E l : l <= 0 ->
  variations_with_restr a b f l = variations a b f.
Proof.
move=> l0.
rewrite eqEsubset; split => A; first by move=> [p [? ? _]]; exists p.
move=> [p pabp vA].
exists p; split => //.
apply: (le_trans l0).
exact: mesh_ge0.
Abort.

Lemma lemma5_sup :
  ereal_sup
     [set v%:E | v in variations_with_restr a b f l] @[l --> 0^'+]
     --> total_variation a b f.
Proof.
have -> : total_variation a b f =
   ereal_sup [set v%:E | v in variations_with_restr a b f 0].
  admit.
apply: right_continuousW.
move=> U.
have := (@near_cst_continuous _ _ (total_variation a b f)
  (fun l : R => ereal_sup [set v%:E | v in variations_with_restr a b f l]) 0).
Abort.

Lemma variations_with_max_restr :
\forall l \near 0^'+,
  (ereal_inf
     [set v%:E | v in variations_with_max a b f l]
  <= ereal_sup
     [set v%:E | v in variations_with_restr a b f l])%E.
Proof.
near=> l.
apply: le_ereal_sup_tmp.
exists (total_variation a b f).
Abort.

Lemma ene5 (l : R^nat) (s : (seq R)^nat) :
  (forall n, itv_partition a b (s n)) ->
  (forall n, mesh a (s n) <= l n) ->
  l i @[i --> \oo] --> 0 ->
  (variation a b f (s n))%:E @[n --> \oo] --> total_variation a b f.
Proof.
move=> pabx xl lcvg0.
have vletv n : ((variation a b f (s n))%:E <= total_variation a b f)%E.
  apply: le_ereal_sup_tmp.
  exists (variation a b f (s n))%:E => //=.
  exists (variation a b f (s n))=> //.
  by exists (s n).
have := total_variation_ge0 f (ltW ab).
rewrite le_eqVlt => /predU1P[tvf0|tvfgt0].
  apply: cvg_near_cst; apply: nearW => n.
  apply/eqP; rewrite eq_le; apply/andP; split => //.
  by rewrite -tvf0; exact: variation_ge0.
have [tvfoo|] := eqVneq (total_variation a b f) +oo%E.
  rewrite tvfoo.
  move=> /= U; rewrite /nbhs/= => -[A [_ HA]].
  have [A0|A0] := ltP A 0.
    exists 0%N => // k/= => _; apply: HA.
    by rewrite (@lt_le_trans _ _ 0%E)// lee_fin variation_ge0.
  have : (0 <= A%:E < total_variation a b f)%E.
    by rewrite lee_fin A0 tvfoo ltry.
  move/mesh_variation => /= [e e0].
  have lne : \forall n \near \oo, l n < e.
    move: lcvg0.
    move/(cvgr_dist_lt _ 0) /(_ e e0).
    under eq_near => n.
      rewrite sub0r normrN ger0_norm.
        by rewrite (le_trans _ (xl _))// mesh_ge0.
      over.
    by [].
  have mxe : \forall n \near \oo, mesh a (s n) < e.
    by apply: filterS lne => n; exact: le_lt_trans.
  move=> abA.
  apply: filterS mxe => n /abA - /(_ (pabx n)).
  by rewrite -lte_fin => /HA.
rewrite -ltey => tvfltey.
have tvf_fin : total_variation a b f \is a fin_num.
  by rewrite ge0_fin_numE // (total_variation_ge0 _ (ltW ab)).
rewrite -(@fineK _ (total_variation a b f))//; apply/fine_cvgP.
split; first exact: nearW.
apply/cvgrPdist_ltp; near=> e.
have : (0%:E <= (fine (total_variation a b f) - e)%:E < total_variation a b f)%E.
  apply/andP; split; rewrite ?lee_fin.
    rewrite subr_ge0.
    near: e; apply: nbhs_right_le.
    by rewrite fine_gt0// tvfgt0.
  by rewrite EFinB fineK// gte_subl// lte_fin.
move/mesh_variation => [/= d d0 Hd].
near=> n.
rewrite ger0_norm; first by rewrite subr_ge0 -lee_fin !fineK.
rewrite ltrBlDl -ltrBlDr/=.
apply: Hd => //.
apply: (le_lt_trans (xl n)).
near: n.
exact: (cvgr_lt _ lcvg0 _ d0).
Unshelve. all: end_near. Qed.

End ene5.

Section lemma5_le.
Context {R : realType}.
Implicit Types (a b c : R) (f : R -> R) (s : seq R).

Lemma variation_itv_partitionLR_new a b c f s :
  sorted <=%R s ->
  variation a b f s <=
  variation a b f (itv_partitionL s c ++ itv_partitionR s c).
Proof.
elim: s a.
  move=> a.
  by rewrite variation_nil variation_ge0.
move=> s0 s1 IH a sorted_s.
have [cs0|]:= ltP c s0.
  admit.
rewrite le_eqVlt => /predU1P[|].
  move=> ->.
  rewrite /itv_partitionL/=.
  rewrite ltxx.
(*
  rewrite 
rewrite ifF; first by apply/negP/negP; rewrite -leNgt.
  have -> : [seq y <- s1 | y < c] = [::].
    rewrite (@eq_in_filter _ _ xpred0) ?filter_pred0 // => y ys/=.
    apply: le_gtF.
    apply: (le_trans cs0).
    have/le_path_min/allP := sorted_s.
    exact.
    case: ifP => /=.
      move=> _.
      rewrite /variation/=.
      rewrite !big_nat_recl//.
      rewrite addrA lerD//.
        admit.
      rewrite -/(variation _ _ _ _).
      apply: (le_trans (IH _ _)).
        by have/=/path_sorted := sorted_s.
      rewrite (@variation_cat _ c).
      exact: le_variation.
    move/negP/negP.
    by move: cs0; rewrite le_eqVlt => /predU1P[-> _|->//].
  move=> s1 s2 IH0 IH1.
    

  move: cs0; rewrite le_eqVlt => /predU1P[|].
    move=> ->; rewrite ltxx.
    have -> : itv_partitionR s1 s0 = s1.
      rewrite /itv_partitionR.
      rewrite (@eq_in_filter _ _ xpredT) ?filter_predT// => y ys.
  rewrite variation_cons.
  rewrite /itv_partitionL/=.
  rewrite L0.
  rewrite /=.



have RT : c < x -> [seq y <- s | c < y] = s.
  move=> cx; apply/all_filterP/allP => y ys.
  have xy := allP (order_path_min le_trans ss) y ys.
  exact: lt_le_trans cx xy.
have [xc|cx|eqxc] := ltgtP x c.
- rewrite /itv_partitionL /itv_partitionR /= xc (le_gtF (ltW xc)) /=.
  rewrite !variation_consE lerD2l; exact: IH st.
- rewrite /itv_partitionL /itv_partitionR /= (le_gtF (ltW cx)) cx.
  rewrite (L0 (ltW cx)) (RT cx) /=.
  exact: le_variation.
- subst x; have h := IH c st.
  rewrite /itv_partitionL /itv_partitionR (L0 (lexx c)) /= in h.
  rewrite variation_consE subrr normr0 add0r in h.
  rewrite /itv_partitionL /itv_partitionR /= !ltxx (L0 (lexx c)) /=.
  by rewrite !variation_consE lerD2l.
Qed.
*)
Abort.

Lemma variation_merge1_oscillation_new a b f s :
  {within `[a, b], continuous f} ->
  path <=%R a s -> last a s = b ->
  forall x, x \in `[a, b] -> x \notin s ->
  forall k, (k < size s)%N ->
    x \in `]nth b (a :: s) k, nth b (a :: s) k.+1[ ->
  ((variation a b f (merge <%R s [:: x]))%:E <=
   (variation a b f s)%:E +
   2 * oscillation f `[nth b (a :: s) k, nth b (a :: s) k.+1])%E.
Proof.
(*
move=> cf pas lsb x xab xs k ks xk.
have : a <= b.
  rewrite -lsb.
  have/le_path_min/allP := pas; apply.
  case: s pas lsb xs ks xk => //.
  by move=> s0 s1 _ _ _  _ _; rewrite last_cons mem_last.
move=> ab.
set s' := merge _ _ _.
apply: (@le_trans _ _ (variation a b f
    (itv_partitionL s' x ++ itv_partitionR s' x))%:E).
  rewrite lee_fin.
  apply: variation_itv_partitionLR.
  by move: xab; rewrite in_itv/= => /andP[].
  by move: xab; rewrite in_itv/= => /andP[].
  exact: itv_partition_merge1.
rewrite (@variation_cat _ x).
  by move: xab; rewrite in_itv/= => /andP[/ltW].
  by move: xab; rewrite in_itv/= => /andP[_ /ltW].
  apply: (@itv_partitionLP _ _ _ b).
  by move: xab; rewrite in_itv/= => /andP[].
  by move: xab; rewrite in_itv/= => /andP[].
  exact: itv_partition_merge1.
  apply: (@itv_partitionRP _ _ a).
  by move: xab; rewrite in_itv/= => /andP[].
  by move: xab; rewrite in_itv/= => /andP[].
  exact: itv_partition_merge1.
have s'E : s' = itv_partitionL s x ++ itv_partitionR s x.
  rewrite /s' merge1E//.
  exact: itv_partition_sorted abs.
set x_k := nth b (a :: s) k.
set x_k1 := nth b (a :: s) k.+1.
have axk : a <= x_k.
  rewrite /x_k.
  destruct k as [|k]; first by [].
  rewrite /=.
  exact/ltW/itv_partition_gt_lb.
have xkx : x_k <= x.
  move: xk.
  rewrite -/x_k.
  by rewrite in_itv/= => /andP[/ltW].
have sa : itv_partitionL s a = [:: a].
  rewrite /itv_partitionL.
  rewrite [X in rcons X _](_ : _ = [::])//.
  rewrite -(filter_pred0 s).
  apply: eq_in_filter => r rs.
  apply/negbTE.
  rewrite -leNgt.
  move/(nthP b) : rs => -[m ms <-{r}].
  apply/ltW.
  by apply/itv_partition_gt_lb.
have K1 : [seq x0 <- itv_partitionR s x | x0 < x] = [::].
  rewrite /itv_partitionR.
  rewrite -filter_predI.
  rewrite -(filter_pred0 s).
  apply: eq_in_filter => r rs/=.
  apply/negbTE/negP => /andP[/lt_trans/[apply]].
  by rewrite ltxx.
move: xk; rewrite -/x_k -/x_k1 in_itv/= => /andP[{}xkx xxk1].
have H1 : variation a x f (itv_partitionL s' x) =
    variation a x_k f (itv_partitionL s x_k)
    + variation x_k x f [:: x].
  destruct k as [|k].
    rewrite /x_k/=.
    rewrite sa.
    rewrite {2}/variation/= big_nat1/= subrr normr0 add0r.
    rename xkx into xa.
    rename xxk1 into xs0.
    have s'x : itv_partitionL s' x = [:: x].
      rewrite /itv_partitionL.
      rewrite [X in rcons X](_ : _ = [::])//.
      rewrite s'E.
      rewrite filter_cat.
    have H1 : [seq x0 <- itv_partitionL s x | x0 < x] = [::].
      rewrite filter_rcons ltxx filter_id.
      case: abs.
      destruct s as [|s0 s1].
        rewrite /= => _ /eqP.
        move: ab => /[swap] ->.
        by rewrite ltxx.
      rewrite [X in X -> _ -> _]/= => /andP[as0].
      move/order_path_min => /(_ lt_trans)/allP s1s0 /eqP ?.
      rewrite -(filter_pred0 (s0 :: s1)).
      rewrite /= in xs0.
      apply: eq_in_filter => r/=.
      rewrite inE => /predU1P[rs0|].
        apply/negbTE/negP => rx.
        rewrite rs0 in rx.
        by rewrite ltNge (ltW xs0) in rx.
      move/s1s0 => s0r.
      apply/negbTE/negP => rx.
      have := lt_trans s0r rx.
      by rewrite ltNge (ltW xs0).
    rewrite H1.
    by rewrite K1.
    by rewrite s'x.
  rewrite -variation_cat.
  by [].
  exact/ltW.
  apply: (@itv_partitionLP _ _ _ b) => //.
    rewrite /x_k /=.
    by apply/itv_partition_gt_lb.
  move: xab; rewrite in_itv/= => /andP[_].
  by apply: le_lt_trans; exact/ltW.
  rewrite /itv_partition/=.
  by rewrite xkx.
  rewrite s'E.
  congr variation.
  rewrite /itv_partitionL.
  rewrite filter_cat rcons_cat filter_rcons ltxx filter_id.
  rewrite -cats1.
  rewrite catA.
  congr cat.
  rewrite K1 cats0.
  rewrite [in LHS](@in_itv_partition _ _ x_k _ (itv_partition_sorted abs)).
    apply/(nthP b).
    rewrite /x_k.
    exists k => //.
    by rewrite (leq_trans _ ks).
  rewrite filter_cat.
  rewrite /itv_partitionL.
  rewrite filter_rcons.
  rewrite xkx.
  have H1 : [seq x0 <- itv_partitionR s x_k | x0 < x] = [::].
    rewrite /itv_partitionR.
    rewrite -filter_predI.
    rewrite -(filter_pred0 s).
    apply: eq_in_filter => r rs/=.
    apply/negbTE/negP => /andP[rx xkr].
    move: rs.
    apply/negP.
    apply: (@itv_partition_inbetween_notin _ _ _ _ _ abs _ k.+1) => //.
    by rewrite -/x_k -/x_k1 in_itv/= xkr/= (lt_le_trans rx)//= ltW.
  rewrite H1 cats0.
  rewrite -filter_predI.
  congr rcons.
  apply: eq_in_filter => r rs/=.
  by rewrite andb_idl// => /lt_trans; exact.
have K2 : [seq x0 <- itv_partitionL s x | x < x0] = [::].
  rewrite /itv_partitionL.
  rewrite filter_rcons ltxx -filter_predI.
  rewrite -(filter_pred0 s).
  apply: eq_in_filter => r sr/=.
  apply/negbTE/negP => /andP[/lt_trans] /[apply].
  by rewrite ltxx.
have H2 : variation x b f (itv_partitionR s' x) =
  variation x x_k1 f [:: x_k1]
  + variation x_k1 b f (itv_partitionR s x_k1).
  rewrite -variation_cat.
    exact: ltW.
    by apply: (itv_partition_le_ub abs).
    rewrite /itv_partition/=.
    by rewrite xxk1.
    move: ks.
    rewrite leq_eqVlt => /predU1P[k1s|k1s].
      have xk1b : x_k1 = b.
        rewrite /x_k1 k1s.
        rewrite nth_last/=.
        by case: abs => _ /eqP.
      have sxk1 : itv_partitionR s x_k1 = [::].
        rewrite -(filter_pred0 s) /itv_partitionR.
        rewrite xk1b.
        apply: eq_in_filter => r rs.
        apply/negbTE.
        rewrite -leNgt.
        move/(nthP b) : rs => [m ms <-].
        by apply: (itv_partition_le_ub abs).
      by rewrite sxk1 /itv_partition xk1b/=.
    apply: (@itv_partitionRP _ _ a) => //.
      by rewrite (le_lt_trans axk)// (lt_trans xkx).
    rewrite /x_k1.
    destruct s as [|s0 s1] => //.
    rewrite (@lt_le_trans _ _ (nth b [:: a, s0 & s1] k.+2))//.
      case: abs => /pathP /[swap]/eqP asb.
      by apply => //.
    by move/itv_partition_le_ub : abs => /(_ k.+1)/=.
  congr variation.
  rewrite s'E.
  rewrite [LHS]filter_cat.
  rewrite K2/= /itv_partitionR filter_id.
  rewrite [in LHS](@in_itv_partition _ _ x_k1 _ (itv_partition_sorted abs)).
    by apply/(nthP b); exists k.
  rewrite filter_cat.
  have -> : [seq x0 <- itv_partitionL s x_k1 | x < x0] = [:: x_k1].
    rewrite /itv_partitionL.
    rewrite filter_rcons xxk1 -filter_predI.
    rewrite -cats1.
    suff : [seq x0 <- s | predI [eta > x] (<%R^~ x_k1) x0] = [::] by move=> ->.
    rewrite -(filter_pred0 s).
    apply: eq_in_filter => r sr/=.
    apply/negbTE/negP => /andP[xr rxk1].
    move: sr.
    apply/negP.
    apply: (@itv_partition_inbetween_notin _ _ _ _ _ abs _ k) => //.
    by rewrite -/x_k -/x_k1 in_itv/= rxk1 (lt_trans xkx xr).
  rewrite /=; congr cons.
  rewrite /itv_partitionR.
  rewrite -filter_predI.
  apply: eq_in_filter => r sr/=.
  rewrite andb_idl// => xk1r.
  exact: (lt_trans _ xk1r).
rewrite H1 H2.
rewrite (addrC (variation x x_k1 _ _)).
rewrite addrACA.
rewrite EFinD.
rewrite leeD//.
  destruct k as [|k].
    rewrite {1}/variation.
    have -> : itv_partitionL s x_k = [:: a].
      rewrite /itv_partitionL -cats1 /x_k/=.
      rewrite [X in X ++ _](_ : _ = [::])//.
      rewrite -(filter_pred0 s).
      apply: eq_in_filter => r sr.
      apply/negbTE; rewrite -leNgt.
      move/(nthP b) : sr => [m ms mr].
      rewrite -mr.
      apply/ltW.
      by apply/itv_partition_gt_lb.
    rewrite big_nat1/= subrr normr0 add0r.
    rewrite lee_fin.
    have -> : itv_partitionR s x_k1 = behead s.
      destruct s as [|s0 s1] => //=.
      rewrite /x_k1/= ltxx.
      rewrite /itv_partitionR.
      rewrite -[RHS](filter_predT s1).
      apply: eq_in_filter => r rs1.
      case: abs => /= /andP[as0].
      move=> /order_path_min => /(_ lt_trans) + _ => /allP.
      by apply.
    rewrite /x_k1 /=.
    exact: variation_behead.
  move: ks.
  rewrite leq_eqVlt => /predU1P[k1s|k1s].
    (* copipe *) have xk1b : x_k1 = b.
      rewrite /x_k1 k1s.
      rewrite nth_last/=.
      by case: abs => _ /eqP.
    (* copipe *) have sxk1 : itv_partitionR s x_k1 = [::].
      rewrite -(filter_pred0 s) /itv_partitionR.
      rewrite xk1b.
      apply: eq_in_filter => r rs.
      apply/negbTE.
      rewrite -leNgt.
      move/(nthP b) : rs => [m ms <-].
      by apply: (itv_partition_le_ub abs).
    rewrite sxk1.
    rewrite variation_nil addr0.
    rewrite lee_fin.
    rewrite /x_k/=.
    rewrite variation_nth//.
    by rewrite -k1s.
  rewrite lee_fin.
  rewrite [in leRHS](@in_itv_partition _ _ x_k1 _ (itv_partition_sorted abs)).
    apply/(nthP b).
    exists k.+1 => //.
    by rewrite (leq_trans _ k1s).
  rewrite (@variation_cat _ x_k1)//.
    by rewrite (le_trans axk)// (le_trans (ltW xkx))// ltW.
    rewrite /x_k1.
    rewrite /=.
    exact: (@itv_partition_le_ub _ _ a).
    apply: itv_partitionLP (abs) => //.
    rewrite /x_k1/=.
    exact: itv_partition_gt_lb => //.
    rewrite /x_k1/=.
    exact: (itv_partition_lt_ub abs).
    apply: itv_partitionRP (abs) => //.
    rewrite /x_k1/=.
    exact: itv_partition_gt_lb.
    rewrite /x_k1/=.
    exact: (itv_partition_lt_ub abs).
  by rewrite lerD2r /x_k /x_k1/= variation_nth_nth.
rewrite mule_natl.
rewrite mule2n.
rewrite EFinD.
rewrite leeD//.
  rewrite /variation/= big_nat_recr//= big_nil add0r.
  apply: (@variation_oscillation _ _ _ _ f).
  apply: continuous_subspaceW cf.
  apply: subset_itv; rewrite bnd_simp//.
  by apply: (itv_partition_le_ub abs).
  by rewrite in_itv/= (ltW xkx) (ltW xxk1).
  by rewrite in_itv/= lexx (ltW (lt_trans xkx _)).
rewrite /variation/= big_nat_recr//= big_nil add0r.
apply: (@variation_oscillation _ _ _ _ f).
apply: continuous_subspaceW cf.
apply: subset_itv; rewrite bnd_simp//.
by apply: (itv_partition_le_ub abs).
rewrite in_itv/= lexx ltW//.
by rewrite (lt_trans xkx).
by rewrite in_itv/= (ltW xkx) (ltW xxk1).
Qed.
*)
Abort.

Lemma variation_merge1_omega_max_new a b f s :
  s != [::] ->
  itv_partition a b s ->
  forall x, x \in `[a, b] ->
    ((variation a b f (merge <%R s [:: x]))%:E <=
       (variation a b f s)%:E + 2 * omega_max a s f)%E.
Proof.
elim/last_ind : s => //s d _ _ ps.
case: (ps) => + lsb; move: ps.
move/eqP : lsb.
rewrite last_rcons => ->.
move=> psb asb x.
have ab : a < b.
  have/lt_path_min/allP/(_ b) := asb.
  by rewrite mem_rcons in_cons eqxx/= => /(_ isT).
have [xs|xs] := boolP (x \in s).
  move=> _.
  rewrite in_variation_merge1//.
    by rewrite mem_rcons in_cons xs orbT.
  rewrite leeDl// mule_ge0// omega_max_ge0//.
  rewrite -size_eq0 -lt0n.
  by rewrite size_rcons.
rewrite in_itv/= => /andP[].
rewrite le_eqVlt => /predU1P[ax|ax].
  rewrite le_eqVlt => /predU1P[xb|xb].
    by move: ab; rewrite ax xb ltxx.
  subst x => {xb}.
  rewrite lt_merge_min.
   by move/order_path_min : asb => /(_ lt_trans).
   rewrite variationxx leeDl// mule_ge0// omega_max_ge0//.
   by destruct s.
rewrite le_eqVlt => /predU1P[xb|xb].
  subst x => {ax}; move: xs => bs.
  rewrite merge_ltEle//.
    apply: path_sorted.
    by apply: path_ltW asb.
  rewrite merge1_max.
    rewrite all_rcons lexx/=.
    move: asb.
    move/path_ltW; rewrite le_path_sortedE => /andP[_].
    by rewrite le_sorted_rconsE => /andP[].
  have := last_mem_itv_partition psb ab.
  admit.
(*
have := @variation_merge1_oscillation R a b f s cf abs x.
rewrite in_itv/= ax xb => /(_ isT xs).
have := @itv_partition_notin_inbetween _ _ a b s x abs xs.
rewrite ax xb => /(_ isT)[k ks xk].
move/(_ k ks xk)/le_trans; apply.
rewrite leeD2l//.
rewrite lee_pmul ?oscillation_ge0//.
rewrite /omega_max.
pose h := fun k => oscillation f `[(nth b (a :: s) k), (nth b s k)].
apply: (le_bigmax_seq -oo%E k xpredT h) => //.
by rewrite mem_index_iota ks.
Qed.
*)
Abort.

Lemma itv_partition_sorted_rcons_new a b s (t0 : seq R) (t : R) :
  a < b -> path <=%R a s -> last a s = b ->
  sorted <=%R (rcons t0 t) ->
  (forall x, x \in rcons t0 t -> (x \in `[a, b]) /\ x \notin s) ->
  exists2 k : nat,
    (k.+1 < size (a :: merge <=%R s t0))%N &
    t \in `](nth b (a :: merge <=%R s t0) k),
    (nth b (a :: merge <=%R s t0) k.+1)[.
Proof.
move=> ab pas lsb.
rewrite le_sorted_rconsE => /andP[st0 t0t] xnotin.
have tt0t : t \in rcons t0 t by rewrite mem_rcons mem_head.
have alet : (t <= a) = false.
  apply/negP/negP; rewrite -ltNge.
  admit.
set i := (find (>= t) (a :: merge <=%R s t0)).-1.

have i0 : (0 < find (>= t) (a :: merge <=%R s t0))%N by rewrite /= ifF.
have : has (>= t) (a :: merge <=%R s t0).
  apply/hasP; exists b.
    rewrite -lsb.
    rewrite in_cons; apply/predU1P; right.
    rewrite mem_merge mem_cat; apply/orP; left.
    have := mem_last a s.
    rewrite in_cons => /predU1P[]//.
    by rewrite lsb => eqab; rewrite eqab ltxx in ab.
  have[+ ] := xnotin _ tt0t.
  by rewrite in_itv/= => /andP[].
exists i.
  by rewrite prednK// -has_find.

rewrite (lock (a :: merge <=%R s t0)).
rewrite in_itv/=; apply/andP; split; unlock.
  have : (i < find (>= t) (a :: merge <=%R s t0))%N.
    rewrite ltn_predL.
    by rewrite /= ifF.
  move/(@before_find _ b _ _ _).
  by move/negP/negP; rewrite -ltNge.
(*
apply/negP => /eqP it.
have [+ ts] := xnotin t tt0t.
rewrite in_itv/= => /andP[altt tltb].
  move/negP : (ts). ; apply; rewrite -it.
  have [hi|hi] := ltnP i (size (a :: merge <%R s t0)).
    have : t \notin a :: merge <%R s t0.
      rewrite inE mem_merge mem_cat !negb_or; apply/and3P; split => //.
        by rewrite gt_eqF//.
      apply/negP => tt0.
      have/allP := t0t.
      by move/(_ t tt0); rewrite ltxx.
    by rewrite -it mem_nth.
  move: it; rewrite nth_default//.
  move/eqP.
  rewrite eq_le => /andP[].
  by rewrite leNgt tltb.
rewrite prednK//.
exact: nth_find.
*)
Abort.

Lemma variation_merge_notin_new f a b (ab : a < b) s t :
  {within `[a, b], continuous f} ->
  (path <=%R a s) ->
  (last a s = b) ->
  sorted <=%R t ->
  (forall x, x \in t -> (x \in `]a, b[) /\ x \notin s) ->
  ((variation a b f (merge <=%R s t))%:E <= (variation a b f s)%:E +
  (size t)%:R%:E * 2 * omega_max a s f)%E.
Proof.
elim/last_ind : t a b ab s.
  move=> a b ab s cf abs _ _.
  rewrite /= !mul0e adde0.
  rewrite merge0r.
  done.
move=> t0 t1 ih a b ab s cf pas lsb sorted_t notins.
have le_sorted_s: sorted <=%R s.
  by have /path_sorted := pas.
have le_sorted_t0: sorted <=%R t0.
  have := sorted_t.
  by rewrite le_sorted_rconsE => /andP[].
rewrite -cats1.
rewrite merge_cats1//; first by rewrite cats1.
have [k ks t1k] : exists2 k,
   (k.+1 < size (a :: merge <%R s t0))%N &
     t1 \in `](nth b (a :: merge <%R s t0) k),
     (nth b (a :: merge <%R s t0) k.+1)[.
(*
  exact: itv_partition_sorted_rcons_new.
  
rewrite -merge_ltEle//.
  by rewrite merge_sorted//; exact: le_total.
apply: le_trans.
  apply: (@variation_merge1_oscillation _ _ _ _ _ _ _ _ _ _ k) => //.
  - rewrite -merge_ltEle//.
    apply: sorted_itv_partition_merge => //.
      by move: st; rewrite -cats1 => /cat_sorted2[].
    move=> x xt0.
    apply: tabs.
    by rewrite mem_rcons inE xt0 orbT.
  - have := tabs t1.
    by rewrite mem_rcons inE eqxx/= => /(_ isT)[].
  - rewrite mem_merge mem_cat negb_or; apply/andP; split.
      apply tabs.
      by rewrite mem_rcons mem_head.
    exact: lt_sorted_rcons_notin.
  - by rewrite -merge_ltEle.
  - by rewrite -merge_ltEle.
(*  rewrite (leq_trans ks)//=. size_merge size_cat leq_addr.*)
apply: (@le_trans _ _ (
  (variation a b f s)%:E + ((size t0)%:R)%:E * 2 * omega_max a b f s
  +
  2 * oscillation f `[(nth b (a :: merge <=%R s t0) k), (nth b (a :: merge <=%R s t0) k.+1)])%E).
  rewrite leeD2r//.
  rewrite -merge_ltEle//.
  apply: ih => //.
  move: st.
  by rewrite -cats1 => /cat_sorted2[].
  move=> x xt0.
  apply: tabs.
  by rewrite mem_rcons inE xt0 orbT.
rewrite -addeA.
rewrite leeD2l//.
rewrite cats1 size_rcons.
rewrite -(natr1 (size t0)).
rewrite (EFinD (size t0)%:R) muleDl// mul1e.
have [?|] := boolP (omega_max a b f s \is a fin_num); last first.
  rewrite ge0_fin_numE ?omega_max_ge0//.
    destruct s => //.
    move/itv_partition_nil : abs.
    move: ab => /[swap] ->.
    by rewrite ltxx.
  rewrite -leNgt leye_eq => /eqP abfsy.
  rewrite abfsy.
  rewrite [in leRHS]gt0_muley ?leey//.
  by rewrite lte_paddl//.
rewrite muleDl//.
rewrite leeD2l//.
rewrite lee_pmul//; first exact: oscillation_ge0.
set st0 := merge <=%R s t0.
pose hst0 := fun k => oscillation f `[(nth b (a :: st0) k), (nth b st0 k)].
rewrite (@le_trans _ _ (omega_max a b f (merge <=%R s t0)))//.
  apply: (le_bigmax_seq -oo%E k xpredT hst0) => //.
  rewrite mem_index_iota leq0n/=.
  rewrite /= ltnS in ks.
  by rewrite /st0 -merge_ltEle.
rewrite /omega_max.
rewrite -/st0.
pose hs := fun k => oscillation f `[(nth b (a :: s) k), (nth b s k)].
apply: ereal_le_bigmax_seq2 => /= i.
rewrite mem_index_iota leq0n/= => ist0.
move: st; rewrite -cats1 => /cat_sorted2[sorted_t0 _].
have Htmp : forall x, x \in t0 -> (x \in `]a, b[) /\ x \notin s.
  move=> x xt0.
  apply: tabs.
  by rewrite mem_rcons inE xt0 orbT.
rewrite /st0 -merge_ltEle// in ist0.
have [j js H] := itv_partition_mergeS ab abs sorted_t0 Htmp ist0.
exists j => //.
  by rewrite mem_index_iota.
apply: oscillation_sub.
by rewrite /st0 -merge_ltEle.
*)
Abort.

Lemma variation_merge_new f a b (ab : a < b) s t :
  {within `[a, b], continuous f} ->
  (path <=%R a s) ->
  (last a s = b) ->
  sorted <=%R t ->
  (forall x, x \in t -> x \in `[a, b]) ->
  ((variation a b f (merge <%R s t))%:E <= (variation a b f s)%:E +
  (size t)%:R%:E * 2 * omega_max a s f)%E.
Proof.
move=> cf pas lsb sorted_t tab.
pose t' := seq.filter [pred x | x \notin s] t.
have : ((variation a b f (merge <%R s t'))%:E <=
  (variation a b f s)%:E + ((size t')%:R)%:E * 2 * omega_max a s f)%E.
(*
  apply: variation_merge_notin_new => //.
    apply: lt_sorted_filter.
admit.
  admit.
have -> : variation a b f (merge <%R s t') = (variation a b f (merge <%R s t)).
  rewrite [RHS]variation_undup//.
  - rewrite merge_ltEle//.
    exact: path_sorted pas.
  - apply: merge_path => //.
      exact: le_total.
    rewrite le_path_sortedE; apply/andP; split => //.
    by apply/allP => x /tab; rewrite in_itv/= => /andP[].
  - 
rewrite path_min_sorted; last exact: sorted_ltW.
    apply/allP => x /tab.
    by rewrite in_itv/= => /andP[/ltW].
  - have : s != [::].
      apply: itv_partition_neq0 abs => //.
      by rewrite neq_lt; apply/orP; left.
rewrite (lastr_lt_merge (eqP abs.2))// => x .
    move/tab.
    by apply: subset_itv_oo_cc.
  - congr variation.
    apply: merge_filter_undup => //.
    by apply: (itv_partition_sorted abs).
move/le_trans; apply.
rewrite leeD2l//.
rewrite lee_pmul//.
  apply: omega_max_ge0.
  apply: itv_partition_neq0 abs.
  by rewrite lt_eqF//.
rewrite lee_pmul// lee_fin ler_nat.
by rewrite size_filter count_size.
*)
Abort.

Lemma lemma5'_le a b f :
  forall A : R, (0%:E <= A%:E < total_variation a b f)%E ->
    exists2 delta, 0 < delta &
      (forall p, (path <=%R a p /\ last a p <= b) ->
       mesh a p < delta -> (* le? *)
              A < variation a b f p).
Proof.
move=> A /andP[].
rewrite lee_fin => A0.
move/ereal_sup_gt => [_ /=[V' [X' partX' X'V'] <-]].
rewrite lte_fin => AV'.
have : @unif_continuous (subspace `[a, b]) R f.
(*
  exact/compact_unif_continuousP.
move/unif_continuousP => /=.
pose m := size X'.
have mE : m = size X' by [].
pose eps := ((V' - A) / (4 * m)%:R).
have eps0 : 0 < eps.
  rewrite divr_gt0 => //; first by rewrite subr_gt0.
  rewrite -(mulr0n 1) ltr_nat muln_gt0; apply/andP; split => //.
  exact: (itv_partitionNnil ab partX').
move/(_ _ eps0) => [d d0 unifcf].
exists d => // p [pap lpb] abpd. (* p is (I) in the paper *)

apply: (@lt_le_trans _ _ ((V' + A) / 2)).
  rewrite ltr_pdivlMr//.
  rewrite -ltrBlDr -{2}(mulr1 A) -mulrBr.
  by rewrite -{2}(mulr1n 1) -natrB// subSnn mulr1.
pose V0 : R := variation a b f (merge <%R p X').
have sleX' : sorted <=%R X' by have [/path_sorted/sorted_ltW] := partX'.
have slep : sorted <=%R p by have [/path_sorted] := pap.
apply: (@le_trans _ _ (V0 - (V' - A) / 2)).
  rewrite [leRHS](_ : _ = V0 - V' + (V' + A) / 2).
    rewrite -[in LHS](@subrK _ V' V0).
    rewrite -(addrA (V0 - V')).
    congr +%R.
    rewrite -mulNr opprD opprK 2!mulrDl addrA.
    congr +%R.
    rewrite -{1}(@mulfK _ 2 _ V')// mulrDr mulr1.
    by rewrite mulrDl mulNr addrK.
  rewrite lerDr subr_ge0.
  rewrite -X'V'.
  rewrite sorted_variation_subseq //.
    by rewrite merge_ltEle ?merge_sorted//; exact: le_total.
  apply: (subseq_merger _ lt_trans).
  exact: itv_partition_sorted partX'.
rewrite lerBlDr -lee_fin EFinD.
have sorted_X' : (sorted <%R X') by have [/path_sorted] := partX'.
have V0E : V0 = variation a b f (merge <%R p X') by [].
have epsE : eps = (V' - A) / (4 * m)%:R by [].
elim/last_ind : X' partX' X'V' m mE eps epsE eps0 unifcf V0 sleX' V0E sorted_X'.
  by move/(itv_partitionNnil ab).
move=> X'0 X'1 _(* ih *); pose X' := rcons X'0 X'1.
move=> partX' X'V' m mE eps epsE eps0 unifcf V0 sleX' V0E sorted_X'.
have X'E : X' = rcons X'0 X'1 by [].
have X'0ab : (forall x, x \in X'0 -> x \in `]a, b[).
  move=> x xX'0.
  exact: (itv_partition_head_in_itv partX').
have sX'0 : sorted <%R X'0.
  by have[/= + _] := partX'; rewrite rcons_path => /andP[/path_sorted].
have X'1E : X'1 = b.
  have [_] := partX'.
  by rewrite last_rcons => /eqP->.
rewrite V0E.

have -> : variation a b f (merge <%R p (rcons X'0 X'1)) =
   variation a b f (merge <%R p X'0).
  rewrite variation_undup//.
  - rewrite merge_ltEle//.
    apply: merge_path => //.
    + exact: le_total.
    + by have[/path_ltW] := partX'.
  - rewrite (@itv_partition_last_merge _ _ b)//.
      exact: ltW.
    move=> x; rewrite mem_rcons inE => /predU1P[->|].
      by rewrite X'1E !in_itv/= lexx andbT.
    move/X'0ab.
    exact: subset_itv_oo_oc.
  rewrite [RHS]variation_undup//.
  - rewrite merge_ltEle//; first exact: sorted_ltW.
    apply: merge_path.
    + exact: le_total.
    + by have[/path_ltW] := pabp.
    + have[/path_ltW] := partX'.
      by rewrite rcons_path => /andP[].
  - rewrite (@itv_partition_last_merge _ _  _ (ltW ab))//.
    move=> x /X'0ab.
    by apply: subset_itv_oo_oc.
  congr (variation a b f).
  apply: lt_sorted_eq => //.
  - apply: le_sorted_lt_sorted_undup.
    rewrite merge_ltEle//.
    apply: merge_sorted => //.
    exact: le_total.
  - apply: le_sorted_lt_sorted_undup.
    have sorted_X'0 : sorted <=%R X'0.
      by have := sleX'; rewrite le_sorted_rconsE => /andP[].
    rewrite merge_ltEle//.
    apply: merge_sorted => //.
    exact: le_total.
  have sp : sorted <%R p by exact: itv_partition_sorted pabp.
  rewrite -2?merge_filter_undup//.
  rewrite filter_rcons ifN//.
  rewrite negbK.
  have[_ /eqP] := partX'; rewrite last_rcons => ->.
  exact: last_mem_itv_partition pabp ab.
have := @variation_merge _ f a b ab p X'0 cf pabp sX'0 X'0ab.
move/le_trans; apply.
apply: leeD2l.
(* unifcf *)
rewrite -/m.
case: X'0 mE X' X'E partX' X'V' sleX' V0E sorted_X' X'0ab sX'0 => //=.
  by move=> _ _ _ _ _ _ _ _; rewrite 2!mul0e lee_fin divr_ge0// subr_ge0 ltW.
move=> X'00 X'01 mE X' X'E partX' X'V' sleX' V0E sorted_X' X'0ab sX'0.
rewrite -lee_pdivlMl.
  by rewrite mulr_gt0.
rewrite (_ : ((V' - A) / 2) = (m%:R * 2)%R * eps)%R.
  rewrite epsE.
  rewrite (_ : 4 = 2 * 2)%N//.
  rewrite mulnAC 2!natrM.
  rewrite 2!invfM 2!mulrA.
  congr *%R.
  rewrite mulrA.
  rewrite -(mulrA m%:R 2).
  rewrite -(mulrA m%:R (2 * (V' - A))).
  rewrite mulrC.
  rewrite (mulrA m%:R^-1).
  rewrite mulVf ?mul1r.
    apply: lt0r_neq0.
    by rewrite -(mulr0n 1) ltr_nat mE.
  by rewrite mulrAC divff// mul1r.
rewrite /omega_max.
rewrite big_nat_cond.
apply: bigmax_le; first by rewrite leNye.
move=> n.
rewrite leq0n/= andbT => np.
rewrite /oscillation/=.
rewrite -image_comp.
have : compact (f @` `[(nth b (a :: p) n), (nth b p n)]).
  apply: continuous_compact.
    apply: continuous_subspaceW cf.
    apply: subset_itv; rewrite bnd_simp//.
      case: n => //= ? in np *.
      exact/ltW/itv_partition_gt_lb.
    exact: (itv_partition_le_ub pabp).
  exact: segment_compact.
rewrite Rcompact_boundE/= => -[cimg ubimg lbimg].
have nonempty_img : [set f x | x in `[(nth b (a :: p) n), (nth b p n)]] !=set0.
  exists (f (nth b (a :: p) n)) => //.
  exists (nth b (a :: p) n) => //=.
  rewrite boundl_in_itv/= bnd_simp.
  apply/ltW/pathP => //.
  by have [] := pabp.
rewrite ereal_sup_EFin// ereal_inf_EFin//.
rewrite ifN.
  move/set0P : nonempty_img; apply: contra_neq => ->.
  by rewrite image_set0.
rewrite -EFinB lee_fin.

have : forall x y, x \in `[(nth b (a :: p) n), (nth b p n)] ->
 y \in `[(nth b (a :: p) n), (nth b p n)] ->
  `|f x - f y| < eps.
  move=> x y Hx Hy.
  have @x' : subspace `[a, b].
    red.
    exact: x.
  have @y' : subspace `[a, b].
    red.
    exact: y.
  have := unifcf (x', y').
  rewrite /=/ball/=.
  move=> /(_ _).
  apply.
  rewrite /subspace_ball.
  rewrite ifT.
    rewrite inE/=.
    apply: subset_itv Hx; rewrite bnd_simp.
      case: n cimg ubimg lbimg nonempty_img Hy => //=n _ _ _ _ _ in np *.
      exact/ltW/itv_partition_gt_lb.
    exact: (itv_partition_le_ub pabp).
  rewrite /=; split.
    apply: subset_itv Hy; rewrite bnd_simp.
      case: n cimg ubimg lbimg nonempty_img Hx => //=n _ _ _ _ _ in np *.
      exact/ltW/itv_partition_gt_lb.
    exact: (itv_partition_le_ub pabp).
  rewrite /ball/=.
  apply: (@le_lt_trans _ _ `|nth b p n - nth b (a :: p) n|).
    rewrite [in leRHS]distrC.
    exact: mem_interval_le.
  apply: le_lt_trans abpd.
  apply: (@le_trans _ _ (\big[maxr/0]_(0 <= n0 < size p)
      `|nth b p n0 - nth b (a :: p) n0|)); last first.
    by rewrite /mesh/= -bigmaxr_morph.
  apply: (le_bigmax_seq _ _ _ (fun=> _)(*TODO: wtf*)) => //=.
  by rewrite mem_index_iota leq0n.
move=> H.
rewrite lerBlDl; apply: ge_sup => //.
move=> _/= [x px <-].
rewrite -lerBlDr.
apply: lb_le_inf => // _/=[x' px' <-].
rewrite lerBlDr -lerBlDl.
apply: (@le_trans _ _ `|f x - f x'|); first exact: ler_norm.
rewrite 2!mulrA -[leLHS]mul1r.
  apply: ler_pM => //.
  rewrite -mulrA mulrC.
  rewrite -mulf_div divff// mulr1.
  rewrite ler_pdivlMr// mul1r mE.
  by rewrite ler_nat size_rcons.
exact/ltW/H.
*)
Abort.

Lemma lemma5_le a b f (l : R^nat) (s : (seq R)^nat) :
  (forall n, path <=%R a (s n)) ->
  (forall n, last a (s n) <= b) ->
  (forall n, mesh a (s n) <= l n) ->
  l i @[i --> \oo] --> 0 ->
  (variation a b f (s n))%:E @[n --> \oo] --> total_variation a b f.
Proof.
Abort.
(*
move=> pas lsb xl lcvg0.
have vletv n : ((variation a b f (s n))%:E <= total_variation a b f)%E.
  exact: variation_le_total_variation.
have := total_variation_ge0 f (ltW ab).
rewrite le_eqVlt => /predU1P[tvf0|tvfgt0].
  apply: cvg_near_cst; apply: nearW => n.
  apply/eqP; rewrite eq_le; apply/andP; split => //.
  by rewrite -tvf0; exact: variation_ge0.
have [tvfoo|] := eqVneq (total_variation a b f) +oo%E.
  rewrite tvfoo.
  move=> /= U.
  rewrite /nbhs/= => -[A [_ HA]].
  have [A0|A0] := ltP A 0.
    exists 0%N => // k/= => _; apply: HA.
    by rewrite (@lt_le_trans _ _ 0%E)// lee_fin variation_ge0.
  have : (0%:E <= A%:E < total_variation a b f)%E.
    by rewrite lee_fin A0 tvfoo ltry.
  move/lemma5' => /=[e e0].
  have lne : \forall n \near \oo, l n < e.
    move: lcvg0.
    move/(cvgr_dist_lt _ 0) /(_ e e0).
    under eq_near => n.
      rewrite sub0r normrN ger0_norm.
        by rewrite (le_trans _ (xl _))// mesh_ge0.
      over.
    by [].
  have mxe : \forall n \near \oo, mesh a b (s n) < e.
    by apply: filterS lne => n; exact: le_lt_trans.
  move=> abA.
  apply: filterS mxe => n /abA. - /(_ (pabx n)).
  by rewrite -lte_fin => /HA.
rewrite -ltey => tvfltey.
have tvf_fin : total_variation a b f \is a fin_num.
  by rewrite ge0_fin_numE // (total_variation_ge0 _ (ltW ab)).
rewrite -(@fineK _ (total_variation a b f))//; apply/fine_cvgP.
split; first exact: nearW.
apply/cvgrPdist_ltp; near=> e.
have : (0%:E <= (fine (total_variation a b f) - e)%:E < total_variation a b f)%E.
  apply/andP; split; rewrite ?lee_fin.
    rewrite subr_ge0.
    near: e; apply: nbhs_right_le.
    by rewrite fine_gt0// tvfgt0.
  by rewrite EFinB fineK// gte_subl// lte_fin.
move/lemma5' => [d d0 H].
near=> n.
rewrite ger0_norm; first by rewrite subr_ge0 -lee_fin !fineK.
rewrite ltrBlDl -ltrBlDr/=.
apply: (H) => //.
apply: (le_lt_trans (xl n)).
near: n.
exact: (cvgr_lt _ lcvg0 _ d0).
Unshelve. all: end_near. Qed.
*)

(*
Lemma lemma5_cvg_style :
(*  {within `[a, b], continuous f} ->*)
  ereal_inf
     [set v%:E | v in variations_with_max a b f l] @[l --> 0^'+]
       --> total_variation a b f.
Proof.
have [|] := eqVneq (total_variation a b f) +oo%E.
  move=> tvfoo; rewrite tvfoo.
  apply/cvgeyPgey.
  near=> A.
  have : (0%:E <= A%:E < total_variation a b f)%E.
    by rewrite lee_fin tvfoo ltry andbT.
  move/lemma5' => /=[l l0 Hl].
  exists l => // x/=.
  rewrite sub0r normrN.
  move/ltr_normlW => xl x0.
  apply/ereal_infP => _ [_ [s [-> pabs sx]] <-].
  rewrite lee_fin; apply: ltW.
  apply: Hl => //.
  exact: le_lt_trans xl.
rewrite -ltey => bvf.
suff H : inf (variations_with_max a b f l) @[l --> 0^'+] -->
    sup (variations a b f).
  rewrite /total_variation ereal_sup_EFin; last 2 first.
  - exists (fine (total_variation a b f)) => _ [s ps <-].
    rewrite -lee_fin fineK; last first.
      rewrite ge0_fin_numE//.
      apply: total_variation_ge0.
      exact: ltW.
    exact: variation_le_total_variation.
  - exists `|f b - f a|.
    exists [:: b].
      exact: itv_partition1.
    by rewrite /variation/= big_seq1.
  apply: cvg_EFin.
    apply: nearW => l.
    rewrite ge0_fin_numE => //; last first.
      apply: le_ereal_inf.
    admit.
  under eq_cvg => l/=.
    rewrite ereal_inf_EFin/=; last 2 first.
    - admit.
    - admit.
    over.
  done.
  apply/cvg_at_rightP => l [l0 cvgl].
apply/cvgrPdist_le => /= e e0.
have : (0%:E <= (fine (total_variation a b f) - e)%:E < total_variation a b f)%E.
  admit.
move/lemma5' => /= [L L0 HL].
have := cvgl (ball 0 L) (nbhsx_ballx _ _ L0).
  move=> [m _ mL].
near=> n.
rewrite gtr0_norm; last first.
  rewrite subr_gt0.
  apply: (@lt_le_trans _ _ (sup (variations_with_max a b f (l n)))).
    apply: has_bound_not_subset1_inf_sup.
        exists 0 => /= _ [? [-> _ _]].
        exact: variation_ge0.
      exists (fine (total_variation a b f)).
      move=> v [s [-> pabs _]].
      rewrite -lee_fin fineK; last first.
        rewrite ge0_fin_numE//.
        exact/total_variation_ge0/ltW.
      apply: le_ereal_sup_tmp.
      exists (variation a b f s)%:E => //.
      exists (variation a b f s) => //.
      by exists s.
    rewrite -existsNE.
    have : exists k, l k < l n.
      move: cvgl.
      move/(_ (ball 0 (l n))).
      move/(_ (nbhsx_ballx _ _ (l0 n))).
      move=> [k _].
      move/(_ k (leqnn k)).
      rewrite /ball/= sub0r normrN gtr0_norm// => lkn.
      by exists k.
    move=> [k lkn].
    exists (variation a b f (lambda_partition a b (l n))).
    rewrite -existsNE.
    exists (variation a b f (lambda_partition a b (l k))).
    apply/not_implyP; split; last (apply/not_implyP; split).
    - exact: variations_with_max_lambda.
    - exists (lambda_partition a b (l k)); split => //.
        exact: itv_partition_lambda.
      rewrite itv_partition_max_lambda.
        apply: ltW.
        apply: le_lt_trans lkn.
        exact: divr_ceil_le.
    admit.
  apply: sup_le; last 2 first.
  - exists (variation a b f (lambda_partition a b (l n))).
    exact: variations_with_max_lambda.
  - split.
      exists (variation a b f [:: b]).
      exists [:: b] => //.
      exact: itv_partition1.
    exists (fine (total_variation a b f)) => _ [s ps <-].
    rewrite -lee_fin fineK; last first.
      by rewrite ge0_fin_numE ?total_variation_ge0 ?ltW.
    exact: variation_le_total_variation.
  move=> _ [s [-> ps _]].
  exists (variation a b f s); split => //.
  exact: variations_variation.
rewrite lerBlDr -lerBlDl.
rewrite -lee_fin.
rewrite -ereal_inf_EFin; last 2 first.
- admit.
- admit.
apply: le_ereal_inf_tmp.
move=> _ [_ [s [-> ps sl] <-]].
rewrite EFinB -ereal_sup_EFin; last 2 first.
- admit.
- admit.
rewrite -[X in (X - _ <= _)%E]fineK; last first.
  admit.
rewrite lee_fin.
apply: ltW.
apply: HL => //.
apply: (le_lt_trans sl).
have : (m <= n)%N.
  near: n.
  exact: nbhs_infty_ge.
move/(mL n) => /=.
by rewrite/ball/= sub0r normrN gtr0_norm.
Unshelve. all: end_near. Admitted.

(* from old lemma6 proof *)
(*
rewrite -{1}(@fineK _ (total_variation a b f)); last first.
  by apply/bounded_variationP => //; exact: ltW.
move/fine_cvgP => [fin_inf].
move/cvg_at_rightP.
move/(_ lambda).
have Hlambda : (forall n : nat, 0 < lambda n) /\ lambda n @[n --> \oo] --> 0.
  split; last exact: cvg_lambda0.
  move=> k.
  exact: lambda_gt0.
move/(_ Hlambda); move{Hlambda} => Hl.
apply: squeeze_cvgr _ Hl (cvg_cst Vcd).
near=> n.
apply/andP; split; last first.
  rewrite /Vcd/total_variation.
  rewrite -lee_fin fineK; last by apply/bounded_variationP => //; exact: ltW.
  apply: le_ereal_sup_tmp.
  exists (S_ n)%:E => //.
  exists (S_ n) => //.
  by exists (x n).
rewrite -lee_fin fineK; last first.
  have := fin_inf.
  move=> [l /= l0].
  apply => //=.
  rewrite sub0r normrN ger0_norm; last first.
    exact/ltW/lambda_gt0.
  move: l l0; near: n.
  admit.
  exact: lambda_gt0.
apply: ge_ereal_inf.
exists (S_ n)%:E => //.
exists (S_ n) => //.
by exists (x n); split.
Unshelve. end_near. Admitted.
*)

have [tvfoo|] := eqVneq (total_variation a b f) +oo%E.
  rewrite tvfoo.
  admit.
have -> : total_variation a b f
    = ereal_inf [set v%:E | v in variations_with_max a b f 0].
  rewrite /total_variation.
  admit.
*)

End lemma5_le.
