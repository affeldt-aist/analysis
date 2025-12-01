From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import all_ssreflect interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype.
From mathcomp Require Import sequences measure lebesgue_measure realfun.
From mathcomp Require Import absolute_continuity.

(**md**************************************************************************)
(* # Banach–Zarecki Theorem (lemma 5)                                         *)
(*                                                                            *)
(* ref: https://archive.org/details/theoryoffunction00nata *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section merge_lemmas.
Context {T : Type} {r : rel T}.
Implicit Type (s t : seq T).

Lemma merge0r s : merge r s [::] = s.
Proof. by elim: s. Qed.

(* unnecessary? *)
Lemma merge0l s : merge r [::] s = s.
Proof. by []. Qed.

End merge_lemmas.

Lemma subseq_merge {T : eqType} {r : rel T} (s t : seq T) :
   subseq s (merge r s t).
Proof.
Admitted.

Section seq_itv_partitionLR_lemmas.
Context {R : realType}.

Implicit Types (s : seq R) (x : R).

Lemma merge_rcons s x :
  all (<%R x) s ->
  merge <%R s [:: x] = rcons s x.
Proof.
Admitted.

Lemma itv_partitionL_nil x :
  itv_partitionL [::] x = [:: x].
Proof. by []. Qed.

Lemma itv_partitionR_nil x :
  itv_partitionR [::] x = [::].
Proof. by []. Qed.

Lemma sorted_rcons_all s x : sorted <%R (rcons s x) -> all (<%R^~ x) s.
Proof.
rewrite -(revK (rcons _ _)) rev_sorted rev_rcons/= -all_rev.
by move/order_path_min; move/(_ (rev_trans lt_trans)).
Qed.

Lemma itv_partitionL_rcons1 s x :
  sorted <%R (rcons s x) ->
  itv_partitionL (rcons s x) x = rcons s x.
Proof.
move=> ss.
rewrite /itv_partitionL.
suff -> : [seq x0 <- rcons s x | x0 < x] = s by [].
rewrite filter_rcons ifF//.
apply/all_filterP.
exact: sorted_rcons_all.
Qed.

Lemma itv_partitionR_cons s x :
  all (> x) s ->
  itv_partitionR (x :: s) x = s.
Proof.
move=> pxs.
rewrite /itv_partitionR/= ifF//.
by apply/all_filterP.
Qed.

Lemma lt_sorted_itv_partitionL s x :
  sorted <%R s -> sorted <%R (itv_partitionL s x).
Proof.
move=> ss.
rewrite/itv_partitionL.
rewrite -(revK (rcons _ _)).
rewrite rev_sorted.
rewrite rev_rcons/=.
rewrite -filter_rev.
rewrite (path_sortedE (rev_trans lt_trans)); apply/andP; split.
  rewrite all_filter.
  rewrite all_rev.
  apply/allP.
  move=> t ts/=.
  exact: implybb.
apply: (sorted_filter (rev_trans lt_trans)).
by rewrite rev_sorted.
Qed.

Lemma lt_sorted_itv_partitionR s x :
  sorted <%R s -> sorted <%R (itv_partitionR s x).
Proof. move=> ?; exact: lt_sorted_filter. Qed.

Lemma itv_partitionL_idem s x :
  sorted <%R (itv_partitionL s x) ->
  itv_partitionL (itv_partitionL s x) x = itv_partitionL s x.
Proof. by move=> H; rewrite itv_partitionL_rcons1. Qed.

Lemma itv_partitionR_idem s x :
  sorted <%R (itv_partitionR s x) ->
  itv_partitionR (itv_partitionR s x) x = itv_partitionR s x.
Proof. move=> H; exact/all_filterP/filter_all. Qed.

Lemma itv_partitionL_all_lt l x :
 all (<%R ^~ x) l ->
 itv_partitionL l x = rcons l x.
Proof. by move=> lx; congr rcons; exact: all_filterP. Qed.

Lemma itv_partitionR_all_gt l x :
 all (> x) l ->
 itv_partitionR l x = l.
Proof. by exact: all_filterP. Qed.

Lemma itv_partitionL_cons h l x :
  h < x ->
  itv_partitionL (h :: l) x = h :: itv_partitionL l x.
Proof. by move=> hx; rewrite /itv_partitionL/= hx rcons_cons. Qed.

Lemma itv_partitionL_seq1 l x :
  all (> x) l -> itv_partitionL l x = [:: x].
Proof.
move/allP => xl.
rewrite /itv_partitionL.
suff -> : [seq x0 <- l | x0 < x] = [::] by [].
apply/notP.
move/eqP.
rewrite -has_filter.
apply/negP.
apply/hasPn.
move=> e el.
rewrite -leNgt.
rewrite le_eqVlt.
apply/orP; right.
exact: xl.
Qed.

Lemma itv_partition_merge_concat1 (s : seq R) (x : R) :
    sorted <%R s -> x \notin s ->
    merge <%R s [:: x] = itv_partitionL s x ++ itv_partitionR s x.
Proof.
elim: s x => //.
move=> h l IH/= x pl xl.
case: ifPn.
- move=> hx.
  rewrite IH; last 2 first.
  + exact: path_sorted pl.
  + by move: xl; rewrite inE negb_or gt_eqF.
  rewrite ifF; last by apply/negP/negP; rewrite -leNgt ltW.
  by rewrite itv_partitionL_cons.
- rewrite -leNgt.
  rewrite le_eqVlt => /orP; case.
    move: (xl); rewrite inE/=.
    by rewrite negb_or => /andP[/negP].
  move=> xh; rewrite xh.
  rewrite itv_partitionL_seq1; last first.
    apply: lt_path_min.
    by rewrite /= xh pl.
  rewrite itv_partitionR_all_gt//.
  apply: lt_path_min.
  exact: (path_lt_head xh).
Qed.

End seq_itv_partitionLR_lemmas.

Section monoid_nonnegR.
Context {R : numDomainType}.

Lemma maxr0 : right_id (0%:nng : {nonneg R}) maxr.
Proof.
move=> /= x.
have [|] := leP 0%:nng x.
  by [].
rewrite -num_lt/=.
rewrite lt0F//.
Qed.

Lemma max0r : left_id (0%:nng : {nonneg R}) maxr.
Proof.
move=> x.
rewrite maxC.
exact: maxr0.
Qed.

HB.instance Definition _ :=
  Monoid.isLaw.Build {nonneg R} 0%:nng maxr maxA max0r maxr0.

End monoid_nonnegR.

Section itv_partition_length.
Context {R : realType}.
Implicit Types (a b : R) (f : R -> R).
Implicit Types (s : seq R) (x : R).

Definition itv_partition_max a b s : R := let pnth := nth b (a :: s) in
  (\big[maxr/0%:nng]_(0 <= n < size s) `|pnth n.+1 - pnth n|%:nng)%:num.

Definition itv_partition_with_max a b l s :=
  itv_partition a b s /\ itv_partition_max a b s = l.

Definition variations_with_max a b f l : set R :=
   [set variation a b f s | s in itv_partition_with_max a b l].

Definition omega_max a b f s : \bar R :=
   \big[maxe/0%E]_(0 <= n < size s) oscillation f
    `[(nth b (a :: s)) n, (nth b (a :: s)) n.+1].

Lemma oscillation_ge0 f a b : (0 <= oscillation f `[a, b])%E.
Proof.
Admitted.

Lemma omega_max_ge0 a b f s : (0 <= omega_max a b f s)%E.
Proof.
case: s => //.
  by rewrite /omega_max/= big_mkord big_ord0.
move=> h s.
apply: (@le_trans _ _ (oscillation f
    `[(nth b (a :: h :: s)) 0, (nth b (a :: h :: s)) 1])).
exact: oscillation_ge0.
rewrite /omega_max.
exact: (le_bigmax_seq _ 0) => //.
Qed.

Lemma oscillation_sub f i j :
i `<=` j -> (oscillation f i <= oscillation f j)%E.
Proof.
move=> ij.
rewrite /oscillation/=.
apply: leeB.
- apply: ereal_sup_le.
  exact: image_subset.
- apply: ereal_inf_le_tmp.
  exact: image_subset.
Qed.

Lemma lt_path_uniq a s : path <%R a s -> uniq (a :: s).
Proof.
move=> pas.
by exact: lt_sorted_uniq.
Qed.

Lemma itv_partition_in_itv a b s :
  itv_partition a b s -> {in s, forall x, x \in `]a, b]}.
Proof.
move=> /[dup]parts.
move=> [/[dup]/lt_path_min/allP sa].
move=> /[dup]pas.
rewrite lt_path_pairwise.
move/pairwiseP => pwltas.
move/eqP => lsb.
move=> x xs.
rewrite in_itv/=; apply/andP; split; first exact: sa.
rewrite -lsb (last_nth a).
have xas : x \in a :: s by rewrite in_cons; apply/orP; right.
rewrite -(nth_index a xas).
rewrite le_eqVlt; apply/predU1P.
rewrite -implyNp => nlast.
apply: pwltas.
- rewrite inE/=.
  case: ifP => // _.
  by rewrite ltnS index_mem.
- by rewrite inE//.
- rewrite /=.
 move: s lsb parts sa pas x nlast xs xas.
  apply: last_ind => // s t IH.
  rewrite last_rcons => ->.
  move=> patsb asb psb x/[swap] xsb.
  rewrite nth_index; last first.
    by rewrite in_cons; apply/orP; right.
    move/[swap] => _.
    rewrite -last_nth last_rcons => xb.
  rewrite ifF; last first.
    rewrite -subr_eq0; apply/negP/negP.
    apply: ltr0_neq0.
    rewrite subr_lt0.
    exact: asb.
  rewrite (_ : index x (rcons s b) = index x s); last first.
    rewrite -cats1 index_cat.
    rewrite ifT//.
    move: xsb.
    by rewrite mem_rcons in_cons => /predU1P; case.
  rewrite size_rcons ltnS.
  rewrite index_mem.
  move: xsb.
  rewrite mem_rcons in_cons.
  by move/predU1P; case.
Qed.

Lemma omega_max_le_oscillation a b f s :
 itv_partition a b s ->
(omega_max a b f s <= oscillation f `[a, b])%E.
Proof.
move/[dup]/itv_partition_in_itv => xab parts.
rewrite /omega_max.
apply: bigmax_le.
  exact: oscillation_ge0.
move=> n _.
apply: oscillation_sub.
case: n => //=.
have ss0 : (0 < size s)%N.
  admit.
apply: subset_itvl; rewrite bnd_simp.
  have := xab (nth b s 0).
  move/(_ (mem_nth b ss0)).
  by rewrite in_itv/= => /andP[].
move=> n.
have [|] :=  ltnP n (size s).
  move/(mem_nth b) => nths.
  apply: subset_itvScc; rewrite bnd_simp.
Admitted.

Lemma omega_max_merge a b f s t :
(omega_max a b f s < +oo)%E ->
(omega_max a b f (merge <%R s t) < +oo)%E.
Proof.
Admitted.

Lemma le_omega_max a b f s t :
  subseq s t ->
  (omega_max a b f t <= omega_max a b f s)%E.
Proof.
Admitted.

End itv_partition_length.

Section itv_partition_length_lemmas.
Context {R : realType}.
Implicit Types (a b : R) (f : R -> R).
Implicit Types (s : seq R) (x : R).

Lemma itv_partition_max_nil a b : itv_partition_max a b [::] = 0.
Proof. by rewrite /itv_partition_max big_nil. Qed.

Lemma itv_partition_rcons a b s t : itv_partition a b (rcons s t) -> t = b.
Proof. move=> [_ /=]; by rewrite last_rcons=> /eqP. Qed.

Lemma itv_partition_mem_last a b s : s != [::] -> itv_partition a b s ->
  b \in s.
Proof.
move: s; apply: last_ind => // s t _ _.
by move/itv_partition_rcons ->; rewrite mem_rcons mem_head.
Qed.

Lemma itv_partition_nonnil_last a b s : s != [::] -> itv_partition a b s ->
  forall e, last e s = b.
Proof.
move: s; apply: last_ind => // s t _ _ pst e.
rewrite last_rcons; exact: itv_partition_rcons pst.
Qed.

Lemma itv_partition_last a b s : itv_partition a b s ->
  last a s = b.
Proof.
have [s0 ps|] := pselect (s != [::]).
  exact: (itv_partition_nonnil_last s0 ps).
by move/negP/negPn/eqP ->; move/itv_partition_nil <-.
Qed.

Lemma itv_partition_lteif a b s : itv_partition a b s ->
  (a < b ?<= if ~~ (s != [::])).
Proof.
move=> ps.
have [|] := boolP (s != [::]); move=> s0/=; last exact: itv_partition_le ps.
move: (ps).
move=> [].
move/lt_path_min/allP => allas.
move=> lsb.
apply: allas.
exact: (itv_partition_mem_last s0 ps).
Qed.

Lemma itv_partition_seq1 a b x :
 itv_partition a b [:: x] -> x = b.
Proof.
by move=> abx; rewrite -(itv_partition_last abx).
Qed.

Lemma itv_partition_max_cons a b s x : s != [::] ->
  itv_partition a b (x :: s) ->
  itv_partition_max a b (x :: s) <= itv_partition_max a b s.
Proof.
case: s => // h tl _.
move=> [/= /and3P[ax xh] _ _].
rewrite /itv_partition_max/=.
rewrite 3?big_nat_recl//=.
rewrite maxA.
rewrite !num_max//=.
rewrite ge_max/=; apply/andP; split; last first.
  rewrite num_le_max; apply/orP; right => //.
rewrite num_le_max/=; apply/orP; left.
have := (lt_trans ax xh).
rewrite -subr_gt0 => ha.
rewrite (gtr0_norm ha)//.
rewrite -[in leRHS](subrKC x a).
rewrite opprD addrA.
rewrite opprB.
rewrite -subr_gt0 in ax; rewrite (gtr0_norm ax).
rewrite -subr_gt0 in xh; rewrite (gtr0_norm xh).
rewrite /maxr; case: ifP => _.
  by rewrite lerDl ltW.
by rewrite lerDr ltW.
Qed.

Lemma itv_partition_max_merge1 a b l s x :
  itv_partition_max a b s <= l ->
  itv_partition_max a b (merge <=%R s [:: x]) <= l.
Proof.
Admitted.

Lemma itv_partition_max_merge a b l s t :
  itv_partition_max a b s <= l ->
  itv_partition_max a b (merge <=%R s t) <= l.
Proof.
Admitted.

End itv_partition_length_lemmas.

Section lt_merge_lemmas.
Context {R : realType}.
Implicit Types (s t r : seq R) (x : R).

Local Notation sorted := (@sorted R <%R).
Local Notation path := (@path R <%R).
Local Notation merge := (@merge R <%R).

Definition udmerge s t := (undup (merge s t)).
(*
Lemma udmerge0r s : sorted s -> udmerge s [::] = s.
Proof.
move=> ss.
rewrite merge0r.
apply: undup_id.
exact: lt_sorted_uniq.
Qed.

Lemma udmerge0l s : sorted s -> udmerge [::] s = s.
Proof.
move=> ss.
rewrite merge0l.
apply: undup_id.
exact: lt_sorted_uniq.
Qed.

Lemma udmerge_seq1l s t x : path x s -> sorted t ->
  udmerge (x :: s) t = if x \in t then udmerge s t else x :: udmerge s t.
Proof.
move=> pxs st.
case: ifP.
  move=> xt.
  admit.
elim: t st.
  move=> _ _.
  rewrite 2?udmerge0r//.
  exact: path_sorted pxs.
move=> h t IH/= pht.
rewrite in_cons.
move/orb_false_elim => [xh xt].
Admitted.
*)

Let lt_pathNmem x s : path x s -> x \in s = false.
Proof.
move/lt_path_min/allP => ltxs.
apply/negP => xs.
have := ltxs x xs.
by rewrite ltxx.
Qed.

Lemma merge_path_seq1 x s : path x s -> merge s [:: x] = x :: s.
Proof.
elim: s => // a s IH/=/andP[xa pas].
rewrite ifF//.
by apply/negP/negP; rewrite -leNgt ltW.
Qed.

Lemma merge_cons s t x :
  path x t -> merge s (x :: t) = merge (merge s [:: x]) t.
Proof.
move=> pxt.
Admitted.

(*
Lemma udmerge_mem s x : sorted s -> x \in s -> udmerge s [:: x] = s.
Proof.
elim: s => //.
move=> h s IH shs.
rewrite in_cons => /predU1P[->|xs].
  rewrite /= ltxx/= ifT; last by rewrite mem_head.
  rewrite ifF; last first.
    exact: lt_pathNmem.
  rewrite undup_id//.
  apply: lt_sorted_uniq.
  exact: path_sorted shs.
rewrite /=ifT; last first.
  by have/lt_path_min/allP := shs; exact.
rewrite /=ifF; last first.
  rewrite mem_merge.
  rewrite mem_cat.
  apply: orb_false_intro; first exact: lt_pathNmem.
  rewrite mem_seq1.
  apply/negP => /eqP hx.
  move: xs; rewrite -hx.
  apply: (@contraFnot _ (h \in s)) => //.
  exact: lt_pathNmem.
congr cons.
apply: IH => //.
exact: path_sorted shs.
Qed.

Lemma sorted_udmerge s t :
sorted s -> sorted t -> sorted (udmerge s t).
Proof.
elim: s t => //=.
  move=> t _ st.
  rewrite merge0l.
  apply: undup_sorted => //.
  exact: lt_trans.
move=> a s IH.
elim.
  move=> pas _ /=.
  rewrite ifF; last exact: lt_pathNmem.
  rewrite /= undup_path//.
  exact: lt_trans.
move=> b t IH2 pas pbt/=.
case: ifP.
  move=> ab.
  rewrite /= ifF; last first.
    rewrite mem_merge.
    rewrite mem_cat.
    apply: orb_false_intro.
      exact: lt_pathNmem.
    by apply: lt_pathNmem; rewrite /= ab.
  rewrite /= path_min_sorted; last first.
    rewrite all_undup all_merge; apply/andP; split.
      exact: lt_path_min.
    by apply: lt_path_min => //=; rewrite ab.
  apply: IH => //.
  exact: path_sorted pas.
move/negP/negP; rewrite -leNgt.
rewrite le_eqVlt => /predU1P[ba|ba].
(*
  rewrite [X in sorted _ X](_ : _ = a :: s)//.
  case: t IH2 pbt => //=.
    move=> _ _.
    rewrite ifT; rewrite -ba; last exact: mem_head.
    rewrite ba ifF; last exact: lt_pathNmem.
    rewrite undup_id// lt_sorted_uniq//.
    exact: path_sorted pas.
  rewrite /=.

  move: pbt; rewrite {}ba => pat.
  rewrite /=.
  rewrite ifT => //; last first.
    case: t IH2 pat => //=; first by rewrite mem_head.
    by move=> ? ? _ /andP[-> _]; rewrite mem_head.
  case: t IH2 pat => //.
    move=> _ _/=.
    rewrite ifF; last exact: lt_pathNmem.
    by rewrite /= undup_path//; exact: lt_trans.
  move=> bb t H /andP[-> pbbt].
  rewrite /= ifF; last first.
    apply: lt_pathNmem.
    rewrite merge_path//.
*)

Admitted.
*)

Lemma lt_mergeA (x y z : seq R) : sorted x -> sorted y -> sorted z ->
 (merge x (merge y z)) = merge (merge x y) z.
Proof.
move: x y z.
elim=> // x xs IHxs; elim=> // y ys IHys; elim=> [|z zs IHzs] /=.
  by case: ifP.
move=> px py pz.
case: ifP; case: ifP => /= ltxy ltyz.
- rewrite ltxy.
(*
- by rewrite lexy (leT_tr lexy leyz) -IHxs /= leyz.
- by rewrite lexy leyz -IHys.
- case: ifP => lexz; first by rewrite -IHxs //= leyz.
  by rewrite -!/(merge (_ :: _)) IHzs /= lexy.
- suff->: leT x z = false by rewrite leyz // -!/(merge (_ :: _)) IHzs /= lexy.
  by apply/contraFF/leT_tr: leyz; have := leT_total x y; rewrite lexy.
*)
Admitted.

End lt_merge_lemmas.

Definition disj_seq {T : eqType}(s t : seq T) :=
[disjoint [set` s] & [set` t]].

Lemma disj_seq_allP {T : eqType} (s t : seq T) :
  disj_seq s t <-> (all (fun x => x \notin s) t /\ all (fun x => x \notin t) s).
Proof.
Admitted.

Section itv_partition_lemmas.
Context {R : realType}.
Variables (a b : R) (f : R -> R).
Hypothesis (ab : a < b).
Implicit Types (s : seq R) (x : R).

Lemma itv_partition_merge s t :
 itv_partition a b s ->
 itv_partition a b t ->
 disj_seq s t -> itv_partition a b (merge <%R s t).
Proof.
move=> ps pt.
move=> /disj_seq_allP[/allP ts /allP st].
Admitted.

Lemma itv_partition_udmerge s t :
 itv_partition a b s ->
 itv_partition a b t ->
 itv_partition a b (udmerge s t).
Proof.
Admitted.

End itv_partition_lemmas.

Section lemma5.
Context {R : realType}.
Variables (a b : R) (f : R -> R).
Hypothesis (ab : a < b).
Implicit Types (s : seq R) (x : R).

Arguments unif_continuous : clear implicits.

Let variation_merge1 s :
  itv_partition a b s -> (* not necessary? *)
  forall x, x \in `]a, b[ -> x \notin s ->
    ((variation a b f (merge <%R s [:: x]))%:E <=
          (variation a b f s)%:E + 2 * omega_max a b f s)%E.
Proof.
move=> parts.
move=> x; rewrite in_itv/= => /andP[ax xb] xs.

have : exists s0 s1 : R, [/\ s0 \in s, s1 \in s &
 merge <%R s [:: x] = itv_partitionL s s0 ++ [:: x; s1] ++ itv_partitionR s s1].
 admit.

(*
rewrite (@in_itv_partition _ x (merge <%R s [:: x])); last 2 first.
- admit.
- admit.
(* rewrite variation_cat. *)
have Rx : (itv_partitionR (merge <%R s [:: x]) x) = itv_partitionR s x.
  admit.
rewrite (@variation_cat _ _ _ x) ?ltW//; last 2 first.
- apply: (itv_partitionLP ax xb) => //.
  rewrite itv_partition_merge_concat1//; last first.
    have [+ _] := parts.
    exact: path_sorted.
  apply: (@itv_partition_cat _ _ x).
  + exact: (itv_partitionLP ax xb).
  + exact: (itv_partitionRP ax xb).
- rewrite Rx.
  exact: (itv_partitionRP ax xb).
rewrite Rx.
rewrite merge_rcons; last first.
  admit.
rewrite itv_partitionL_rcons1; last first.
  admit.
rewrite -cats1.
rewrite (@variation_cat _ _ _ ) //; last 3 first.
- exact: ltW.
- admit.
- admit.
rewrite -addrAC EFinD.
*)
Admitted.

Let variation_merge l s t :
  itv_partition a b s -> itv_partition_max a b s <= l ->
  itv_partition a b t ->
  disj_seq s t ->
  ((variation a b f (merge <%R s t))%:E <= (variation a b f s)%:E +
  (size t)%:R%:E * 2 * omega_max a b f s)%E.
Proof.
have [->|] := pselect (omega_max a b f s = +oo%E).
  move=> _ _ _ _.
  rewrite -muleA mulry/= gtr0_sg// mul1e.
  case: t => /=.
    rewrite merge0r mul0e adde0//.
  move=> ht t.
  rewrite mulry gtr0_sg ?mul1e//.
  rewrite addey//.
  exact: leey.
move/eqP; rewrite -ltey => maxoo.
elim: t s maxoo.
- move=> s _ _.
  by rewrite merge0r 2!mul0e adde0.
move=> h t IH s maxoo ps sl pht disjst.
rewrite merge_cons; last first.
  have [+ _] := pht.
  by rewrite /= => /andP[].
apply: (le_trans (IH _ _ _ _ _ _)).
- admit. (* lemma *)
- admit.
- admit.
- admit.
- admit.
have hab : h \in `]a, b[.
  admit.
rewrite -(natr1 (size t)) (EFinD (size t)%:R).
rewrite 2?muleDl ?mul1e => //; last first.
  admit.
rewrite addeA.
apply: (@le_trans _ _ ((variation a b f (merge <%R s [:: h]))%:E +
  ((size t)%:R)%:E * 2 * omega_max a b f s)%E).
  rewrite leeD2l//.
  rewrite lee_pmul//.
    exact: omega_max_ge0.
  apply: le_omega_max.
  exact: subseq_merge.
rewrite -addeAC leeD2r//.
apply: variation_merge1 => //.
have /disj_seq_allP[/allP + _] := disjst.
apply.
exact: mem_head.
Admitted.

(*
apply: last_ind.
- move=> s _ _.
  by rewrite merge0r 2!mul0e adde0.
move=> h t IH s ps sl pht.
rewrite merge_rcons.

apply: (le_trans (IH _ _ _ _)).
- admit.
- admit.
- admit.

rewrite lt_mergeA.
*)
(*

rewrite mergeA; last 2 first.
- exact: lt_total.
- exact: le_trans.

apply: (le_trans (IH _ _ _ _)).
- admit. (* add an assumption (h \notin s), or weaken the statement? *)
- exact: itv_partition_max_merge1.
- rewrite -(@itv_partitionR_all_gt _ t h); last first.
   apply/allP.
   rewrite allrel1l in all_lt_ht.
rewrite (_ : t = itv_partitionL 
  itv_partitionL_all_lt
  apply: itv_partition_cons.
xxx

elim: s t => /=.
- move=> t [].
  move=> /itv_partition_nil <- _.
  move/itv_partitionxx -> => /=.
  by rewrite variation_nil add0e 2!mul0e.
move=> hs s IH t.
move=> [].

rewrite (@in_itv_partition _ x (merge <%R s [:: x])); last 2 first.

(*
- move=> + /itv_partition_nil; move/[swap] <-.
  move=> [/itv_partitionxx -> _]/=.
  by rewrite 2!mul0e adde0.

move=> h t IH pmaxl partht/=.
elim: s .
rewrite /merge.
elim: s IH pmaxl => /=.
rewrite /merge.
*)
*)

Lemma lemma5' :
  {within `[a, b], continuous f} ->
  bounded_variation a b f ->
  forall A : R, (0%:E < A%:E < total_variation a b f)%E ->
    exists l, forall p, itv_partition_with_max a b l p ->
              A < variation a b f p.
Proof.
move=> cf.
move/(bounded_variationP f (ltW ab)) => bvf.
move=> A /andP[]; rewrite lte_fin => A0.
set Tf : \bar R := total_variation a b f.
rewrite /Tf/total_variation.
move=> ATf.
have TfA0 : 0 < fine Tf - A.
  admit.
have [eV' /= [V' [X' partX' X'V'] V'eV']] := ub_ereal_sup_adherent TfA0 bvf.
rewrite -/(total_variation a b f) -/Tf.
rewrite EFinN EFinB fineK//.
rewrite oppeB; last first.
  by rewrite fin_num_adde_defl.
rewrite addeA subee// add0r.
rewrite -{}V'eV' lte_fin => AV'.
have : unif_continuous (subspace `[a, b]) R f.
  admit.
move/unif_continuousP => /=.
pose m := size X'.
pose eps := ((V' - A) / (4 * m)%:R).
have eps0 : 0 < eps.
  admit.
move/(_ _ eps0) => [d d0 unifcf].
exists d => p pmaxd.

apply: (@lt_le_trans _ _ ((V' + A) / 2)).
  (* AV' *)
  admit.
pose V0 : R := variation a b f (merge <%R p X').
apply: (@le_trans _ _ (V0 - (V' - A) / 2)).
  (* V' < V0, variation_subseq *)
  admit.
rewrite lerBlDr -lee_fin EFinD.
have [pabp abpd] := pmaxd.
have abp_led : itv_partition_max a b p <= d.
  by rewrite le_eqVlt; apply/predU1P; left.
apply: (le_trans (@variation_merge _ p X' pabp abp_led partX' _)).
  admit.
apply: leeD2l.
(* unifcf *)
Admitted.

Lemma lemma5 :
  {within `[a, b], continuous f} ->
  ereal_inf
     [set v%:E | v in variations_with_max a b f l] @[l --> 0^'+]
       --> total_variation a b f.
Proof.
move=> cf.
rewrite /total_variation.
rewrite /variations.
rewrite image_comp.

Abort.

End lemma5.
