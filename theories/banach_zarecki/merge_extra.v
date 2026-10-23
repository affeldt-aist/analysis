From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import boot order ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import interval_inference archimedean.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp contra classical_sets functions.
From mathcomp Require Import cardinality fsbigop interval set_interval.
From mathcomp Require Import reals ereal topology normedtype sequences.
From mathcomp Require Import real_interval esum measure.
From mathcomp Require Import lebesgue_stieltjes_measure lebesgue_measure numfun.
From mathcomp Require Import measurable_realfun.
From mathcomp Require Import realfun exp derive.
From mathcomp Require Import absolute_continuity bz_mathcomp_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition disj_seq {T : eqType} (s t : seq T) :=
  [disjoint [set` s] & [set` t]].

Lemma disj_seq_sym {T : eqType} (s t : seq T) :
  disj_seq s t = disj_seq t s.
Proof. by rewrite /disj_seq disj_set_sym. Qed.

Lemma disj_seq_allP {T : eqType} (s t : seq T) :
  disj_seq s t <-> all (fun x => x \notin s) t.
Proof.
split.
- move=> dsst.
  + apply/allP => x xt; apply/negP => xs.
    have := dsst.
    move/disj_set2P/eqP.
    apply/negP.
    apply/set0P.
    by exists x.
- move/allP=> ts.
  apply/disj_setPRL => x/= xt.
  apply/negP.
  exact: ts.
Qed.

Lemma disj_seq_filterr {T : eqType} (s t : seq T) (P : pred T) :
  disj_seq s t -> disj_seq s [seq x <- t | P x].
Proof.
move/disj_seq_allP => /allP st.
apply/disj_seq_allP; apply/allP => x; rewrite mem_filter.
by move=> /andP[_ xt]; exact: st.
Qed.

Lemma disj_seq_filterl {T : eqType} (s t : seq T) (P : pred T) :
  disj_seq s t -> disj_seq [seq x <- s | P x] t.
Proof.
by rewrite disj_seq_sym => ?; rewrite disj_seq_sym; exact: disj_seq_filterr.
Qed.

Lemma disj_seq_consr {T : eqType} (s t : seq T) (a : T) :
  disj_seq s (a :: t) -> disj_seq s t.
Proof.
move/disj_seq_allP => /allP st.
apply/disj_seq_allP; apply/allP => x memx.
by apply: st; rewrite in_cons memx orbT.
Qed.

Lemma disj_seq_consl {T : eqType} (s t : seq T) (a : T) :
  disj_seq (a :: s) t -> disj_seq s t.
Proof.
by rewrite disj_seq_sym => H; rewrite disj_seq_sym; exact: disj_seq_consr H.
Qed.

Section merge_lemmas.
Context {T : Type} {r : rel T}.
Implicit Type (s t : seq T).

Lemma merge_step (a : T) (s : seq T) (b : T) (t : seq T) :
  merge r (a :: s) (b :: t) =
     if r a b then a :: merge r s (b :: t) else b :: merge r (a :: s) t.
Proof. by []. Qed.

Lemma merge0r s : merge r s [::] = s.
Proof. by elim: s. Qed.

End merge_lemmas.

Section merge_lemmas_eqType.
Context {T : eqType} {r : rel T}.
Implicit Types (s t : seq T) (x : T).

Lemma merger_cons s t x : all (r x) t ->
  merge r (x :: s) t = x :: merge r s t.
Proof.
elim: t.
  by rewrite 2!merge0r.
move=> b t' IH.
move/allP => allxt.
rewrite /=.
rewrite ifT//.
apply: allxt.
exact: mem_head.
Qed.

Lemma merge_cons_mergel s t x :
  transitive r ->
  all (r x) t -> merge r s (x :: t) = merge r (merge r s [:: x]) t.
Proof.
move=> transr.
elim: s => /=.
  elim: t => // b t' IHt.
  rewrite /= => /andP[rxb rbt'].
  by rewrite rxb.
move=> a s' IH pxt.
case: ifP.
- rewrite (IH pxt).
  move=> rax.
  rewrite merger_cons//.
  apply/allP => z zt.
  apply: (@transr x _ _ rax).
  by have /allP := pxt; exact.
- move=> raxf.
  by rewrite merger_cons.
Qed.

Lemma subseq_mergel s t : subseq s (merge r s t).
Proof.
elim: s t => [t|a l ih t]; first exact: sub0seq.
elim: t l ih => // t0 t1 ih s IH.
rewrite /=; case: ifPn => rat0.
  by rewrite /= eqxx IH.
rewrite /=; case: ifPn => [/eqP|] at0.
  move: rat0; rewrite -{}at0 {t0} => raa.
  rewrite [X in subseq _ X](_ : _ = merge r (a :: s) t1)//.
  exact: (subseq_trans (subseq_cons _ _) (ih s IH)).
rewrite [X in subseq _ X](_ : _ = merge r (a :: s) t1)//.
exact: ih.
Qed.

Lemma subseq_merger s t : transitive r ->
  sorted r t -> subseq t (merge r s t).
Proof.
move=> rtrans.
elim: t s => [s _|t0 t1 ih s]; first exact: sub0seq.
elim: s t0 t1 ih => // s0 s1 ih t0 t1 IH t0t1.
rewrite /=; case: ifPn => rs0t0.
  rewrite /=; case: ifPn => [/eqP ->|t0s0]; last exact: ih.
  have : subseq (s0 :: t1) (merge r s1 (s0 :: t1)).
    by apply: ih => //; exact: path_le t0t1.
  by apply: subseq_trans; exact: subseq_cons.
rewrite /= eqxx.
rewrite [X in subseq _ X](_ : _ = merge r (s0 :: s1) t1)// IH//.
exact: path_sorted t0t1.
Qed.

Lemma merge_neq0 s t :
  (s != [::]) || (t != [::]) -> merge r s t != [::].
Proof.
elim: t s => [s|t0 t1 ih s].
  by rewrite eqxx orbF merge0r.
move=> /orP[|_].
  by move: s => [//|s0 s1 _ /=]; case: ifPn.
by move: s => [//|s0 s1/=]; case: ifPn.
Qed.

End merge_lemmas_eqType.

Section merge_lemmas_orderType.

Context {d} {T : orderType d}.
Implicit Types (a b : T) (s t : seq T).

Lemma all_merge1rl (s : seq T) (x : T) :
  all (>= x)%O s -> merge <=%O s [:: x] = x :: s.
Proof.
elim: s => // a s IH.
rewrite merge_step/= => /andP[+ xs].
rewrite le_eqVlt => /predU1P[xa|xa].
  subst a; rewrite lexx IH//.
rewrite ifN//.
by rewrite -ltNge.
Qed.

Lemma all_merge1rr (s : seq T) (x : T) :
  all (<= x)%O s -> merge <=%O s [:: x] = rcons s x.
Proof.
elim: s => //= a s IH /andP[ax sx].
by rewrite ax IH.
Qed.

Lemma merge_ltEle (s t : seq T) :
 sorted <=%O s -> sorted <=%O t ->
 merge <%O s t = merge <=%O s t.
Proof.
elim: s t => // a s IH t.
elim: t a s IH.
  by [].
move=> b t IHt a s IHs sorted_as sorted_bt.
rewrite 2!merge_step.
case: ifPn => [ab|].
  rewrite ifT; first exact: ltW.
  rewrite IHs//.
  exact: path_sorted sorted_as.
rewrite -leNgt => ba.
case: ifPn => [ab|_]; last first.
  rewrite IHt//.
  exact: path_sorted sorted_bt.
have {ab ba}eqab : a = b by apply/eqP; rewrite eq_le ab ba.
subst a.
rewrite IHt//; first exact: path_sorted sorted_bt.
rewrite merger_cons//; first exact: le_path_min.
rewrite merge_cons_mergel.
- exact: le_trans.
- exact: le_path_min.
rewrite all_merge1rl//; first exact: le_path_min.
rewrite merger_cons//.
exact: le_path_min.
Qed.

Lemma last_lt_merger_rcons a b s t :
  all (<= b)%O t -> last a (merge <%O (rcons s b) t) = b.
Proof.
elim: s t a.
  elim=> //.
  move=> y t IH a.
  rewrite (_ : all (<= b)%O (y :: t) = (y <= b)%O && (all (<= b)%O t))//.
  move=> /andP[yb tb].
  rewrite /= (le_gtF yb).
  exact: IH.
move=> s0 s1 IHs.
elim.
  by move=> a _; rewrite /= last_rcons.
move=> t0 t1 IHt a.
rewrite (_ : all (<= b)%O (t0 :: t1) = (t0 <= b)%O && (all (<= b)%O t1))//.
move=> /andP[t0b t1b].
rewrite /=.
case: ifP.
  move=> s0t0/=.
  by apply: IHs => //=; apply/andP; split.
move/negP/negP; rewrite -leNgt =>t0s0/=.
exact: IHt.
Qed.

Lemma last_lt_mergel_rcons a b s t :
  all (<= b)%O s ->
  sorted <=%O s -> (* (b \in s -> last a s = b)? *)
  last a (merge <%O s (rcons t b)) = b.
Proof.
Abort.

Lemma merge_cons_step_le (x y : T) s t :
  merge <%O (x :: s) (y :: t) =
  if (x <= y)%O then x :: (merge <%O s (y :: t)) else y :: (merge <%O (x :: s) t).
Proof.
rewrite merge_step; case: ifPn.
  by move/ltW => ->.
rewrite -leNgt le_eqVlt => /predU1P[->|].
  rewrite lexx.
  elim: s t => //=.
    elim => // t0 t1 IH.
Abort.

Lemma last_lt_mergel_rcons a b s t :
  all (<= b)%O s -> sorted <=%O s ->
 last a (merge <%O s (rcons t b)) = b.
Proof.
elim: t s a.
  elim/last_ind => //.
  move=> s y IH a.
  rewrite (_ : all (<= b)%O (rcons s y) = (y <= b)%O && (all (<= b)%O s))//.
    by rewrite all_rcons.
  move=> /andP[yb sb]/=.
  move: yb; rewrite le_eqVlt => /predU1P[yb|yb]//.
    by rewrite yb last_lt_merger_rcons//= lexx.
  elim: s sb IH => //=.
    by move=> _ _; rewrite yb.
  move=> s0 s1 IHs sb IH s0s1y.
Abort.

Lemma lastr_lt_merge a b s t :
  s != [::] ->
  last a s = b ->
  (all (<= b)%O t) ->
  last a (merge <%O s t) = b.
Proof.
elim/last_ind: s => // s x IHs _.
rewrite last_rcons => xb.
move=> tb; rewrite last_lt_merger_rcons//.
by rewrite xb.
Qed.

End merge_lemmas_orderType.

Lemma path_merge d {R : orderType d} (a : R) s h :
  (a < h)%O ->
  path <%O a s -> path <=%O a (merge <%O s [:: h]).
Proof.
elim: s a h => [a h ah _/=|s0 s1 ih a h ah].
  by rewrite ltW// andbT.
rewrite /= => /andP[as0 s0s1].
case: ifPn => s0h /=.
  by rewrite (ltW as0)/= ih.
rewrite (ltW ah)/=.
rewrite leNgt/= s0h/=.
by apply: sub_path s0s1 => x y /ltW.
Qed.

Lemma le_sorted_mergeA d {R : orderType d}  (r s t : seq R) :
   sorted <=%O r -> sorted <=%O s -> sorted <=%O t ->
   merge <%O r (merge <%O s t) =
   merge <%O (merge <%O r s) t.
Proof.
move=> sr ss st.
rewrite !merge_ltEle//.
- by rewrite merge_sorted//; exact: le_total.
- by rewrite merge_sorted//; exact: le_total.
by rewrite mergeA//; first exact: le_total; exact: le_trans.
Qed.

Lemma le_sorted_merge_sym d {R : orderType d} (s t : seq R) :
  sorted <=%O s -> sorted <=%O t -> merge <=%O s t = merge <=%O t s.
Proof.
elim: s t.
  by move=> t; rewrite merge0r.
move=> a s IHs t.
elim: t a s IHs => // b t IHt a s IHs sas sbt.
rewrite 2!merge_step.
case: ifPn => [|]; last rewrite -ltNge; first rewrite le_eqVlt => /predU1P[|].
- move=> ?; subst a.
  rewrite lexx.
  rewrite IHs//; first exact: path_sorted sas.
  rewrite merger_cons; first exact: le_path_min.
  rewrite -IHt//; first exact: path_sorted sbt.
  rewrite merger_cons; first exact: le_path_min.
  rewrite IHs//.
    exact: path_sorted sas.
  exact: path_sorted sbt.
- move=> ab.
  rewrite ifN; first by rewrite -ltNge.
  rewrite IHs//.
  exact: path_sorted sas.
- move=> ba.
  rewrite ifT ?ltW//.
  rewrite IHt//.
  exact: path_sorted sbt.
Qed.

Lemma sorted_undup_merge_subseq d {R : orderType d} (s t : seq R) :
  sorted <=%O s -> sorted <%O t ->
  subseq s t -> undup (merge <%O t s) = t.
Proof.
move=> ss st subseq_st.
have lest : sorted <=%O t by exact: sorted_ltW.
apply: (le_sorted_eq _ lest).
  apply: undup_sorted; first exact: le_trans.
  rewrite merge_ltEle//.
  apply: merge_sorted => //; first exact: le_total.
rewrite -{2}(@undup_id _ t).
  by have := st; rewrite lt_sorted_uniq_le => /andP[].
apply: perm_undup.
move=> x.
rewrite mem_merge mem_cat.
apply: orb_idr.
exact: mem_subseq.
Qed.

Fixpoint merge_lt_seq d {R : orderType d} (l s : seq R) :=
  match s with
  | [::] => l
  | h :: s' =>
     [seq x <- l | x < h]%O ++ [:: h] ++ merge_lt_seq [seq x <- l | h < x]%O s'
  end.

Lemma merge_lt_seq_merge d {R : orderType d} (t s : seq R) :
  sorted <%O t -> sorted <%O s ->
  disj_seq t s ->
  merge <%O t s = merge_lt_seq t s.
Proof.
elim: s t => //= a s.
- move=> _ _.
  by rewrite merge0r.
move=> IH t st pas dast.
rewrite -IH.
- exact: lt_sorted_filter.
- exact: path_sorted pas.
- apply: disj_seq_filterl.
  exact: disj_seq_consr dast.
elim: t st dast; first by [].
move=> b t IH' pbt dasbt /=.
case: ifPn => [ba|]; last rewrite -leNgt le_eqVlt => /predU1P[ab|ab].
- rewrite cat_cons; congr cons.
  rewrite ifN.
    by rewrite -leNgt ltW.
  apply: IH'.
   exact: path_sorted pbt.
  exact: disj_seq_consl dasbt.
- have /disj_seq_allP/allP := dasbt.
  move/(_ a (mem_head a s)).
  rewrite in_cons; move/norP => [/negP].
  by rewrite ab.
- rewrite ab.
    have ->/= : [seq x <- t | x < a]%O = [::].
      apply/path_lt_filter0.
      apply: path_le ab pbt.
      exact: lt_trans.
    congr cons.
    rewrite path_lt_filterT.
      apply: path_le ab pbt.
      exact: lt_trans.
  by elim: s IH pas IH' dasbt.
Qed.

Lemma sorted_merge_lt_seq  d {R : orderType d} (l s : seq R) :
  sorted <%O l -> sorted <%O s ->
  sorted <%O (merge_lt_seq l s).
Proof.
case: s => //= hs s sl ps.
rewrite sorted_cat_cons sorted_filter_rcons => //=.
elim: s hs l sl ps => /=.
  move=> ? ? ? ?; exact: sorted_filter_path.
move=> hs s IH hhs l sl /andP[hhshs ps].
rewrite cat_path; apply/andP; split.
  rewrite -filter_predI/=.
  under eq_filter do rewrite /= andbC.
  rewrite filter_predI.
  apply: sorted_filter_path.
  exact: lt_sorted_filter.
rewrite /=; apply/andP; split.
  move: (mem_last hhs [seq x <- [seq x <- l | hhs < x] | x < hs]%O).
  rewrite inE => /predU1P[->//|].
  by rewrite mem_filter => /andP[].
apply: IH => //.
exact: lt_sorted_filter.
Qed.

Lemma merge_filter_undup d {R : orderType d} (s t : seq R) :
  sorted <%O s -> sorted <%O t ->
  let t' := [seq x <- t | x \notin s] in
  merge <%O s t' = undup (merge <%O s t).
Proof.
move=> sorted_s sorted_t t'.
set t0 := [seq x <- t | x \in s].
have less : sorted <=%O s by exact: sorted_ltW.
have lest : sorted <=%O t by exact: sorted_ltW.
have -> : merge <%O s t = merge <%O (merge <%O s t') t0.
  rewrite (filterC_split s lest).
  rewrite merge_ltEle//; first by rewrite -filterC_split.
  rewrite [X in merge _ _ X]le_sorted_merge_sym ?le_sorted_filter//.
  rewrite -merge_ltEle//.
    by rewrite le_sorted_merge_sym ?le_sorted_filter// -filterC_split.
  rewrite -merge_ltEle// ?le_sorted_filter//.
  by rewrite le_sorted_mergeA// ?le_sorted_filter.
rewrite sorted_undup_merge_subseq//.
- exact: le_sorted_filter.
- rewrite merge_lt_seq_merge//.
  + exact: lt_sorted_filter.
  + by apply/disj_seq_allP/allP => x; rewrite mem_filter => /andP[].
  apply: sorted_merge_lt_seq => //.
  exact: lt_sorted_filter.
apply: (@subseq_trans _ s); last exact: subseq_mergel.
rewrite /t0 lt_sorted_mem_filter_exchange//.
exact: filter_subseq.
Qed.

Section merge_cats1.
Context {d} {R : orderType d}.
Variables (f : R -> R).
Implicit Types (s : seq R) (x : R).

Lemma merge_cats1 s t x : sorted <=%O s -> sorted <=%O (t ++ [:: x]) ->
  merge <=%O s (t ++ [:: x]) = merge <=%O (merge <=%O s t) [:: x].
Proof.
move=> ss st.
elim: s t x ss st.
  move=> t x ss st /=.
  rewrite sorted_merge//=; first exact: le_trans.
  by rewrite sorted_merge//; exact: le_trans.
move=> s0 s1 ih t.
move: t s0 s1 ih.
elim=> // t0 t1 ih' s0 s1 ih x ss stx.
rewrite /=.
rewrite -!/(merge <=%O (s0 :: s1) _).
have t0x : (t0 <= x)%O.
  move: stx.
  rewrite /sorted/=.
  move/le_path_min => /allP; apply.
  by rewrite mem_cat mem_head orbT.
have [s0t0|t0s0] := leP s0 t0.
  rewrite -/((t0 :: t1) ++ [:: x]).
  rewrite ih//; first exact: path_sorted ss.
  move: s0t0.
  rewrite le_eqVlt => /predU1P[s0t0|s0t0].
    subst t0.
    by rewrite merge_step// t0x.
  rewrite merge_step ifT//.
  apply: ltW.
  apply: lt_le_trans s0t0 t0x.
rewrite ih'//.
  move: stx.
  apply: subseq_sorted; first exact: le_trans.
  rewrite [in X in subseq _ X]/=.
  by apply: subseq_cons.
rewrite [RHS]merger_cons//.
by rewrite /=andbT.
Qed.

End merge_cats1.

Section sorted_merge1.

Context {d} {T : orderType d}.
Implicit Types (a b x : T) (s : seq T).

Lemma sorted_merge1 h s : h \notin s ->
  sorted <%O s -> sorted <%O (merge <%O s [:: h]).
Proof.
elim: s h => // s0 s1 ih h hs /= s0s1.
have [s0h|s0h]/= := ltP s0 h.
  have s1h : sorted <%O (merge <%O s1 [:: h]).
    apply: ih (path_sorted s0s1).
    by apply: contra hs; rewrite inE orbC => ->.
  rewrite path_min_sorted//; apply/allP => x.
  rewrite mem_merge mem_cat => /orP[xs1|].
    by move/order_path_min : s0s1 => /(_ lt_trans)/allP/(_ _ xs1).
  by rewrite mem_seq1 => /eqP ->.
rewrite lt_neqAle s0h andbT.
by move: hs; rewrite !inE negb_or => /andP[->].
Qed.

End sorted_merge1.
