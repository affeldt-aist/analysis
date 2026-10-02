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
From mathcomp Require Import realfun exp derive borel_hierarchy.
From mathcomp Require Import absolute_continuity.

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

(* NB: unused *)
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

(* NB: unused *)
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
