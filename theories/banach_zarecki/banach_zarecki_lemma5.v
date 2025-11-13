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


Section itv_partition_length.
Context {R : realType}.
Implicit Types (a b : R) (f : R -> R).

Definition itv_partition_max a b s : R := let pnth := nth b (a :: s) in
  \big[maxr/0%R]_(0 <= n < size s) `|pnth n.+1 - pnth n|%R.

Definition itv_partition_with_max a b l s :=
  itv_partition a b s /\ itv_partition_max a b s = l.

Definition variations_with_max a b f l : set R :=
   [set variation a b f s | s in itv_partition_with_max a b l].

Definition omega_max a b f s : \bar R :=
   \big[maxe/0%E]_(0 <= n < size s) oscillation f
    `[(nth b (a :: s)) n, (nth b (a :: s)) n.+1].

End itv_partition_length.

Section lemma5.
Context {R : realType}.
Variables (a b : R) (f : R -> R).
Hypothesis (ab : a < b).

Implicit Types (s : seq R) (x : R).

Arguments unif_continuous : clear implicits.

Lemma itv_partitionL_nil x :
  itv_partitionL [::] x = [:: x].
Proof. by []. Qed.

Lemma itv_partitionR_nil x :
  itv_partitionR [::] x = [::].
Proof. by []. Qed.

Lemma itv_partitionL_rcons1 s x :
  path <%R a (rcons s x) ->
  itv_partitionL (rcons s x) x = s ++ [:: x].
Proof.
move=> ss.
rewrite /itv_partitionL.
Admitted.

Lemma itv_partitionL_all_lt l x :
 sorted <%R l -> all (> x) l ->
 itv_partitionL l x = l ++ [:: x].
Proof.
Admitted.

Lemma itv_partitionL_cons h l x :
  h < x ->
  itv_partitionL (h :: l) x = h :: itv_partitionL l x.
Proof.
by move=> hx; rewrite /itv_partitionL/= hx rcons_cons.
Qed.

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

Lemma itv_partitionR_id l x :
  all (> x) l -> itv_partitionR l x = l.
Proof.
exact/all_filterP.
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
  rewrite itv_partitionR_id//.
  apply: lt_path_min.
  exact: (path_lt_head xh).
Qed.

Let variation_merge1 s :
  itv_partition a b s -> (* not necessary? *)
  forall x, x \in `[a, b] ->
    ((variation a b f (merge <%R s [:: x]))%:E <=
          (variation a b f s)%:E + 2 * omega_max a b f s)%E.
Proof.
move=> parts.
move=> x; rewrite in_itv/= => /andP[ax xb].
rewrite (@in_itv_partition _ x (merge <%R s [:: x])); last 2 first.
- admit.
- admit.
(* rewrite variation_cat. *)
Admitted.

Let variation_merge l s t :
 itv_partition_with_max a b l s ->
  itv_partition a b t ->
  ((variation a b f (merge <%R s t))%:E <= (variation a b f s)%:E +
  (size t)%:R%:E * 2 * omega_max a b f s)%E.
Proof.
elim: t => /=.
- move=> _ _.
  rewrite 2!mul0e adde0 allrel_merge ?cats0; last by exact: allrel0r.
  exact: lexx.
move=> h t IH pmaxl partht.
rewrite /merge.
elim: s IH pmaxl => /=.
rewrite /merge.


Admitted.

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
apply: (le_trans (@variation_merge _ p X' pmaxd partX')).
apply: leeD2l.
(* unifcf *)
Admitted.

Lemma lemma5 a b f :
  {within `[a, b], continuous f} ->
  ereal_inf
     [set v%:E | s in variations_with_max a b f l] @[l --> 0^'+]
       --> total_variation a b f.
Proof.
move=> cf.
rewrite /total_variation.
rewrite /variations.
rewrite image_comp.
apply/cvgrPdist_lt.
Abort.

End lemma5.
