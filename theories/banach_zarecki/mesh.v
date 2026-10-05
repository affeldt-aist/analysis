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

(**md**************************************************************************)
(*                                                                            *)
(* `mesh a b s`                                                               *)
(* : the mesh of the subdivision of the interval $[a, b]$, i.e., the max      *)
(* : of $|p_{i+1} - p_i|$ where $p$ is the list representing the subdivision  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* TODO: move *)
Lemma bigmaxr_morph {R : realType} n (f : nat -> R) :
  \big[maxr/0]_(0 <= i < n) `|f i| =
  (\big[maxr/0%:nng]_(0 <= i < n) `|f i|%:nng)%:num.
Proof.
elim/big_ind2 : _ => //= x1 _ y1 _ -> ->.
rewrite !/maxr.
case: ifPn => x1y1; case: ifPn => // y1x1.
  by apply/eqP; rewrite eq_le (ltW x1y1) andbT leNgt.
by apply/eqP; rewrite eq_le andbC leNgt x1y1/= ltW.
Qed.

Section mesh_def.
Context {R : realType}.
Implicit Types (a : R) (f : R -> R) (s t : seq R) (x : R).

(* NB: We can use 0 as a default element because inside the definition the list
   is never addressed out-of-bounds. *)
Definition mesh a s : R :=
  let pnth := nth 0 (a :: s) in
  (\big[@maxr {nonneg R}/0%:nng]_(0 <= i < size s) `|pnth i.+1 - pnth i|%:nng)%:num.

End mesh_def.

Section mesh_lemmas.
Context {R : realType}.
Implicit Types (a : R) (f : R -> R) (s : seq R) (x : R).

Lemma mesh_ge0 a s : 0 <= mesh a s.
Proof. by rewrite /mesh. Qed.

Lemma mesh0 a : mesh a [::] = 0.
Proof.
by rewrite /mesh/= big_mkord big_ord0.
Qed.

Lemma mesh_seq1 a x : mesh a [:: x] = `|x - a|.
Proof.
rewrite /mesh big_nat1_id/=.
rewrite widen_itvE.
(* note: _%:num := num _ *)
rewrite num_max/=.
by rewrite max_l.
Qed.

Lemma mesh_cons a x s :
  mesh a (x :: s) = maxr `|x - a| (mesh x s).
Proof.
by rewrite /mesh -!bigmaxr_morph/= big_nat_recl.
Qed.

Lemma mesh_cat a s t :
  mesh a (s ++ t) = maxr (mesh a s) (mesh (last a s) t).
Proof.
elim: s a.
  by move=> ?; rewrite mesh0 max_r// mesh_ge0.
move=> s0 s1 IH a.
by rewrite !mesh_cons IH maxA.
Qed.

Lemma mesh_flatten a b (ss : seq (seq R)) :
  all (fun s => s != [::]) ss ->
  all (fun x => a <= x <= b) (flatten ss) ->
  sorted <=%R (flatten ss) ->
  mesh a (flatten ss) =
  \big[maxr/0%R]_(i < size ss)
    mesh
     (nth b [seq last b s | s <- [:: a] :: ss] i)
     (nth [::] ss i).
Proof.
elim: ss a.
  by move=> ?; rewrite mesh0 big_ord0.
move=> s.
case => //.
  rewrite /= => IH a.
  rewrite cats0 andbT => s0 abs ss.
  (* rewrite big_ord1. *)
  rewrite big_ord_recl big_ord0/= max_l//.
  exact: mesh_ge0.
move=> s' ss IH a/=.
move=> /andP[s0 /andP[s'0 ss0]].
rewrite all_cat => /andP[abs abss].
have last_s t : last t s = last 0 s.
  by apply: set_last_default; case: s s0 abs.
have : flatten (s' :: ss) != [::] by exact: cons_flatten_neq_nil.
move/(sorted_catP b s0) => [_ Hsorted2].
move/Hsorted2 => [sorted_s sorted_s'ss ls_hs'].
rewrite big_ord_recl/=.
  under eq_bigr do rewrite add0n.
rewrite -IH//.
- by rewrite /= s'0 ss0.
- move: abss => /=; rewrite !all_cat => /andP[abs' abss].
  apply/andP; split.
    apply/all_andbP; move/all_andbP/andP : abs' => [_ ->]; rewrite andbT.
    apply/(all_nthP b) => x xs'.
    apply: (le_trans ls_hs').
    rewrite head_flatten// -nth0.
    move: sorted_s'ss.
    move/cat_sorted2 => [+ _].
    move/le_sorted_leq_nth; apply => //.
    by rewrite inE; apply: leq_ltn_trans xs'.
- apply/all_andbP.
  move/all_andbP : abss => /andP[_ ->]//; rewrite andbT.
  apply/(all_nthP b) => x xs'.
  apply: (le_trans ls_hs').
  rewrite head_flatten// -nth0.
  have := sorted_s'ss => /=.
  have : flatten ss != [::].
    case: ss IH ss0 Hsorted2 sorted_s'ss ls_hs' xs' => //.
    move=> // hss ss _ /andP[ss0 _] _ _ _ _.
    exact: cons_flatten_neq_nil.
  move/(sorted_catP b s'0)=> -[_ H]; move/H => [sorted_s' sorted_ss ls'_hss].
  apply: (@le_trans _ _ (nth b s' (size s').-1)).
    move/le_sorted_leq_nth : sorted_s'; apply => //; rewrite inE.
      by move: s'0; case s'.
    by move: s'0; case s'.
  rewrite nth_last.
  apply: (le_trans ls'_hss).
  rewrite -nth0.
  move: sorted_ss.
  move/le_sorted_leq_nth; apply => //.
    by rewrite inE; apply: leq_ltn_trans xs'.
rewrite mesh_cat; congr (maxr _ (mesh _ _)).
apply: set_last_default.
by case: s s0 abs last_s Hsorted2 sorted_s ls_hs'.
Qed.

Lemma mesh_merge1_le a s x :
  a <= x ->
  mesh a (merge <=%R s [:: x]) <= mesh a s.
Proof.
move=> ax.
set n := find (> x) (a :: s).
rewrite /mesh.
rewrite size_merge size_cat/= addn1.
(*

rewrite (@big_cat_nat {nonneg R} 0%:nng (@maxr {nonneg R})).
 (fun n0 => `|nth b (merge <=%R s [:: x]) n0 - nth b (a :: merge <=%R s [:: x]) n0|%:nng)).
(bigmaxr_morph (size s).+1
  (fun i => (nth b (a :: merge <=%R s [:: x]) i - _))).
move=> ps /eqP sb.
have [xs|xs] := boolP (x \in s).
  (* rewrite itv_partition_max_merge_subseq. *)
  admit.
apply: subseq_itv_partition_max.
have itv_partition_max_merge :
*)
Abort.

Lemma mesh_merge1' a b l s x :
  path <=%R a s -> last a s == b ->
  mesh a s <= l ->
  mesh a (merge <=%R s [:: x]) <= l.
Proof.
elim: s => //.
  move=> ? /=.
  rewrite /mesh/=.
  rewrite big_nat_recl// big_nil/=.
rewrite /mesh /=.
Abort.

Lemma mesh_merge a l s t :
  mesh a s <= l ->
  mesh a (merge <=%R s t) <= l.
Proof.
Abort.


Lemma mesh_mem_filter (a b c d : R) (s : seq R) :
  a <= c -> d <= b ->
  mesh c [seq x <- s | x \in `[c, d]] <= mesh a s.
Proof.
Abort.

Lemma mesh_filter (a : R) (s : seq R) (P : pred R) :
  mesh a [seq x <- s | P x] <= mesh a s.
Proof.
Abort.

End mesh_lemmas.

Section lambda_partition.
Context {R : realType}.

Definition lambda_partition (a b : R) (lambda : R) :=
  let n := (truncn ((b - a) / lambda)).+1 in
  [seq (a + (b - a) * i.+1%:R / n%:R) | i <- iota 0 n].

Local Notation lp := lambda_partition.

Lemma lambda_partition_size0_tmp (a b l : R) :
  (0 < (truncn ((b - a) / l)).+1)%N.
Proof. by []. Qed.

Lemma size_lambda_partition0 (a b l : R) :
  a < b -> 0 < l ->
  (0 < size (lp a b l))%N.
Proof.
move=> ab l0; by rewrite size_map size_iota lambda_partition_size0_tmp.
Qed.

Lemma lambda_partition_mesh (a b l : R) :
  a < b -> 0 < l ->
   mesh a (lp a b l) < l.
Proof.
move=> ab l0.
rewrite /mesh.

have : forall n : nat, (0 <= n < (truncn ((b - a) / l)).+1)%N ->
 `|(a :: lp a b l)`_n.+1 - (a :: lp a b l)`_ n|%:nng < NngNum (ltW l0).
  move=> n /andP[_ nl]; rewrite -num_lt/=.
  rewrite /lp nth_map_iota//.
  case: n nl.
    move=> _ /=.
    rewrite mulr1 addrAC subrr add0r ger0_norm.
      by rewrite mulr_ge0// subr_ge0 ltW.
    rewrite ltr_pdivrMr// mulrC -ltr_pdivrMr//.
    exact: truncnS_gt.
  move=> n.
  rewrite ltnS => nbal.
  rewrite [X in _ - X]
      (_: _ = a + (b - a) * n.+1%:R / (truncn ((b - a) / l)).+1%:R).
    transitivity (
    ([seq a + (b - a) * i.+1%:R /
     (truncn ((b - a) / l)).+1%:R | i <- iota 0 (truncn ((b - a) / l)).+1])`_
    n).
      done.
    rewrite nth_map_iota//.
    by rewrite ltnW// ltnS.
  rewrite opprD addrACA subrr add0r.
  rewrite -nat1r mulrDr mulrDl addrK mulr1.
  rewrite ger0_norm.
    by rewrite mulr_ge0// subr_ge0 ltW.
  rewrite ltr_pdivrMr// mulrC -ltr_pdivrMr//.
  exact: truncnS_gt.
have l0_nng : 0%:nng < NngNum (ltW l0).
  by rewrite -num_lt.
move/(bigmax_lt (iota 0 (size (lp a b l) - 0)) l0_nng).
rewrite -num_lt//.
apply: le_lt_trans.
rewrite num_le.
rewrite big_nat_cond.
apply: sub_bigmax.
move=> n; rewrite andbT => /andP[-> ]/leq_trans; apply.
by rewrite size_map size_iota.
Qed.

Lemma last_lambda (a b l d : R) :
  a < b -> 0 < l ->
  last d (lp a b l) = b.
Proof.
move=> ab l0.
rewrite (last_nth b).
rewrite -(@prednK (size _))//.
rewrite /lp (lock (iota 0))/=; unlock; rewrite nth_map_iota.
  by rewrite size_map size_iota.
by rewrite size_map size_iota/= -mulrA divff// mulr1 addrCA subrr addr0.
Qed.

Lemma lt_path_lambda (a b l : R) :
  a < b -> 0 < l ->
  path <%R a (lp a b l).
Proof.
move=> ab l0.
rewrite lt_path_pairwise.
apply/(pairwiseP 0) => i j; rewrite !inE/= size_map size_iota.
case: i j => //=.
  case => //= j _; rewrite ltnS => jl _.
  rewrite nth_map_iota// ltrDl.
  by rewrite divr_gt0 ?mulr_gt0 ?subr_gt0.
move=> i; case => // j.
rewrite ltnS => il; rewrite ltnS => jl; rewrite ltnS => ij/=.
rewrite !nth_map_iota//.
rewrite ltrD2l ltr_pM2r// ltr_pM2l//.
  by rewrite subr_gt0.
by rewrite ltr_nat ltnS.
Qed.

Lemma lt_sorted_lambda (a b l : R) :
  a < b -> 0 < l ->
  sorted <%R (lp a b l).
Proof.
move=> ab l0.
exact: path_sorted (lt_path_lambda ab l0).
Qed.

Lemma lb_lambda (a b l : R) :
  a < b -> 0 < l ->
  forall x : R, x \in lp a b l ->
  a < x.
Proof.
move=> ab l0 /= x slp.
by have/lt_path_min/allP := lt_path_lambda ab l0; apply.
Qed.

Lemma lambda_partition_partition (a b l : R) :
  a < b -> 0 < l ->
  itv_partition a b (lp a b l).
Proof.
move=> ab l0.
split; last by rewrite last_lambda.
exact: lt_path_lambda.
Qed.

End lambda_partition.
