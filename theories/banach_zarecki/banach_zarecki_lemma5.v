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

End merge_lemmas.

Lemma subseq_mergel {T : eqType} {r : rel T} (s t : seq T) :
   subseq s (merge r s t).
Proof.
Admitted.

Lemma subseq_merger {T : eqType} {r : rel T} (s t : seq T) :
   sorted r t -> subseq t (merge r s t).
Proof.
Admitted.

Section itv_partition_lemmas.
Context {R : realType}.
Variables (a b : R) (s : seq R).
Hypothesis (parts : itv_partition a b s).

Lemma last_mem_itv_partition : a < b ->
 b \in s.
Proof.
move: s parts; apply: last_ind => //.
- by move/itv_partition_nil ->; rewrite ltxx.
- move=> s' x' _ [_].
  rewrite last_rcons => /eqP -> _.
  by rewrite mem_rcons mem_head.
Qed.

Lemma itv_partitionNnil : a < b ->
  (0 < size s)%N.
Proof.
move=> ab; apply: (@leq_trans (size [:: b])); rewrite ?size_subseq ?sub1seq//.
exact: last_mem_itv_partition.
Qed.

End itv_partition_lemmas.

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
   \big[maxe/-oo%E]_(0 <= n < size s) oscillation f
    `[(nth b (a :: s)) n, (nth b (a :: s)) n.+1].
(*
Lemma bigmaxE T Q FH :
forall (F : T -> R) (HF : forall x, 0 <= F x),
  (\big[max/0%:nng]_(i in Q) (FH i)%:nng)%:num = (\big[max/0]_(i in Q) (F i)).

   reflect (\big[maxr/0%:nng]_(0 <= k < n) (P k)%:nng)%:num)
   (\big[maxr/0%R]_(0 <= k < n) P k).
*)

(* change definition? *)
Lemma oscillation_ge0 f a b : a <= b -> (0 <= oscillation f `[a, b])%E.
Proof.
move=> ab.
have fab0 : [set (EFin \o f) x | x in `[a, b]] !=set0.
 by exists (f b)%:E; exists b => //=; rewrite boundr_in_itv bnd_simp ab.
have [|] := pselect (ereal_sup [set (EFin \o f) x | x in `[a, b]] = +oo%E).
  rewrite /oscillation => ->.
  rewrite addye//.
  apply/negP; move/eqP/eqe_oppP; rewrite oppeK/=.
  move/ereal_inf_pinfty.
  have [x [r abr frx]] := fab0.
  move/(_ x) => /=.
Admitted.

Lemma omega_max_ge0 a b f s : a <= b -> path <%R a s ->
  (0 <= omega_max a b f s)%E.
Proof.
move=> ab.
case: s => //.
  admit.
  (* by rewrite /omega_max/= big_mkord big_ord0. *)
move=> h s pahs.
apply: (@le_trans _ _ (oscillation f
    `[(nth b (a :: h :: s)) 0, (nth b (a :: h :: s)) 1])).
apply: oscillation_ge0; last first.
  admit.
rewrite /omega_max.
exact: (le_bigmax_seq _ 0) => //.
Admitted.

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
  a < b ->
 itv_partition a b s ->
(omega_max a b f s <= oscillation f `[a, b])%E.
Proof.
move=> ab.
move/[dup]/itv_partition_in_itv => xab parts.
rewrite /omega_max.
apply: bigmax_le.
  admit.
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

Let lt_pathNmem x s : path x s -> x \in s = false.
Proof.
move/lt_path_min/allP => ltxs.
apply/negP => xs.
have := ltxs x xs.
by rewrite ltxx.
Qed.

Lemma merge_cons s t x :
  path x t -> merge s (x :: t) = merge (merge s [:: x]) t.
Proof.
move=> pxt.
rewrite /merge//=.
elim: s => //.
Admitted.

End lt_merge_lemmas.

Definition disj_seq {T : eqType}(s t : seq T) :=
[disjoint [set` s] & [set` t]].

(* unlike subseq, disj_seq s t is true when s and t is disjoint as sets,
   not that each one be not a subseq of the other.
   i.e. disj_seq [:: a; a; b] [:: a; b; b] is false although
~ (subseq [:: a; a; b] [:: a; b; b] \/ subseq [:: a; b; b] [:: a; a; b]) is true *)
Example subseqNdisj_seq {T : eqType} :
let disj_seq' s t := ~~ (subseq s t || subseq t s) in
  forall a b : T, a == b = false ->
   let s := [:: a; a; b] in
   let t := [:: a; b; b] in
  disj_seq' s t /\ ~ disj_seq s t.
Proof.
move=> disj_seq' a b ab s t.
split.
- apply/norP; split.
  + by rewrite /= eqxx ?ifF ?ifF.
  + rewrite /= eqxx ifF; last by rewrite eq_sym.
    by rewrite eqxx.
- rewrite /disj_seq disj_set2E; apply/negP.
  apply/set0P.
  exists a => /=; split; exact: mem_head.
Qed.

Lemma disj_seq_allP {T : eqType} (s t : seq T) :
  disj_seq s t <-> (all (fun x => x \notin s) t /\ all (fun x => x \notin t) s).
Proof.
Admitted.

Section itv_partition_lemmas.
Context {R : realType}.
Variables (a b : R).
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
    apply: omega_max_ge0.
    admit.
    admit.
  apply: le_omega_max.
  apply: subseq_mergel.
rewrite -addeAC leeD2r//.
apply: variation_merge1 => //.
have /disj_seq_allP[/allP + _] := disjst.
apply.
exact: mem_head.
Admitted.

Lemma variation_subseq' s t :
  subseq s t ->
  variation a b f s <= variation a b f t.
Proof.
elim: s a t.
- move=> ? ? _; by rewrite variation_nil variation_ge0.
move=> hs s IHs a'.
elim => //.
move=> ht t IHt.
(*
apply: (@le_trans _ _ (variation a b f s)).
  exact: variation_cons.
elim: t; first by move=> /=/eqP ->.
move=> h t IH.
move=> sht.
apply: (le_trans (IH _)).
*)
Admitted.

(* TODO: generalize to compact set K *)
Lemma compact_unif_continuousP :
  {within `[a, b], continuous f} <-> unif_continuous (subspace `[a, b]) R f.
Proof.
split.
- move=> cf; apply/unif_continuousP => /= e e0.
  have : exists d : R -> R, [/\ (forall x, 0 < d x) &
   (forall x y, `|x - y| < d x -> `|f x - f y| < e / 4)].
    admit.
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
  by rewrite subr_gt0 -lte_fin fineK.
have [eV' /= [V' [X' partX' X'V'] V'eV']] := ub_ereal_sup_adherent TfA0 bvf.
rewrite -/(total_variation a b f) -/Tf.
rewrite EFinN EFinB fineK//.
rewrite oppeB; last first.
  by rewrite fin_num_adde_defl.
rewrite addeA subee// add0r.
rewrite -{}V'eV' lte_fin => AV'.
have : unif_continuous (subspace `[a, b]) R f.
  exact/compact_unif_continuousP.
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
  rewrite [leRHS](_ : _ = V0 - V' + (V' + A)%E / 2); last first.
    admit.
  rewrite lerDr subr_ge0.
  rewrite -X'V'.
  apply: variation_subseq' => //.
  - apply: subseq_merger.
    have [+ _] := partX'.
    exact: path_sorted.
rewrite lerBlDr -lee_fin EFinD.
have [pabp abpd] := pmaxd.
have abp_led : itv_partition_max a b p <= d.
  by rewrite le_eqVlt; apply/predU1P; left.
apply: (le_trans (@variation_merge _ p X' pabp abp_led partX' _)).
  admit.
apply: leeD2l.
(* unifcf *)
rewrite -/m.
rewrite -lee_pdivlMl; last first.
  rewrite mulr_gt0//.
  rewrite -(mulr0n 1) ltr_nat.
  admit.
(*  exact: itv_partition_size.
  rewrite (@leq_ltn_trans (index b X'))//.
  rewrite index_mem.
  apply: *)
rewrite (_ : ((V' - A) / 2) = (m%:R * 2)%R * eps)%R; last first.
  admit.
rewrite EFinM muleA -EFinM.
rewrite mulVf; last first.
  admit.
rewrite mul1r.
rewrite /omega_max.
apply: bigmax_le; first by rewrite leNye.
move=> n _.
rewrite /oscillation/=.
rewrite -image_comp.
rewrite ereal_sup_EFin; last 2 first.
- admit.
- admit.
rewrite ereal_inf_EFin; last 2 first.
- admit.
- admit.
rewrite -EFinB lee_fin.
suff : forall x y, x \in `[(nth b (a :: p) n), (nth b p n)] ->
 y \in `[(nth b (a :: p) n), (nth b p n)] ->
  `|f x - f y| <= eps.
  admit.
move=> x y Hx Hy.
have @x' : subspace `[a, b].
  red.
  exact: x.
have @y' : subspace `[a, b].
  red.
  exact: y.
have := unifcf (x', y').
rewrite /=/ball/=.
move=> /(_ _ )/ltW.
apply.
rewrite /subspace_ball.
rewrite ifT; last first.
  rewrite inE/=.
  admit.
rewrite /=; split.
  admit.
rewrite /ball/=.
rewrite -abpd.
rewrite /itv_partition_max/=.
(* HB instance, {nonneg R} is Monoid *)
rewrite lt_neqAle; apply/andP; split.
  admit.
have : `|x' - y'|%:nng <=
  (\big[maxr/widen_itv 0%:itv]_(0 <= n0 < size p)
      widen_itv `|nth b p n0 - nth b (a :: p) n0|%:itv).
  rewrite big_mkord.
  have [|] := leqP (size (a :: p)) n.
    move=> /= apn.
    move: Hx Hy.
    rewrite nth_default//= nth_default//.
    move/itvxxP=> xb.
    move/itvxxP=> yb.
    rewrite num_abs_le /x'/y' xb yb subrr//.
    exact: ltnW.
  rewrite /= ltnS (leq_eqVlt n) => /predU1P[np|np].
    move: Hx Hy.
    have -> := nth_default _ (eq_leq (esym np)).
    have -> : (n = (size (a :: p)).-1)%N by [].
    rewrite nth_last last_cons.
    have [[_ /eqP ->] _] := pmaxd.
    move/itvxxP=> xb.
    move/itvxxP=> yb.
    by rewrite num_abs_le /x'/y' xb yb subrr.
  apply: (bigmax_sup (Ordinal np)) => //=.
(* have [yx|] := ltP y x. *)
have xx' : x = x' by [].
have yy' : y = y' by [].
   wlog  : x y x' y' Hx Hy xx' yy' / y < x. 
(*
    move=> H.

    rewrite distrC.

    have [xy|] := ltP x y; first apply: (H y x) => //.
    rewrite le_eqVlt => /predU1P[xy|].
      have <- : x' = y' by [].
      by rewrite subrr num_abs_le.
    exact: (H x y).
  move=> xy.
  rewrite num_abs_le; last first.
  rewrite subr_ge0.
  apply: ltW.
  
  rewrite /x'/y' => //.
  exact: n.

rewrite /=.

have := (@bigmax_sup _ {nonneg R}).
*)
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
