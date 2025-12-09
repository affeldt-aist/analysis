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

Section merge_lemmas_eqType.
Context {T : eqType} {r : rel T}.
Implicit Types (s t : seq T) (x : T).

(* unused *)
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

(* unused *)
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

Lemma subseq_mergel s t :
   subseq s (merge r s t).
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

Lemma merge_neq0 {T : eqType} {r : rel T} s t :
  (s != [::]) || (t != [::]) -> merge r s t != [::].
Proof.
elim: t s => [s|t0 t1 ih s].
  by rewrite eqxx orbF merge0r.
move=> /orP[|_].
  by move: s => [//|s0 s1 _ /=]; case: ifPn.
by move: s => [//|s0 s1/=]; case: ifPn.
Qed.

End merge_lemmas_eqType.

Section itv_partition_lemmas.
Context {R : realType}.
Variables (a b : R) (s : seq R).
Hypothesis (parts : itv_partition a b s).

Lemma itv_partition_neq0 : a != b -> itv_partition a b s -> s != [::].
Proof. by elim: s a b => // a' b' /negbTE a'b' []/=; rewrite a'b'. Qed.

Lemma itv_partition_sorted : itv_partition a b s -> sorted <%R s.
Proof. by case => sa _; exact: path_sorted sa. Qed.

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

(* TODO: PR *)
Lemma ereal_inf_sup (A : set (\bar R)) : A !=set0 ->
  (ereal_inf A <= ereal_sup A)%E.
Proof.
move=> [a Aa].
by rewrite (@le_trans _ _ a)//; [exact: ereal_inf_lbound|exact: ereal_sup_ubound].
Qed.

Lemma oscillation_ge0 f a b : a <= b -> (0 <= oscillation f `[a, b])%E.
Proof.
move=> ab.
rewrite /oscillation.
have [fb fb0] : [set (EFin \o f) x | x in `[a, b]] !=set0.
  by exists (f b)%:E; exists b => //=; rewrite boundr_in_itv bnd_simp ab.
set s : \bar R := ereal_sup _.
set i : \bar R := ereal_inf _.
have fbsup : (fb <= s)%E by rewrite ereal_sup_ubound.
have inffb : (i <= fb)%E by rewrite ereal_inf_lbound.
have [sfin|] := boolP (s \is a fin_num); last first.
  rewrite fin_numE negb_and !negbK => /predU1P[sy|/eqP sy].
    move/ereal_sup_ninfty : (sy) => /(_ _ fb0)/=.
    by case: fb0 => [x _ <-].
  have [iy|iy] := eqVneq i +oo%E.
    move: inffb.
    case: fb0 => [x _ <-/=].
    by rewrite iy leye_eq.
  rewrite sy.
  case: i iy {inffb} => // [r _|].
    by rewrite addye.
  by rewrite leey.
have [ifin|] := boolP (i \is a fin_num); last first.
  rewrite fin_numE negb_and !negbK => /predU1P[iy|/eqP iy].
    rewrite iy addey//.
    by move: sfin; rewrite fin_numE => /andP[].
  move: inffb.
  case: fb0 => [x _ <-/=].
  by rewrite iy.
rewrite sube_ge0 ?sfin ?ifin//.
by apply: ereal_inf_sup; exists fb.
Qed.

Lemma omega_max_ge0 a b f s : s != [::] -> a <= b -> path <=%R a s ->
  (0 <= omega_max a b f s)%E.
Proof.
move=> s0 ab sa.
rewrite /omega_max.
rewrite (@le_trans _ _ ( oscillation f `[a, (nth b s 0)]))//.
  apply: oscillation_ge0.
  move/pathP : sa => /(_ b 0)/=.
  by rewrite lt0n size_eq0 s0 => /(_ isT).
rewrite (le_bigmax_seq -oo%E O xpredT
  (fun i => oscillation f `[(nth b (a :: s) i), (nth b (a :: s) i.+1)]))//.
by rewrite mem_index_iota leqnn lt0n size_eq0.
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
rewrite big_seq.
apply: bigmax_le.
  by rewrite leNye.
move=> /= n.
rewrite mem_iota add0n subn0 leq0n/= => ns.
apply: oscillation_sub.
apply: subset_itvScc; rewrite bnd_simp.
  apply: itv_partition_nth_ge => //.
  by rewrite ltnS ltnW.
rewrite -[leLHS]/(nth b (a :: s) n.+1).
by apply: itv_partition_nth_le => //.
Qed.

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

Lemma path_merge {R : realType} (a : R) s h :
  a < h ->
  path <%R a s -> path <=%R a (merge <%R s [:: h]).
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
    - by apply: merge_neq0; rewrite orbT.
    - exact: ltW.
    - apply: path_merge.
        by move: hab; rewrite in_itv/= => /andP[].
      by case: ps.
  apply: le_omega_max.
  exact: subseq_mergel.
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
      exact: lt_trans.
    exact: itv_partition_sorted partX'.
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
      widen_itv `|nth b (a :: p) n0 - nth b p n0|%:itv).
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
    move=> H.
    have [xy|] := ltP x y.
      rewrite (_ : widen_itv `|x' - y'|%:itv = widen_itv `|y' - x'|%:itv); last first.
        admit.
      exact: (H y x).
    rewrite le_eqVlt => /predU1P[xy|].
      have <- : x' = y' by [].
      by rewrite subrr num_abs_le.
    exact: (H x y).
  move=> xy.
  rewrite -xx' -yy'.
  rewrite num_abs_le; last first.
    by rewrite subr_ge0 ltW.
  rewrite nngE/=.
  rewrite ger0_norm; last first.
    rewrite subr_ge0 ltW//.
    case: n np Hx Hy => //=.
      move=> p0 Hx Hy.
    have := itv_partition_in_itv pabp.
rewrite /=.

have := (@bigmax_sup _ {nonneg R}).

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
