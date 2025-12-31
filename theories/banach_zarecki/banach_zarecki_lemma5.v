From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import all_ssreflect interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean.
From mathcomp Require Import mathcomp_extra boolp contra classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype derive.
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

Section itv_partition_lemmas.
Context {R : realType}.
Implicit Types (a b x : R) (s : seq R).

Lemma itv_partition_neq0 a b s : a != b -> itv_partition a b s -> s != [::].
Proof. by elim: s a b => // a' b' /negbTE a'b' []/=; rewrite a'b'. Qed.

Lemma itv_partition_sorted a b s : itv_partition a b s -> sorted <%R s.
Proof. by case => sa _; exact: path_sorted sa. Qed.

Lemma last_mem_itv_partition a b s :
  itv_partition a b s ->
  a < b -> b \in s.
Proof.
move: s; apply: last_ind => //.
- by move/itv_partition_nil ->; rewrite ltxx.
- move=> s' x' _ [_].
  rewrite last_rcons => /eqP -> _.
  by rewrite mem_rcons mem_head.
Qed.

Lemma itv_partitionNnil a b s : a < b ->
 itv_partition a b s -> (0 < size s)%N.
Proof.
move=> ab p; apply: (@leq_trans (size [:: b])); rewrite ?size_subseq ?sub1seq//.
exact: last_mem_itv_partition ab.
Qed.


Lemma itv_partition_cons1 a b s x :
  s != [::] ->
  itv_partition a b (x :: s) -> itv_partition a b s.
Proof.
move: s; apply: last_ind => // s t _ _ [/[swap]/eqP].
rewrite /= last_rcons => -> /andP[ax pxs].
have ab : a < b.
  apply: (lt_le_trans ax); have := path_lt_le_last pxs; by rewrite last_rcons.
split; last by rewrite last_rcons.
exact: path_lt_head pxs.
Qed.

Lemma itv_partition_head a b h s :
s != [::] ->
a < h < head b s -> itv_partition a b s ->
 itv_partition a b (h :: s).
Proof.
case: s => // s0 s1 _ /andP[ah hs0] /[dup]pabs [/=/andP[as0 pas] /eqP sb].
split; first by rewrite /=; apply/and3P; split => //.
by rewrite -sb.
Qed.

Lemma sorted_merge1 h s : h \notin s ->
  sorted <%R s -> sorted <%R (merge <%R s [:: h]).
Proof.
elim: s h => // s0 s1 ih h hs /= s0s1.
have [s0h|s0h]/= := ltP s0 h.
  have s1h : sorted <%R (merge <%R s1 [:: h]).
    apply: ih (path_sorted s0s1).
    by apply: contra hs; rewrite inE orbC => ->.
  rewrite path_min_sorted//; apply/allP => x.
  rewrite mem_merge mem_cat => /orP[xs1|].
    by move/order_path_min : s0s1 => /(_ lt_trans)/allP/(_ _ xs1).
  by rewrite mem_seq1 => /eqP ->.
rewrite lt_neqAle s0h andbT.
by move: hs; rewrite !inE negb_or => /andP[->].
Qed.

Lemma notin_sorted_rcons s h :
  h \notin s -> sorted <%R s ->
  sorted <%R (rcons [seq x <- s | x < h] h).
Proof.
elim: s h => // s0 s1 ih h.
rewrite in_cons negb_or => /andP[hs0 hs1]/= s0s1.
have [s0h|] := ltP s0 h.
  have : sorted <%R s1 by exact: path_sorted s0s1.
  move/(ih _ hs1) => {}ih /=.
  rewrite path_min_sorted//; apply/allP => x.
  rewrite mem_rcons inE => /predU1P[->//|].
  rewrite mem_filter => /andP[xh xs1].
  move/order_path_min: s0s1 => /(_ lt_trans).
  by move/allP; exact.
rewrite le_eqVlt (negbTE hs0)/= => {}hs0.
rewrite path_lt_filter0//.
apply: path_le s0s1 => //.
exact: lt_trans.
Qed.

Lemma merge1E s h : h \notin s -> sorted <%R s ->
  merge <%R s [:: h] = itv_partitionL s h ++ itv_partitionR s h.
Proof.
move=> hs ss; apply: (@irr_sorted_eq _ <%R) => //.
- exact: lt_trans.
- exact: sorted_merge1.
- have sE := notin_itv_partition ss hs.
  rewrite /itv_partitionL -cats1 -catA/= sorted_cat_cons.
  rewrite notin_sorted_rcons//= path_min_sorted//.
    by apply: sorted_filter => //; exact: lt_trans.
  by apply/allP => x; rewrite mem_filter => /andP[].
- move=> i.
  rewrite mem_merge [in RHS]mem_cat mem_filter mem_rcons in_cons mem_filter.
  rewrite mem_cat mem_seq1.
  by have [//||] := ltgtP i h; rewrite ?(orbF,orbT).
Qed.

Lemma itv_partition_merge1 a b h s :
  a < b -> a < h < b -> h \notin s ->
  itv_partition a b s ->
  itv_partition a b (merge <%R s [:: h]).
Proof.
move=> ab /andP[ah hb] hs abs; rewrite merge1E//.
- apply: itv_partition_cat.
    exact: itv_partitionLP abs.
  exact: itv_partitionRP abs.
- exact: itv_partition_sorted abs.
Qed.

Let itv_partition_in_itv a b s :
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

Let itv_partition_head_in_itv a b s t :
  itv_partition a b (rcons s t) -> {in s, forall x, x \in `]a, b[}.
Proof.
move=> pst x xs.
have in_ab := itv_partition_in_itv pst.
rewrite in_itv/=; apply/andP; split.
  have := in_ab x.
  rewrite mem_rcons in_cons.
  have H : (x == t) || (x \in s) by apply/orP; right.
  by move/(_ H); rewrite in_itv/= => /andP[ax xb].
have [] := pst.
rewrite lt_path_pairwise.
move/pairwiseP => lt_ast.
move/eqP <-; rewrite (last_nth a).
have : x \in a :: (rcons s t).
  rewrite in_cons; apply/orP; right.
  by rewrite mem_rcons in_cons xs orbT.
move/(nth_index a) <-.
apply: lt_ast; last 2 first.
- by rewrite inE.
- rewrite /=.
  rewrite ifF; last first.
    rewrite lt_eqF => //.
    have [/lt_path_min/allP + _] := pst.
    by apply; rewrite mem_rcons in_cons xs orbT.
  by rewrite size_rcons -cats1 index_cat xs ltnS index_mem.
rewrite inE index_mem.
rewrite in_cons; apply/orP; right.
by rewrite mem_rcons in_cons xs orbT.
Qed.

(* convenience of itv_partition(?) *)
Lemma itv_partition_gt_lb a b s : a < b ->
  itv_partition a b s -> forall n, a < nth b s n.
Proof.
move=> ab ps n.
have [ns|ns] := ltnP n (size s).
  suff : nth b s n \in `]a, b].
    by rewrite in_itv/= => /andP[].
  apply: (itv_partition_in_itv ps).
  exact: mem_nth.
by rewrite nth_default.
Qed.

Lemma itv_partition_le_ub a b s :
  itv_partition a b s -> forall n, nth b s n <= b.
Proof.
move=> ps n.
have [ns|ns] := ltnP n (size s).
  suff : nth b s n \in `]a, b].
    by rewrite in_itv/= => /andP[].
  apply: (itv_partition_in_itv ps).
  exact: mem_nth.
by rewrite nth_default.
Qed.

Lemma itv_partition_lt_ub a b s :
  itv_partition a b s -> forall n, (n.+1 < size s)%N -> nth b s n < b.
Proof.
elim/last_ind : s => // s0 s1 _ ps n.
rewrite size_rcons ltnS => ns0.
pose s := rcons s0 s1.
rewrite -/s.
suff : nth b s n \in `]a, b[.
  by rewrite in_itv/= => /andP[].
apply: (@itv_partition_head_in_itv _ _ s0 s1) => //.
apply/(nthP b).
exists n => //.
by rewrite nth_rcons ns0.
Qed.

End itv_partition_lemmas.

Section twice.
Context {R : realType}.
Implicit Types (a b : R) (f : R -> R).
Implicit Types (s : seq R) (x : R).

Lemma itv_partition_no_inbtween a b s : itv_partition a b s ->
  forall x k, (k < (size s))%N ->
  x \in `]nth b (a :: s) k, nth b (a :: s) k.+1[ ->
  x \notin s.
Proof.
elim: s a b => // s0 s1 ih a b abs0s1 x [_/=|k].
  rewrite in_itv/= => /andP[ax xs0].
  rewrite inE negb_or; apply/andP; split.
    apply/negP => /eqP s0x.
    by rewrite s0x ltxx in xs0.
  apply/negP => xs1.
  case: abs0s1 => /= /andP[as0].
  move/lt_path_min => /allP/(_ x).
  rewrite xs1 => /(_ isT).
  by rewrite ltNge (ltW xs0).
rewrite /= ltnS => ks1.
rewrite in_itv/= => /andP[kx xk].
rewrite inE negb_or; apply/andP; split.
  apply/negP => /eqP s0x.
  case: abs0s1 => /= /andP[as0].
  destruct k as [|k].
    simpl in *.
    by rewrite s0x ltxx in kx.
  move/lt_path_min => /allP/(_ (nth b (s0 :: s1) k.+1)).
  have : nth b (s0 :: s1) k.+1 \in s1.
    apply/(nthP b).
    exists k => //=.
    by rewrite (leq_trans _ ks1).
  move=> /[swap] /[apply] /=.
  rewrite -s0x.
  by rewrite ltNge (ltW kx).
have : itv_partition s0 b s1.
  by case: abs0s1 => /= => /andP[as0 s0s1 s1b].
move/ih => /(_ _ _ ks1); apply.
by rewrite in_itv/= kx xk.
Qed.

Lemma variation_behead a b s f :
  variation (nth b s 0) b f (behead s) <= variation a b f s.
Proof.
case: s => [|s0 s1]/=.
  by rewrite !variation_nil.
by rewrite /variation/= big_nat_recl//= lerDr.
Qed.

Lemma variation_nth a b f s : a < b ->
  itv_partition a b s ->
  forall k, (k.+2 <= size s)%N ->
  variation a (nth b s k) f (itv_partitionL s (nth b s k)) <= variation a b f s.
Proof.
move=> ab abs k ks.
rewrite [in leRHS](@in_itv_partition _ (nth b s k) s); last 2 first.
  exact: itv_partition_sorted abs.
  apply/(nthP b).
  exists k => //.
  by rewrite (leq_trans _ ks).
rewrite (@variation_cat _ _ _ (nth b s k))//; last 4 first.
  apply/ltW.
  by apply: (itv_partition_gt_lb _ abs).
  apply: (@itv_partition_nth_le _ a _ _ k.+1) => //.
  by rewrite (leq_trans ks)//.
  apply: itv_partitionLP (abs).
  by apply: itv_partition_gt_lb => //.
  by apply: (itv_partition_lt_ub abs) => //.
  apply: itv_partitionRP (abs).
  by apply: itv_partition_gt_lb => //.
  by apply: (itv_partition_lt_ub abs) => //.
by rewrite lerDl variation_ge0.
Qed.

Lemma filter_iota a b s : a < b ->
  itv_partition a b s ->
  forall k, (k < size s)%N ->
  [seq x <- s | x < nth b s k] = take k s.
Proof.
elim: s a b => //= s0 s1 ih a b ab abs [_|k].
  rewrite /= ltxx.
  rewrite -(filter_pred0 s1).
  apply: eq_in_filter => r s1r.
  apply/negbTE/negP => rs0.
  case: abs => /= /andP[as0] + _.
  move/order_path_min => /(_ lt_trans)/allP => /(_ _ s1r).
  rewrite ltNge.
  by rewrite (ltW rs0).
rewrite ltnS => ks1.
rewrite /=.
rewrite ifT; last first.
  case: abs => /= /andP[as0].
  move/order_path_min => /(_ lt_trans)/allP + _; apply.
  apply/(nthP b).
  by exists k.
rewrite (ih s0)//=.
have /= := @itv_partition_lt_ub _ _ _ _ abs O.
apply.
by rewrite ltnS (leq_trans _ ks1).
by case: abs => /= /andP[as0 s0s1 s0s1b].
Qed.

Lemma variation_nth_nth a b f s : a < b ->
  itv_partition a b s ->
  forall k, (k.+2 < size s)%N ->
  variation a (nth b s k) f (itv_partitionL s (nth b s k)) <=
  variation a (nth b s k.+1) f (itv_partitionL s (nth b s k.+1)).
Proof.
move=> ab abs k ks.
have H : nth b s k < nth b s k.+1.
  case: abs => sa /eqP asb.
  move/pathP : sa => /(_ b) /(_ k.+1) /=.
  apply.
  by rewrite (leq_trans _ ks).
have H1 : itv_partitionL s (nth b s k.+1) =
    rcons (itv_partitionL s (nth b s k)) (nth b s k.+1).
  rewrite /itv_partitionL.
  rewrite -!cats1.
  congr cat.
  rewrite (@filter_iota a)//; last first.
    by rewrite (leq_trans _ ks).
  rewrite (@filter_iota a)//; last first.
    by rewrite (leq_trans _ ks)// ltnW.
  rewrite (take_nth b) -?cats1//.
  by rewrite (leq_trans _ ks)// ltnW.
rewrite H1.
rewrite -cats1.
rewrite (@variation_cat _ _ _ (nth b s k))//; last 4 first.
  apply/ltW.
  by apply: (itv_partition_gt_lb _ abs).
  by apply/ltW.
  apply: itv_partitionLP (abs).
  by apply: itv_partition_gt_lb => //.
  apply: (itv_partition_lt_ub abs) => //.
  by rewrite (leq_trans _ ks).
  rewrite /itv_partition/=.
  split => //.
  by rewrite H.
by rewrite lerDl// variation_ge0.
Qed.

Lemma variation_oscillation a b c1 c2 f :
  {within `[a, b], continuous f} -> c1 \in `[a, b] -> c2 \in `[a, b] ->
  (`|f c1 - f c2|%:E <=
   ereal_sup [set (EFin \o f) x | x in `[a, b]] -
   ereal_inf [set (EFin \o f) x | x in `[a, b]])%E.
Proof.
have [ab|] := ltP a b; last first.
 rewrite le_eqVlt => /predU1P[-> cf|ba _].
   rewrite !in_itv/= -!eq_le => /eqP <- /eqP <-.
   rewrite subrr normr0 sube_ge0.
     rewrite ereal_inf_sup//; exists (f a)%:E => /=.
     exists a => //.
     by rewrite !in_itv/= lexx.
   apply/orP; left.
   rewrite set_itv1.
   rewrite image_set1.
   by rewrite ereal_inf1.
  rewrite in_itv/= => /andP[/le_trans] /[apply].
  by rewrite leNgt ba.
move=> cf c1ab c2ab.
have [d dab maxd] := EVT_max (ltW ab) cf.
have [e eab mine] := EVT_min (ltW ab) cf.
rewrite (@le_trans _ _ (f d - f e)%:E)//.
  have [fac|fca] := leP (f c2) (f c1).
    rewrite ger0_norm ?subr_ge0// lee_fin.
    by rewrite lerB// ?maxd ?mine// ?in_itv/= ?lexx ?(ltW ac) ?(ltW cb)// (ltW (lt_trans ac cb)).
  rewrite ler0_norm ?subr_le0//; last first.
    by rewrite ltW.
  rewrite lee_fin opprB lerB//.
    by rewrite maxd.
    by rewrite mine.
rewrite EFinB leeB//.
  apply: le_ereal_sup_tmp.
  exists (f d)%:E => //=.
  by exists d.
apply: ge_ereal_inf.
exists (f e)%:E => //=.
by exists e.
Qed.

Lemma variation_merge1_tmp_new a b f s : a < b ->
  {within `[a, b], continuous f} ->
  itv_partition a b s ->
  forall x, x \in `]a, b[ -> x \notin s ->
  forall k, (k < (size s))%N ->
    x \in `]nth b (a :: s) k, nth b (a :: s) k.+1[ ->
  ((variation a b f (merge <%R s [:: x]))%:E <=
   (variation a b f s)%:E +
   2 * oscillation f `[nth b (a :: s) k, nth b (a :: s) k.+1])%E.
Proof.
move=> ab cf abs x xab xs k ks xk.
set s' := merge _ _ _.
apply: (@le_trans _ _ (variation a b f
    (itv_partitionL s' x ++ itv_partitionR s' x))%:E).
  rewrite lee_fin.
  apply: variation_itv_partitionLR.
  by move: xab; rewrite in_itv/= => /andP[].
  by move: xab; rewrite in_itv/= => /andP[].
  exact: itv_partition_merge1.
rewrite (@variation_cat _ _ _ x); last 4 first.
  by move: xab; rewrite in_itv/= => /andP[/ltW].
  by move: xab; rewrite in_itv/= => /andP[_ /ltW].
  apply: (@itv_partitionLP _ _ b).
  by move: xab; rewrite in_itv/= => /andP[].
  by move: xab; rewrite in_itv/= => /andP[].
  exact: itv_partition_merge1.
  apply: (@itv_partitionRP _ a).
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
  destruct k as [|k].
    done.
  rewrite /=.
  apply/ltW.
  by apply: itv_partition_gt_lb.
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
  rewrite -variation_cat; last 4 first.
  by [].
  exact/ltW.
  apply: (@itv_partitionLP _ _ b) => //.
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
  rewrite [in LHS](@in_itv_partition _ x_k _ (itv_partition_sorted abs)); last first.
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
    apply: (@itv_partition_no_inbtween _ _ _ abs _ k.+1) => //.
    rewrite -/x_k -/x_k1.
    rewrite in_itv/= xkr/=.
    rewrite (lt_le_trans rx)//=.
    by rewrite ltW.
  rewrite H1 cats0.
  rewrite -filter_predI.
  congr rcons.
  apply: eq_in_filter => r rs.
  rewrite /=.
  by rewrite andb_idl// => /lt_trans; apply.
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
  rewrite -variation_cat; last 4 first.
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
    apply: (@itv_partitionRP _ a) => //.
      rewrite (le_lt_trans axk)//.
      by rewrite (lt_trans xkx).
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
  rewrite [in LHS](@in_itv_partition _ x_k1 _ (itv_partition_sorted abs)); last first.
    apply/(nthP b).
    by exists k.
  rewrite filter_cat.
  have -> : [seq x0 <- itv_partitionL s x_k1 | x < x0] = [:: x_k1].
    rewrite /itv_partitionL.
    rewrite filter_rcons xxk1 -filter_predI.
    rewrite -cats1.
    have -> : [seq x0 <- s | predI [eta > x] (<%R^~ x_k1) x0] = [::].
      rewrite -(filter_pred0 s).
      apply: eq_in_filter => r sr/=.
      apply/negbTE/negP => /andP[xr rxk1].
      move: sr.
      apply/negP.
      apply: (@itv_partition_no_inbtween _ _ _ abs _ k) => //.
      rewrite -/x_k -/x_k1.
      by rewrite in_itv/= rxk1 (lt_trans xkx xr).
    done.
  rewrite /=.
  congr cons.
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
  rewrite [in leRHS](@in_itv_partition _ x_k1 _ (itv_partition_sorted abs)); last first.
    apply/(nthP b).
    exists k.+1 => //.
    by rewrite (leq_trans _ k1s).
  rewrite (@variation_cat _ _ _ x_k1)//; last 4 first.
    by rewrite (le_trans axk)// (le_trans (ltW xkx))// ltW.
    rewrite /x_k1.
    rewrite /=.
    by apply: (@itv_partition_le_ub _ a) => /=.
    apply: itv_partitionLP (abs) => //.
    rewrite /x_k1/=.
    by apply: itv_partition_gt_lb => //.
    rewrite /x_k1/=.
    by apply: (itv_partition_lt_ub abs).
    apply: itv_partitionRP (abs) => //.
    rewrite /x_k1/=.
    by apply: itv_partition_gt_lb => //.
    rewrite /x_k1/=.
    by apply: (itv_partition_lt_ub abs).
  rewrite lerD2r.
  rewrite /x_k /x_k1/=.
  by rewrite variation_nth_nth//.
rewrite mule_natl.
rewrite mule2n.
rewrite EFinD.
have xkxk10 : `[x_k, x_k1]%classic != set0.
  apply/set0P; exists x => /=.
  by rewrite in_itv/= (ltW xkx) (ltW xxk1).
rewrite leeD//.
  rewrite /variation/= big_nat_recr//= big_nil add0r.
  rewrite /oscillation.
  rewrite (negbTE xkxk10).
  apply: (@variation_oscillation _ _ _ _ f).
  apply: continuous_subspaceW cf.
  apply: interval.subset_itv; rewrite bnd_simp//.
  by apply: (itv_partition_le_ub abs).
  by rewrite in_itv/= (ltW xkx) (ltW xxk1).
  by rewrite in_itv/= lexx (ltW (lt_trans xkx _)).
rewrite /variation/= big_nat_recr//= big_nil add0r.
rewrite /oscillation.
rewrite (negbTE xkxk10).
apply: (@variation_oscillation _ _ _ _ f).
apply: continuous_subspaceW cf.
apply: interval.subset_itv; rewrite bnd_simp//.
by apply: (itv_partition_le_ub abs).
rewrite in_itv/= lexx ltW//.
by rewrite (lt_trans xkx).
by rewrite in_itv/= (ltW xkx) (ltW xxk1).
Qed.

End twice.

Section itv_partition_length.
Context {R : realType}.
Implicit Types (a b : R) (f : R -> R).
Implicit Types (s : seq R) (x : R).

Definition itv_partition_max a b s : R := let pnth := nth b (a :: s) in
  (\big[maxr/0%:nng]_(0 <= n < size s) `|pnth n.+1 - pnth n|%:nng)%:num.

(*
Definition itv_partition_with_max a b l s :=
  itv_partition a b s /\ itv_partition_max a b s = l.
*)

Definition variations_with_max a b f l : set R :=
   [set r| exists s, [/\ r = variation a b f s,
 itv_partition a b s & itv_partition_max a b = l]].

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

Lemma omega_max_nil a b f : omega_max a b f [::] = -oo%E.
Proof. by rewrite /omega_max /= big_nil. Qed.

Lemma omega_max_ge0 a b f s : s != [::] -> (0 <= omega_max a b f s)%E.
Proof.
case: s => [//|h t s0].
by rewrite /omega_max/= big_nat_recl//= le_max oscillation_ge0.
Qed.

Lemma omega_max_le_oscillation a b f s :
  itv_partition a b s ->
  (omega_max a b f s <= oscillation f `[a, b])%E.
Proof.
move=> ps.
rewrite /omega_max big_seq bigmax_le//.
  by rewrite leNye.
move=> /= n.
rewrite mem_iota add0n subn0 leq0n/= => ns.
apply: oscillation_sub.
apply: subset_itvScc; rewrite bnd_simp//.
  by apply: itv_partition_nth_ge => //; rewrite ltnS ltnW.
exact: (itv_partition_le_ub ps).
Qed.

Lemma omega_max_cons a b f s x :
  a <= x <= head a s ->
  s != [::] ->
  (omega_max a b f (x :: s) <= omega_max a b f s)%E.
Proof.
elim: s => // h s' IH /=/andP[ax xh] _.
rewrite /omega_max/=.
rewrite 3?big_nat_recl//=.
rewrite maxA.
apply: le_max2 => //.
rewrite maxEge; case: ifPn => _; apply: oscillation_sub.
  by apply: subset_itvl; rewrite bnd_simp.
by apply: subset_itvr; rewrite bnd_simp.
Qed.

Lemma le_omega_max a b f s t :
  s != [::] ->
  path <=%R a s ->
  sorted <=%R t ->
  subseq s t ->
  (omega_max a b f t <= omega_max a b f s)%E.
Proof.
elim: t a s.
  by move=> ? ?; rewrite omega_max_nil leNye.
move=> ht t IHt a s s0.
elim: s t s0 IHt => // hs s IHs t _ IHt /= /andP[ahs phss] phtt.
case: ifPn.
  move/eqP => hsht qst.
  case: s IHs phss qst => [|h s IHs phss qst].
(*
    rewrite hsht.

    rewrite /omega_max/=.
    rewrite big_nat1/= big_nat_recl/=.
    apply: bigmax_le.
*)
  admit.
  rewrite /omega_max/=.
  rewrite 2?big_nat_recl//= hsht.
  rewrite le_max2 => //.
  (* apply: IHt => //. *)
    admit.
  (* rewrite le_max; apply/orP. *)
    admit.

Abort.
(*
rewrite /=; case: ifPn => hshht /andP[ahs] phss.
  move=> /andP[hhtht phtt] sub_stt.
  apply: (@le_trans _ _ (omega_max a b f [:: ht & t])).
    apply: omega_max_cons => //=.
    rewrite hhtht andbT.
    by have /eqP <- := hshht.
  have := (IHs s).
  have := @omega_max_cons a b f s hs.
  have /eqP <- := hshht; rewrite ahs/=.
  have := (IHs s).
  by rewrite /= eqxx IH.

rewrite /=; case: ifPn => [/eqP|] at0.
  move: rat0; rewrite -{}at0 {t0} => raa.
  rewrite [X in subseq _ X](_ : _ = merge r (a :: s) t1)//.
  exact: (subseq_trans (subseq_cons _ _) (ih s IH)).
rewrite [X in subseq _ X](_ : _ = merge r (a :: s) t1)//.
exact: ih.



  rewrite /=; case: ifPn => hsht phss.
  move=> sub_stt.
  have := @omega_max_cons a b f t ht.
  have := (IHs s).
  by rewrite /= eqxx IH.
rewrite /=; case: ifPn => [/eqP|] at0.
  move: rat0; rewrite -{}at0 {t0} => raa.
  rewrite [X in subseq _ X](_ : _ = merge r (a :: s) t1)//.
  exact: (subseq_trans (subseq_cons _ _) (ih s IH)).
rewrite [X in subseq _ X](_ : _ = merge r (a :: s) t1)//.
exact: ih.


elim: t s.
  by move => ? /negP.
move=> x t' IHs s; move/IHs => IHs'.
elim: s IHs' => //.
Admitted.
*)

Import Order.Def.

Lemma omega_max_merge1 a b f s x :
  s != [::] -> path <=%R a s -> last a s == b ->
  a <= x <= b ->
(omega_max a b f (merge <%R s [:: x]) <= omega_max a b f s)%E.
Proof.
move: s a.
elim => // h s IH a _ pahs lsb.
case: s IH pahs lsb => [_|].
  rewrite /= andbT => /[swap]/eqP -> ab.
  move=> /andP[ax xb].
  rewrite ifF; last by apply/negP/negP; rewrite -leNgt.
  rewrite /omega_max/=.
  rewrite !big_nat_recl//= !big_nil/=.
  rewrite 2!maxeNy.
  rewrite ge_max; apply/andP; split; apply: oscillation_sub.
  - exact: subset_itvl.
  - exact: subset_itvr.
move=> s0 s1 IH.
rewrite [s0 :: s1]lock => /=/andP[ah phs] ls1b /andP[ax xb].
case: ifPn => [hx|].
  rewrite /omega_max/=.
  rewrite !big_nat_recl//=.
  rewrite le_max2//.
  rewrite -lock IH//=.
  - by move: phs; rewrite -lock.
  - by move: ls1b; rewrite -lock.
  - by rewrite xb ltW.
rewrite -leNgt => xh.
rewrite /omega_max/=.
rewrite !big_nat_recl//=.
rewrite maxA le_max2// ge_max; apply/andP; split; apply: oscillation_sub.
- exact: subset_itvl.
- exact: subset_itvr.
Qed.

End itv_partition_length.

Section nonnegR_is_monoid.
Context {R : realType}.

Notation maxr := (@maxr {nonneg R}).

Lemma maxrA : associative maxr.
Proof. exact: maxA. Qed.

Lemma maxr0 : left_id 0%:nng maxr.
Proof.
move=> x.
apply/max_idPr.
rewrite (_ : widen_itv 0%:itv = widen_itv `|@GRing.zero R|%:itv).
  by rewrite num_abs_le.
apply/esym/eqP.
by rewrite num_abs_eq0.
Qed.

Lemma max0r : right_id 0%:nng maxr.
Proof.
move=> x.
apply/max_idPl.
rewrite (_ : widen_itv 0%:itv = widen_itv `|@GRing.zero R|%:itv).
  by rewrite num_abs_le.
apply/esym/eqP.
by rewrite num_abs_eq0.
Qed.

HB.instance Definition _ := Monoid.isLaw.Build {nonneg R} 0%:nng maxr maxrA maxr0 max0r.

End nonnegR_is_monoid.

Section itv_partition_length_lemmas.
Context {R : realType}.
Implicit Types (a b : R) (f : R -> R).
Implicit Types (s : seq R) (x : R).

Lemma itv_partition_max0 a b s :
  0 <= itv_partition_max a b s.
Proof. by rewrite /itv_partition_max. Qed.

Lemma itv_partition_max_eq_merge_subseq a b s t :
  path <=%R a s -> path <=%R a t ->
  subseq t s ->
  itv_partition_max a b (merge <=%R s t) = itv_partition_max a b s.
Proof.
elim: t s => //=.
  move=> pas _ _.
  by rewrite merge0r.
move=> h t IH s pas /andP[ah pht] subhts.
rewrite merge_cons_mergel; last 2 first.
- exact: le_trans.
- exact: le_path_min.
rewrite IH; last 3 first.
- apply: merge_path => //.
  by rewrite /= ah.
- apply: (path_le _ ah) => //; exact: le_trans.
- apply: (@subseq_trans _ s); last exact: subseq_mergel.
  apply: subseq_trans subhts.
  exact: subseq_cons.
rewrite /itv_partition_max => //.
rewrite size_merge.
have hs : h \in s.
  have /mem_subseq/subsetP := subhts.
  move/(_ h); rewrite 2!inE; apply.
  exact: mem_head.
set n := index h (s ++ [:: h]).
have : (n <= size (s ++ [:: h]))%N.
  by rewrite index_size.
rewrite size_cat/= addn1 => ns.
(* needs Monoid instance! *)
(* have : (\big[@Num.max {nonneg R}/_]_(0 <= n0 < (size s).+1)
      widen_itv `|nth b (merge <=%R s [:: h]) n0 - nth b (a :: merge <=%R s [:: h]) n0|%:itv)%:num = a.
rewrite big_cat_nat.
have := (@big_cat_nat {nonneg R} (0%:nng) (@maxr {nonneg R})). (leq0n n) ns).
*)
Admitted.

Lemma path_merge_ltW a b (s t : seq R) :
  path <=%R a s -> subseq t s ->
itv_partition_max a b s = itv_partition_max a b (merge <=%R s t).
Proof.
Admitted.

Lemma itv_partition_max_merge1_le a b s x :
  path <%R a s -> a <= x <= b -> last a s == b ->
  itv_partition_max a b (merge <%R s [:: x]) <= itv_partition_max a b s.
Proof.
move=> ps /eqP sb.
have [xs|xs] := boolP (x \in s).
  (* rewrite itv_partition_max_merge_subseq. *)
  admit.
(*
apply: subseq_itv_partition_max.
have itv_partition_max_merge : 
*)
Admitted.

Lemma itv_partition_max_merge1' a b l s x :
  path <=%R a s -> last a s == b ->
  itv_partition_max a b s <= l ->
  itv_partition_max a b (merge <=%R s [:: x]) <= l.
Proof.
elim: s => //.
  move=> ? /=.
  rewrite /itv_partition_max/=.
  rewrite big_nat_recl// big_nil/=.
  
rewrite /itv_partition_max/=.

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
move=> xt.
elim: s x t xt => [x t xt|s0 s1 ih x t xt].
  by rewrite /= merger_cons// order_path_min//; exact: lt_trans.
rewrite /=.
rewrite -/(merge (s0 :: s1) t).
case: ifPn => [s0x|].
  rewrite merger_cons//; last first.
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

Lemma disj_seq_merge_ltW {R : realType} (s t : seq R) : disj_seq s t ->
 merge <%R s t = merge <=%R s t.
Proof.
Admitted.

Section itv_partition_udmerge_disj_seq_lemmas.
Context {R : realType}.
Implicit Types (a b : R) (s : seq R) (x : R).

Lemma itv_partition_merge a b s t :
 itv_partition a b s ->
 itv_partition a b t ->
 disj_seq s t -> itv_partition a b (merge <%R s t).
Proof.
move=> ps pt.
(*move=> /disj_seq_allP[/allP ts /allP st].*)
Abort.

Lemma itv_partition_udmerge a b s t :
 itv_partition a b s ->
 itv_partition a b t ->
 itv_partition a b (udmerge s t).
Proof.
Abort.

End itv_partition_udmerge_disj_seq_lemmas.

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

(* *)
Lemma path_ltW {R : realType} (a : R) s : path <%R a s -> path <=%R a s.
Proof.
rewrite le_path_pairwise lt_path_pairwise => H.
apply: (@sub_in_pairwise _ (fun x => x \in [set: R]) _ _ _ _ _ H).
  move=> x y _ _; exact: ltW.
apply/allP => x _; exact: in_setT.
Qed.


Section lemma5.
Context {R : realType}.
Variables (a b : R) (f : R -> R).
Hypothesis (ab : a < b).
Implicit Types (s : seq R) (x : R).

Arguments unif_continuous : clear implicits.

Let variation_merge1_tmp s :
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

Let variation_merge1 s :
  path <=%R a s -> last a s == b ->
  forall x, x \in `[a, b] ->
    ((variation a b f (merge <%R s [:: x]))%:E <=
          (variation a b f s)%:E + 2 * omega_max a b f s)%E.
Proof.
move=> pas lsb x.
have [xs|xs] := boolP (x \in s).
- admit.
have [us|us] := boolP (uniq s); last first.
- admit.
have [hsa|hsa] := eqVneq (head b s) a.
  admit.
rewrite in_itv/= => /andP[].
have {}pas : path <%R a s.
  admit.
rewrite le_eqVlt => /predU1P[]ax; rewrite le_eqVlt => /predU1P[]xb.
- admit.
- admit.
- admit.
- apply: variation_merge1_tmp => //.
  by rewrite in_itv/=; apply/andP.
Admitted.

Let variation_merge_tmp l s t :
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
have s0 : s != [::].
    apply: itv_partition_neq0 ps.
    by move: ab; rewrite lt_neqAle => /andP[].
rewrite merge_cons; last first.
  have [+ _] := pht.
  by rewrite /= => /andP[].
move: t s maxoo ps sl s0 IH pht disjst; apply: last_ind.
  move=> s maxoo ps sl s0 IH pht disjst.
  rewrite merge0r/= mul1e.
  apply: variation_merge1_tmp => //.
  - admit.
  - admit.
(* apply: variation_merge1 => //.
  - apply: path_ltW.
    by have [] := ps.
  - by have [] := ps.
  - apply: subset_itv_oc_cc.
    apply: (itv_partition_in_itv pht).
    by rewrite mem_seq1.
*)
move=> t tt IH1 s maxoo ps sl s0 IH2 pht disjst.
have ttb : tt = b.
  move: pht => [_].
  by rewrite last_cons last_rcons => /eqP.
apply: (le_trans (IH2 _ _ _ _ _ _)).
- apply: le_lt_trans maxoo.
  have [ps_lt lsb] := ps.
  apply: omega_max_merge1 => //.
  exact: path_ltW.
- have [] := ps.
  move/path_ltW => psle lasb.
  apply/andP; split.
  + by have [/=/andP[/ltW+ _] _] := pht.
  + rewrite -(@nth_index _ b h (h :: (rcons t tt))); last exact: mem_head.
    apply: itv_partition_nth_le; first by rewrite /= eqxx//.
    exact: itv_partition_cons pht.
- apply: itv_partition_merge1 => //.
  + admit.
  + admit.
- apply: (le_trans (itv_partition_max_merge1_le _ _ _)) => //.
  + by have [] := ps.
  + admit.
  + by have [] := ps.
(*
rewrite disj_seq_merge_ltW; last first.
    apply/disj_seq_allP; split; apply/allP.
      admit.
    admit.
  exact: itv_partition_max_merge1'.
*)
- apply: (itv_partition_cons1 _ pht).
  have pt := itv_partition_cons pht.
  apply: (itv_partition_neq0 _ pt).
  rewrite lt_eqF//.
  rewrite -rcons_cons in pht.
  have [+ _] := pht.
  rewrite -rev_path.
  move/order_path_min.
  have lt_trans_rev : transitive (fun x => <%R ^~ x).
    admit.
  move/(_ lt_trans_rev).
  move/allP.
  rewrite last_rcons ttb.
  apply.
  by rewrite mem_rev belast_rcons in_cons; apply/orP; right; exact: mem_head.
  (* have := (itv_partition_head_in_itv pht). *)
- admit.
have hab : h \in `]a, b[.
  admit.
(*
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
  apply: omega_max_merge1 => //.
  - apply: path_ltW.
    by have [] := ps.
  - admit.
  - admit.
rewrite -addeAC leeD2r//.
apply: variation_merge1 => //.
have /disj_seq_allP[/allP + _] := disjst.
apply.
exact: mem_head.
*)
Admitted.

(* without disj_seq *)
Lemma variation_merge l s t :
  itv_partition a b s -> itv_partition_max a b s <= l ->
  itv_partition a b t ->
  ((variation a b f (merge <%R s t))%:E <= (variation a b f s)%:E +
  (size t)%:R%:E * 2 * omega_max a b f s)%E.
Proof.
have [|] := boolP (disj_seq s t).
  move=> ? ? ? ?.
  exact: variation_merge_tmp.
move=> ndsst.
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
    exists l, forall p, itv_partition a b p ->
       itv_partition_max a b p = l ->
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
  rewrite divr_gt0 => //; first by rewrite subr_gt0.
  rewrite -(mulr0n 1) ltr_nat muln_gt0; apply/andP; split => //.
  exact: (itv_partitionNnil ab partX').
move/(_ _ eps0) => [d d0 unifcf].
exists d => p pabp abpd. (* p is (I) in the paper *)

apply: (@lt_le_trans _ _ ((V' + A) / 2)).
  rewrite ltr_pdivlMr//.
  rewrite -ltrBlDr -{2}(mulr1 A) -mulrBr.
  by rewrite -{2}(mulr1n 1) -natrB// subSnn mulr1.
pose V0 : R := variation a b f (merge <%R p X').
apply: (@le_trans _ _ (V0 - (V' - A) / 2)).
  rewrite [leRHS](_ : _ = V0 - V' + (V' + A)%E / 2); last first.
    rewrite -[in LHS](@subrK _ V' V0).
    rewrite -(addrA (V0 - V')).
    congr +%R.
    rewrite -mulNr opprD opprK 2!mulrDl addrA.
    congr +%R.
    rewrite -{1}(@mulfK _ 2 _ V')// mulrDr mulr1.
    by rewrite mulrDl mulNr addrK.
  rewrite lerDr subr_ge0.
  rewrite -X'V'.
  apply: variation_subseq' => //.
  - apply: subseq_merger.
      exact: lt_trans.
    exact: itv_partition_sorted partX'.
rewrite lerBlDr -lee_fin EFinD.
have abp_led : itv_partition_max a b p <= d.
  by rewrite le_eqVlt; apply/predU1P; left.
apply: (le_trans (@variation_merge _ p X' pabp abp_led partX')).
apply: leeD2l.
(* unifcf *)
rewrite -/m.
rewrite -lee_pdivlMl; last first.
  rewrite mulr_gt0//.
  rewrite -(mulr0n 1) ltr_nat.
  exact: (itv_partitionNnil ab partX').
rewrite (_ : ((V' - A) / 2) = (m%:R * 2)%R * eps)%R; last first.
  rewrite /eps.
  rewrite (_ : 4 = 2 * 2)%N//.
  rewrite mulnAC 2!natrM.
  rewrite 2!invfM 2!mulrA.
  congr *%R.
  rewrite mulrA.
  rewrite -(mulrA m%:R 2).
  rewrite -(mulrA m%:R (2 * (V' - A))).
  rewrite mulrC.
  rewrite (mulrA m%:R^-1).
  rewrite mulVf ?mul1r; last first.
    apply: lt0r_neq0.
    rewrite -(mulr0n 1) ltr_nat.
    exact: (itv_partitionNnil ab partX').
  by rewrite mulrAC divff// mul1r.
rewrite /omega_max.
apply: bigmax_le; first by rewrite leNye.
move=> n _.
rewrite /oscillation/=.
rewrite -image_comp.
have : compact (f @` `[(nth b (a :: p) n), (nth b p n)]).
  apply: continuous_compact.
    apply: continuous_subspaceW cf.
    apply: subset_itv; rewrite bnd_simp//.
      case: n => //= n.
      exact/ltW/itv_partition_gt_lb.
    exact: (itv_partition_le_ub pabp).
  exact: segment_compact.
rewrite Rcompact_boundE/= => -[cimg ubimg lbimg].
have nonempty_img : [set f x | x in `[(nth b (a :: p) n), (nth b p n)]] !=set0.
  exists (f (nth b (a :: p) n)) => //.
  exists (nth b (a :: p) n) => //=.
  rewrite boundl_in_itv/= bnd_simp.
  have [np|] := ltnP n (size p).
    apply/ltW/pathP => //.
    by have [] := pabp.
  rewrite leq_eqVlt => /predU1P[<-|np].
    rewrite nth_last nth_default// last_cons.
    by have [_ /eqP ->] := pabp.
  by rewrite !nth_default// ltnW.
rewrite ereal_sup_EFin// ereal_inf_EFin//.
rewrite ifF; last first.
  apply/negbTE.
  move/set0P : nonempty_img; apply: contra_neq => ->.
  by rewrite image_set0.
rewrite -EFinB lee_fin.
suff : forall x y, x \in `](nth b (a :: p) n), (nth b p n)[ ->
 y \in `](nth b (a :: p) n), (nth b p n)[ ->
  `|f x - f y| < eps.
  
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
move=> /(_ _ ).
apply.
rewrite /subspace_ball.
rewrite ifT; last first.
  rewrite inE/=.
  apply: subset_itv Hx; rewrite bnd_simp.
    case: n cimg ubimg lbimg nonempty_img Hy => //=n _ _ _ _ _.
    exact/ltW/itv_partition_gt_lb.
  exact: (itv_partition_le_ub pabp).
rewrite /=; split.
  apply: subset_itv Hy; rewrite bnd_simp.
    case: n cimg ubimg lbimg nonempty_img Hx => //=n _ _ _ _ _.
    exact/ltW/itv_partition_gt_lb.
  exact: (itv_partition_le_ub pabp).
rewrite /ball/=.
rewrite -abpd.
rewrite /itv_partition_max/=.
rewrite lt_neqAle; apply/andP; split.
  admit.
have xx' : x = x' by [].
have yy' : y = y' by [].
wlog  : x y x' y' Hx Hy xx' yy' / y < x.
  move=> H.
  have [xy|] := ltP x y.
    rewrite -normrN opprB.
    exact: (H y x).
  rewrite le_eqVlt => /predU1P[xy|].
    have <- : x' = y' by [].
    by rewrite subrr normr0.
  move=> yx.
  exact: (H x y).
move=> yx.
rewrite -xx' -yy' -normrN opprB.
rewrite ltr0_norm ?opprB; last by rewrite subr_lt0.
have xyge0 : 0 <= x - y by rewrite subr_ge0 ltW.
rewrite -num_abs_le// big_mkord.
have [pn|] := ltnP n (size p).
  apply: (bigmax_sup (Ordinal pn)) => //=.
  rewrite num_abs_le//=.
  rewrite ger0_norm; last first.
    rewrite subr_ge0.
    apply/pathP => //.
    apply: path_ltW.
    by have [] := pabp.
  apply: lerB.
  - by apply/ltW; have := Hx; rewrite in_itv/= => /andP[].
  - by apply/ltW; have := Hy; rewrite in_itv/= => /andP[].
move=> pn.
move: Hx.
rewrite (nth_default _ pn).
move: pn.
rewrite leq_eqVlt => /predU1P[|pn].
  move=> <-.
  rewrite -last_nth.
  have [_ /eqP ->] := pabp.
  by rewrite in_itv/= => /andP[bx /(lt_trans bx)]; rewrite ltxx.
rewrite nth_default//=.
by rewrite in_itv/= => /andP[bx /(lt_trans bx)]; rewrite ltxx.
Admitted.

(* 
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
*)

End lemma5.
