From mathcomp Require Import boot order path.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory.

Local Open Scope ring_scope.

Lemma le_bigmax_seq2 {T : eqType} d {T' : orderType d} idx idx' (r s : seq T)
   (F F' : T -> T') :
  (exists2 j, j \in s & (idx <= F' j)%O) ->
  (forall i, i \in r -> exists2 j, j \in s & (F i <= F' j)%O) ->
  (\big[Order.Def.max/idx]_(i <- r) F i <=
        \big[Order.Def.max/idx']_(i <- s) F' i)%O.
Proof.
elim: r s F F' => [s F F' [j0 hj0 lej0] _|/= r0 r1 ih s F F' idx_min h].
  rewrite big_nil//.
  exact: (bigmax_sup_seq idx' j0 _).
rewrite big_cons ge_max; apply/andP; split.
  have := h r0.
  rewrite mem_head => /(_ isT)[j js] /le_trans; apply.
  by apply: le_bigmax_seq.
apply: ih => [//|i ir1].
have := h i.
by rewrite inE ir1 orbT => /(_ isT).
Qed.

Lemma reshape_nseq1 {T} (s : seq T) (n : nat) : size s = n ->
  reshape (nseq n 1%N) s = [seq [:: x] | x <- s].
Proof.
by elim: s n => [[]//| s0 s1/= ih [//|n] [s1n]/=]; rewrite take0 drop0 ih.
Qed.

Lemma filterC_split d {R : orderType d} (s t : seq R) :
  sorted <=%O s ->
  s = merge <=%O [seq x <- s | x \in t] [seq x <- s | x \notin t].
Proof.
move=> sorted_s.
apply: le_sorted_eq => //.
  by rewrite merge_sorted ?le_sorted_filter//; exact: le_total.
by rewrite perm_sym perm_merge perm_filterC.
Qed.

(* TODO: PR? *)
Lemma path_ltW d {T : orderType d} (a : T) s : path <%O a s -> path <=%O a s.
Proof.
rewrite le_path_pairwise lt_path_pairwise.
apply: (@sub_in_pairwise _ xpredT); last exact/allP.
by move=> x y _ _; exact: ltW.
Qed.

Lemma sorted_rconsE {T : eqType} (leT : rel T) :
  transitive leT ->
  forall {x : T} {s : seq T},
  sorted leT (rcons s x) = sorted leT s && all (leT ^~ x) s.
Proof.
move=> tr x s.
rewrite -rev_sorted rev_rcons/= path_sortedE; first exact: rev_trans.
by rewrite all_rev rev_sorted andbC.
Qed.

Lemma le_sorted_rconsE d {R : porderType d} (x : R) (s : seq R) :
  sorted <=%O (rcons s x) = sorted <=%O s && all (<=%O ^~ x) s.
Proof. rewrite sorted_rconsE//; exact: le_trans. Qed.

Lemma lt_sorted_rconsE d {R : porderType d} (x : R) (s : seq R) :
  sorted <%O (rcons s x) = sorted <%O s && all (<%O ^~ x) s.
Proof. rewrite sorted_rconsE//; exact: lt_trans. Qed.

Lemma le_sorted_flatten {disp} {R : porderType disp} (d : R) (ss : seq (seq R)) :
  all (fun s => s != [::]) ss ->
  all (sorted <=%O) ss ->
  sorted (fun s t => last d s <= head d t)%O ss ->
  sorted <=%O (flatten ss).
Proof.
elim: ss => //= s0.
case => //=.
  move=> _ _ + _.
  by rewrite andbT cats0.
case => //=.
  by rewrite andbF.
move=> hs1 s1 ss1 IH.
move=> /andP[s00 s10Ass10] /andP[sorted_s0 sorted_s1Asorted_ss1].
move=> /andP[s0s1 lh_s1ss1].
rewrite sorted_cat_cons; apply/andP; split.
  rewrite le_sorted_rconsE sorted_s0/=.
  apply/allP => x xs0.
  apply: le_trans s0s1.
  move/(nthP d) : xs0 => [n ns0 <-].
  rewrite -nth_last.
  apply: le_sorted_leq_nth => //.
    by rewrite inE prednK// (leq_trans _ ns0).
  by rewrite ltnSE// prednK// (leq_trans _ ns0).
exact: IH.
Qed.

Lemma sorted_ltW d {T : porderType d} (s : seq T) :
  sorted <%O s -> sorted <=%O s.
Proof. by apply: sub_sorted; exact: ltW. Qed.

Lemma lt_sorted_flatten {disp} {R : porderType disp} (d : R) (ss : seq (seq R)) :
  all (fun s => s != [::]) ss ->
  all (sorted <%O) ss ->
  sorted (fun s t => last d s < head d t)%O ss ->
  sorted <%O (flatten ss).
Proof.
elim: ss => //= s0.
case => //=.
  move=> _ _ + _.
  by rewrite andbT cats0.
case => //=.
  by rewrite andbF.
move=> hs1 s1 ss1 IH.
move=> /andP[s00 s10Ass10] /andP[sorted_s0 sorted_s1Asorted_ss1].
move=> /andP[s0s1 lh_s1ss1].
rewrite sorted_cat_cons; apply/andP; split.
  rewrite lt_sorted_rconsE sorted_s0/=.
  apply/allP => x xs0.
  apply: le_lt_trans s0s1.
  move/(nthP d) : xs0 => [n ns0 <-].
  rewrite -nth_last.
  rewrite le_sorted_leq_nth//.
  - exact: sorted_ltW.
  - by rewrite inE prednK// (leq_trans _ ns0).
  - by rewrite ltnSE// prednK// (leq_trans _ ns0).
exact: IH.
Qed.

Lemma sorted_filter_rcons d {R : porderType d} y (l : seq R) : sorted <%O l ->
  sorted <%O (rcons [seq x <- l | (x < y)%O] y).
Proof.
move=> sl; apply/(sortedP y)=> i; rewrite size_rcons ltnS => ily.
rewrite lt_sorted_ltn_nth ?inE ?size_rcons ?ltnS//; last by rewrite ltnW.
rewrite lt_sorted_pairwise pairwise_rcons.
apply/andP; split; first exact: filter_all.
by rewrite -lt_sorted_pairwise lt_sorted_filter.
Qed.

Lemma sorted_filter_path d {R : porderType d} y (l : seq R) :
  sorted <%O l -> path <%O y [seq x <- l | (y < x)%O].
Proof.
move=> sl; rewrite lt_path_sortedE.
by apply/andP; split; last exact: lt_sorted_filter; exact: filter_all.
Qed.

Lemma lt_sorted_mem_filter_exchange d {R : porderType d} (s t : seq R) :
  sorted <%O s -> sorted <%O t ->
  [seq x <- s | x \in t] = [seq x <- t | x \in s].
Proof.
move=> ss st; apply: lt_sorted_eq; rewrite ?lt_sorted_filter//.
by move=> ?; rewrite 2!mem_filter andbC.
Qed.

Section notin_sorted_rcons.
Context {d} {T : orderType d}.
Implicit Types (a b x : T) (s : seq T).

Lemma notin_sorted_rcons s h :
  h \notin s -> sorted <%O s ->
  sorted <%O (rcons [seq x <- s | (x < h)%O] h).
Proof.
elim: s h => // s0 s1 ih h.
rewrite in_cons negb_or => /andP[hs0 hs1]/= s0s1.
have [s0h|] := ltP s0 h.
  have : sorted <%O s1 by exact: path_sorted s0s1.
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

End notin_sorted_rcons.

Lemma lt_sorted_rcons_notin d {R : porderType d} s (x : R) :
  sorted <%O (rcons s x) -> x \notin s.
Proof.
elim: s x => // s0 [|s1 s2] ih x.
  by rewrite /= inE andbT => ?; rewrite gt_eqF.
rewrite [s1 :: s2]lock/= /= rcons_path => /andP[s0s1 s1x].
rewrite inE negb_or; apply/andP; split.
  rewrite gt_eqF//.
  move/order_path_min : s0s1 => /(_ lt_trans)/allP s0s1.
  rewrite (le_lt_trans _ s1x)//.
  apply/ltW.
  apply/s0s1.
  by rewrite -lock/= mem_last.
rewrite -lock.
apply: ih.
rewrite -lock in s0s1 s1x.
apply: (@path_sorted _ _ s0). (* TODO: path_sorted implicits *)
by rewrite rcons_path s1x s0s1.
Qed.
