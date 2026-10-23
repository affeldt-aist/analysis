From mathcomp Require Import boot order path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory.

Local Open Scope ring_scope.

Lemma reshape_nseq1 {T} (s : seq T) (n : nat) : size s = n ->
  reshape (nseq n 1%N) s = [seq [:: x] | x <- s].
Proof.
by elim: s n => [[]//| s0 s1/= ih [//|n] [s1n]/=]; rewrite take0 drop0 ih.
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
