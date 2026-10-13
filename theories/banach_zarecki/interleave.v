From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import boot order interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean perm finmap.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions contra cardinality.
From mathcomp Require Import reals topology normedtype ereal sequences derive.
From mathcomp Require Import measure lebesgue_measure numfun realfun.
From mathcomp Require Import measurable_realfun.
From mathcomp Require Import absolute_continuity.

(**md**************************************************************************)
(* # interleave                                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Section interleave.

Definition seq_of_pair {T} (s : seq (T * T)) : seq (seq T) :=
  [seq [:: ab.1; ab.2] | ab <- s].

Fixpoint intlv {T} (s t : seq T) :=
  match s, t with
  | x :: s', y :: t' => x :: y :: intlv s' t'
  | _, _ => [::]
  end.

Lemma intlvE {T} (s t : seq T) :
  intlv s t = flatten (seq_of_pair (zip s t)).
Proof. by elim: s t => [|x s' IH] [|]// y t'//=; rewrite IH. Qed.

Lemma shape_pairs {T} (s : seq (T * T)) :
  shape (seq_of_pair s) = nseq (size s) 2.
Proof. by elim: s => [|[x y] s IH] //=; rewrite IH. Qed.

Lemma size_intlv {T} (s t : seq T) :
   (size (intlv s t) = (minn (size s) (size t)).*2)%N.
Proof. by rewrite intlvE size_flatten shape_pairs sumn_nseq size_zip mul2n. Qed.

Lemma intlv0s {T} (t : seq T) :
  intlv [::] t = [::].
Proof. by []. Qed.

Lemma intlvs0 {T} (s : seq T) :
  intlv s [::] = [::].
Proof. by elim: s. Qed.

Lemma intlv_cons {T} (x y : T) (s t : seq T) :
  intlv (x :: s) (y :: t) = x :: y :: intlv s t.
Proof. by []. Qed.

Lemma subseq_intlvr {T : eqType} (s t : seq T) :
  (size s <= size t)%N ->
   subseq s (intlv s t).
Proof.
elim: s t.
  by move=> ? _; apply: sub0seq.
move=> s0 s1 IHs.
case => // t0 t1; rewrite [X in X -> _]/= ltnS => st.
rewrite intlv_cons -(cat1s s0) -(cat1s s0 (t0 :: _)) subseq_cat2l.
apply: (@subseq_trans _ (intlv s1 t1)).
  exact: IHs.
exact: cons_subseq.
Qed.

Lemma subseq_intlvl {T : eqType} (s t : seq T) :
  (size t <= size s)%N ->
   subseq t (intlv s t).
Proof.
elim: s t; first by case.
move=> s0 s1 IHs.
case => // t0 t1; rewrite [X in X -> _]/= ltnS => ts.
rewrite intlv_cons.
apply: (@subseq_trans _ (t0 :: (intlv s1 t1))).
  by rewrite /= ifT//; apply: IHs.
exact: cons_subseq.
Qed.

Lemma mem_intlvr {T : eqType} (s t : seq T) :
  (size s <= size t)%N ->
  forall x, x \in s -> x \in intlv s t.
Proof.
elim: s t => //=.
move=> s0 s1 IHs.
case => // t0 t1; rewrite [X in X -> _]/= ltnS => s1t1 x.
rewrite !in_cons => /predU1P[->|xs1].
  by apply/orP; left.
by apply/orP; right; apply/orP; right; apply: IHs.
Qed.

Lemma mem_intlvl {T : eqType} (s t : seq T) :
  (size t <= size s)%N ->
  forall x, x \in t -> x \in intlv s t.
Proof.
elim: t s => //=.
move=> t0 t1 IHt.
case => // s0 s1; rewrite [X in X -> _]/= ltnS => t1s1 x.
rewrite intlv_cons !in_cons => /predU1P[->|xs1].
  by apply/orP; right; apply/orP; left.
by apply/orP; right; apply/orP; right; apply: IHt.
Qed.

Lemma perm_intlv {T : eqType} (s t : seq T) :
  size s = size t ->
  perm_eq (intlv s t) (s ++ t).
Proof.
elim: s t.
  by move=> t /=/esym/size0nil ->.
move=> s0 s1 IHs.
case => // t0 t1.
rewrite [X in X -> _]/= => /eq_add_S s1t1.
rewrite intlv_cons /= perm_cons.
rewrite -[X in _ _ (_ ++ X)]cat1s perm_sym perm_catCA cat1s perm_cons perm_sym.
exact: IHs.
Qed.

Lemma mem_intlv {T : eqType} (s t : seq T) :
  size s = size t ->
  intlv s t =i s ++ t.
Proof.
move=> st; apply: perm_mem.
exact: perm_intlv.
Qed.

Lemma le_sorted_intlvl d {T : orderType d} (s t : seq T) :
  (size s <= size t)%N ->
   sorted <=%O (intlv s t) -> sorted <=%O s.
Proof.
elim: s t => // s0 s1 IH; case => // t0 t1.
rewrite [X in X -> _]/= ltnS => s1t1; rewrite intlv_cons/= => /andP[s0t0].
rewrite !le_path_sortedE => /andP[/allP t0st sst]; apply/andP; split.
  by apply/allP => ? ?; apply: (le_trans s0t0); apply: t0st; apply: mem_intlvr.
exact: (IH _ s1t1).
Qed.

Lemma le_sorted_intlvr d {T : orderType d} (s t : seq T) :
  (size t <= size s)%N ->
   sorted <=%O (intlv s t) -> sorted <=%O t.
Proof.
elim: t s => // t0 t1 IH; case => // s0 s1.
rewrite [X in X -> _]/= ltnS => t1s1; rewrite intlv_cons/= => /andP[s0t0].
rewrite !le_path_sortedE => /andP[/allP t0st sst]; apply/andP; split.
  by apply/allP => ? ?; apply: t0st; apply: mem_intlvl.
exact: (IH _ t1s1).
Qed.

Lemma sorted_seq_of_pairP {T : eqType} (e : rel T) (st : seq (T * T)) :
  transitive e ->
  (sorted e (flatten (seq_of_pair st))) <->
    [/\ (forall i d, (i < (size st))%N ->
                 e (nth d (unzip1 st) i) (nth d (unzip2 st) i)) &
     (forall i d, (i.+1 < (size st))%N ->
              e (nth d (unzip2 st) i) (nth d (unzip1 st) i.+1))].
Proof.
move=> te.
elim: st => // st0 st [IH1 IH2]; split.
  move=> /=/andP[st0le]; rewrite path_sortedE => // /andP[st02st].
  move/IH1 => [st12 st21]; split => i d.
    by case: i => //= n; rewrite ltnS; move/st12; apply.
  rewrite ltnS; case: i => /= [sizest0|n sizest_n1].
    move: st02st => /allP; apply.
    move: sizest0; clear; case: st => //; move=> st0 st /= _.
    by rewrite in_cons eqxx.
  exact: st21.
move=> /= [st12 st21]; apply/andP; split.
  by move: (st12 0 st0.1 isT).
apply/(pathP st0.1) => -[|].
  by move: st21; clear; case: st => // st1 st /(_ 0 st0.1).
apply/sortedP/IH2; split => i d.
  exact: (st12 i.+1 d).
exact: (st21 i.+1 d).
Qed.

(* for le. unnecessary? *)
Lemma sorted_seq_of_pairP' {T : eqType} (e : rel T) (st : seq (T * T)) :
  reflexive e ->
  transitive e ->
  (sorted e (flatten (seq_of_pair st))) <->
    [/\ (forall i d, e (nth d (unzip1 st) i) (nth d (unzip2 st) i)) &
     (forall i d, (i.+1 < (size st))%N ->
              e (nth d (unzip2 st) i) (nth d (unzip1 st) i.+1))].
Proof.
move=> re te.
split.
  move/(sorted_seq_of_pairP _ te) => [H1 H2]; split => // i d.
  have [|] := ltnP i (size st).
    by move/H1.
  by move=> sti; rewrite !nth_default// size_map.
move=> [H1 H2]; exact: (sorted_seq_of_pairP _ te).2.
Qed.

Lemma le_sorted_intlvP {R : realType} (s t : seq R) :
  size s = size t ->
  (sorted <=%R (intlv s t)) <->
    [/\ (forall i d, nth d s i <= nth d t i) &
     (forall i d, (i.+1 < (size s))%N -> nth d t i <= nth d s i.+1)].
Proof.
move=> st; rewrite intlvE.
rewrite -{-1}(unzip1_zip (eq_leq st)) size_map -{3 5}(@unzip2_zip _ _ s t)?st//.
exact/sorted_seq_of_pairP'/le_trans/le_refl.
Qed.

Lemma lt_sorted_intlvP {R : realType} (s t : seq R) :
  size s = size t ->
  (sorted <%R (intlv s t)) <->
   (forall (i : nat) d, (i < (size s))%N -> nth d s i < nth d t i) /\
     (forall i d, (i.+1 < (size s))%N -> nth d t i < nth d s i.+1).
Proof.
move=> st; rewrite intlvE.
rewrite -{-1}(unzip1_zip (eq_leq st)) size_map -{4 6}(@unzip2_zip _ _ s t)?st//.
apply/sorted_seq_of_pairP/lt_trans.
Qed.

Lemma intlv_merge {R : realType} (s t : seq R) :
  size s = size t ->
  sorted <=%R (intlv s t) ->
  intlv s t = merge <=%R s t.
Proof.
move=> st /[dup]sorted_st.
have srts : sorted <=%R s by exact: (le_sorted_intlvl (eq_leq st)).
have srtt : sorted <=%R t by exact: (le_sorted_intlvr (eq_leq (esym st))).
move/le_sorted_intlvP => []// slet tles1.
apply: le_sorted_eq => //.
  apply: merge_sorted => //.
  exact: le_total.
rewrite perm_sym perm_merge perm_sym.
exact: perm_intlv.
Qed.

Lemma nth_intlvE {T} (d : T) (s t : seq T) n :
  nth d (intlv s t) n =
    if (n < size (intlv s t))%N then
      if odd n then nth d t n./2 else nth d s n./2
    else d.
Proof.
elim: s t n => [|x s IH] [|y t] [|[|n]] //=.
by rewrite negbK; exact: IH _ n.
Qed.

Lemma last_intlv {T} (d : T) (s t : seq T) :
  (size t <= size s)%N ->
  last d (intlv s t) = last d t.
Proof.
move=> ts.
have size_st : size (intlv s t) = (size t).*2.
  rewrite size_intlv /minn ifF//.
  by apply/negP/negP; rewrite -leqNgt.
rewrite -!nth_last nth_intlvE.
case: ifP; rewrite ltn_predL; last first.
  move/negP/negP; rewrite -eqn0Ngt size_st double_eq0.
  by move/eqP => t0; rewrite nth_default ?t0.
rewrite size_st/=.
set n := size t; have : n = size t by [].
case: n => //n nt _/=.
by rewrite odd_double/= uphalf_double.
Qed.

End interleave.
