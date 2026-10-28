From mathcomp Require Import boot order algebra.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions contra cardinality.
From mathcomp Require Import filter reals ereal topology normedtype numfun.
From mathcomp Require Import bz_mathcomp_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section mv_to_constructive_ereal.
Context {R : realDomainType}.
Implicit Types (x y z u a b : \bar R) (r : R).

(* NB: to appear in MCA 1.19.0 (PR 2134) *)
Lemma bigmaxe_fin_num def (s : seq (\bar R)) : s != [::] ->
  {in s, forall x, (def <= x)%E /\ x \is a fin_num} ->
  \big[maxe/def]_(i <- s) i \is a fin_num.
Proof.
elim: s => // h [_ _ /(_ h)|h' t ih _ /forall_cons[[defh hfin] h'tfin]].
  rewrite mem_seq1 => /(_ (eqxx _))[/max_idPl defh hfin].
  by rewrite big_seq1_id defh.
by rewrite big_cons -fine_max// ih.
Qed.

End mv_to_constructive_ereal.

Lemma ereal_le_bigmax_seq2 {R : realType} {T : eqType} (r s : seq T) (F F' : T -> \bar R) :
  (forall i, i \in r -> exists2 j, j \in s & (F i <= F' j)%O) ->
  (\big[maxe/-oo%E]_(i <- r) F i <=
        \big[maxe/-oo%E]_(i <- s) F' i)%O.
Proof.
case: s => [h|r0 r1 h].
  rewrite big_nil leeNy_eq; apply/eqP.
  rewrite big_seq_cond.
  apply: bigmax_eq_id => i.
  by rewrite andbT => /(h i) -[?].
apply: le_bigmax_seq2 => //.
by exists r0; rewrite ?mem_head ?leNye.
Qed.

(* TODO: to appear in MCA 1.19.0 *)
Lemma itv_partition_nth_ge_with_def {d} {T : porderType d} (def a b : T) s m :
  (m < (size s).+1)%N ->
  itv_partition a b s -> (a <= nth def (a :: s) m)%O.
Proof.
elim: m s a b def => [s a b ? _//|n ih [//|h t] a b def].
rewrite ltnS => nh [/= /andP[ah ht] lb].
rewrite (le_trans (ltW ah))//.
exact: (ih _ _ b).
Qed.

Lemma subset_setCS {R} (X A B : set R) : A `<=` X -> B `<=` X ->
  (A `<=` B) = (X `\` B `<=` X `\` A).
Proof.
move=> AX BX.
apply/propeqP; split => [|H x Ax]; first exact: setDS.
have [Xx|nBx] := pselect (X x).
  apply/not_notP => nBx.
  have /H[_] := conj Xx nBx.
  exact.
by absurd: nBx; exact: AX.
Qed.

(* TODO: put an order on `<`? *)
Lemma proper_subset_trans T (B A C : set T) : A `<` B -> B `<=` C -> A `<` C.
Proof.
move=> AB BC; rewrite properEneq; split; last first.
  by apply: subset_trans BC; exact: properW.
apply/negP => /eqP AC; subst C.
move: AB; rewrite properEneq => -[+ AB].
by move/negP; apply; exact/eqP/seteqP.
Qed.

Lemma proper_itvoo_cc {R : realType} (a b c d : R) : a < b ->
  (c <= a) /\ (b <= d) -> [set` `]a, b[ ] `<` [set` `[c, d] ].
Proof.
move=> ab.
move=> [ca bd].
rewrite properEneq; split; last first.
  by apply/subset_itv; rewrite bnd_simp// ltW.
apply/negP => /eqP abcd.
pose x := (b + d) / 2.
have : `[c, d]%classic x.
  rewrite /= in_itv/= midf_le// andbT.
  by rewrite (le_trans ca)// (le_trans (ltW ab))// midf_le.
rewrite -abcd/= in_itv/= => /andP[_].
rewrite ltNge => /negP; apply.
by rewrite midf_le.
Qed.

Lemma proper_itvoo {R : realType} (a b c d : R) : a < b ->
  (c <= a) /\ (b < d) \/ (c < a) /\ (b <= d) ->
  [set` `]a, b[ ] `<` [set` `]c, d[ ].
Proof.
move=> ab.
move=> [[ca bd]|[cb bd]].
  rewrite properEneq; split; last first.
    by apply/subset_itv; rewrite bnd_simp// ltW.
  apply/negP => /eqP abcd.
  pose x := (b + d) / 2.
  have : `]c, d[%classic x.
    rewrite /= in_itv/= midf_lt// andbT.
    by rewrite (le_lt_trans ca)// (lt_le_trans ab)// midf_le// ltW.
  rewrite -abcd/= in_itv/= => /andP[_].
  rewrite ltNge => /negP; apply.
  by rewrite midf_le// ltW.
rewrite properEneq; split; last first.
  by apply/subset_itv; rewrite bnd_simp// ltW.
apply/negP => /eqP abcd.
pose x := (c + a) / 2.
have : `]c, d[%classic x.
  rewrite /= in_itv/= midf_lt//=.
  by rewrite (lt_le_trans _ bd)// (lt_trans _ ab)// midf_lt//.
rewrite -abcd/= in_itv/= => /andP[+ _].
rewrite ltNge => /negP; apply.
by rewrite midf_le// ltW.
Qed.

Lemma perm_eq_trivIset_ord {T : eqType} {n} (s1 s2 : n.-tuple (set T)) (D : set nat) :
  `I_n `<=` D -> perm_eq s1 s2 -> trivIset D (nth set0 s1) -> trivIset D (nth set0 s2).
Proof.
move=> InD s12.
apply: perm_eq_trivIset => //.
by rewrite size_tuple.
Qed.

Section continuous_interval.
Context {R : realType}.
Variables (D : set R) (f : R -> R).
Hypothesis cf : {within D, continuous f}.

Lemma is_interval_image_cc a b : `[a, b] `<=` D ->
  is_interval (f @` `[a, b]).
Proof.
have [ab abD|ba _] := leP a b; last first.
  rewrite set_itv_ge// ?bnd_simp -?ltNge// image_set0.
  exact/connected_intervalP/connected0.
move=> _ _/= -[x0 x0ab <-] [x1 x1ab <-] z /andP[fx0z zfx1].
have [x01|x10] := leP x0 x1.
  have [x xx01 fxz] : exists2 x : R, x \in `[x0, x1] & f x = z.
    apply: IVT => //.
      apply: continuous_subspaceW cf.
      by apply: subset_trans abD; apply: subset_itv;
        rewrite bnd_simp ?(itvP x0ab) ?(itvP x1ab).
    by rewrite ge_min le_max fx0z/= zfx1 orbT.
  exists x => //.
  by apply: subset_itv xx01; rewrite bnd_simp ?(itvP x0ab) ?(itvP x1ab).
have [x xx01 fxz] : exists2 x : R, x \in `[x1, x0] & f x = z.
  apply: IVT => //.
  - exact: ltW.
  - apply: continuous_subspaceW cf.
    by apply: subset_trans abD; apply: subset_itv;
      rewrite bnd_simp ?(itvP x0ab) ?(itvP x1ab).
  by rewrite ge_min le_max fx0z/= zfx1 orbT.
exists x => //.
by apply: subset_itv xx01; rewrite bnd_simp ?(itvP x0ab) ?(itvP x1ab).
Qed.

End continuous_interval.
