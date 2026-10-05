From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum interval.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp contra classical_sets.
From mathcomp Require Import reals ereal topology normedtype numfun.

(**md**************************************************************************)
(* # Oscillation                                                              *)
(*                                                                            *)
(* `oscillation f A`                                                          *)
(* : oscillation of function `f : R -> R` on `A : set R`                      *)
(* : This is an extended real number.                                         *)
(*                                                                            *)
(* `omega_max a s f`                                                          *)
(* : max of oscillation over the intervals $[(a::s)_i, (a::s)_{i+1}]$         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma is_subset1P (T : Type) (A : set T) : is_subset1 A ->
  A = set0 \/ exists a, A = [set a].
Proof.
move=> A1.
have [|/set0P[x Ax]] := eqVneq A set0; first by left.
right; exists x.
apply/seteqP; split => [y|y ->//].
by move/A1; exact.
Qed.

(* TODO: PR? *)
Lemma setNEFin {R : realType} (f : R -> R) (A : set R) :
  [set (- x)%E | x in ((EFin \o f) @` A)] = (EFin \o (\- f)%R) @` A.
Proof.
apply/seteqP; split => [_ [_/= [r Ar] <- <-]|_/= [r Ar] <-].
  by exists r.
by exists (f r)%:E => //; exists r.
Qed.

(* TODO: PR? *)
Lemma ereal_inf_sup {R : realType} (A : set (\bar R)) : A !=set0 ->
  (ereal_inf A <= ereal_sup A)%E.
Proof.
move=> [a Aa].
by rewrite (@le_trans _ _ a)//;
  [exact: ereal_inf_lbound|exact: ereal_sup_ubound].
Qed.

Section itv_partition_porder.
Context {d} {T : porderType d}.
Implicit Types (a b x : T) (s : seq T).

Lemma itv_partition_neq0 a b s : a != b -> itv_partition a b s -> s != [::].
Proof. by elim: s a b => // a' b' /negbTE a'b' []/=; rewrite a'b'. Qed.

Lemma itv_partition_sorted a b s : itv_partition a b s -> sorted <%O s.
Proof. by case => sa _; exact: path_sorted sa. Qed.

Lemma last_mem_itv_partition a b s :
  itv_partition a b s -> (a < b)%O -> b \in s.
Proof.
move: s; apply: last_ind => //.
- by move/itv_partition_nil ->; rewrite ltxx.
- move=> s' x' _ [_].
rewrite [a]lock.
  rewrite last_rcons => /eqP -> _.
  by rewrite mem_rcons mem_head.
Qed.

Lemma itv_partitionNnil a b s : (a < b)%O ->
 itv_partition a b s -> (0 < size s)%N.
Proof.
move=> ab p; apply: (@leq_trans (size [:: b])); rewrite ?size_subseq ?sub1seq//.
exact: last_mem_itv_partition ab.
Qed.

Lemma itv_partition_cons1 a b s x :
  s != [::] ->
  itv_partition a b (x :: s) -> itv_partition a b s.
Proof.
case: s => // s0 s1 _.
case => /= /and3P[ax xs0 s0s1 s0s1b]; split => //=.
by rewrite s0s1 andbT (lt_trans ax).
Qed.

(*Lemma itv_partition_head a b h s :
s != [::] ->
a < h < head b s -> itv_partition a b s ->
 itv_partition a b (h :: s).
Proof.
case: s => // s0 s1 _ /andP[ah hs0] /[dup]pabs [/=/andP[as0 pas] /eqP sb].
split; first by rewrite /=; apply/and3P; split => //.
by rewrite -sb.
Qed.*)

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
  rewrite nth_index.
    by rewrite in_cons; apply/orP; right.
    move/[swap] => _.
    rewrite -last_nth last_rcons => xb.
  rewrite ifN.
    by rewrite lt_eqF// asb.
  rewrite (_ : index x (rcons s b) = index x s).
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

Lemma itv_partition_head_in_itv a b s t :
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
  rewrite ifF.
    rewrite lt_eqF => //.
    have [/lt_path_min/allP + _] := pst.
    by apply; rewrite mem_rcons in_cons xs orbT.
  by rewrite size_rcons -cats1 index_cat xs ltnS index_mem.
rewrite inE index_mem.
rewrite in_cons; apply/orP; right.
by rewrite mem_rcons in_cons xs orbT.
Qed.

Lemma itv_partition_gt_lb def a b s : (a < def)%O ->
  itv_partition a b s -> forall n, (a < nth def s n)%O.
Proof.
move=> ab ps n.
have [ns|ns] := ltnP n (size s).
  suff : nth def s n \in `]a, b].
    by rewrite in_itv/= => /andP[].
  apply: (itv_partition_in_itv ps).
  exact: mem_nth.
by rewrite nth_default.
Qed.

Lemma itv_partition_le_ub def a b s :
  itv_partition a b s -> forall n, (n < size s)%N -> (nth def s n <= b)%O.
Proof.
move=> ps n ns.
suff : nth def s n \in `]a, b].
  by rewrite in_itv/= => /andP[].
apply: (itv_partition_in_itv ps).
by apply/mem_nth.
Qed.

Lemma itv_partition_lt_ub a b s :
  itv_partition a b s -> forall n, (n.+1 < size s)%N -> (nth b s n < b)%O.
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

End itv_partition_porder.

Definition oscillation {R : realType} (f : R -> R) (A : set R) : \bar R :=
  (if A == set0 then
     0
   else
     ereal_sup ((EFin \o f) @` A) - ereal_inf ((EFin \o f) @` A))%E.

Section oscillation_lemmas.
Context (R : realType).
Local Open Scope ereal_scope.
Implicit Types (f : R -> R) (A : set R).

Lemma oscillation0 f : oscillation f set0 = 0.
Proof. by rewrite /oscillation eqxx. Qed.

Lemma oscillation_set1 (a : R) f : oscillation f [set a] = 0.
Proof.
rewrite /oscillation ifF.
  by apply/negP/negP/set0P; exists a.
by rewrite !image_set1 ereal_sup1 ereal_inf1 subee.
Qed.

Lemma is_subset1_oscillation0 f A : is_subset1 A -> oscillation f A = 0.
Proof.
move=> /is_subset1P[->|[x ->]]; first by rewrite oscillation0.
by rewrite oscillation_set1.
Qed.

Lemma oscillationN f A : oscillation (\- f)%R A = oscillation f A.
Proof.
rewrite /oscillation; case: ifPn => // A0.
rewrite [X in _ = X - _]ereal_supEN [in X in _ = _ - X]ereal_infEN.
by rewrite [RHS]addeC [in RHS]oppeK setNEFin.
Qed.

Lemma oscillation_hasNub f A : ~ has_ubound (f @` A) -> oscillation f A = +oo.
Proof.
move=> hasNubA.
rewrite /oscillation; case: ifPn => [/eqP A0|A0].
  absurd: hasNubA; rewrite A0 image_set0 /has_ubound ubound0.
  by apply/set0P; exact: setT0.
rewrite -image_comp (@hasNub_ereal_sup _ (f @` A))//.
  by apply/set0P; contra: A0; exact: image_set0_set0.
rewrite addye//.
apply/eqP; rewrite eqe_oppLRP/= => /ereal_inf_pinfty fA.
move/set0P : A0 => [x Ax].
have := ltry (f x).
by apply/negP; rewrite -leNgt leye_eq; apply/eqP/fA; exists (f x).
Qed.

Lemma oscillation_hasNlb f A : ~ has_lbound (f @` A) -> oscillation f A = +oo.
Proof.
move=> hasNlbA; have /oscillation_hasNub : ~ has_ubound ((\- f)%R @` A).
  move/has_ub_lbN.
  rewrite [X in has_lbound X](_ : _ = f @` A)//.
  rewrite image_comp//= (_ : _ \o _ = f)//=.
  by apply/funext => r/=; rewrite opprK.
by rewrite oscillationN.
Qed.

Lemma oscillation_ge0 f A : (0 <= oscillation f A)%E.
Proof.
rewrite /oscillation; case: ifPn => // /set0P[r Ar].
set s : \bar R := ereal_sup _; set i : \bar R := ereal_inf _.
have frsup : ((f r)%:E <= s)%E by rewrite ereal_sup_ubound//=; exists r.
have inffr : (i <= (f r)%:E)%E by rewrite ereal_inf_lbound//=; exists r.
have [sfin|] := boolP (s \is a fin_num).
  have [ifin|] := boolP (i \is a fin_num).
    by rewrite sube_ge0 ?sfin ?ifin// ereal_inf_sup//; exists (f r)%:E, r.
  rewrite fin_numE negb_and !negbK => /predU1P[iy|/eqP iy].
    by rewrite iy addey//; move: sfin; rewrite fin_numE => /andP[].
  by move: inffr; rewrite iy.
rewrite fin_numE negb_and !negbK => /predU1P[sy|/eqP sy].
  by absurd; move/ereal_sup_ninfty : (sy) => /(_ _ (ex_intro2 _ _ _ Ar erefl)).
have [iy|iy] := eqVneq i +oo%E.
  by move: inffr; rewrite iy leye_eq.
by rewrite sy addye// eqe_oppLR.
Qed.

Lemma oscillation_sub f i j :
  i `<=` j -> (oscillation f i <= oscillation f j)%E.
Proof.
move=> ij; have [->|i0] := eqVneq i set0.
  by rewrite oscillation0 oscillation_ge0.
have [j0|j0] := eqVneq j set0.
  by move: ij; rewrite j0 subset0 => /eqP; rewrite (negbTE i0).
rewrite /oscillation (negbTE i0) (negbTE j0) leeB//.
- by apply: ereal_sup_le; exact: image_subset.
- by apply: ereal_inf_le_tmp; exact: image_subset.
Qed.

End oscillation_lemmas.

Section omega_max.
Context {R : realType}.
Implicit Types (a : R) (f : R -> R) (s : seq R) (x : R).

(* NB: we can take 0 as a default element since the list is never addressed
   out of bounds in the definition *)
Definition omega_max a s f : \bar R :=
   \big[maxe/-oo%E]_(0 <= n < size s) oscillation f
    `[(a :: s)`_n, (a :: s)`_n.+1].

(*
Lemma bigmaxE T Q FH :
forall (F : T -> R) (HF : forall x, 0 <= F x),
  (\big[max/0%:nng]_(i in Q) (FH i)%:nng)%:num = (\big[max/0]_(i in Q) (F i)).

   reflect (\big[maxr/0%:nng]_(0 <= k < n) (P k)%:nng)%:num)
   (\big[maxr/0%R]_(0 <= k < n) P k).
*)

Lemma omega_max_nil a f : omega_max a [::] f = -oo%E.
Proof. by rewrite /omega_max /= big_nil. Qed.

Lemma omega_max_ge0 a f s : s != [::] -> (0 <= omega_max a s f)%E.
Proof.
case: s => [//|h t s0].
by rewrite /omega_max/= big_nat_recl//= le_max oscillation_ge0.
Qed.

(* TODO: PR *)
Lemma itv_partition_nth_ge_new def a b s m : (m < (size s).+1)%N ->
  itv_partition a b s -> (a <= nth def (a :: s) m)%O.
Proof.
elim: m def s a b => [def s a b _//|n ih def [//|h t] a b].
rewrite ltnS => nh [/= /andP[ah ht] lb].
by rewrite (le_trans (ltW ah))// (ih _ _ _ b).
Qed.

Lemma omega_max_le_oscillation a b f s :
  itv_partition a b s ->
  (omega_max a s f <= oscillation f `[a, b])%E.
Proof.
move=> ps.
rewrite /omega_max big_seq bigmax_le//.
  by rewrite leNye.
move=> /= n.
rewrite mem_iota add0n subn0 leq0n/= => ns.
apply: oscillation_sub.
apply: subset_itvScc; rewrite bnd_simp//.
  apply: itv_partition_nth_ge_new ps => //.
  by rewrite (leq_trans ns).
exact: (itv_partition_le_ub _ ps).
Qed.

Lemma omega_max_cons a f s x :
  a <= x <= head a s ->
  s != [::] ->
  (omega_max a (x :: s) f <= omega_max a s f)%E.
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

Lemma le_omega_max a f s t :
  s != [::] ->
  path <=%R a s ->
  sorted <=%R t ->
  subseq s t ->
  (omega_max a t f <= omega_max a s f)%E.
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
(omega_max a (merge <%R s [:: x]) f <= omega_max a s f)%E.
Proof.
move: s a.
elim => // h s IH a _ pahs lsb.
case: s IH pahs lsb => [_|].
  rewrite /= andbT => /[swap]/eqP -> ab.
  move=> /andP[ax xb].
  rewrite ifN; first by rewrite -leNgt.
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

End omega_max.
