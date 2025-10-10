From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import all_ssreflect interval_inference ssralg ssrnum.
From mathcomp Require Import ssrint interval archimedean.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import reals ereal topology normedtype.
From mathcomp Require Import sequences measure lebesgue_measure realfun.
From mathcomp Require Import absolute_continuity.

(**md**************************************************************************)
(* # Banach–Zarecki Theorem (lemma 4)                                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Lemma image_bigcup_disjoint T U (f : T -> U) I (D : set I)
   (F : I -> set T) :
  trivIset D F -> f @` (\bigcup_(i in D) F i) = \bigcup_(i in D) f @` F i.
Proof.
move=> DS.
apply/seteqP; split => [_ [x [i Di Six <-]]|_ [i Di [x Six <-]]].
  by exists i.
by exists x => //; exists i.
Qed.

Section complement_inner.
Context {R : realType}.
Implicit Type (A : set R).

(* complement hull? *)
Definition complement_inner A := [set` Rhull A] `\` A.

Lemma complement_inner0 A :
  is_interval A -> complement_inner A = set0.
Proof.
by move=> itvA; rewrite /complement_inner -((is_intervalP A).1 itvA) setDv.
Qed.

Lemma complement_inner_set0 :
  complement_inner set0 = set0.
Proof. by rewrite complement_inner0. Qed.

Lemma complement_innerT :
  complement_inner setT = set0.
Proof. by rewrite complement_inner0. Qed.

Lemma complement_inner_subset_Rhull A :
  complement_inner A `<=` [set` Rhull A].
Proof. exact: subDsetl. Qed.

Lemma has_ubound_complement_inner A :
  has_ubound A -> has_ubound (complement_inner A).
Proof.
have [|] := pselect (A !=set0); last first.
  move/set0P/negP/negbNE/eqP => -> _.
  rewrite complement_inner_set0.
  exact: has_ubound0.
move=> A0 /[dup]/asboolP ubA [ub ubAub].
exists ub => x [/= + _].
rewrite in_itv/= => /andP [_].
rewrite ubA/=.
have [Asup|NAsup] := pselect (A (sup A)).
  move /asboolP : (Asup) => -> /=.
  move/le_trans; apply.
  exact: ubAub.
move/asboolPn: (NAsup) => -> /= xsupA.
apply/ltW; apply: (lt_le_trans xsupA).
exact: sup_le_ub.
Qed.

Lemma has_lbound_complement_inner A :
  has_lbound A -> has_lbound (complement_inner A).
Proof.
have [|] := pselect (A !=set0); last first.
  move/set0P/negP/negbNE/eqP => -> _.
  rewrite complement_inner_set0.
  exact: has_lbound0.
move=> A0 /[dup]/asboolP lbA [lb lbAlb].
exists lb => x [/= + _].
rewrite in_itv/= => /andP [+ _].
rewrite lbA/=.
have [Ainf|NAinf] := pselect (A (inf A)).
  move /asboolP : (Ainf) => -> /=.
  apply:le_trans.
  exact: lbAlb.
move/asboolF: (NAinf) => -> /= xinfA.
apply/ltW; apply: (le_lt_trans _ xinfA).
exact: lb_le_inf.
Qed.

Lemma complement_inner_complement A :
  complement_inner A `<=` ~` A.
Proof. rewrite /complement_inner; exact: subDsetr. Qed.

(* *)
Let complement_inner_sup A :
  has_ubound A -> ~ (complement_inner A) (sup A).
Proof.
move=> hasubA.
rewrite /complement_inner/=.
apply/not_andP.
rewrite orpN => Asup.
have lt_sup := sup_ub_strict hasubA Asup.
rewrite in_itv/=.
case: ifP; move/asboolP => //= haslbA; case: ifP; move/asboolP => //= _.
  move/asboolPn : Asup => -> /=.
  by rewrite ltxx andbF.
move/asboolPn : Asup => -> /=.
by rewrite ltxx.
Abort.

Lemma complement_inner_lt_sup A :
  has_ubound A -> complement_inner A `<=` [set x | x < sup A].
Proof.
move=> hasubA x [/= + nAx].
rewrite in_itv/=.
move/andP => [_]; move/asboolP : (hasubA) => ->.
have [|/asboolPn ->//] := pselect (A (sup A)).
move=> /[dup]/asboolP -> AsupA/=.
rewrite le_eqVlt => /orP[|//]; move/eqP => xsupA.
by move: nAx; rewrite xsupA.
Qed.

(* *)
Let complement_inner_inf A :
  has_lbound A -> ~ (complement_inner A) (inf A).
Proof.
move=> haslbA.
rewrite /complement_inner/=.
apply/not_andP.
rewrite orpN => Ainf.
have gt_inf := inf_lb_strict haslbA Ainf.
rewrite in_itv/=.
case: ifP; move/asboolP => //= _.
move/asboolPn/negPf : Ainf => -> /=.
by rewrite ltxx.
Abort.

Lemma inf_lt_complement_inner A :
  has_lbound A -> complement_inner A `<=` [set x | inf A < x].
Proof.
move=> haslbA x [/= + nAx].
rewrite in_itv/=.
move/andP => [+ _]; move/asboolP : (haslbA) => ->.
have [|/asboolF -> //] := pselect (A (inf A)).
move=> /[dup]/asboolP -> AinfA/=.
rewrite le_eqVlt => /orP[|//]; move/eqP => xinfA.
by move: nAx; rewrite -xinfA.
Qed.

Lemma complement_innerEitvoo A :
  has_ubound A -> has_lbound A ->
  complement_inner A = `]inf A, sup A[ `&` ~` A.
Proof.
move/[dup]/complement_inner_lt_sup => ciAsup hasubA.
move/[dup]/inf_lt_complement_inner => ciAinf haslbA.
rewrite eqEsubset; split.
- move=> x ciA/=; split.
  + rewrite in_itv/=; apply/andP; split.
    * exact: ciAinf.
    * exact: ciAsup.
  + by move: ciA; rewrite /complement_inner/= => -[].
rewrite /complement_inner setDE; apply: setSI.
rewrite/Rhull.
move: hasubA haslbA => /asboolP -> /asboolP ->.
case: `[< A (inf A) >]; case: `[< A (sup A) >] => //=.
- exact: subset_itv_oo_cc.
- exact: subset_itv_oo_co.
- exact: subset_itv_oo_oc.
Qed.

Lemma complement_innerEitvyo A :
  has_ubound A -> ~ has_lbound A ->
  complement_inner A = `]-oo, sup A[ `&` ~` A.
Proof.
move/[dup]/complement_inner_lt_sup => ciAsup hasubA.
move=> hasNlbA.
rewrite /complement_inner.
rewrite /Rhull.
move/asboolP : (hasubA) => ->.
move/asboolF : (hasNlbA) => -> /=.
have [Asup|nAsup] := pselect (A (sup A)).
  move/asboolP : (Asup) => ->/=.
  rewrite -setUitv1// setDUl -[RHS]setU0; congr setU.
  rewrite setD_eq0.
  by rewrite sub1set inE.
by move/asboolF : nAsup => ->.
Qed.

Lemma complement_innerEitvoy A :
  ~ has_ubound A -> has_lbound A ->
  complement_inner A = `]inf A, +oo[ `&` ~` A.
Proof.
move=> hasNubA.
move/[dup]/inf_lt_complement_inner => ciAinf haslbA.
rewrite /complement_inner.
rewrite /Rhull.
move/asboolP : (haslbA) => ->.
move/asboolF : (hasNubA) => -> /=.
have [Ainf|nAinf] := pselect (A (inf A)).
  move/asboolP : (Ainf) => ->/=.
  rewrite -setU1itv// setDUl -[RHS]set0U; congr setU.
  rewrite setD_eq0.
  by rewrite sub1set inE.
by move/asboolF : nAinf => ->.
Qed.

Lemma complement_inner_unboundEitvoo A :
  A !=set0 -> ~ has_ubound A -> ~ has_lbound A ->
  complement_inner A = ~` A.
Proof.
move=> [x Ax].
move=> hasNubA hasNlbA.
rewrite -setTD; congr setD.
rewrite/Rhull.
move/asboolF : hasNlbA => ->.
move/asboolF : hasNubA => ->.
exact: interval_unbounded_setT.
Qed.

Let compact_open_complement A : compact A -> open (complement_inner A).
Proof.
move=> cpA.
have := compact_bounded cpA.
move=> -[bnd [_ bndA]].
rewrite complement_innerEitvoo; last 2 first.
- exists (bnd + 1) => x Ax.
  rewrite ler_normlW//.
  apply: bndA => //.
  by rewrite ltrDl.
- exists (- (bnd + 1)) => x Ax.
  rewrite lerNnormlW//.
  apply: bndA => //.
  by rewrite ltrDl.
apply: openI => //.
apply: closed_openC.
exact: (compact_closed _ cpA).
Qed.

Lemma closed_open_complement_inner A : closed A -> open (complement_inner A).
Proof.
move=> cA.
have [ubA|ubA] := pselect (has_ubound A).
- have [lbA|lbA] := pselect (has_lbound A).
  + rewrite complement_innerEitvoo//.
    by apply: openI => //; rewrite openC.
  + rewrite complement_innerEitvyo//.
    by apply: openI => //; rewrite openC.
- have [lbA|lbA] := pselect (has_lbound A).
  + rewrite complement_innerEitvoy//.
    by apply: openI => //; rewrite openC.
  + have [A0|/set0P/negP/negPn/eqP ->] := pselect (A !=set0).
      by rewrite complement_inner_unboundEitvoo// openC.
    by rewrite complement_inner_set0.
Qed.

End complement_inner.

(* NB: A is supposed to be a perfect set so that A is closed *)
Definition contiguous_intervals {R : realType} (A : set R) : (set R)^nat :=
  match pselect (closed A) with
  | left H => open_disjointI (closed_open_complement_inner H)
  | right _ => cst set0
  end.

Definition contiguous_intervals1 {R : realType} (A : set R) : (\bar R)^nat :=
  fun n => ereal_of_itv_bound (Rhull (contiguous_intervals A n)).1.

Definition contiguous_intervals2 {R : realType} (A : set R) : (\bar R)^nat :=
  fun n => ereal_of_itv_bound (Rhull (contiguous_intervals A n)).2.

Section contiguous_intervals_lemmas.
Context {R : realType}.
Implicit Type (A : set R).

Lemma open_contiguous_intervals (A : set R) (i : nat) :
  open (contiguous_intervals A i).
Proof.
rewrite /contiguous_intervals; case: pselect => cA//.
exact: open_disjointI_open.
Qed.

Lemma is_interval_contiguous_intervals (A : set R) (i : nat) :
  is_interval (contiguous_intervals A i).
Proof.
rewrite /contiguous_intervals; case: pselect => cA//.
exact: open_disjointI_is_interval.
Qed.

Lemma disjoint_contiguous_intervals (A : set R) :
  trivIset [set: nat] (contiguous_intervals A).
Proof.
rewrite /contiguous_intervals.
case: pselect => cA//.
  exact: open_disjointI_trivIset.
exact: trivIset_set0.
Qed.

Lemma bigcup_contiguous_intervals A :
  closed A -> complement_inner A = \bigcup_i (contiguous_intervals A) i.
Proof.
move=> cA.
rewrite /contiguous_intervals.
case: pselect => ? //.
by rewrite -open_disjointI_bigcup.
Qed.

(* for subspace of compact interval? *)
Lemma contiguous_intervals_subsetC (A : set R) (i : nat) :
  contiguous_intervals A i `<=` ~` A.
Proof.
rewrite /contiguous_intervals.
case: pselect => cA//=.
apply: (@subset_trans _ (complement_inner A)); last first.
  exact: complement_inner_complement.
rewrite [in X in _ `<=` X](open_disjointI_bigcup (closed_open_complement_inner cA)).
exact: bigcup_sup.
Qed.

Lemma contiguous_ooitv A :
  has_ubound A -> has_lbound A ->
  forall i, EFin @` (contiguous_intervals A i) =
   `]contiguous_intervals1 A i, contiguous_intervals2 A i[%classic.
Proof.
move=> [u Au] [l Al] i.
rewrite /contiguous_intervals1/contiguous_intervals2.
rewrite -{1}(@RhullK _ (contiguous_intervals A i)); last first.
  by rewrite inE; exact: is_interval_contiguous_intervals.
rewrite /Rhull.
rewrite 2?ifT/=.
Abort.

Lemma continuous_intervalS A i :
  contiguous_intervals A i `<=` complement_inner A.
Proof.
have [cA|cA] := pselect (closed A).
  by rewrite (bigcup_contiguous_intervals cA); exact: bigcup_sup.
(* NB: needs lemma here *)
by rewrite /contiguous_intervals; case: pselect.
Qed.

Lemma has_lbound_contiguous_intervals A :
  has_lbound A -> forall i, has_lbound (contiguous_intervals A i).
Proof.
move/inf_lt_complement_inner => lbA i; exists (inf A) => r.
by move/continuous_intervalS/lbA => /= /ltW.
Qed.

Lemma has_ubound_contiguous_intervals A :
  has_ubound A -> forall i, has_ubound (contiguous_intervals A i).
Proof.
move/complement_inner_lt_sup => lbA i; exists (sup A) => r.
by move/continuous_intervalS/lbA => /= /ltW.
Qed.

Lemma contiguous_intervals1_fin_num A : has_lbound A ->
 forall i, contiguous_intervals1 A i \is a fin_num.
Proof.
move=> + i.
move/has_lbound_contiguous_intervals => /(_ i) lbA.
rewrite /contiguous_intervals1 /Rhull; case: ifPn => //=.
by move/asboolP.
Qed.

Lemma contiguous_intervals2_fin_num A : has_ubound A ->
 forall i, contiguous_intervals2 A i \is a fin_num.
Proof.
move=> + i.
move/has_ubound_contiguous_intervals => /(_ i) ubA.
rewrite /contiguous_intervals2 /Rhull; case: ifPn => /=; case: ifPn => //.
  by move/asboolP.
by move/asboolP.
Qed.

End contiguous_intervals_lemmas.

Section lemma4.
Context {R : realType}.
Variables a b : R.
Hypothesis ab : a < b.
Local Notation mu := (@completed_lebesgue_measure R).
Local Open Scope ereal_scope.

Lemma interval_ooS (A : interval R) : A.1 <= A.2 -> `](fine A.1), (fine A.2)[ `<=` [set` A].
Proof.
move: A => [r s].
move: r => [[|]r|[|]]; move: s => [[|]s|[|]]//= rs x/=; rewrite ?in_itv//=.
- by move=> /andP[/ltW -> ->].
- by move=> /andP[/ltW -> /ltW ->].
- by move=> /andP[/ltW ->].
- by move=> /andP[-> /ltW ->].
- by move=> /andP[->].
- by move=> /andP[_ ->].
- by move=> /andP[_ /ltW ->].
- by move=> /andP[] /lt_trans /[apply]; rewrite ltxx.
- by move=> /andP[] /lt_trans /[apply]; rewrite ltxx.
Qed.

Lemma is_subset1_set1 (A : set R) : A !=set0 -> is_subset1 A -> A = [set xget point A].
Proof.
move=> A0 A1.
case: xgetP => /= [_ -> Aget|].
  apply/seteqP; split => [x Ax/=|x/= ->//].
  exact: A1.
by case: A0 => s As /(_ s).
Qed.

(* TODO: move near has_bound_not_subset1_inf_sup in absolute_continuity.v *)
Lemma has_bound_inf_sup (A : set R) : A !=set0 ->
  has_lbound A -> has_ubound A -> (inf A <= sup A)%R.
Proof.
move=> A0 lbA ubA.
have [|/has_bound_not_subset1_inf_sup] := pselect (is_subset1 A); last first.
  by move=> /(_ lbA ubA) /ltW.
move/is_subset1_set1 => /(_ A0) ->.
by rewrite inf1 sup1.
Qed.

Lemma Rull_fst_snd (A : set R) : (Rhull A).1 <= (Rhull A).2.
Proof.
have [->|A0] := eqVneq A set0; first by rewrite !Rhull0.
rewrite /Rhull; case: ifPn => /asboolP lA; case: ifPn => // /asboolP uA /=.
- by rewrite lee_fin has_bound_inf_sup//; exact/set0P.
- by rewrite leey.
- by rewrite leNye.
Qed.

Lemma trivIset_contiguous_intervals (P : set R) :
  let a_ := contiguous_intervals1 P : (\bar R) ^nat in
  let b_ := contiguous_intervals2 P : (\bar R) ^nat in
  trivIset [set: nat] (fun i : nat => `](fine (a_ i)), (fine (b_ i))[%classic).
Proof.
rewrite /= /contiguous_intervals1 /contiguous_intervals2.
apply/trivIsetP => i j _ _ ij.
have /trivIsetP/(_ i j Logic.I Logic.I ij) := @disjoint_contiguous_intervals _ P.
apply: subsetI_eq0. (* TODO: generalize this lemma to trivIset *)
- have /is_intervalP H := @is_interval_contiguous_intervals _ P i.
  rewrite [X in _ `<=` X]H.
  by apply: interval_ooS; exact: Rull_fst_snd.
- have /is_intervalP H := @is_interval_contiguous_intervals _ P j.
  rewrite [X in _ `<=` X]H.
  by apply: interval_ooS; exact: Rull_fst_snd.
Qed.

Lemma lemma4 (f : R -> R) (P : set R) :
  is_interval (f @` `[a, b]) ->
  perfect_set P ->
  a = inf P -> b = sup P ->
  let a_ := contiguous_intervals1 P in
  let b_ := contiguous_intervals2 P in
  `|f b - f a|%:E <= mu (f @` `[a, b])
     <= (mu^*)%mu (f @` P) +
        \sum_(0 <= i <oo) oscillation f `[fine (a_ i), fine (b_ i)]%classic.
Proof.
move=> fab perfectP aP bP/=.
set a_ := contiguous_intervals1 P.
set b_ := contiguous_intervals2 P.
have H1 : f @` `[a, b] = (f @` P) `|` \bigcup_i f @` `]fine (a_ i), fine (b_ i)[.
  rewrite -image_bigcup_disjoint; last first.
    exact: trivIset_contiguous_intervals.
  rewrite -image_setU.
  congr (f @` _).
  admit.
apply/andP; split.
  admit.
rewrite H1.
apply: (@le_trans _ _ (mu [set f x | x in P] +
         mu (\bigcup_i [set f x | x in `]fine (a_ i), fine (b_ i)[]))).
  admit.
rewrite measurable_mu_extE/=; last first.
  admit.
rewrite leeD2l//.
rewrite measure_semi_bigcup//=; last 3 first.
  admit.
  admit.
  admit.
apply: lee_nneseries => // n _.
Abort.
Local Close Scope ereal_scope.

Let ex_perfect_set (cmf : cumulative R R) (cZ : set R) :
  let f := cmf in
  cZ `<=` `[a, b] ->
  {within `[a, b], continuous f} ->
  {in `[a, b], {homo f : x y / (x <= y)}} ->
  bounded_variation a b f ->
  exists n, exists I : nat -> R * R,
  (forall i, trivIset setT (fun i => `[(I i).1, (I i).2]%classic) /\
    `](I i).1, (I i).2[ `<=` cZ) /\
     (\sum_(0 <= i < n) `|f (I i).2 - f (I i).1|)%:E
     = completed_lebesgue_stieltjes_measure f cZ.
Proof.
Abort.

End lemma4.
