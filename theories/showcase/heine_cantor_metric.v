From HB Require Import structures.
From mathcomp Require Import boot algebra finmap all_classical.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import topology metric_structure.

(**md Heine-Cantor using metric spaces *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope relation_scope.

From mathcomp Require Import order.
From mathcomp Require Import metric_structure.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section metric_numDomainType.
Context {R : numDomainType} (T : metricType R).

Let dist := @mdist R T.

Lemma ball_open (x : T) (r : R) : open (ball x r).
Proof.
rewrite openE => y; rewrite ballEmdist /interior/= => xyr.
apply/nbhs_ballP.
have [[e /andP[e0 erxy]]|abs] := pselect (exists e, 0 < e < r - mdist x y).
- exists e => // z yez/=.
  have xrey : ball x (r - e) y by rewrite ballEmdist/= ltrBrDl -ltrBrDr.
  have /= := ball_triangle xrey yez.
  by rewrite subrK// ballEmdist.
- exists (r - mdist x y) => /=.
    by rewrite subr_gt0.
  move=> z; rewrite ballEmdist /= => yz.
  have := mdist_ge0 y z; rewrite le_eqVlt => /predU1P[|d0].
    by move/esym/mdist_positivity => <-.
  absurd: abs => /=.
  by exists (mdist y z); rewrite d0 yz.
Qed.

End metric_numDomainType.

Section MetricHeineCantor.
Context {R : realFieldType} {X Y : pmetricType R (* needed by compact_cover *)}.

Let continuous_on (A : set X) (f : X -> Y) :=
  {in A, forall a e, 0 < e ->
  exists2 r, 0 < r &
    {in A, forall x, mdist a x < r -> mdist (f a) (f x) < e} }.

Let within_continuous_on (A : set X) (f : X -> Y) :
  {within A, continuous f} -> continuous_on A f.
Proof.
move=> cf a Aa /= e e0.
have : within A (nbhs a) (f @^-1` ball (f a) e).
  rewrite nbhs_subspace_in//; first exact/set_mem.
  exact: (cvg_ball (cf a)) e0.
move=> /nbhs_ballP[r /= r0 Hr].
exists r => // x Ax arx.
have /Hr/(_ (set_mem Ax)) : ball a r x by rewrite ballEmdist.
by rewrite ballEmdist.
Qed.

Section heine_cantor_metric_compact_cover.

Lemma heine_cantor_metric_rudin (A : set X) (f : X -> Y) :
  compact A -> {within A, continuous f} ->
  forall e : R, 0 < e ->
  exists2 d : R, 0 < d &
    {in A &, forall x y, mdist x y < d -> mdist (f x) (f y) < e}.
Proof.
move=> cA cf e e0.
have [A0|/set0P[a0 /mem_set Aa0]] := eqVneq A set0.
  by exists 1 => // x x0; rewrite A0 inE.
have e20 : 0 < e / 2 by rewrite divr_gt0.
have /choice[r hr] : forall x, exists r, x \in A ->
    0 < r /\ {in A, forall x0, mdist x x0 < r -> mdist (f x) (f x0) < e / 2}.
  move=> a; have [Aa|Aa] := boolP (a \in A).
  - have [ra ra0 hra] := within_continuous_on cf Aa e20.
    by exists ra => _; split.
  - by exists 1.
have r20 a : a \in A -> 0 < r a / 2 by move=> Aa; rewrite divr_gt0//; apply hr.
have [D DA coverD] : finite_subset_cover A (fun a => ball a (r a / 2)) A.
  move: cA; rewrite compact_cover; apply.
    by move=> a Aa; exact: ball_open.
  move=> x Ax; exists x => //.
  by apply: ballxx; rewrite r20//; exact/mem_set.
pose d : R := \big[Num.min/(r a0 / 2)]_(i <- D) (r i / 2).
have d0 : 0 < d.
  by rewrite /d big_seq lt_bigmin ?r20// => i iD; apply: r20; exact: DA.
exists d => // x y Ax Ay hxy.
have [m /= mD] := coverD x (set_mem Ax).
have drm : d <= r m / 2 by exact: ge_bigmin_seq.
have Am : m \in A by apply/DA.
move/hr : (Am) => -[_ hfm].
rewrite ballEmdist /= => hbx.
rewrite (le_lt_trans (metric_triangle (f x) (f m) (f y)))//.
rewrite metric_sym [e]splitr ltrD// hfm//.
- by rewrite [r m]splitr (lt_le_trans hbx)// lerDl ltW// r20.
- rewrite (le_lt_trans (metric_triangle m x y))//.
  by rewrite [r m]splitr ltrD// (lt_le_trans hxy).
Qed.

End heine_cantor_metric_compact_cover.

Section heine_cantor_metric_near_covering.

Let munif_cont_at (A : set X) (f : X -> Y) (e d : R) (x0 : X) := A x0 ->
  forall x1, A x1 -> mdist x0 x1 < d -> mdist (f x0) (f x1) < e.

Let munif_cont_atP (A : set X) (f : X -> Y) (e : R) :
  {within A, continuous f} -> 0 < e ->
  forall a, A a ->
  \forall x' \near a & d \near (0 : R)^'+, munif_cont_at A f e d x'.
Proof.
move=> cf e0 a Aa.
have e20 : 0 < e / 2 by rewrite divr_gt0.
have [/= r r0 hr] := within_continuous_on cf (mem_set Aa) e20.
have r20 : 0 < r / 2 by rewrite divr_gt0.
near=> x0 d => /= Ax0 x1 Ax1 x0x1.
have : ball a (r / 2) x0 by near: x0; exact: nbhsx_ballx.
rewrite ballEmdist /= => ax0.
have dr : d < r / 2 by near: d; exact: nbhs_right_lt.
rewrite (le_lt_trans (metric_triangle (f x0) (f a) (f x1)))//.
rewrite metric_sym [e]splitr ltrD// hr//; [exact/mem_set| |exact/mem_set|].
  by rewrite [r]splitr (lt_le_trans ax0)// lerDl ?ltW.
rewrite (le_lt_trans (metric_triangle a x0 x1))//.
by rewrite [r]splitr ltrD// ?az (lt_trans x0x1 dr).
Unshelve. all: end_near. Qed.

Lemma heine_cantor_metric_near_covering (A : set X) (f : X -> Y) :
  compact A -> {within A, continuous f} ->
  forall e, 0 < e ->
  exists2 d : R, 0 < d &
    {in A &, forall x y, mdist x y < d -> mdist (f x) (f y) < e}.
Proof.
move=> cA cf e e0.
have A_unif_cont_at : \forall r \near (0 : R)^'+, A `<=` munif_cont_at A f e r.
  have := (compact_near_coveringP A).1 cA.
  move/(_ _ (0 : R)^'+ (munif_cont_at A f e)).
  by apply => a Aa; exact/munif_cont_atP.
near (0 : R)^'+ => d.
exists d; first by near: d; exact: nbhs_right_gt.
move=> x0 x1 Ax0 Ax1 x0x1.
have : A `<=` munif_cont_at A f e d by near: d; exact: A_unif_cont_at.
by move/(_ _ (set_mem Ax0)); apply => //; exact/set_mem.
Unshelve. all: end_near. Qed.

End heine_cantor_metric_near_covering.

Lemma heine_cantor (A : set X) (f : X -> Y) :
  compact A -> {within A, continuous f} ->
  @unif_continuous (subspace A) Y f.
Proof.
move=> cA cf E entE.
have [e /= e0 sE] : entourage_ (@ball R Y) E by rewrite entourage_ballE.
have [d d0 hd] := heine_cantor_metric_near_covering cA cf e0.
rewrite -[nbhs _ E]/(subspace_ent A [set xy : subspace A * subspace A | E (f xy.1, f xy.2)]).
rewrite /subspace_ent /filter_from /=.
exists [set xy : X * X | ball xy.1 d xy.2].
  by rewrite -entourage_ballE; exists d.
move=> [x y] /= [-> | [Ax [Ay dxy]]].
- by apply: entourage_refl; exact: entE.
- apply: sE; rewrite /= ballEmdist /=.
  apply: hd => //; [exact/mem_set..|].
  by move: dxy; rewrite ballEmdist.
Qed.

End MetricHeineCantor.
