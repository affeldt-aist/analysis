(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import boot order algebra interval_inference.
From mathcomp Require Import generic_quotient finmap.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions cardinality fsbigop.
From mathcomp Require Import filter reals.
From mathcomp Require Import topology.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

From Stdlib Require Import Eqdep_dec.

Section Evaluators.
Context {X : choiceType}.
Context {K : forall x:X, ptopologicalType}.
Definition evaluator_dep (x : X) (f : prod_topology K) := f x.

Lemma evaluator_depE x f : evaluator_dep x f = f x.
Proof. by []. Qed.

Definition xval {x : X} (y : K x) i : K i :=
  match (pselect `[< x = i >]) return K i with
  | left r => ltac:(move/asboolP:r => <-; exact y)
  | right _ => point
  end.

Lemma evaluator_dep_continuous x : continuous (evaluator_dep x).
Proof.
move=> f.
have /cvg_sup/(_ x)/cvg_image : (f --> f) by apply: cvg_id.
set P := ( x in (x -> _) -> _).
have P' : P.
  rewrite /P eqEsubset; split => y /=.
  - by [].
  - move=> _; exists (xval y) => //.
    rewrite /xval; case (pselect _).
    + move/asboolP => Q.
      rewrite -Eqdep_dec.eq_rect_eq_dec => //.
      move=> p q.
      exact: pselect (p = q).
    + by move => Q; contradict Q; exact/asboolP.
move/(_ P') => Ff; apply: cvg_trans; last exact: Ff.
rewrite /= /evaluator_dep=> Q /=; rewrite {1}/nbhs /=.
move=> [W nbdW <-]; rewrite /nbhs /=.
by (apply: filterS; last exact: nbdW) => g Wg /=; exists g.
Qed.

Lemma hausdorff_pointwise :
  (forall x, hausdorff_space (K x)) -> hausdorff_space (@prod_topology X K).
Proof.
move=> hsdfV => p q /= clstr.
apply: functional_extensionality_dep => x; apply: hsdfV.
move: clstr; rewrite ?cluster_cvgE /= => [[G PG [GtoQ psubG]]].
exists (evaluator_dep x @ G); first exact: fmap_proper_filter; split.
- rewrite -(evaluator_depE x).
  apply: cvg_trans; last apply: (@evaluator_dep_continuous x q).
  by apply: cvg_app; exact GtoQ.
- move/(cvg_app (evaluator_dep x)):psubG => xpsubxG.
  apply: cvg_trans; first exact: xpsubxG.
  by apply: evaluator_dep_continuous.
Qed.

End Evaluators.

Lemma nbhs_comp {X Y : topologicalType} (f : X -> Y) U x :
  {in f @^-1` U, continuous f} ->
  nbhs (f x) U -> nbhs x (f @^-1` U).
Proof.
rewrite ?nbhsE /= => ctsF [A [openA nbhsA AsubU]].
have oAInv: (open (f @^-1` A)).
  apply: open_comp => //.
  move=> u ufA; apply: ctsF; rewrite in_setE; apply: AsubU.
  by rewrite in_setE /= in ufA.
exists (f @^-1` A); rewrite ?open_nbhsE; repeat split => //.
- rewrite openE //= in oAInv; exact: (oAInv).
- by move=> y /=; apply: AsubU.
Qed.

Lemma ptws_cvg_family_singleton {U : topologicalType} {V : uniformType} F (f : U -> V):
  Filter F ->
  {ptws, F --> f} = {family (@singletons U), F --> f}.
Proof.
move=> FF; rewrite propeqE; split.
- move/cvg_sup => + ; move=> + ; move=> Fx.
  apply/fam_cvgP => A [x _ <-{A}]; move: (Fx x) => Ff.
  move=> P /=.
  move/uniform_nbhs => -[E [entE /filterS]]; apply.
  near=> q => t ->; near: q; apply: Ff => /=.
  move: (nbhs_entourage (f x) entE).
  rewrite nbhsE /= => [[B [onbhsB BfX BsubE]]].
  exists [set q | B (q x)]; split => //=.
  + by exists B => //.
  + move=> q /= Bq.
    exact/set_mem/BsubE.
- move/fam_cvgP => Ffam; apply/cvg_sup => x; move: Ffam.
  move=> /(_ [set x]).
  have : singletons [set x] by exists x.
  move=> /[swap] /[apply].
  move=> Ef'.
  have Ef E : entourage E ->
      \forall g \near F, forall y, [set x] y -> E (f y, g y).
    move=> entE; apply: Ef'; rewrite uniform_nbhs; exists E; split => //.
    by move=> P /=.
  move=> /= P [P' [[A oA <- /=]]] Afx AsubP.
  rewrite openE /interior in oA; case/nbhsP: (oA (f x) (Afx))=> E entE EsubA.
  move:(Ef _ entE) => EF.
  near=> g; apply: AsubP; apply: EsubA.
  apply/mem_set.
  by apply (near EF).
Unshelve. all: end_near. Qed.

Lemma ptws_cvg_compact_family {X : topologicalType} {Y : uniformType} F (f : X -> Y):
  ProperFilter F -> {family compact, F --> f} -> {ptws, F --> f}.
Proof.
move=> PF; rewrite ptws_cvg_family_singleton; apply: family_cvg_subset.
move=> A [x _ <-{A}].
exact: compact_set1.
Qed.

Section PtwsPrecompact.
Context {X : topologicalType} {Y : puniformType}.

Definition pointwisePrecompact (W : set (X -> Y)):=
  forall x, precompact [set (f x) | f in W].

Lemma pointwisePrecompact_precompact (W : set {ptws X -> Y}) :
  hausdorff_space Y ->
  pointwisePrecompact W -> precompact W.
Proof.
move=> hsdf ptwsPreW; set K := fun x => closure [set f x | f in W].
set R := [set f : {ptws X -> Y} | forall x : X, K x (f x)].
have C : compact R.
  apply: tychonoff => x.
  rewrite -precompactE.
  exact: ptwsPreW.
rewrite precompactE.
apply: subclosed_compact.
- exact: closed_closure.
- exact: C.
- set L := (x in _`<=` x).
  have WsubR : W `<=` L.
    rewrite /R/K => f /= Wf x; rewrite /K.
    apply: subset_closure => /=.
    by exists f.
  have cR : closed R.
    apply: compact_closed => //.
    exact: hausdorff_pointwise.
  by rewrite closureE /= => q /=; apply; split.
Qed.

Lemma pointwisePrecomact_subset (W V : set (X -> Y)):
  W `<=` V -> pointwisePrecompact V -> pointwisePrecompact W.
Proof.
move=> WsubV + x => /(_ x) pcptV.
apply: precompact_subset; last exact: pcptV.
exact: image_subset.
Qed.

End PtwsPrecompact.

Definition locally_compact (X : topologicalType) :=
  forall x : X, exists2 U, compact U & nbhs x U.

HB.instance Definition _ {X : topologicalType} {Y : puniformType}
    (fam : set X -> Prop) :=
  Pointed.on {family fam, X -> Y}. (* NB: to be able to use compact_cover *)

Section Arzela.
Context {X : ptopologicalType} {Y : puniformType} {hsdf : hausdorff_space Y}.

Lemma nbhs_entourage_ptws (f : {ptws X -> Y}) x B :
  entourage B -> nbhs f (fun g : {ptws X -> Y} => B (g x, f x)).
Proof.
move=> entB.
apply: nbhs_comp => //=.
- move => t ?.
  rewrite /continuous_at.
  suff: (evaluator_dep x t0, f x) @[t0 --> t] --> (t x, f x) by [].
  apply: (@cvg_pair _ _ _ (nbhs t)) => //=.
  exact: (@evaluator_dep_continuous _ _ x).
- set C := (split_ent B); have entC: entourage C by exact: entourage_split_ent.
  have entCinv: entourage (C^-1)%relation by exact: entourage_inv.
  exists (xsection ((C^-1)%relation) (f x), xsection C (f x)) => //=.
  move=> v [/=X1 X2]; rewrite [v]surjective_pairing.
  apply: entourage_split => //.
    move: X1.
    rewrite /xsection/= => /set_mem.
    exact.
  move: X2.
  rewrite /xsection/= => /set_mem.
  exact.
Qed.

Lemma family_cvg_nbhs {fam} (f : {family fam, X -> Y}) B E :
  entourage E -> fam B ->
  nbhs f [set q | forall x, B x -> E (f x, q x)].
Proof.
move=> entE famB.
have /(_ _ _ famB) := (@fam_cvgP X Y fam (nbhs f) f _).1 cvg_id.
apply; rewrite uniform_nbhs; exists E.
by split.
Qed.

Lemma ptws_compact_cvg (F : set_system {ptws X -> Y}) (f : {ptws X -> Y}) :
  ProperFilter F ->
  (\forall W \near powerset_filter_from F, equicontinuous W id) ->
  {ptws, F --> f} = {family compact, F --> f}.
Proof.
move=> PF /near_powerset_filter_fromP[].
  exact: equicontinuous_subset_id.
move=> W; wlog Wf : f W / W f.
  move=> + FW /equicontinuous_closure ectsCW => /(_ _ _ _ _ ectsCW) H.
  rewrite propeqE; split; last exact: ptws_cvg_compact_family.
  move=> Ftof; rewrite -H//.
    rewrite closureEcvg; exists F => //; split => //.
    move=> /= A AA.
    apply: (filterS _ FW).
    exact: AA.
  apply: (filterS _ FW).
  exact: subset_closure.
move=> FW ectsW.
rewrite propeqE; split; last exact: ptws_cvg_compact_family.
move=> ptwsF; apply/fam_cvgP => A cptA.
move=> P /= /uniform_nbhs => -[E1 [entE1 /filterS]]; apply.
pose E2 := split_ent E1.
have entE2: entourage E2 by exact: entourage_split_ent.
pose E3 := split_ent E2.
have entE3: entourage E3 by exact: entourage_split_ent.
pose E4 := E3 `&` (E3 ^-1)%relation.
have entE4 : entourage E4 by apply: filterI => //; exact: entourage_inv.
rewrite compact_cover cover_compactE /= in cptA.
have mkR : forall x, exists R, open_nbhs x R /\
        (forall (y : X) (q : X -> Y), W q -> R y -> E4 (q x, q y)).
  move=> x.
  have := ectsW x E4 entE4.
  rewrite /prop_near1.
  rewrite nbhsE /= => -[R [onbhsR RsubR']].
  move=> RE'.
  exists R; split => // y q Wq Ry /=.
  exact: RE'.
pose Rnbhd (x : X) := A `&` projT1 (cid (mkR x)).
move/(_ X A Rnbhd): cptA.
case.
- rewrite /open_fam_of; exists (fun x => projT1 (cid (mkR x))) => //.
  move=> x Ax; rewrite /Rnbhd /=; set R := cid _; case R => /=.
  by move=> R'; rewrite open_nbhsE => -[[]].
- rewrite /Rnbhd.
  move=> x Ax /=; exists x => //; split => //.
  set R := cid _; case R => /= R' [? ?]; apply nbhs_singleton.
  exact: open_nbhs_nbhs.
move=> D' D'subA AsubRnbhd.
have Fx0 : F (\bigcap_(x0 in [set x0 | x0 \in D']) [set q | E4 (f x0, q x0)]).
  apply: filter_bigI => x0 x0D'.
  move/cvg_sup/(_ x0) : ptwsF.
  apply => /=.
  have := nbhs_entourage (f x0) entE4.
  rewrite nbhsE /= => -[B [onbhsB BsubE4]].
  exists [set q | B (q x0)]; split => //=.
  - by exists B.
  - move=> q' /= Bq'.
    exact/set_mem/q.
near=> q => t At; have Wq : W q by exact: (near FW).
case /(_ t At) : AsubRnbhd => x0 /= xD' Rx0t.
have E4q : E4(q x0, q t).
  move: Rx0t; rewrite /Rnbhd /= => -[_].
  case: cid => /=.
  by move=> R; rewrite open_nbhsE => -[[oR nbhsR] /(_ t q)] + Rt; exact.
have E4f : E4 (f t, f x0).
  move: Rx0t; rewrite /Rnbhd /= => -[_].
  case: cid => /=.
  move=> R; rewrite open_nbhsE /E4 => -[[oR nbhsR] /(_ t f)] + Rt.
  move/(_ Wf Rt).
  by move=> E4f; split; apply E4f.
have E4subE3 : E4 `<=` E3 by rewrite /E4 => ? [].
do 2 (apply: entourage_split; first by []); apply: E4subE3; first exact: E4f; last exact: E4q.
  by exact: entourage_refl.
have := near Fx0 q.
move/(_ _); exact.
Unshelve. all: end_near. Qed.

Lemma ascoli_forward (W : set (X -> Y)) :
  pointwisePrecompact W ->
  equicontinuous W id ->
  @precompact {family compact, X -> Y} W.
Proof.
move=> /pointwisePrecompact_precompact + ectsW.
rewrite !precompactE compact_ultra compact_ultra.
have -> : @closure {family compact, X -> Y} W =
          @closure {ptws X -> Y} W.
  rewrite !closureEcvg predeqE => g /=.
  split; move=> [F PF [Fg FW]]; exists F => //; split => //.
  - rewrite ptws_compact_cvg => //; apply/near_powerset_filter_fromP.
      exact: equicontinuous_subset_id.
    by exists W => //; exact: FW.
  - rewrite -ptws_compact_cvg => //; apply/near_powerset_filter_fromP.
      exact: equicontinuous_subset_id.
    by exists W => //; exact: FW.
move/(_ hsdf).
move=> /= + F UF FcW => /(_ F UF FcW); case=> p [cWp Fp]; exists p.
split=> //=.
rewrite -ptws_compact_cvg => //; apply/near_powerset_filter_fromP.
  exact: equicontinuous_subset_id.
exists (@closure {ptws X -> Y} W) => //.
exact: equicontinuous_closure.
Qed.

Lemma compact_equicontinuous fam (W : set (X -> Y)) :
  (forall x : X, exists2 U, fam U & nbhs x U) ->
  (forall f, W f -> continuous f) ->
  @precompact {family fam, X -> Y} W ->
  equicontinuous W id.
Proof.
move=> locCptX ctsW cptW => x E1 entE1.
case/(_ x) : locCptX => B cptB nbhsB.
pose E2 := split_ent E1.
have entE2: entourage E2 by exact: entourage_split_ent.
pose E3 := split_ent E2.
have entE3: entourage E3 by exact: entourage_split_ent.
pose E4 := E3 `&` (E3 ^-1)%relation.
have entE4 : entourage E4 by apply: filterI => //; exact: entourage_inv.
pose E5 := split_ent E4.
have entE5: entourage E5 by exact: entourage_split_ent.
pose E6 := E5 `&` (E5 ^-1)%relation.
have entE6 : entourage E6 by apply: filterI => //; exact: entourage_inv.
pose E7 := split_ent E6.
have entE7: entourage E7 by exact: entourage_split_ent.
have E3subE2 : E3 `<=` E2.
  move=> [? ?] E3ab; apply: entourage_split => //.
    exact: E3ab.
  exact: entourage_refl.
have E4subE3 : E4 `<=` E3 by move =>? [] //.
have E4invsubE3 : (E4 ^-1)%relation `<=` E3 by move=> [p q []/=].
have E5subE4 : E5 `<=` E4.
  move=> [? ?] E5ab.
  apply: entourage_split => //.
    exact: E5ab.
  exact: entourage_refl.
have E6subE5 : E6 `<=` E5 by move=> ? [].
have E7subE6 : E7 `<=` E6.
  move=> [? ?] E7ab.
  apply: entourage_split => //.
    exact: E7ab.
  exact: entourage_refl.
pose cptTop := ({family fam, X -> Y}).
pose R1 := fun f => [set h : cptTop | forall y, B y -> E4 (f y, h y)]°.
pose R := fun f => @closure cptTop W `&` R1 f.
have : cover_compact (@closure {family fam, X -> Y} W).
  move: cptW.
  by rewrite precompactE compact_cover.
rewrite cover_compactE/= => {cptW}.
move/(_ {family fam, X -> Y} (@closure cptTop W) R).
case.
- (* open_fam_of (@closure {family fam, X -> Y} W) (@closure {family fam, X -> Y} W) R *)
  exists R1.
  + by move=> f Wf /=; exact: open_interior.
  + by [].
- (* (@closure {family fam, X -> Y} W) `<=` cover (@closure {family fam, X -> Y} W) R *)
  move=> h Wh; exists h => //; rewrite /R/ R1; split => //.
  exact: family_cvg_nbhs.
move=> D DsubW Dcovers.
set U := \bigcap_(g in [set i | i \in D]) [set y | B y -> E4 (g x, g y)].
apply: (@filterS _ _ _ (U `&` B)).
  move=> y [Uy By] f Wf.
  case: (Dcovers f); first exact: subset_closure.
  rewrite /R /R1 => f0 f0D [_ /interior_subset /= E4f].
  apply: (entourage_split (f0 y)) => //; last first.
    by apply E3subE2, E4subE3, E4f.
  apply: (entourage_split (f0 x)) => //.
    by apply E4invsubE3, E4f, nbhs_singleton.
  apply E4subE3 => //.
  by apply: Uy.
apply: filterI => //; apply: filter_bigI => g Dg.
have : (@closure cptTop W) g by rewrite -inE; apply: DsubW.
move=> /(_ [set h | (forall x, B x -> (split_ent E5) (g x, h x)) /\
                    (forall x, B x -> (split_ent E5) (h x, g x))]).
case.
 (* nbhs g
   [set h | (forall x0 : X, B x0 -> split_ent E5 (g x0, h x0)) /\
            (forall x0 : X, B x0 -> split_ent E5 (h x0, g x0))] *)
  apply: filterI; first exact: family_cvg_nbhs.
  by apply: (@family_cvg_nbhs _ g B ((split_ent E5)^-1)%relation).
move=> g' [Wg' [P Q]].
move/cvg_entourageP: (ctsW _ Wg' x) => /(_ (split_ent (split_ent E4))).
have : entourage (split_ent (split_ent E4)) by exact: entourage_split_ent.
move=> /[swap] /[apply].
near_simpl; move=> G'.
near=> y => By.
apply: (entourage_split (g' y)) => //.
  apply: (entourage_split (g' x)) => //.
    by apply: P; exact: nbhs_singleton.
  exact: (near G' y).
by apply: split_ent_subset => //; exact: Q.
Unshelve. all: end_near. Qed.

Lemma compact_pointwisePrecompact (W : set (X -> Y)):
  @compact {family compact, X -> Y} W ->
  pointwisePrecompact W.
Proof.
move=> cptFamW x.
have: @compact {ptws X -> Y} W.
  rewrite compact_ultra /= => F UF FW.
  move: cptFamW; rewrite compact_ultra=> /(_ F UF FW) [h [Wh Fh]].
  exists h; split => //.
  by move=> /= Q Fq; apply: ptws_cvg_compact_family; first exact: Fh.
move/(continuous_compact (f := evaluator_dep x)).
set C := (x in compact x).
set H := (X in (X -> _) -> _).
have : H.
  rewrite /H.
  apply: continuous_subspaceT => //.
  exact: evaluator_dep_continuous.
move=> /[swap] /[apply].
move=> cptC; rewrite precompactE.
rewrite -(_ : [set f x | f in W] = closure [set f x | f in W] ) //.
by apply closure_id; apply: compact_closed.
Qed.

Lemma arzela_ascoli (W : set ({family compact, X -> Y})) :
  locally_compact X ->
  (equicontinuous W id /\ pointwisePrecompact W) <->
  (@precompact {family compact, X -> Y} W /\
    (forall f, W f -> continuous f)).
Proof.
move=> lcptX; split.
- case => ectsW ?; split; first apply: ascoli_forward => //.
  by move=> ? ?; apply: (equicontinuous_continuous ectsW).
- case=> cptWcl ctsW; split.
  + exact: compact_equicontinuous.
  + apply: (@pointwisePrecomact_subset _ _ _ (@closure {family compact, X -> Y} W)).
    - exact: (@subset_closure _ W).
    - apply: compact_pointwisePrecompact.
      by rewrite -precompactE.
Qed.

End Arzela.
