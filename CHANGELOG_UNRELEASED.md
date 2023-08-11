# Changelog (unreleased)

## [Unreleased]

### Added

- in `kernel.v`:
  + `kseries` is now an instance of `Kernel_isSFinite_subdef`
- in `classical_sets.v`:
  + lemma `setU_id2r`
- in `lebesgue_measure.v`:
  + lemma `compact_measurable`

- in `measure.v`:
  + lemmas `outer_measure_subadditive`, `outer_measureU2`

- in `lebesgue_measure.v`:
  + declare `lebesgue_measure` as a `SigmaFinite` instance
  + lemma `lebesgue_regularity_inner_sup`
- in `convex.v`:
  + lemmas `conv_gt0`, `convRE`

- in `exp.v`:
  + lemmas `concave_ln`, `conjugate_powR`


- in `lebesgue_measure.v`:
  + lemma `measurable_mulrr`

- in `constructive_ereal.v`:
  + lemma `eqe_pdivr_mull`

- in `lebesgue_integral.v`:
  + definition `Lnorm`, notations `'N[mu]_p[f]`, `` `|| f ||_p ``
  + lemmas `Lnorm1`, `Lnorm_ge0`, `eq_Lnorm`, `Lnorm_eq0_eq0`
  + lemma `hoelder`

### Changed

- `mnormalize` moved from `kernel.v` to `measure.v` and generalized
- in `constructive_ereal.v`:
  + `lee_adde` renamed to `lee_addgt0Pr` and turned into a reflect
  + `lee_dadde` renamed to `lee_daddgt0Pr` and turned into a reflect

### Renamed

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
