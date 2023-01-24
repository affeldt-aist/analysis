# Changelog (unreleased)

## [Unreleased]

### Added

- in `contructive_ereal.v`:
  + lemmas `ereal_blatticeMixin`, `ereal_tblatticeMixin`
  + canonicals `ereal_blatticeType`, `ereal_tblatticeType`
- in `classical_sets.v`:
  + canonical `unit_pointedType`
- in `measure.v`:
  + definition `finite_measure`
  + mixin `isProbability`, structure `Probability`, type `probability`
  + lemma `probability_le1`
  + definition `discrete_measurable_unit`
  + structures `sigma_finite_additive_measure` and `sigma_finite_measure`

- in file `topology.v`,
  + new definition `perfect_set`.
  + new lemmas `perfectTP`, `perfect_prod`, and `perfect_diagonal`.

- in `constructive_ereal.v`:
  + lemma `oppe_inj`

- in `mathcomp_extra.v`:
  + lemma `add_onemK`
  + function `swap`
- in `classical_sets.v`:
  + lemmas `setT0`, `set_unit`, `set_bool`
  + lemmas `xsection_preimage_snd`, `ysection_preimage_fst`
- in `exp.v`:
  + lemma `expR_ge0`
- in `measure.v`
  + lemmas `measurable_curry`, `measurable_fun_fst`, `measurable_fun_snd`,
    `measurable_fun_swap`, `measurable_fun_pair`, `measurable_fun_if_pair`
  + lemmas `dirac0`, `diracT`
  + lemma `finite_measure_sigma_finite`
- in `lebesgue_measure.v`:
  + lemma `measurable_fun_opp`
- in `lebesgue_integral.v`
  + lemmas `integral0_eq`, `fubini_tonelli`
  + product measures now take `{measure _ -> _}` arguments and their
    theory quantifies over a `{sigma_finite_measure _ -> _}`.

- in `classical_sets.v`:
  + lemma `trivIset_mkcond`
- in `numfun.v`:
  + lemmas `xsection_indic`, `ysection_indic`
- in `classical_sets.v`:
  + lemmas `xsectionI`, `ysectionI`
- in `lebesgue_integral.v`:
  + notations `\x`, `\x^` for `product_measure1` and `product_measure2`

- file `probability.v`:
  + mixin `isConvn`, structure `Convn`, notation `convn`
  + lemmas `probability_fin_num`, `probability_integrable_cst`,
  + definition `mexp`, instance of `isMeasurableFun`
  + definition `subr`, instance of `isMeasurableFun`
  + definition `mabs`, instance of `isMeasurableFun`
  + `\*` instance of `isMeasurableFun`
  + `\o` instance of `isMeasurableFun`
  + definition `random_variable`, notation `{RV _ >-> _}`
  + lemmas `notin_range_probability`, `probability_range`
  + definition `comp_RV`, notation ``` `o ````,
    definition `exp_RV`, notation ``` `^+ ```,
    definition `add_RV`, notation ``` `+ ```,
    definition `sub_RV`, notation ``` `- ```,
    definition `mul_RV`, notation ``` `* ```,
    definition `scale_RV`, notation ``` `\o* ```
  + lemma `mul_cst`
  + definition `expectation`, notation `'E`
  + lemmas `expectation_cst`, `expectation_indic`, `integrable_expectation`,
    `expectationM`, `expectation_ge0`, `expectation_le`, `expectationD`,
    `expectationB`
  + definition `Lspace`, notation `.-Lspace`
  + lemmas `Lspace1`, `Lspace2`
  + definition `variance`, `'V`
  + lemma `varianceE`
  + definition `distribution`, instance of `isProbability`
  + lemmas `integral_distribution`, `markov`, `chebyshev`,
  + mixin `isDiscreteRV`, structure `DiscreteRV`, type `discrete_random_variable`,
    notation `{dRV _ >-> _}`
  + definitions `dRV_dom_enum`, `dRV_dom`, `dRV_enum`, `enum_prob`
  + lemmas `distribution_dRV_enum`, `distribution_dRV`, `convn_enum_prob`,
    `probability_distribution`, `dRV_expectation`
  + definion `pmf`, lemma `expectation_pmf`

### Changed

### Renamed

### Generalized

### Deprecated

### Removed

### Infrastructure

### Misc
