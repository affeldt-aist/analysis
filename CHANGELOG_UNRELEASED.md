# Changelog (unreleased)

## [Unreleased]

### Added

- in `constructive_ereal.v`:
  + lemmas `gte_addl`, `gte_addr`
  + lemmas `gte_daddl`, `gte_daddr`
  + lemma `lte_spadder`, `lte_spaddre`
  + lemma `lte_spdadder`

### Changed

- in `constructive_ereal.v`:
  + lemmas `lee_paddl`, `lte_paddl`, `lee_paddr`, `lte_paddr`, `lte_spaddr` generalized to `realDomainType`
- in `constructive_ereal.v`:
  + generalize `lte_addl`, `lte_addr`, `gte_subl`, `gte_subr`,
    `lte_daddl`, `lte_daddr`, `gte_dsubl`, `gte_dsubr`

### Renamed

- in `constructive_ereal.v`:
  + `lte_spdaddr` -> `lte_spdaddre`

### Deprecated

- in `constructive_ereal.v`:
  + lemma `lte_spaddr` replaced by `lte_spaddre`

### Removed

### Infrastructure

### Misc
