import GeneralizedResearch
import Lean.Util.CollectAxioms

/-! Exact types and transitive axioms of the unchanged imported dependencies
used directly by the original-statement correspondence inventory. The main
exhaustive audit separately covers every new namespace theorem. -/
set_option pp.fullNames true
set_option pp.universes true
set_option pp.funBinderTypes true

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[`OQ7.capped_fourier_moment_Ioo,
    `OQ7.sineSquare_triangleIntegral_capped_Ioo,
    `OQ7.ResourceScalar.g_convex_half,
    `OQ7.ResourceScalar.g_tangent_full,
    `OQ7.ResourceScalar.f_lower_half,
    `OQ7.stackResourceInvariant_eq_fluxDefect]
  logInfo m!"THEOREM_CENSUS_COUNT {names.size}"
  for name in names do
    let some info := env.find? name | throwError m!"Missing correspondence dependency: {name}"
    unless info.isTheorem do throwError m!"Expected theorem: {name}"
    let axioms ← Lean.collectAxioms name
    let forbidden := axioms.filter fun ax =>
      ax != `propext && ax != `Classical.choice && ax != `Quot.sound
    unless forbidden.isEmpty do throwError m!"Nonstandard correspondence dependency axioms: {forbidden.toList}"
    logInfo m!"THEOREM {name}"
    logInfo m!"TYPE {info.type}"
    logInfo m!"AXIOMS {axioms.toList}"
