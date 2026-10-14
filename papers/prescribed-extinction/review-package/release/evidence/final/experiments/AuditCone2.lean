import PrescribedExtinction
open Lean Elab Command
def auditorDeps (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[root]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut used := ci.type.getUsedConstants
    match ci with
    | .defnInfo d => used := used ++ d.value.getUsedConstants
    | .thmInfo t => used := used ++ t.value.getUsedConstants
    | .opaqueInfo o => used := used ++ o.value.getUsedConstants
    | .inductInfo i => used := used ++ i.ctors.toArray ++ i.all.toArray
    | .ctorInfo c => used := used.push c.induct
    | .recInfo r =>
        used := used ++ r.all.toArray
        for rule in r.rules do used := used ++ rule.rhs.getUsedConstants
    | .quotInfo _ => pure ()
    | .axiomInfo _ => pure ()
    for u in used do
      unless seen.contains u do stack := stack.push u
  return seen


elab "#cone2" : command => do
  let env ← getEnv
  let deps := auditorDeps env `OQ7Prescribed.theorem11_complete
  let mut axs : Array Name := #[]
  let mut unsafes := 0
  let mut proj := 0
  let mut projMods : NameSet := {}
  for n in deps do
    if let some ci := env.find? n then
      if ci matches .axiomInfo _ then axs := axs.push n
      if ci.isUnsafe then unsafes := unsafes + 1
      if let some idx := env.getModuleIdxFor? n then
        let m := env.header.moduleNames[idx.toNat]!
        let top := (m.components.headD `none).toString
        if top == "PrescribedExtinction" || top == "OQ7" then
          proj := proj + 1; projMods := projMods.insert m
  logInfo m!"reachable constants: {deps.size}; project constants: {proj}; project modules: {projMods.size}"
  logInfo m!"axioms: {axs}; unsafe: {unsafes}"
  let newMods := [`PrescribedExtinction.ArbitraryStateOpticalBalance, `PrescribedExtinction.CompactFieldTestSeparation,
    `PrescribedExtinction.DistributionVacuumHelmholtz, `PrescribedExtinction.ExteriorSphereContinuity,
    `PrescribedExtinction.ForwardOpticalTheorem, `PrescribedExtinction.FullPhysicalOpticalTheorem,
    `PrescribedExtinction.FullPrescribedSuprema, `PrescribedExtinction.OutgoingWeakEnergy,
    `PrescribedExtinction.PhysicalPowersAE, `PrescribedExtinction.PhysicalSphereFlux,
    `PrescribedExtinction.PhysicalTheorem11, `PrescribedExtinction.PrescribedExtinctionClass,
    `PrescribedExtinction.ScatteringStatePhysicalRadiation, `PrescribedExtinction.SmoothSourceWeakDecay,
    `PrescribedExtinction.UniversalFieldPowers, `PrescribedExtinction.UniversalPassivity,
    `PrescribedExtinction.UniversalPhysicalBounds, `PrescribedExtinction.UniversalStrictAbsorption,
    `PrescribedExtinction.VacuumOutgoingWeakUniqueness, `PrescribedExtinction.WeakCurlFourier,
    `PrescribedExtinction.WeakCurlLocalization, `PrescribedExtinction.WeakCurlPlaneWave,
    `PrescribedExtinction.WeakCurlProducts, `PrescribedExtinction.WeakCurlWeightedGreen,
    `PrescribedExtinction.WeakLorentzBoundaryBound, `PrescribedExtinction.WeakPhysicalRepresentation,
    `PrescribedExtinction.WeakPhysicalUniqueness, `PrescribedExtinction.WeakPoynting,
    `PrescribedExtinction.WeakScatteringResidual, `PrescribedExtinction.WeakSmoothLorentz,
    `PrescribedExtinction.WeightedRadiationEnergy]
  for m in newMods do
    logInfo m!"new module {m}: constants reached = {projMods.contains m}"
  logInfo m!"OQ7Prescribed.theorem11: in cone = {deps.contains `OQ7Prescribed.theorem11}, exists = {(env.find? `OQ7Prescribed.theorem11).isSome}"
  logInfo m!"OQ7Prescribed.physicalScatteringState_unique_ae: in cone = {deps.contains `OQ7Prescribed.physicalScatteringState_unique_ae}, exists = {(env.find? `OQ7Prescribed.physicalScatteringState_unique_ae).isSome}"
  logInfo m!"OQ7Prescribed.physicalScatteringState_exists: in cone = {deps.contains `OQ7Prescribed.physicalScatteringState_exists}, exists = {(env.find? `OQ7Prescribed.physicalScatteringState_exists).isSome}"
  logInfo m!"OQ7Prescribed.scatteringState_outgoing_volume_representation: in cone = {deps.contains `OQ7Prescribed.scatteringState_outgoing_volume_representation}, exists = {(env.find? `OQ7Prescribed.scatteringState_outgoing_volume_representation).isSome}"
  logInfo m!"OQ7Prescribed.scatteringState_energy_balance: in cone = {deps.contains `OQ7Prescribed.scatteringState_energy_balance}, exists = {(env.find? `OQ7Prescribed.scatteringState_energy_balance).isSome}"
  logInfo m!"OQ7Prescribed.scatteringState_forward_optical_theorem: in cone = {deps.contains `OQ7Prescribed.scatteringState_forward_optical_theorem}, exists = {(env.find? `OQ7Prescribed.scatteringState_forward_optical_theorem).isSome}"
  logInfo m!"OQ7Prescribed.exteriorSphereFlux_tendsto: in cone = {deps.contains `OQ7Prescribed.exteriorSphereFlux_tendsto}, exists = {(env.find? `OQ7Prescribed.exteriorSphereFlux_tendsto).isSome}"
  logInfo m!"OQ7Prescribed.scatteringState_absorption_le_extinction: in cone = {deps.contains `OQ7Prescribed.scatteringState_absorption_le_extinction}, exists = {(env.find? `OQ7Prescribed.scatteringState_absorption_le_extinction).isSome}"
  logInfo m!"OQ7Prescribed.scatteringState_extinction_reciprocity: in cone = {deps.contains `OQ7Prescribed.scatteringState_extinction_reciprocity}, exists = {(env.find? `OQ7Prescribed.scatteringState_extinction_reciprocity).isSome}"
  logInfo m!"OQ7Prescribed.physicalScattering_eq_Haar: in cone = {deps.contains `OQ7Prescribed.physicalScattering_eq_Haar}, exists = {(env.find? `OQ7Prescribed.physicalScattering_eq_Haar).isSome}"
  logInfo m!"OQ7Prescribed.scatteringState_currentFarField_is_physical: in cone = {deps.contains `OQ7Prescribed.scatteringState_currentFarField_is_physical}, exists = {(env.find? `OQ7Prescribed.scatteringState_currentFarField_is_physical).isSome}"
  logInfo m!"OQ7Prescribed.outgoing_weak_source_work_nonneg: in cone = {deps.contains `OQ7Prescribed.outgoing_weak_source_work_nonneg}, exists = {(env.find? `OQ7Prescribed.outgoing_weak_source_work_nonneg).isSome}"
  logInfo m!"OQ7Prescribed.prescribedExtinctionAsymmetryValues_isLUB: in cone = {deps.contains `OQ7Prescribed.prescribedExtinctionAsymmetryValues_isLUB}, exists = {(env.find? `OQ7Prescribed.prescribedExtinctionAsymmetryValues_isLUB).isSome}"
  logInfo m!"OQ7Prescribed.AnalyticTestWeakCurl: in cone = {deps.contains `OQ7Prescribed.AnalyticTestWeakCurl}, exists = {(env.find? `OQ7Prescribed.AnalyticTestWeakCurl).isSome}"
  logInfo m!"OQ7Prescribed.HasWeakCurl.implies_analyticTestWeakCurl: in cone = {deps.contains `OQ7Prescribed.HasWeakCurl.implies_analyticTestWeakCurl}, exists = {(env.find? `OQ7Prescribed.HasWeakCurl.implies_analyticTestWeakCurl).isSome}"
  logInfo m!"sorryAx: in cone = {deps.contains `sorryAx}, exists = {(env.find? `sorryAx).isSome}"
  logInfo m!"Lean.ofReduceBool: in cone = {deps.contains `Lean.ofReduceBool}, exists = {(env.find? `Lean.ofReduceBool).isSome}"
  logInfo m!"Lean.trustCompiler: in cone = {deps.contains `Lean.trustCompiler}, exists = {(env.find? `Lean.trustCompiler).isSome}"
#cone2
