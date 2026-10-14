import PrescribedExtinction
run_cmd do
  let env ← Lean.getEnv
  unless (env.find? `OQ7Prescribed.MaterialAdmissible).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.MaterialAdmissible"
  unless (env.find? `OQ7Prescribed.Outgoing).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.Outgoing"
  unless (env.find? `OQ7Prescribed.TwoLayerBody).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.TwoLayerBody"
  unless (env.find? `OQ7Prescribed.WeakMaxwell).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.WeakMaxwell"
  unless (env.find? `OQ7Prescribed.absorption).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.absorption"
  unless (env.find? `OQ7Prescribed.activeMaterialEquiv_inverse_norm_le).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.activeMaterialEquiv_inverse_norm_le"
  unless (env.find? `OQ7Prescribed.activePhysicalSolution_sine_factorization).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.activePhysicalSolution_sine_factorization"
  unless (env.find? `OQ7Prescribed.admissibleScatteringState_extinction_reciprocity).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.admissibleScatteringState_extinction_reciprocity"
  unless (env.find? `OQ7Prescribed.compactOutgoingOperator_norm_le).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.compactOutgoingOperator_norm_le"
  unless (env.find? `OQ7Prescribed.compactStaticOperator_apply_norm_le).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.compactStaticOperator_apply_norm_le"
  unless (env.find? `OQ7Prescribed.currentFarField).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.currentFarField"
  unless (env.find? `OQ7Prescribed.exists_nearlyPerfect_absorber_with_loss_cap).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.exists_nearlyPerfect_absorber_with_loss_cap"
  unless (env.find? `OQ7Prescribed.exists_planar_design_near_unit_asymmetry).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.exists_planar_design_near_unit_asymmetry"
  unless (env.find? `OQ7Prescribed.exists_plateDesign_within_cap).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.exists_plateDesign_within_cap"
  unless (env.find? `OQ7Prescribed.extinction).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.extinction"
  unless (env.find? `OQ7Prescribed.incidentElectric).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.incidentElectric"
  unless (env.find? `OQ7Prescribed.incidentMagnetic).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.incidentMagnetic"
  unless (env.find? `OQ7Prescribed.isotropicRankOneBody_admissible).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.isotropicRankOneBody_admissible"
  unless (env.find? `OQ7Prescribed.losslessPlateDesign_actual_coefficients).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.losslessPlateDesign_actual_coefficients"
  unless (env.find? `OQ7Prescribed.losslessPlateDesign_coupled_power_values).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.losslessPlateDesign_coupled_power_values"
  unless (env.find? `OQ7Prescribed.physicalAbsorption_sine_squared_factorization).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.physicalAbsorption_sine_squared_factorization"
  unless (env.find? `OQ7Prescribed.physicalAsymmetry_normalized_factorization).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.physicalAsymmetry_normalized_factorization"
  unless (env.find? `OQ7Prescribed.physicalBody_normalized_asymmetry_uniform_aperture_localization).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.physicalBody_normalized_asymmetry_uniform_aperture_localization"
  unless (env.find? `OQ7Prescribed.physicalBody_normalized_powers_uniform_aperture_localization).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.physicalBody_normalized_powers_uniform_aperture_localization"
  unless (env.find? `OQ7Prescribed.physicalBody_normalized_response_uniform_aperture_localization).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.physicalBody_normalized_response_uniform_aperture_localization"
  unless (env.find? `OQ7Prescribed.physicalBody_uniform_sharp_response_estimate).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.physicalBody_uniform_sharp_response_estimate"
  unless (env.find? `OQ7Prescribed.physicalExtinction_sine_squared_factorization).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.physicalExtinction_sine_squared_factorization"
  unless (env.find? `OQ7Prescribed.physicalIsotropic_prescribedExtinctionOfPlanarDesign).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.physicalIsotropic_prescribedExtinctionOfPlanarDesign"
  unless (env.find? `OQ7Prescribed.physicalOutgoingVolume_farField_work).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.physicalOutgoingVolume_farField_work"
  unless (env.find? `OQ7Prescribed.physicalPerturbed_preserves_compact_bracket).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.physicalPerturbed_preserves_compact_bracket"
  unless (env.find? `OQ7Prescribed.physicalRankOne_exists_extinction_bracket).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.physicalRankOne_exists_extinction_bracket"
  unless (env.find? `OQ7Prescribed.physicalRankOne_original_powers_uniform_aperture_localization).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.physicalRankOne_original_powers_uniform_aperture_localization"
  unless (env.find? `OQ7Prescribed.physicalRankOne_prescribedExtinctionOfPlanarDesign).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.physicalRankOne_prescribedExtinctionOfPlanarDesign"
  unless (env.find? `OQ7Prescribed.physicalScatteringState_wellposed_ae).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.physicalScatteringState_wellposed_ae"
  unless (env.find? `OQ7Prescribed.physicalScattering_sine_squared_factorization).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.physicalScattering_sine_squared_factorization"
  unless (env.find? `OQ7Prescribed.physicalScattering_zero_extinction).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.physicalScattering_zero_extinction"
  unless (env.find? `OQ7Prescribed.plateDesign_phases).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.plateDesign_phases"
  unless (env.find? `OQ7Prescribed.prescribedExtinctionAsymmetryValues_sSup).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.prescribedExtinctionAsymmetryValues_sSup"
  unless (env.find? `OQ7Prescribed.prescribedExtinctionDifferenceValues_sSup).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.prescribedExtinctionDifferenceValues_sSup"
  unless (env.find? `OQ7Prescribed.scattering).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.scattering"
  unless (env.find? `OQ7Prescribed.scatteringState_converse_material_volume_equation).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.scatteringState_converse_material_volume_equation"
  unless (env.find? `OQ7Prescribed.scatteringState_energy_balance).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.scatteringState_energy_balance"
  unless (env.find? `OQ7Prescribed.scatteringState_forward_optical_theorem).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.scatteringState_forward_optical_theorem"
  unless (env.find? `OQ7Prescribed.scatteringState_full_optical_theorem).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.scatteringState_full_optical_theorem"
  unless (env.find? `OQ7Prescribed.slabDesignAsymmetry_joint_continuousAt_zero).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.slabDesignAsymmetry_joint_continuousAt_zero"
  unless (env.find? `OQ7Prescribed.theorem11).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.theorem11"
  unless (env.find? `OQ7Prescribed.theorem11_complete).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.theorem11_complete"
  unless (env.find? `OQ7Prescribed.universal_physical_asymmetry_eq_scattering_difference).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.universal_physical_asymmetry_eq_scattering_difference"
  unless (env.find? `OQ7Prescribed.universal_physical_asymmetry_lt_one).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.universal_physical_asymmetry_lt_one"
  unless (env.find? `OQ7Prescribed.vacuum_outgoing_weak_unique_zero).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.vacuum_outgoing_weak_unique_zero"
  unless (env.find? `OQ7Prescribed.woodburyElectricOperator_left_inverse).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.woodburyElectricOperator_left_inverse"
  unless (env.find? `OQ7Prescribed.woodburyElectricOperator_right_inverse).isSome do
    throwError "Missing correspondence declaration: OQ7Prescribed.woodburyElectricOperator_right_inverse"
  Lean.logInfo "CORRESPONDENCE-DECLARATION-EXISTENCE-PASS: 52 names"
