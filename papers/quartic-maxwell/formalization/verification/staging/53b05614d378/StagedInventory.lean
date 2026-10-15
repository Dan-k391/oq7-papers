import QuarticMaxwell.SourceTaylor
import QuarticMaxwell.StaticInverse
import QuarticMaxwell.StaticReciprocity
import QuarticMaxwell.RadiationGram
import QuarticMaxwell.RadiationTaylor
import QuarticMaxwell.GramEstimates
import QuarticMaxwell.FixedPatternWork
import QuarticMaxwell.LocalTensorClass
import QuarticMaxwell.FixedPatternScattering
import QuarticMaxwell.FixedPatternContrast
import QuarticMaxwell.StaticHessian
import QuarticMaxwell.PhysicalDilation
import QuarticMaxwell.FixedPatternDilation
import QuarticMaxwell.CrossBlockOperator
import QuarticMaxwell.BlockResolvent
import QuarticMaxwell.BallAffineMoments
import QuarticMaxwell.SphereNewton
import QuarticMaxwell.SphereStatic
import QuarticMaxwell.SphereResponse
import QuarticMaxwell.StaticOffSupport
import QuarticMaxwell.StaticCrossIdentification
import QuarticMaxwell.SupportBlocks
import QuarticMaxwell.TwoSupportStatic
import QuarticMaxwell.TwoSupportBounds
import QuarticMaxwell.TwoSphereGeometry
import QuarticMaxwell.SphereExterior
import QuarticMaxwell.SphereHessianMean
import QuarticMaxwell.SphereDoubleMean
import QuarticMaxwell.MomentOperator
import QuarticMaxwell.BlockSourceMoments
import QuarticMaxwell.QuantitativeQuotient
import QuarticMaxwell.HeterogeneousCertificate
import QuarticMaxwell.HeterogeneousRemainder
import QuarticMaxwell.HeterogeneousAttainment
import QuarticMaxwell.SphereCrossMoment
import QuarticMaxwell.BlockInteractionMoments
import QuarticMaxwell.HomogeneousScalars
import QuarticMaxwell.MomentPerturbation
import QuarticMaxwell.StaticHessianExact
import QuarticMaxwell.HeterogeneousAuxiliary
import QuarticMaxwell.PaperSignConvention
import QuarticMaxwell.SharpnessClass
import QuarticMaxwell.LorentzMaterial
import QuarticMaxwell.HomogeneousMoments
import QuarticMaxwell.HomogeneousErrors
import QuarticMaxwell.HomogeneousCoefficient
import QuarticMaxwell.HomogeneousUniform
import QuarticMaxwell.HomogeneousBounds
import QuarticMaxwell.HomogeneousSharpness
import QuarticMaxwell.HomogeneousQuantitative
set_option pp.fullNames true
set_option pp.explicit false
set_option pp.universes true
set_option format.width 120
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
#check @QuarticMaxwell.SourceTaylor.scalar_memLp
#print axioms QuarticMaxwell.SourceTaylor.scalar_memLp
#check @QuarticMaxwell.SourceTaylor.scalarSource
#print axioms QuarticMaxwell.SourceTaylor.scalarSource
#check @QuarticMaxwell.SourceTaylor.scalarSource_coe
#print axioms QuarticMaxwell.SourceTaylor.scalarSource_coe
#check @QuarticMaxwell.SourceTaylor.constantSource
#print axioms QuarticMaxwell.SourceTaylor.constantSource
#check @QuarticMaxwell.SourceTaylor.cosSource
#print axioms QuarticMaxwell.SourceTaylor.cosSource
#check @QuarticMaxwell.SourceTaylor.sinSource
#print axioms QuarticMaxwell.SourceTaylor.sinSource
#check @QuarticMaxwell.SourceTaylor.direction_bound
#print axioms QuarticMaxwell.SourceTaylor.direction_bound
#check @QuarticMaxwell.SourceTaylor.momentSource
#print axioms QuarticMaxwell.SourceTaylor.momentSource
#check @QuarticMaxwell.SourceTaylor.constantSource_coe
#print axioms QuarticMaxwell.SourceTaylor.constantSource_coe
#check @QuarticMaxwell.SourceTaylor.cosSource_coe
#print axioms QuarticMaxwell.SourceTaylor.cosSource_coe
#check @QuarticMaxwell.SourceTaylor.sinSource_coe
#print axioms QuarticMaxwell.SourceTaylor.sinSource_coe
#check @QuarticMaxwell.SourceTaylor.momentSource_coe
#print axioms QuarticMaxwell.SourceTaylor.momentSource_coe
#check @QuarticMaxwell.SourceTaylor.norm_comparison
#print axioms QuarticMaxwell.SourceTaylor.norm_comparison
#check @QuarticMaxwell.SourceTaylor.cos_scalar_remainder
#print axioms QuarticMaxwell.SourceTaylor.cos_scalar_remainder
#check @QuarticMaxwell.SourceTaylor.cosine_remainder
#print axioms QuarticMaxwell.SourceTaylor.cosine_remainder
#check @QuarticMaxwell.SourceTaylor.sine_remainder
#print axioms QuarticMaxwell.SourceTaylor.sine_remainder
#check @QuarticMaxwell.SourceTaylor.moment_norm
#print axioms QuarticMaxwell.SourceTaylor.moment_norm
#check @QuarticMaxwell.SourceTaylor.sine_norm
#print axioms QuarticMaxwell.SourceTaylor.sine_norm
#check @QuarticMaxwell.SourceTaylor.cosine_norm
#print axioms QuarticMaxwell.SourceTaylor.cosine_norm
#check @QuarticMaxwell.SourceTaylor.phase_cos_sin
#print axioms QuarticMaxwell.SourceTaylor.phase_cos_sin
#check @QuarticMaxwell.SourceTaylor.source_decomposition
#print axioms QuarticMaxwell.SourceTaylor.source_decomposition
#check @QuarticMaxwell.SourceTaylor.cosine_neg
#print axioms QuarticMaxwell.SourceTaylor.cosine_neg
#check @QuarticMaxwell.SourceTaylor.sine_neg
#print axioms QuarticMaxwell.SourceTaylor.sine_neg
#check @QuarticMaxwell.SourceTaylor.source_reverse_decomposition
#print axioms QuarticMaxwell.SourceTaylor.source_reverse_decomposition
#check @QuarticMaxwell.SourceTaylor.constant_eq_source_zero
#print axioms QuarticMaxwell.SourceTaylor.constant_eq_source_zero
#check @QuarticMaxwell.SourceTaylor.constant_norm_sq
#print axioms QuarticMaxwell.SourceTaylor.constant_norm_sq
#check @QuarticMaxwell.SourceTaylor.vectorConjugate_real_smul
#print axioms QuarticMaxwell.SourceTaylor.vectorConjugate_real_smul
#check @QuarticMaxwell.SourceTaylor.scalarSource_fixed
#print axioms QuarticMaxwell.SourceTaylor.scalarSource_fixed
#check @QuarticMaxwell.SourceTaylor.cosine_fixed
#print axioms QuarticMaxwell.SourceTaylor.cosine_fixed
#check @QuarticMaxwell.SourceTaylor.sine_fixed
#print axioms QuarticMaxwell.SourceTaylor.sine_fixed
#check @QuarticMaxwell.inverse_difference_eq
#print axioms QuarticMaxwell.inverse_difference_eq
#check @QuarticMaxwell.inverse_difference_norm_le
#print axioms QuarticMaxwell.inverse_difference_norm_le
#check @QuarticMaxwell.StaticInverse.operator
#print axioms QuarticMaxwell.StaticInverse.operator
#check @QuarticMaxwell.StaticInverse.negative_coercive
#print axioms QuarticMaxwell.StaticInverse.negative_coercive
#check @QuarticMaxwell.StaticInverse.equiv
#print axioms QuarticMaxwell.StaticInverse.equiv
#check @QuarticMaxwell.StaticInverse.equiv_apply
#print axioms QuarticMaxwell.StaticInverse.equiv_apply
#check @QuarticMaxwell.StaticInverse.inverse_norm_le
#print axioms QuarticMaxwell.StaticInverse.inverse_norm_le
#check @QuarticMaxwell.StaticInverse.dynamic_static_resolvent_norm_le
#print axioms QuarticMaxwell.StaticInverse.dynamic_static_resolvent_norm_le
#check @QuarticMaxwell.StaticInverse.forward_work_pos
#print axioms QuarticMaxwell.StaticInverse.forward_work_pos
#check @QuarticMaxwell.nonpositive_of_le_mul_sq
#print axioms QuarticMaxwell.nonpositive_of_le_mul_sq
#check @QuarticMaxwell.domainStaticOperator_reciprocity
#print axioms QuarticMaxwell.domainStaticOperator_reciprocity
#check @QuarticMaxwell.StaticInverse.operator_reciprocity
#print axioms QuarticMaxwell.StaticInverse.operator_reciprocity
#check @QuarticMaxwell.StaticInverse.inverse_reciprocity
#print axioms QuarticMaxwell.StaticInverse.inverse_reciprocity
#check @QuarticMaxwell.linear_inner_of_norm_sq
#print axioms QuarticMaxwell.linear_inner_of_norm_sq
#check @QuarticMaxwell.sphereAntipode
#print axioms QuarticMaxwell.sphereAntipode
#check @QuarticMaxwell.sphereAntipode_coe
#print axioms QuarticMaxwell.sphereAntipode_coe
#check @QuarticMaxwell.angularProjection_antipode
#print axioms QuarticMaxwell.angularProjection_antipode
#check @QuarticMaxwell.radiationPhase_antipode
#print axioms QuarticMaxwell.radiationPhase_antipode
#check @QuarticMaxwell.radiationField_antipode
#print axioms QuarticMaxwell.radiationField_antipode
#check @QuarticMaxwell.domainRadiationMap_norm_sq_even
#print axioms QuarticMaxwell.domainRadiationMap_norm_sq_even
#check @QuarticMaxwell.radiationGram
#print axioms QuarticMaxwell.radiationGram
#check @QuarticMaxwell.radiationGram_inner
#print axioms QuarticMaxwell.radiationGram_inner
#check @QuarticMaxwell.radiationGram_even
#print axioms QuarticMaxwell.radiationGram_even
#check @QuarticMaxwell.supportMomentLinear
#print axioms QuarticMaxwell.supportMomentLinear
#check @QuarticMaxwell.radiationField_zero_moment
#print axioms QuarticMaxwell.radiationField_zero_moment
#check @QuarticMaxwell.domainRadiationMap_zero_norm_sq
#print axioms QuarticMaxwell.domainRadiationMap_zero_norm_sq
#check @QuarticMaxwell.radiationGram_zero_moment
#print axioms QuarticMaxwell.radiationGram_zero_moment
#check @QuarticMaxwell.constantSource_inner_moment
#print axioms QuarticMaxwell.constantSource_inner_moment
#check @QuarticMaxwell.boundedRadiation_integrand_memLp
#print axioms QuarticMaxwell.boundedRadiation_integrand_memLp
#check @QuarticMaxwell.boundedRadiation_field_square_bound
#print axioms QuarticMaxwell.boundedRadiation_field_square_bound
#check @QuarticMaxwell.operator_norm_sq_of_apply_sq
#print axioms QuarticMaxwell.operator_norm_sq_of_apply_sq
#check @QuarticMaxwell.radiationPhase_sub_one_norm_bound
#print axioms QuarticMaxwell.radiationPhase_sub_one_norm_bound
#check @QuarticMaxwell.radiationPhase_even_remainder
#print axioms QuarticMaxwell.radiationPhase_even_remainder
#check @QuarticMaxwell.radiationField_difference_integral
#print axioms QuarticMaxwell.radiationField_difference_integral
#check @QuarticMaxwell.radiationField_even_remainder_integral
#print axioms QuarticMaxwell.radiationField_even_remainder_integral
#check @QuarticMaxwell.domainRadiationMap_difference_apply_sq
#print axioms QuarticMaxwell.domainRadiationMap_difference_apply_sq
#check @QuarticMaxwell.domainRadiationMap_even_remainder_apply_sq
#print axioms QuarticMaxwell.domainRadiationMap_even_remainder_apply_sq
#check @QuarticMaxwell.nonnegative_norm_of_square_bound
#print axioms QuarticMaxwell.nonnegative_norm_of_square_bound
#check @QuarticMaxwell.domainRadiationMap_difference_apply_norm_le
#print axioms QuarticMaxwell.domainRadiationMap_difference_apply_norm_le
#check @QuarticMaxwell.domainRadiationMap_even_remainder_apply_norm_le
#print axioms QuarticMaxwell.domainRadiationMap_even_remainder_apply_norm_le
#check @QuarticMaxwell.inner_central_difference
#print axioms QuarticMaxwell.inner_central_difference
#check @QuarticMaxwell.even_gram_pairing_bound
#print axioms QuarticMaxwell.even_gram_pairing_bound
#check @QuarticMaxwell.domainRadiationMap_apply_norm_bound
#print axioms QuarticMaxwell.domainRadiationMap_apply_norm_bound
#check @QuarticMaxwell.radiationGram_norm_le
#print axioms QuarticMaxwell.radiationGram_norm_le
#check @QuarticMaxwell.radiationGram_difference_pairing_bound
#print axioms QuarticMaxwell.radiationGram_difference_pairing_bound
#check @QuarticMaxwell.radiationGram_difference_norm_le
#print axioms QuarticMaxwell.radiationGram_difference_norm_le
#check @QuarticMaxwell.FixedPatternWork.rho
#print axioms QuarticMaxwell.FixedPatternWork.rho
#check @QuarticMaxwell.FixedPatternWork.correction
#print axioms QuarticMaxwell.FixedPatternWork.correction
#check @QuarticMaxwell.FixedPatternWork.rho_pos
#print axioms QuarticMaxwell.FixedPatternWork.rho_pos
#check @QuarticMaxwell.FixedPatternWork.correction_nonneg
#print axioms QuarticMaxwell.FixedPatternWork.correction_nonneg
#check @QuarticMaxwell.FixedPatternWork.staticResponse
#print axioms QuarticMaxwell.FixedPatternWork.staticResponse
#check @QuarticMaxwell.FixedPatternWork.dynamicResponse
#print axioms QuarticMaxwell.FixedPatternWork.dynamicResponse
#check @QuarticMaxwell.FixedPatternWork.constantInput
#print axioms QuarticMaxwell.FixedPatternWork.constantInput
#check @QuarticMaxwell.FixedPatternWork.linearInput
#print axioms QuarticMaxwell.FixedPatternWork.linearInput
#check @QuarticMaxwell.FixedPatternWork.cosineInput
#print axioms QuarticMaxwell.FixedPatternWork.cosineInput
#check @QuarticMaxwell.FixedPatternWork.sineInput
#print axioms QuarticMaxwell.FixedPatternWork.sineInput
#check @QuarticMaxwell.FixedPatternWork.q0
#print axioms QuarticMaxwell.FixedPatternWork.q0
#check @QuarticMaxwell.FixedPatternWork.q1
#print axioms QuarticMaxwell.FixedPatternWork.q1
#check @QuarticMaxwell.FixedPatternWork.u
#print axioms QuarticMaxwell.FixedPatternWork.u
#check @QuarticMaxwell.FixedPatternWork.v
#print axioms QuarticMaxwell.FixedPatternWork.v
#check @QuarticMaxwell.FixedPatternWork.D0
#print axioms QuarticMaxwell.FixedPatternWork.D0
#check @QuarticMaxwell.FixedPatternWork.static_norm_le
#print axioms QuarticMaxwell.FixedPatternWork.static_norm_le
#check @QuarticMaxwell.FixedPatternWork.dynamic_norm_le
#print axioms QuarticMaxwell.FixedPatternWork.dynamic_norm_le
#check @QuarticMaxwell.FixedPatternWork.resolvent_norm_le
#print axioms QuarticMaxwell.FixedPatternWork.resolvent_norm_le
#check @QuarticMaxwell.FixedPatternWork.u_norm
#print axioms QuarticMaxwell.FixedPatternWork.u_norm
#check @QuarticMaxwell.FixedPatternWork.v_norm
#print axioms QuarticMaxwell.FixedPatternWork.v_norm
#check @QuarticMaxwell.FixedPatternWork.q0_norm
#print axioms QuarticMaxwell.FixedPatternWork.q0_norm
#check @QuarticMaxwell.FixedPatternWork.q1_norm
#print axioms QuarticMaxwell.FixedPatternWork.q1_norm
#check @QuarticMaxwell.FixedPatternWork.u_error
#print axioms QuarticMaxwell.FixedPatternWork.u_error
#check @QuarticMaxwell.FixedPatternWork.v_error
#print axioms QuarticMaxwell.FixedPatternWork.v_error
#check @QuarticMaxwell.FixedPatternWork.D0_pos
#print axioms QuarticMaxwell.FixedPatternWork.D0_pos
#check @QuarticMaxwell.FixedPatternWork.inner_im_error
#print axioms QuarticMaxwell.FixedPatternWork.inner_im_error
#check @QuarticMaxwell.FixedPatternWork.forwardWork
#print axioms QuarticMaxwell.FixedPatternWork.forwardWork
#check @QuarticMaxwell.FixedPatternWork.forward_work_error
#print axioms QuarticMaxwell.FixedPatternWork.forward_work_error
#check @QuarticMaxwell.FixedPatternWork.actual_forward_decomposition
#print axioms QuarticMaxwell.FixedPatternWork.actual_forward_decomposition
#check @QuarticMaxwell.LocalTensorClass.zeroExtension
#print axioms QuarticMaxwell.LocalTensorClass.zeroExtension
#check @QuarticMaxwell.LocalTensorClass.zeroExtension_measurable
#print axioms QuarticMaxwell.LocalTensorClass.zeroExtension_measurable
#check @QuarticMaxwell.LocalTensorClass.zeroExtension_on_domain
#print axioms QuarticMaxwell.LocalTensorClass.zeroExtension_on_domain
#check @QuarticMaxwell.LocalTensorClass.zeroExtension_outside
#print axioms QuarticMaxwell.LocalTensorClass.zeroExtension_outside
#check @QuarticMaxwell.LocalTensorClass.zeroExtension_cap
#print axioms QuarticMaxwell.LocalTensorClass.zeroExtension_cap
#check @QuarticMaxwell.LocalTensorClass.zeroExtension_loss
#print axioms QuarticMaxwell.LocalTensorClass.zeroExtension_loss
#check @QuarticMaxwell.LocalTensorClass.zeroExtension_reciprocal
#print axioms QuarticMaxwell.LocalTensorClass.zeroExtension_reciprocal
#check @QuarticMaxwell.LocalTensorClass.matrixOperator
#print axioms QuarticMaxwell.LocalTensorClass.matrixOperator
#check @QuarticMaxwell.LocalTensorClass.matrixOperator_apply
#print axioms QuarticMaxwell.LocalTensorClass.matrixOperator_apply
#check @QuarticMaxwell.LocalTensorClass.matrixOperator_norm
#print axioms QuarticMaxwell.LocalTensorClass.matrixOperator_norm
#check @QuarticMaxwell.LocalTensorClass.matrixOperator_bijective
#print axioms QuarticMaxwell.LocalTensorClass.matrixOperator_bijective
#check @QuarticMaxwell.LocalTensorClass.bilinear_transpose
#print axioms QuarticMaxwell.LocalTensorClass.bilinear_transpose
#check @QuarticMaxwell.LocalTensorClass.matrixOperator_reciprocal
#print axioms QuarticMaxwell.LocalTensorClass.matrixOperator_reciprocal
#check @QuarticMaxwell.LocalTensorClass.matrixOperator_measurable
#print axioms QuarticMaxwell.LocalTensorClass.matrixOperator_measurable
#check @QuarticMaxwell.norm_sq_opposite_i
#print axioms QuarticMaxwell.norm_sq_opposite_i
#check @QuarticMaxwell.gram_cross_error
#print axioms QuarticMaxwell.gram_cross_error
#check @QuarticMaxwell.FixedPatternScattering.moment0
#print axioms QuarticMaxwell.FixedPatternScattering.moment0
#check @QuarticMaxwell.FixedPatternScattering.moment1
#print axioms QuarticMaxwell.FixedPatternScattering.moment1
#check @QuarticMaxwell.FixedPatternScattering.leading
#print axioms QuarticMaxwell.FixedPatternScattering.leading
#check @QuarticMaxwell.FixedPatternScattering.gramBound
#print axioms QuarticMaxwell.FixedPatternScattering.gramBound
#check @QuarticMaxwell.FixedPatternScattering.gramCorrection
#print axioms QuarticMaxwell.FixedPatternScattering.gramCorrection
#check @QuarticMaxwell.FixedPatternScattering.errorConstant
#print axioms QuarticMaxwell.FixedPatternScattering.errorConstant
#check @QuarticMaxwell.FixedPatternScattering.signedScattering
#print axioms QuarticMaxwell.FixedPatternScattering.signedScattering
#check @QuarticMaxwell.FixedPatternScattering.signedScattering_inner
#print axioms QuarticMaxwell.FixedPatternScattering.signedScattering_inner
#check @QuarticMaxwell.FixedPatternScattering.leading_moment
#print axioms QuarticMaxwell.FixedPatternScattering.leading_moment
#check @QuarticMaxwell.FixedPatternScattering.denominator_moment
#print axioms QuarticMaxwell.FixedPatternScattering.denominator_moment
#check @QuarticMaxwell.FixedPatternScattering.errorConstant_nonneg
#print axioms QuarticMaxwell.FixedPatternScattering.errorConstant_nonneg
#check @QuarticMaxwell.FixedPatternScattering.signedScattering_error
#print axioms QuarticMaxwell.FixedPatternScattering.signedScattering_error
#check @QuarticMaxwell.FixedPatternContrast.denominatorError
#print axioms QuarticMaxwell.FixedPatternContrast.denominatorError
#check @QuarticMaxwell.FixedPatternContrast.coefficient
#print axioms QuarticMaxwell.FixedPatternContrast.coefficient
#check @QuarticMaxwell.FixedPatternContrast.remainderConstant
#print axioms QuarticMaxwell.FixedPatternContrast.remainderConstant
#check @QuarticMaxwell.FixedPatternContrast.interval
#print axioms QuarticMaxwell.FixedPatternContrast.interval
#check @QuarticMaxwell.FixedPatternContrast.contrast
#print axioms QuarticMaxwell.FixedPatternContrast.contrast
#check @QuarticMaxwell.FixedPatternContrast.denominatorError_nonneg
#print axioms QuarticMaxwell.FixedPatternContrast.denominatorError_nonneg
#check @QuarticMaxwell.FixedPatternContrast.state_extinction_forwardWork
#print axioms QuarticMaxwell.FixedPatternContrast.state_extinction_forwardWork
#check @QuarticMaxwell.FixedPatternContrast.state_scattering_difference
#print axioms QuarticMaxwell.FixedPatternContrast.state_scattering_difference
#check @QuarticMaxwell.FixedPatternContrast.contrast_eq_quotient
#print axioms QuarticMaxwell.FixedPatternContrast.contrast_eq_quotient
#check @QuarticMaxwell.FixedPatternContrast.interval_pos
#print axioms QuarticMaxwell.FixedPatternContrast.interval_pos
#check @QuarticMaxwell.FixedPatternContrast.coefficient_moment
#print axioms QuarticMaxwell.FixedPatternContrast.coefficient_moment
#check @QuarticMaxwell.FixedPatternContrast.fixed_pattern_quartic
#print axioms QuarticMaxwell.FixedPatternContrast.fixed_pattern_quartic
#check @QuarticMaxwell.StaticHessian.newtonHessianOperator
#print axioms QuarticMaxwell.StaticHessian.newtonHessianOperator
#check @QuarticMaxwell.StaticHessian.newtonHessianOperator_measurable
#print axioms QuarticMaxwell.StaticHessian.newtonHessianOperator_measurable
#check @QuarticMaxwell.StaticHessian.newtonHessianOperator_apply
#print axioms QuarticMaxwell.StaticHessian.newtonHessianOperator_apply
#check @QuarticMaxwell.StaticHessian.projectionTriple_norm_le
#print axioms QuarticMaxwell.StaticHessian.projectionTriple_norm_le
#check @QuarticMaxwell.StaticHessian.newtonHessianOperator_norm_le
#print axioms QuarticMaxwell.StaticHessian.newtonHessianOperator_norm_le
#check @QuarticMaxwell.StaticHessian.normalizedComplex
#print axioms QuarticMaxwell.StaticHessian.normalizedComplex
#check @QuarticMaxwell.StaticHessian.normalizedComplex_norm
#print axioms QuarticMaxwell.StaticHessian.normalizedComplex_norm
#check @QuarticMaxwell.StaticHessian.normalizedComplex_projection
#print axioms QuarticMaxwell.StaticHessian.normalizedComplex_projection
#check @QuarticMaxwell.StaticHessian.normalizedComplex_difference
#print axioms QuarticMaxwell.StaticHessian.normalizedComplex_difference
#check @QuarticMaxwell.StaticHessian.radialProjection_difference
#print axioms QuarticMaxwell.StaticHessian.radialProjection_difference
#check @QuarticMaxwell.StaticHessian.reciprocal_cube_difference
#print axioms QuarticMaxwell.StaticHessian.reciprocal_cube_difference
#check @QuarticMaxwell.StaticHessian.hessian_scalar_difference
#print axioms QuarticMaxwell.StaticHessian.hessian_scalar_difference
#check @QuarticMaxwell.StaticHessian.newtonHessianOperator_difference
#print axioms QuarticMaxwell.StaticHessian.newtonHessianOperator_difference
#check @QuarticMaxwell.PhysicalDilation.scaleEquiv
#print axioms QuarticMaxwell.PhysicalDilation.scaleEquiv
#check @QuarticMaxwell.PhysicalDilation.scaleEquiv_apply
#print axioms QuarticMaxwell.PhysicalDilation.scaleEquiv_apply
#check @QuarticMaxwell.PhysicalDilation.integral_scale
#print axioms QuarticMaxwell.PhysicalDilation.integral_scale
#check @QuarticMaxwell.PhysicalDilation.memLp_scale
#print axioms QuarticMaxwell.PhysicalDilation.memLp_scale
#check @QuarticMaxwell.PhysicalDilation.locallySquareIntegrable_scale
#print axioms QuarticMaxwell.PhysicalDilation.locallySquareIntegrable_scale
#check @QuarticMaxwell.PhysicalDilation.curl_scale
#print axioms QuarticMaxwell.PhysicalDilation.curl_scale
#check @QuarticMaxwell.PhysicalDilation.bilinear_scale_right
#print axioms QuarticMaxwell.PhysicalDilation.bilinear_scale_right
#check @QuarticMaxwell.PhysicalDilation.bilinear_scale_left
#print axioms QuarticMaxwell.PhysicalDilation.bilinear_scale_left
#check @QuarticMaxwell.PhysicalDilation.weakCurl_scale
#print axioms QuarticMaxwell.PhysicalDilation.weakCurl_scale
#check @QuarticMaxwell.PhysicalDilation.radial_scale
#print axioms QuarticMaxwell.PhysicalDilation.radial_scale
#check @QuarticMaxwell.PhysicalDilation.outgoing_scale
#print axioms QuarticMaxwell.PhysicalDilation.outgoing_scale
#check @QuarticMaxwell.PhysicalDilation.scaled_subset_ball
#print axioms QuarticMaxwell.PhysicalDilation.scaled_subset_ball
#check @QuarticMaxwell.PhysicalDilation.medium
#print axioms QuarticMaxwell.PhysicalDilation.medium
#check @QuarticMaxwell.PhysicalDilation.currentField_scale
#print axioms QuarticMaxwell.PhysicalDilation.currentField_scale
#check @QuarticMaxwell.PhysicalDilation.phase_scale
#print axioms QuarticMaxwell.PhysicalDilation.phase_scale
#check @QuarticMaxwell.PhysicalDilation.incident_scale
#print axioms QuarticMaxwell.PhysicalDilation.incident_scale
#check @QuarticMaxwell.PhysicalDilation.magnetic_scale
#print axioms QuarticMaxwell.PhysicalDilation.magnetic_scale
#check @QuarticMaxwell.PhysicalDilation.factor_scale
#print axioms QuarticMaxwell.PhysicalDilation.factor_scale
#check @QuarticMaxwell.PhysicalDilation.state
#print axioms QuarticMaxwell.PhysicalDilation.state
#check @QuarticMaxwell.PhysicalDilation.setIntegral_inverse_scale
#print axioms QuarticMaxwell.PhysicalDilation.setIntegral_inverse_scale
#check @QuarticMaxwell.PhysicalDilation.absorption_scale
#print axioms QuarticMaxwell.PhysicalDilation.absorption_scale
#check @QuarticMaxwell.PhysicalDilation.extinction_scale
#print axioms QuarticMaxwell.PhysicalDilation.extinction_scale
#check @QuarticMaxwell.PhysicalDilation.absorption_congr
#print axioms QuarticMaxwell.PhysicalDilation.absorption_congr
#check @QuarticMaxwell.PhysicalDilation.extinction_congr
#print axioms QuarticMaxwell.PhysicalDilation.extinction_congr
#check @QuarticMaxwell.PhysicalDilation.state_electric_unique
#print axioms QuarticMaxwell.PhysicalDilation.state_electric_unique
#check @QuarticMaxwell.FixedPatternDilation.contrast_congr
#print axioms QuarticMaxwell.FixedPatternDilation.contrast_congr
#check @QuarticMaxwell.FixedPatternDilation.contrast_scale
#print axioms QuarticMaxwell.FixedPatternDilation.contrast_scale
#check @QuarticMaxwell.FixedPatternDilation.fixed_wavenumber_quartic
#print axioms QuarticMaxwell.FixedPatternDilation.fixed_wavenumber_quartic
#check @QuarticMaxwell.FixedPatternDilation.interval_pos
#print axioms QuarticMaxwell.FixedPatternDilation.interval_pos
#check @QuarticMaxwell.CrossBlockOperator.field
#print axioms QuarticMaxwell.CrossBlockOperator.field
#check @QuarticMaxwell.CrossBlockOperator.kernel_norm_bound
#print axioms QuarticMaxwell.CrossBlockOperator.kernel_norm_bound
#check @QuarticMaxwell.CrossBlockOperator.integrand_aestronglyMeasurable
#print axioms QuarticMaxwell.CrossBlockOperator.integrand_aestronglyMeasurable
#check @QuarticMaxwell.CrossBlockOperator.integrand_memLp
#print axioms QuarticMaxwell.CrossBlockOperator.integrand_memLp
#check @QuarticMaxwell.CrossBlockOperator.integrand_integrable
#print axioms QuarticMaxwell.CrossBlockOperator.integrand_integrable
#check @QuarticMaxwell.CrossBlockOperator.field_aestronglyMeasurable
#print axioms QuarticMaxwell.CrossBlockOperator.field_aestronglyMeasurable
#check @QuarticMaxwell.CrossBlockOperator.field_pointwise_norm
#print axioms QuarticMaxwell.CrossBlockOperator.field_pointwise_norm
#check @QuarticMaxwell.CrossBlockOperator.field_memLp
#print axioms QuarticMaxwell.CrossBlockOperator.field_memLp
#check @QuarticMaxwell.CrossBlockOperator.field_pointwise_square
#print axioms QuarticMaxwell.CrossBlockOperator.field_pointwise_square
#check @QuarticMaxwell.CrossBlockOperator.field_add
#print axioms QuarticMaxwell.CrossBlockOperator.field_add
#check @QuarticMaxwell.CrossBlockOperator.field_smul
#print axioms QuarticMaxwell.CrossBlockOperator.field_smul
#check @QuarticMaxwell.CrossBlockOperator.output
#print axioms QuarticMaxwell.CrossBlockOperator.output
#check @QuarticMaxwell.CrossBlockOperator.output_coe
#print axioms QuarticMaxwell.CrossBlockOperator.output_coe
#check @QuarticMaxwell.CrossBlockOperator.output_add
#print axioms QuarticMaxwell.CrossBlockOperator.output_add
#check @QuarticMaxwell.CrossBlockOperator.output_smul
#print axioms QuarticMaxwell.CrossBlockOperator.output_smul
#check @QuarticMaxwell.CrossBlockOperator.output_norm_sq
#print axioms QuarticMaxwell.CrossBlockOperator.output_norm_sq
#check @QuarticMaxwell.CrossBlockOperator.output_norm
#print axioms QuarticMaxwell.CrossBlockOperator.output_norm
#check @QuarticMaxwell.CrossBlockOperator.linear
#print axioms QuarticMaxwell.CrossBlockOperator.linear
#check @QuarticMaxwell.CrossBlockOperator.operator
#print axioms QuarticMaxwell.CrossBlockOperator.operator
#check @QuarticMaxwell.CrossBlockOperator.operator_norm_le
#print axioms QuarticMaxwell.CrossBlockOperator.operator_norm_le
#check @QuarticMaxwell.CrossBlockOperator.field_eq_full_integral
#print axioms QuarticMaxwell.CrossBlockOperator.field_eq_full_integral
#check @QuarticMaxwell.CrossBlockOperator.operator_coe_on
#print axioms QuarticMaxwell.CrossBlockOperator.operator_coe_on
#check @QuarticMaxwell.BlockResolvent.norm_comp_three_le
#print axioms QuarticMaxwell.BlockResolvent.norm_comp_three_le
#check @QuarticMaxwell.BlockResolvent.identity_of_apply
#print axioms QuarticMaxwell.BlockResolvent.identity_of_apply
#check @QuarticMaxwell.BlockResolvent.difference_identity
#print axioms QuarticMaxwell.BlockResolvent.difference_identity
#check @QuarticMaxwell.BlockResolvent.inverse_norm_le
#print axioms QuarticMaxwell.BlockResolvent.inverse_norm_le
#check @QuarticMaxwell.BlockResolvent.inverse_difference_norm_le
#print axioms QuarticMaxwell.BlockResolvent.inverse_difference_norm_le
#check @QuarticMaxwell.BlockResolvent.inverse_difference_norm_le_of_common_bound
#print axioms QuarticMaxwell.BlockResolvent.inverse_difference_norm_le_of_common_bound
#check @QuarticMaxwell.BlockResolvent.first_order_remainder_identity
#print axioms QuarticMaxwell.BlockResolvent.first_order_remainder_identity
#check @QuarticMaxwell.BlockResolvent.second_order_remainder_norm_le
#print axioms QuarticMaxwell.BlockResolvent.second_order_remainder_norm_le
#check @QuarticMaxwell.BlockResolvent.second_order_remainder_apply_norm_le
#print axioms QuarticMaxwell.BlockResolvent.second_order_remainder_apply_norm_le
#check @QuarticMaxwell.BallAffineMoments.ball_measure_ne_top
#print axioms QuarticMaxwell.BallAffineMoments.ball_measure_ne_top
#check @QuarticMaxwell.BallAffineMoments.sphere_real_inner_square
#print axioms QuarticMaxwell.BallAffineMoments.sphere_real_inner_square
#check @QuarticMaxwell.BallAffineMoments.radial_second_moment
#print axioms QuarticMaxwell.BallAffineMoments.radial_second_moment
#check @QuarticMaxwell.BallAffineMoments.ball_zero_inner_square
#print axioms QuarticMaxwell.BallAffineMoments.ball_zero_inner_square
#check @QuarticMaxwell.BallAffineMoments.ball_zero_inner_mean
#print axioms QuarticMaxwell.BallAffineMoments.ball_zero_inner_mean
#check @QuarticMaxwell.BallAffineMoments.ball_translate_integral
#print axioms QuarticMaxwell.BallAffineMoments.ball_translate_integral
#check @QuarticMaxwell.BallAffineMoments.ball_volume
#print axioms QuarticMaxwell.BallAffineMoments.ball_volume
#check @QuarticMaxwell.BallAffineMoments.ball_inner_square
#print axioms QuarticMaxwell.BallAffineMoments.ball_inner_square
#check @QuarticMaxwell.BallAffineMoments.ball_inner_mean
#print axioms QuarticMaxwell.BallAffineMoments.ball_inner_mean
#check @QuarticMaxwell.BallAffineMoments.ball_zero_norm_square
#print axioms QuarticMaxwell.BallAffineMoments.ball_zero_norm_square
#check @QuarticMaxwell.BallAffineMoments.ball_norm_square
#print axioms QuarticMaxwell.BallAffineMoments.ball_norm_square
#check @QuarticMaxwell.BallAffineMoments.weighted_current_norm_integral
#print axioms QuarticMaxwell.BallAffineMoments.weighted_current_norm_integral
#check @QuarticMaxwell.BallAffineMoments.centered_bound
#print axioms QuarticMaxwell.BallAffineMoments.centered_bound
#check @QuarticMaxwell.BallAffineMoments.oddSource
#print axioms QuarticMaxwell.BallAffineMoments.oddSource
#check @QuarticMaxwell.BallAffineMoments.oddSource_coe
#print axioms QuarticMaxwell.BallAffineMoments.oddSource_coe
#check @QuarticMaxwell.BallAffineMoments.oddSource_integral
#print axioms QuarticMaxwell.BallAffineMoments.oddSource_integral
#check @QuarticMaxwell.BallAffineMoments.oddSource_norm_sq
#print axioms QuarticMaxwell.BallAffineMoments.oddSource_norm_sq
#check @QuarticMaxwell.BallAffineMoments.oddSource_norm
#print axioms QuarticMaxwell.BallAffineMoments.oddSource_norm
#check @QuarticMaxwell.BallAffineMoments.oddResponse_norm
#print axioms QuarticMaxwell.BallAffineMoments.oddResponse_norm
#check @QuarticMaxwell.BallAffineMoments.weighted_current_from_norm_bound
#print axioms QuarticMaxwell.BallAffineMoments.weighted_current_from_norm_bound
#check @QuarticMaxwell.BallAffineMoments.affineSource_decomposition
#print axioms QuarticMaxwell.BallAffineMoments.affineSource_decomposition
#check @QuarticMaxwell.SphereNewton.shellRadicand
#print axioms QuarticMaxwell.SphereNewton.shellRadicand
#check @QuarticMaxwell.SphereNewton.shellIntegrand
#print axioms QuarticMaxwell.SphereNewton.shellIntegrand
#check @QuarticMaxwell.SphereNewton.shellPrimitive
#print axioms QuarticMaxwell.SphereNewton.shellPrimitive
#check @QuarticMaxwell.SphereNewton.shellRadicand_pos
#print axioms QuarticMaxwell.SphereNewton.shellRadicand_pos
#check @QuarticMaxwell.SphereNewton.shellPrimitive_derivative
#print axioms QuarticMaxwell.SphereNewton.shellPrimitive_derivative
#check @QuarticMaxwell.SphereNewton.shellIntegrand_continuous
#print axioms QuarticMaxwell.SphereNewton.shellIntegrand_continuous
#check @QuarticMaxwell.SphereNewton.angular_shell_integral
#print axioms QuarticMaxwell.SphereNewton.angular_shell_integral
#check @QuarticMaxwell.SphereNewton.angular_shell_inner
#print axioms QuarticMaxwell.SphereNewton.angular_shell_inner
#check @QuarticMaxwell.SphereNewton.angular_shell_outer
#print axioms QuarticMaxwell.SphereNewton.angular_shell_outer
#check @QuarticMaxwell.SphereNewton.integrable_spherical_actual
#print axioms QuarticMaxwell.SphereNewton.integrable_spherical_actual
#check @QuarticMaxwell.SphereNewton.spherical_integral_iterated
#print axioms QuarticMaxwell.SphereNewton.spherical_integral_iterated
#check @QuarticMaxwell.SphereNewton.spherical_axis_distance
#print axioms QuarticMaxwell.SphereNewton.spherical_axis_distance
#check @QuarticMaxwell.SphereNewton.radialIntegrand
#print axioms QuarticMaxwell.SphereNewton.radialIntegrand
#check @QuarticMaxwell.SphereNewton.radialPotential
#print axioms QuarticMaxwell.SphereNewton.radialPotential
#check @QuarticMaxwell.SphereNewton.radialIntegrand_continuous
#print axioms QuarticMaxwell.SphereNewton.radialIntegrand_continuous
#check @QuarticMaxwell.SphereNewton.radialPotential_exterior
#print axioms QuarticMaxwell.SphereNewton.radialPotential_exterior
#check @QuarticMaxwell.SphereNewton.radialPotential_zero
#print axioms QuarticMaxwell.SphereNewton.radialPotential_zero
#check @QuarticMaxwell.SphereNewton.radialPotential_interior
#print axioms QuarticMaxwell.SphereNewton.radialPotential_interior
#check @QuarticMaxwell.SphereNewton.angular_shell_max
#print axioms QuarticMaxwell.SphereNewton.angular_shell_max
#check @QuarticMaxwell.SphereNewton.angular_set_integral
#print axioms QuarticMaxwell.SphereNewton.angular_set_integral
#check @QuarticMaxwell.SphereNewton.azimuth_constant_integral
#print axioms QuarticMaxwell.SphereNewton.azimuth_constant_integral
#check @QuarticMaxwell.SphereNewton.ballNewtonPotential
#print axioms QuarticMaxwell.SphereNewton.ballNewtonPotential
#check @QuarticMaxwell.SphereNewton.ballNewton_axis
#print axioms QuarticMaxwell.SphereNewton.ballNewton_axis
#check @QuarticMaxwell.SphereNewton.ballNewtonPotential_orthogonal
#print axioms QuarticMaxwell.SphereNewton.ballNewtonPotential_orthogonal
#check @QuarticMaxwell.SphereNewton.ballNewton_radial
#print axioms QuarticMaxwell.SphereNewton.ballNewton_radial
#check @QuarticMaxwell.SphereNewton.ballNewton_interior
#print axioms QuarticMaxwell.SphereNewton.ballNewton_interior
#check @QuarticMaxwell.SphereNewton.ballNewton_exterior
#print axioms QuarticMaxwell.SphereNewton.ballNewton_exterior
#check @QuarticMaxwell.SphereStatic.zDirection
#print axioms QuarticMaxwell.SphereStatic.zDirection
#check @QuarticMaxwell.SphereStatic.ball_measure_ne_top
#print axioms QuarticMaxwell.SphereStatic.ball_measure_ne_top
#check @QuarticMaxwell.SphereStatic.ballSource
#print axioms QuarticMaxwell.SphereStatic.ballSource
#check @QuarticMaxwell.SphereStatic.ballSource_coe
#print axioms QuarticMaxwell.SphereStatic.ballSource_coe
#check @QuarticMaxwell.SphereStatic.ball_support_bound
#print axioms QuarticMaxwell.SphereStatic.ball_support_bound
#check @QuarticMaxwell.SphereStatic.ballPolarization
#print axioms QuarticMaxwell.SphereStatic.ballPolarization
#check @QuarticMaxwell.SphereStatic.ballPolarization_current
#print axioms QuarticMaxwell.SphereStatic.ballPolarization_current
#check @QuarticMaxwell.SphereStatic.shiftedNewtonPotential
#print axioms QuarticMaxwell.SphereStatic.shiftedNewtonPotential
#check @QuarticMaxwell.SphereStatic.shiftedNewtonPotential_eq
#print axioms QuarticMaxwell.SphereStatic.shiftedNewtonPotential_eq
#check @QuarticMaxwell.SphereStatic.outgoingPotential_ball
#print axioms QuarticMaxwell.SphereStatic.outgoingPotential_ball
#check @QuarticMaxwell.SphereStatic.interiorPotential
#print axioms QuarticMaxwell.SphereStatic.interiorPotential
#check @QuarticMaxwell.SphereStatic.interiorPotential_contDiff
#print axioms QuarticMaxwell.SphereStatic.interiorPotential_contDiff
#check @QuarticMaxwell.SphereStatic.interiorPotential_hasLineDerivAt
#print axioms QuarticMaxwell.SphereStatic.interiorPotential_hasLineDerivAt
#check @QuarticMaxwell.SphereStatic.interiorPotential_lineDeriv
#print axioms QuarticMaxwell.SphereStatic.interiorPotential_lineDeriv
#check @QuarticMaxwell.SphereStatic.interiorGradient
#print axioms QuarticMaxwell.SphereStatic.interiorGradient
#check @QuarticMaxwell.SphereStatic.interiorGradient_contDiff
#print axioms QuarticMaxwell.SphereStatic.interiorGradient_contDiff
#check @QuarticMaxwell.SphereStatic.interiorGradient_lineDeriv
#print axioms QuarticMaxwell.SphereStatic.interiorGradient_lineDeriv
#check @QuarticMaxwell.SphereStatic.testPartial_tsupport
#print axioms QuarticMaxwell.SphereStatic.testPartial_tsupport
#check @QuarticMaxwell.SphereStatic.interiorPotential_test_second
#print axioms QuarticMaxwell.SphereStatic.interiorPotential_test_second
#check @QuarticMaxwell.SphereStatic.outgoingPotential_ball_interior
#print axioms QuarticMaxwell.SphereStatic.outgoingPotential_ball_interior
#check @QuarticMaxwell.SphereStatic.potentialPairing_ball
#print axioms QuarticMaxwell.SphereStatic.potentialPairing_ball
#check @QuarticMaxwell.SphereStatic.outgoingVolume_ball_test
#print axioms QuarticMaxwell.SphereStatic.outgoingVolume_ball_test
#check @QuarticMaxwell.SphereStatic.staticFourier_ball_test
#print axioms QuarticMaxwell.SphereStatic.staticFourier_ball_test
#check @QuarticMaxwell.SphereStatic.staticFourier_ball_interior
#print axioms QuarticMaxwell.SphereStatic.staticFourier_ball_interior
#check @QuarticMaxwell.SphereStatic.domainStatic_ballSource
#print axioms QuarticMaxwell.SphereStatic.domainStatic_ballSource
#check @QuarticMaxwell.SphereResponse.scalarSusceptibility
#print axioms QuarticMaxwell.SphereResponse.scalarSusceptibility
#check @QuarticMaxwell.SphereResponse.scalar_measurable
#print axioms QuarticMaxwell.SphereResponse.scalar_measurable
#check @QuarticMaxwell.SphereResponse.scalar_cap
#print axioms QuarticMaxwell.SphereResponse.scalar_cap
#check @QuarticMaxwell.SphereResponse.scalar_loss
#print axioms QuarticMaxwell.SphereResponse.scalar_loss
#check @QuarticMaxwell.SphereResponse.scalar_nonzero
#print axioms QuarticMaxwell.SphereResponse.scalar_nonzero
#check @QuarticMaxwell.SphereResponse.scalar_norm_pos
#print axioms QuarticMaxwell.SphereResponse.scalar_norm_pos
#check @QuarticMaxwell.SphereResponse.scalar_operator
#print axioms QuarticMaxwell.SphereResponse.scalar_operator
#check @QuarticMaxwell.SphereResponse.scalar_inverse
#print axioms QuarticMaxwell.SphereResponse.scalar_inverse
#check @QuarticMaxwell.SphereResponse.beta
#print axioms QuarticMaxwell.SphereResponse.beta
#check @QuarticMaxwell.SphereResponse.three_add_nonzero
#print axioms QuarticMaxwell.SphereResponse.three_add_nonzero
#check @QuarticMaxwell.SphereResponse.beta_inverse_identity
#print axioms QuarticMaxwell.SphereResponse.beta_inverse_identity
#check @QuarticMaxwell.SphereResponse.ballEquiv
#print axioms QuarticMaxwell.SphereResponse.ballEquiv
#check @QuarticMaxwell.SphereResponse.ballEquiv_source
#print axioms QuarticMaxwell.SphereResponse.ballEquiv_source
#check @QuarticMaxwell.SphereResponse.ball_inverse_source
#print axioms QuarticMaxwell.SphereResponse.ball_inverse_source
#check @QuarticMaxwell.SphereResponse.ball_volume_real
#print axioms QuarticMaxwell.SphereResponse.ball_volume_real
#check @QuarticMaxwell.SphereResponse.ball_volume_pos
#print axioms QuarticMaxwell.SphereResponse.ball_volume_pos
#check @QuarticMaxwell.SphereResponse.ball_integrable
#print axioms QuarticMaxwell.SphereResponse.ball_integrable
#check @QuarticMaxwell.SphereResponse.ballSource_pairing
#print axioms QuarticMaxwell.SphereResponse.ballSource_pairing
#check @QuarticMaxwell.SphereResponse.scalar_reciprocal
#print axioms QuarticMaxwell.SphereResponse.scalar_reciprocal
#check @QuarticMaxwell.SphereResponse.ball_inverse_mean
#print axioms QuarticMaxwell.SphereResponse.ball_inverse_mean
#check @QuarticMaxwell.StaticOffSupport.test_zero_of_norm_le
#print axioms QuarticMaxwell.StaticOffSupport.test_zero_of_norm_le
#check @QuarticMaxwell.StaticOffSupport.newton_double_ibp_away
#print axioms QuarticMaxwell.StaticOffSupport.newton_double_ibp_away
#check @QuarticMaxwell.StaticOffSupport.exteriorHessianEntry
#print axioms QuarticMaxwell.StaticOffSupport.exteriorHessianEntry
#check @QuarticMaxwell.StaticOffSupport.exteriorHessianEntry_measurable
#print axioms QuarticMaxwell.StaticOffSupport.exteriorHessianEntry_measurable
#check @QuarticMaxwell.StaticOffSupport.exteriorHessianEntry_bound
#print axioms QuarticMaxwell.StaticOffSupport.exteriorHessianEntry_bound
#check @QuarticMaxwell.StaticOffSupport.exteriorHessianEntry_locallyIntegrable
#print axioms QuarticMaxwell.StaticOffSupport.exteriorHessianEntry_locallyIntegrable
#check @QuarticMaxwell.StaticOffSupport.scalarNewton_double_ibp_away
#print axioms QuarticMaxwell.StaticOffSupport.scalarNewton_double_ibp_away
#check @QuarticMaxwell.StaticOffSupport.correlation_zero_near
#print axioms QuarticMaxwell.StaticOffSupport.correlation_zero_near
#check @QuarticMaxwell.StaticOffSupport.correlation_tsupport_separated
#print axioms QuarticMaxwell.StaticOffSupport.correlation_tsupport_separated
#check @QuarticMaxwell.StaticOffSupport.realCorrelation_tsupport_separated
#print axioms QuarticMaxwell.StaticOffSupport.realCorrelation_tsupport_separated
#check @QuarticMaxwell.StaticOffSupport.potentialComponent_separated_hessian
#print axioms QuarticMaxwell.StaticOffSupport.potentialComponent_separated_hessian
#check @QuarticMaxwell.StaticOffSupport.bounded_kernel_test_joint
#print axioms QuarticMaxwell.StaticOffSupport.bounded_kernel_test_joint
#check @QuarticMaxwell.StaticOffSupport.bounded_kernel_correlation_joint
#print axioms QuarticMaxwell.StaticOffSupport.bounded_kernel_correlation_joint
#check @QuarticMaxwell.StaticOffSupport.bounded_kernel_correlation_pairing
#print axioms QuarticMaxwell.StaticOffSupport.bounded_kernel_correlation_pairing
#check @QuarticMaxwell.StaticOffSupport.scalarKernelField
#print axioms QuarticMaxwell.StaticOffSupport.scalarKernelField
#check @QuarticMaxwell.StaticOffSupport.scalarKernelField_integrable
#print axioms QuarticMaxwell.StaticOffSupport.scalarKernelField_integrable
#check @QuarticMaxwell.StaticOffSupport.scalarKernelField_aestronglyMeasurable
#print axioms QuarticMaxwell.StaticOffSupport.scalarKernelField_aestronglyMeasurable
#check @QuarticMaxwell.StaticOffSupport.scalarKernelField_norm_le
#print axioms QuarticMaxwell.StaticOffSupport.scalarKernelField_norm_le
#check @QuarticMaxwell.StaticOffSupport.scalarKernelField_locallyIntegrable
#print axioms QuarticMaxwell.StaticOffSupport.scalarKernelField_locallyIntegrable
#check @QuarticMaxwell.StaticOffSupport.separatedStaticComponent
#print axioms QuarticMaxwell.StaticOffSupport.separatedStaticComponent
#check @QuarticMaxwell.StaticOffSupport.separatedStaticComponent_locallyIntegrable
#print axioms QuarticMaxwell.StaticOffSupport.separatedStaticComponent_locallyIntegrable
#check @QuarticMaxwell.StaticOffSupport.vectorL2ComponentDistribution_integral
#print axioms QuarticMaxwell.StaticOffSupport.vectorL2ComponentDistribution_integral
#check @QuarticMaxwell.StaticOffSupport.staticFourier_test_separated
#print axioms QuarticMaxwell.StaticOffSupport.staticFourier_test_separated
#check @QuarticMaxwell.StaticOffSupport.staticFourier_separated_ae
#print axioms QuarticMaxwell.StaticOffSupport.staticFourier_separated_ae
#check @QuarticMaxwell.StaticOffSupport.exteriorHessian
#print axioms QuarticMaxwell.StaticOffSupport.exteriorHessian
#check @QuarticMaxwell.StaticOffSupport.exteriorHessian_measurable
#print axioms QuarticMaxwell.StaticOffSupport.exteriorHessian_measurable
#check @QuarticMaxwell.StaticOffSupport.exteriorHessian_apply
#print axioms QuarticMaxwell.StaticOffSupport.exteriorHessian_apply
#check @QuarticMaxwell.StaticOffSupport.exteriorHessian_norm_le
#print axioms QuarticMaxwell.StaticOffSupport.exteriorHessian_norm_le
#check @QuarticMaxwell.StaticOffSupport.vectorKernelField
#print axioms QuarticMaxwell.StaticOffSupport.vectorKernelField
#check @QuarticMaxwell.StaticOffSupport.vectorKernelField_integrable
#print axioms QuarticMaxwell.StaticOffSupport.vectorKernelField_integrable
#check @QuarticMaxwell.StaticOffSupport.vectorKernelField_component
#print axioms QuarticMaxwell.StaticOffSupport.vectorKernelField_component
#check @QuarticMaxwell.StaticOffSupport.staticFourier_vector_separated_ae
#print axioms QuarticMaxwell.StaticOffSupport.staticFourier_vector_separated_ae
#check @QuarticMaxwell.StaticCrossIdentification.staticFourier_cross_representation
#print axioms QuarticMaxwell.StaticCrossIdentification.staticFourier_cross_representation
#check @QuarticMaxwell.StaticCrossIdentification.staticCrossBlock
#print axioms QuarticMaxwell.StaticCrossIdentification.staticCrossBlock
#check @QuarticMaxwell.StaticCrossIdentification.staticCrossBlock_eq_kernel
#print axioms QuarticMaxwell.StaticCrossIdentification.staticCrossBlock_eq_kernel
#check @QuarticMaxwell.StaticCrossIdentification.staticCrossBlock_norm_le
#print axioms QuarticMaxwell.StaticCrossIdentification.staticCrossBlock_norm_le
#check @QuarticMaxwell.SupportBlocks.inclusionLinear
#print axioms QuarticMaxwell.SupportBlocks.inclusionLinear
#check @QuarticMaxwell.SupportBlocks.inclusion
#print axioms QuarticMaxwell.SupportBlocks.inclusion
#check @QuarticMaxwell.SupportBlocks.inclusion_coe
#print axioms QuarticMaxwell.SupportBlocks.inclusion_coe
#check @QuarticMaxwell.SupportBlocks.inclusion_norm
#print axioms QuarticMaxwell.SupportBlocks.inclusion_norm
#check @QuarticMaxwell.SupportBlocks.restriction
#print axioms QuarticMaxwell.SupportBlocks.restriction
#check @QuarticMaxwell.SupportBlocks.restriction_coe
#print axioms QuarticMaxwell.SupportBlocks.restriction_coe
#check @QuarticMaxwell.SupportBlocks.restriction_inclusion
#print axioms QuarticMaxwell.SupportBlocks.restriction_inclusion
#check @QuarticMaxwell.SupportBlocks.disjoint_inner
#print axioms QuarticMaxwell.SupportBlocks.disjoint_inner
#check @QuarticMaxwell.SupportBlocks.restriction_other
#print axioms QuarticMaxwell.SupportBlocks.restriction_other
#check @QuarticMaxwell.SupportBlocks.injectLeft
#print axioms QuarticMaxwell.SupportBlocks.injectLeft
#check @QuarticMaxwell.SupportBlocks.injectRight
#print axioms QuarticMaxwell.SupportBlocks.injectRight
#check @QuarticMaxwell.SupportBlocks.projectLeft
#print axioms QuarticMaxwell.SupportBlocks.projectLeft
#check @QuarticMaxwell.SupportBlocks.projectRight
#print axioms QuarticMaxwell.SupportBlocks.projectRight
#check @QuarticMaxwell.SupportBlocks.support_decomposition
#print axioms QuarticMaxwell.SupportBlocks.support_decomposition
#check @QuarticMaxwell.SupportBlocks.joined_norm_sq
#print axioms QuarticMaxwell.SupportBlocks.joined_norm_sq
#check @QuarticMaxwell.SupportBlocks.split_norm_sq
#print axioms QuarticMaxwell.SupportBlocks.split_norm_sq
#check @QuarticMaxwell.SupportBlocks.diagonal
#print axioms QuarticMaxwell.SupportBlocks.diagonal
#check @QuarticMaxwell.SupportBlocks.offDiagonal
#print axioms QuarticMaxwell.SupportBlocks.offDiagonal
#check @QuarticMaxwell.SupportBlocks.diagonal_norm_le
#print axioms QuarticMaxwell.SupportBlocks.diagonal_norm_le
#check @QuarticMaxwell.SupportBlocks.offDiagonal_norm_le
#print axioms QuarticMaxwell.SupportBlocks.offDiagonal_norm_le
#check @QuarticMaxwell.SupportBlocks.projectLeft_injectLeft
#print axioms QuarticMaxwell.SupportBlocks.projectLeft_injectLeft
#check @QuarticMaxwell.SupportBlocks.projectRight_injectRight
#print axioms QuarticMaxwell.SupportBlocks.projectRight_injectRight
#check @QuarticMaxwell.SupportBlocks.projectLeft_injectRight
#print axioms QuarticMaxwell.SupportBlocks.projectLeft_injectRight
#check @QuarticMaxwell.SupportBlocks.projectRight_injectLeft
#print axioms QuarticMaxwell.SupportBlocks.projectRight_injectLeft
#check @QuarticMaxwell.SupportBlocks.component_ext
#print axioms QuarticMaxwell.SupportBlocks.component_ext
#check @QuarticMaxwell.SupportBlocks.projectLeft_diagonal
#print axioms QuarticMaxwell.SupportBlocks.projectLeft_diagonal
#check @QuarticMaxwell.SupportBlocks.projectRight_diagonal
#print axioms QuarticMaxwell.SupportBlocks.projectRight_diagonal
#check @QuarticMaxwell.SupportBlocks.projectLeft_offDiagonal
#print axioms QuarticMaxwell.SupportBlocks.projectLeft_offDiagonal
#check @QuarticMaxwell.SupportBlocks.projectRight_offDiagonal
#print axioms QuarticMaxwell.SupportBlocks.projectRight_offDiagonal
#check @QuarticMaxwell.SupportBlocks.diagonal_inverse_cancel
#print axioms QuarticMaxwell.SupportBlocks.diagonal_inverse_cancel
#check @QuarticMaxwell.TwoSupportStatic.indicatorL2_nested_subset
#print axioms QuarticMaxwell.TwoSupportStatic.indicatorL2_nested_subset
#check @QuarticMaxwell.TwoSupportStatic.ScalarPair.cap
#print axioms QuarticMaxwell.TwoSupportStatic.ScalarPair.cap
#check @QuarticMaxwell.TwoSupportStatic.ScalarPair.loss
#print axioms QuarticMaxwell.TwoSupportStatic.ScalarPair.loss
#check @QuarticMaxwell.TwoSupportStatic.ScalarPair.cap_pos
#print axioms QuarticMaxwell.TwoSupportStatic.ScalarPair.cap_pos
#check @QuarticMaxwell.TwoSupportStatic.ScalarPair.loss_pos
#print axioms QuarticMaxwell.TwoSupportStatic.ScalarPair.loss_pos
#check @QuarticMaxwell.TwoSupportStatic.susceptibility
#print axioms QuarticMaxwell.TwoSupportStatic.susceptibility
#check @QuarticMaxwell.TwoSupportStatic.susceptibility_measurable
#print axioms QuarticMaxwell.TwoSupportStatic.susceptibility_measurable
#check @QuarticMaxwell.TwoSupportStatic.susceptibility_cap
#print axioms QuarticMaxwell.TwoSupportStatic.susceptibility_cap
#check @QuarticMaxwell.TwoSupportStatic.susceptibility_loss
#print axioms QuarticMaxwell.TwoSupportStatic.susceptibility_loss
#check @QuarticMaxwell.TwoSupportStatic.equiv
#print axioms QuarticMaxwell.TwoSupportStatic.equiv
#check @QuarticMaxwell.TwoSupportStatic.isolatedEquiv
#print axioms QuarticMaxwell.TwoSupportStatic.isolatedEquiv
#check @QuarticMaxwell.TwoSupportStatic.inverseMaterial
#print axioms QuarticMaxwell.TwoSupportStatic.inverseMaterial
#check @QuarticMaxwell.TwoSupportStatic.inverseMaterial_left
#print axioms QuarticMaxwell.TwoSupportStatic.inverseMaterial_left
#check @QuarticMaxwell.TwoSupportStatic.inverseMaterial_right
#print axioms QuarticMaxwell.TwoSupportStatic.inverseMaterial_right
#check @QuarticMaxwell.TwoSupportStatic.staticCrossBlock_self
#print axioms QuarticMaxwell.TwoSupportStatic.staticCrossBlock_self
#check @QuarticMaxwell.TwoSupportStatic.staticCrossBlock_union_split
#print axioms QuarticMaxwell.TwoSupportStatic.staticCrossBlock_union_split
#check @QuarticMaxwell.TwoSupportStatic.projectLeft_domainStatic
#print axioms QuarticMaxwell.TwoSupportStatic.projectLeft_domainStatic
#check @QuarticMaxwell.TwoSupportStatic.projectRight_domainStatic
#print axioms QuarticMaxwell.TwoSupportStatic.projectRight_domainStatic
#check @QuarticMaxwell.TwoSupportStatic.isolatedEquiv_apply
#print axioms QuarticMaxwell.TwoSupportStatic.isolatedEquiv_apply
#check @QuarticMaxwell.TwoSupportStatic.equiv_apply
#print axioms QuarticMaxwell.TwoSupportStatic.equiv_apply
#check @QuarticMaxwell.TwoSupportStatic.left_block_equation
#print axioms QuarticMaxwell.TwoSupportStatic.left_block_equation
#check @QuarticMaxwell.TwoSupportStatic.right_block_equation
#print axioms QuarticMaxwell.TwoSupportStatic.right_block_equation
#check @QuarticMaxwell.TwoSupportStatic.blockInverse
#print axioms QuarticMaxwell.TwoSupportStatic.blockInverse
#check @QuarticMaxwell.TwoSupportStatic.interaction
#print axioms QuarticMaxwell.TwoSupportStatic.interaction
#check @QuarticMaxwell.TwoSupportStatic.assembled_equation
#print axioms QuarticMaxwell.TwoSupportStatic.assembled_equation
#check @QuarticMaxwell.TwoSupportStatic.inverse_interaction_identity
#print axioms QuarticMaxwell.TwoSupportStatic.inverse_interaction_identity
#check @QuarticMaxwell.TwoSupportBounds.crossBound
#print axioms QuarticMaxwell.TwoSupportBounds.crossBound
#check @QuarticMaxwell.TwoSupportBounds.crossBound_nonneg
#print axioms QuarticMaxwell.TwoSupportBounds.crossBound_nonneg
#check @QuarticMaxwell.TwoSupportBounds.gap_disjoint
#print axioms QuarticMaxwell.TwoSupportBounds.gap_disjoint
#check @QuarticMaxwell.TwoSupportBounds.interaction_norm_le
#print axioms QuarticMaxwell.TwoSupportBounds.interaction_norm_le
#check @QuarticMaxwell.TwoSupportBounds.isolatedRho
#print axioms QuarticMaxwell.TwoSupportBounds.isolatedRho
#check @QuarticMaxwell.TwoSupportBounds.isolatedRho_pos
#print axioms QuarticMaxwell.TwoSupportBounds.isolatedRho_pos
#check @QuarticMaxwell.TwoSupportBounds.isolatedEquiv_inverse_norm_le
#print axioms QuarticMaxwell.TwoSupportBounds.isolatedEquiv_inverse_norm_le
#check @QuarticMaxwell.TwoSupportBounds.blockInverse_norm_le
#print axioms QuarticMaxwell.TwoSupportBounds.blockInverse_norm_le
#check @QuarticMaxwell.TwoSupportBounds.response
#print axioms QuarticMaxwell.TwoSupportBounds.response
#check @QuarticMaxwell.TwoSupportBounds.response_identity
#print axioms QuarticMaxwell.TwoSupportBounds.response_identity
#check @QuarticMaxwell.TwoSupportBounds.response_norm_le
#print axioms QuarticMaxwell.TwoSupportBounds.response_norm_le
#check @QuarticMaxwell.TwoSupportBounds.response_difference_norm_le
#print axioms QuarticMaxwell.TwoSupportBounds.response_difference_norm_le
#check @QuarticMaxwell.TwoSupportBounds.response_resource_norm_le
#print axioms QuarticMaxwell.TwoSupportBounds.response_resource_norm_le
#check @QuarticMaxwell.TwoSupportBounds.homogeneousPair
#print axioms QuarticMaxwell.TwoSupportBounds.homogeneousPair
#check @QuarticMaxwell.TwoSupportBounds.homogeneous_cap
#print axioms QuarticMaxwell.TwoSupportBounds.homogeneous_cap
#check @QuarticMaxwell.TwoSupportBounds.homogeneous_loss
#print axioms QuarticMaxwell.TwoSupportBounds.homogeneous_loss
#check @QuarticMaxwell.TwoSupportBounds.homogeneous_isolatedRho
#print axioms QuarticMaxwell.TwoSupportBounds.homogeneous_isolatedRho
#check @QuarticMaxwell.TwoSupportBounds.homogeneous_remainder
#print axioms QuarticMaxwell.TwoSupportBounds.homogeneous_remainder
#check @QuarticMaxwell.TwoSphereGeometry.leftCenter
#print axioms QuarticMaxwell.TwoSphereGeometry.leftCenter
#check @QuarticMaxwell.TwoSphereGeometry.rightCenter
#print axioms QuarticMaxwell.TwoSphereGeometry.rightCenter
#check @QuarticMaxwell.TwoSphereGeometry.leftBall
#print axioms QuarticMaxwell.TwoSphereGeometry.leftBall
#check @QuarticMaxwell.TwoSphereGeometry.rightBall
#print axioms QuarticMaxwell.TwoSphereGeometry.rightBall
#check @QuarticMaxwell.TwoSphereGeometry.domain
#print axioms QuarticMaxwell.TwoSphereGeometry.domain
#check @QuarticMaxwell.TwoSphereGeometry.gap
#print axioms QuarticMaxwell.TwoSphereGeometry.gap
#check @QuarticMaxwell.TwoSphereGeometry.leftCenter_norm
#print axioms QuarticMaxwell.TwoSphereGeometry.leftCenter_norm
#check @QuarticMaxwell.TwoSphereGeometry.rightCenter_norm
#print axioms QuarticMaxwell.TwoSphereGeometry.rightCenter_norm
#check @QuarticMaxwell.TwoSphereGeometry.center_distance
#print axioms QuarticMaxwell.TwoSphereGeometry.center_distance
#check @QuarticMaxwell.TwoSphereGeometry.gap_pos
#print axioms QuarticMaxwell.TwoSphereGeometry.gap_pos
#check @QuarticMaxwell.TwoSphereGeometry.sphere_separation
#print axioms QuarticMaxwell.TwoSphereGeometry.sphere_separation
#check @QuarticMaxwell.TwoSphereGeometry.sphere_disjoint
#print axioms QuarticMaxwell.TwoSphereGeometry.sphere_disjoint
#check @QuarticMaxwell.TwoSphereGeometry.left_subset
#print axioms QuarticMaxwell.TwoSphereGeometry.left_subset
#check @QuarticMaxwell.TwoSphereGeometry.right_subset
#print axioms QuarticMaxwell.TwoSphereGeometry.right_subset
#check @QuarticMaxwell.TwoSphereGeometry.domain_subset
#print axioms QuarticMaxwell.TwoSphereGeometry.domain_subset
#check @QuarticMaxwell.TwoSphereGeometry.domain_finite
#print axioms QuarticMaxwell.TwoSphereGeometry.domain_finite
#check @QuarticMaxwell.TwoSphereGeometry.left_volume
#print axioms QuarticMaxwell.TwoSphereGeometry.left_volume
#check @QuarticMaxwell.TwoSphereGeometry.right_volume
#print axioms QuarticMaxwell.TwoSphereGeometry.right_volume
#check @QuarticMaxwell.TwoSphereGeometry.domain_volume
#print axioms QuarticMaxwell.TwoSphereGeometry.domain_volume
#check @QuarticMaxwell.TwoSphereGeometry.crossBound_formula
#print axioms QuarticMaxwell.TwoSphereGeometry.crossBound_formula
#check @QuarticMaxwell.TwoSphereGeometry.heterogeneous
#print axioms QuarticMaxwell.TwoSphereGeometry.heterogeneous
#check @QuarticMaxwell.TwoSphereGeometry.heterogeneous_rho
#print axioms QuarticMaxwell.TwoSphereGeometry.heterogeneous_rho
#check @QuarticMaxwell.TwoSphereGeometry.fixed_coupling
#print axioms QuarticMaxwell.TwoSphereGeometry.fixed_coupling
#check @QuarticMaxwell.TwoSphereGeometry.fixed_static_difference
#print axioms QuarticMaxwell.TwoSphereGeometry.fixed_static_difference
#check @QuarticMaxwell.TwoSphereGeometry.medium
#print axioms QuarticMaxwell.TwoSphereGeometry.medium
#check @QuarticMaxwell.TwoSphereGeometry.response_eq_staticResponse
#print axioms QuarticMaxwell.TwoSphereGeometry.response_eq_staticResponse
#check @QuarticMaxwell.TwoSphereGeometry.medium_volume
#print axioms QuarticMaxwell.TwoSphereGeometry.medium_volume
#check @QuarticMaxwell.TwoSphereGeometry.medium_volume_pos
#print axioms QuarticMaxwell.TwoSphereGeometry.medium_volume_pos
#check @QuarticMaxwell.TwoSphereGeometry.medium_reciprocal
#print axioms QuarticMaxwell.TwoSphereGeometry.medium_reciprocal
#check @QuarticMaxwell.SphereExterior.translateTest
#print axioms QuarticMaxwell.SphereExterior.translateTest
#check @QuarticMaxwell.SphereExterior.translateTest_partial
#print axioms QuarticMaxwell.SphereExterior.translateTest_partial
#check @QuarticMaxwell.SphereExterior.translateTest_support
#print axioms QuarticMaxwell.SphereExterior.translateTest_support
#check @QuarticMaxwell.SphereExterior.newton_shifted_double_ibp
#print axioms QuarticMaxwell.SphereExterior.newton_shifted_double_ibp
#check @QuarticMaxwell.SphereExterior.ballVolume
#print axioms QuarticMaxwell.SphereExterior.ballVolume
#check @QuarticMaxwell.SphereExterior.ballVolume_eq_measure
#print axioms QuarticMaxwell.SphereExterior.ballVolume_eq_measure
#check @QuarticMaxwell.SphereExterior.potential_ball_exterior
#print axioms QuarticMaxwell.SphereExterior.potential_ball_exterior
#check @QuarticMaxwell.SphereExterior.potentialPairing_ball_exterior
#print axioms QuarticMaxwell.SphereExterior.potentialPairing_ball_exterior
#check @QuarticMaxwell.SphereExterior.exteriorField
#print axioms QuarticMaxwell.SphereExterior.exteriorField
#check @QuarticMaxwell.SphereExterior.exteriorEntry_test_integrable
#print axioms QuarticMaxwell.SphereExterior.exteriorEntry_test_integrable
#check @QuarticMaxwell.SphereExterior.hessianEntry_test_eq
#print axioms QuarticMaxwell.SphereExterior.hessianEntry_test_eq
#check @QuarticMaxwell.SphereExterior.outgoingVolume_ball_exterior_test
#print axioms QuarticMaxwell.SphereExterior.outgoingVolume_ball_exterior_test
#check @QuarticMaxwell.SphereExterior.exteriorField_measurable
#print axioms QuarticMaxwell.SphereExterior.exteriorField_measurable
#check @QuarticMaxwell.SphereExterior.exteriorField_norm_le
#print axioms QuarticMaxwell.SphereExterior.exteriorField_norm_le
#check @QuarticMaxwell.SphereExterior.exteriorField_locallyIntegrable
#print axioms QuarticMaxwell.SphereExterior.exteriorField_locallyIntegrable
#check @QuarticMaxwell.SphereExterior.staticFourier_ball_exterior_test
#print axioms QuarticMaxwell.SphereExterior.staticFourier_ball_exterior_test
#check @QuarticMaxwell.SphereExterior.staticFourier_ball_exterior_ae
#print axioms QuarticMaxwell.SphereExterior.staticFourier_ball_exterior_ae
#check @QuarticMaxwell.SphereHessianMean.hessian_continuousAt
#print axioms QuarticMaxwell.SphereHessianMean.hessian_continuousAt
#check @QuarticMaxwell.SphereHessianMean.ballHessian
#print axioms QuarticMaxwell.SphereHessianMean.ballHessian
#check @QuarticMaxwell.SphereHessianMean.ball_separation
#print axioms QuarticMaxwell.SphereHessianMean.ball_separation
#check @QuarticMaxwell.SphereHessianMean.ballHessian_continuousOn
#print axioms QuarticMaxwell.SphereHessianMean.ballHessian_continuousOn
#check @QuarticMaxwell.SphereHessianMean.vectorKernelField_ball
#print axioms QuarticMaxwell.SphereHessianMean.vectorKernelField_ball
#check @QuarticMaxwell.SphereDoubleMean.ball_mean
#print axioms QuarticMaxwell.SphereDoubleMean.ball_mean
#check @QuarticMaxwell.SphereDoubleMean.hessian_even
#print axioms QuarticMaxwell.SphereDoubleMean.hessian_even
#check @QuarticMaxwell.SphereDoubleMean.ball_mean_reverse
#print axioms QuarticMaxwell.SphereDoubleMean.ball_mean_reverse
#check @QuarticMaxwell.SphereDoubleMean.double_ball_mean
#print axioms QuarticMaxwell.SphereDoubleMean.double_ball_mean
#check @QuarticMaxwell.MomentOperator.norm_le
#print axioms QuarticMaxwell.MomentOperator.norm_le
#check @QuarticMaxwell.MomentOperator.map
#print axioms QuarticMaxwell.MomentOperator.map
#check @QuarticMaxwell.MomentOperator.map_norm_le
#print axioms QuarticMaxwell.MomentOperator.map_norm_le
#check @QuarticMaxwell.MomentOperator.map_apply
#print axioms QuarticMaxwell.MomentOperator.map_apply
#check @QuarticMaxwell.MomentOperator.full_integral
#print axioms QuarticMaxwell.MomentOperator.full_integral
#check @QuarticMaxwell.MomentOperator.response_difference_norm_le
#print axioms QuarticMaxwell.MomentOperator.response_difference_norm_le
#check @QuarticMaxwell.BlockSourceMoments.union_finite
#print axioms QuarticMaxwell.BlockSourceMoments.union_finite
#check @QuarticMaxwell.BlockSourceMoments.restriction_constantSource
#print axioms QuarticMaxwell.BlockSourceMoments.restriction_constantSource
#check @QuarticMaxwell.BlockSourceMoments.restriction_momentSource
#print axioms QuarticMaxwell.BlockSourceMoments.restriction_momentSource
#check @QuarticMaxwell.BlockSourceMoments.moment_constantSource
#print axioms QuarticMaxwell.BlockSourceMoments.moment_constantSource
#check @QuarticMaxwell.BlockSourceMoments.moment_inclusion
#print axioms QuarticMaxwell.BlockSourceMoments.moment_inclusion
#check @QuarticMaxwell.BlockSourceMoments.ball_inverse_moment
#print axioms QuarticMaxwell.BlockSourceMoments.ball_inverse_moment
#check @QuarticMaxwell.BlockSourceMoments.moment_ball_affine
#print axioms QuarticMaxwell.BlockSourceMoments.moment_ball_affine
#check @QuarticMaxwell.BlockSourceMoments.joined
#print axioms QuarticMaxwell.BlockSourceMoments.joined
#check @QuarticMaxwell.BlockSourceMoments.joined_finite
#print axioms QuarticMaxwell.BlockSourceMoments.joined_finite
#check @QuarticMaxwell.BlockSourceMoments.moment_blockInverse
#print axioms QuarticMaxwell.BlockSourceMoments.moment_blockInverse
#check @QuarticMaxwell.BlockSourceMoments.moment_blockInverse_constant
#print axioms QuarticMaxwell.BlockSourceMoments.moment_blockInverse_constant
#check @QuarticMaxwell.BlockSourceMoments.moment_blockInverse_affine
#print axioms QuarticMaxwell.BlockSourceMoments.moment_blockInverse_affine
#check @QuarticMaxwell.quartic_quotient_error_of_lower_bound
#print axioms QuarticMaxwell.quartic_quotient_error_of_lower_bound
#check @QuarticMaxwell.HeterogeneousCertificate.body
#print axioms QuarticMaxwell.HeterogeneousCertificate.body
#check @QuarticMaxwell.HeterogeneousCertificate.volume
#print axioms QuarticMaxwell.HeterogeneousCertificate.volume
#check @QuarticMaxwell.HeterogeneousCertificate.isolated
#print axioms QuarticMaxwell.HeterogeneousCertificate.isolated
#check @QuarticMaxwell.HeterogeneousCertificate.isolatedMoment0
#print axioms QuarticMaxwell.HeterogeneousCertificate.isolatedMoment0
#check @QuarticMaxwell.HeterogeneousCertificate.isolatedMoment1
#print axioms QuarticMaxwell.HeterogeneousCertificate.isolatedMoment1
#check @QuarticMaxwell.HeterogeneousCertificate.volume_eq
#print axioms QuarticMaxwell.HeterogeneousCertificate.volume_eq
#check @QuarticMaxwell.HeterogeneousCertificate.volume_pos
#print axioms QuarticMaxwell.HeterogeneousCertificate.volume_pos
#check @QuarticMaxwell.HeterogeneousCertificate.static_difference
#print axioms QuarticMaxwell.HeterogeneousCertificate.static_difference
#check @QuarticMaxwell.HeterogeneousCertificate.isolated_norm
#print axioms QuarticMaxwell.HeterogeneousCertificate.isolated_norm
#check @QuarticMaxwell.HeterogeneousCertificate.constant_norm_sq
#print axioms QuarticMaxwell.HeterogeneousCertificate.constant_norm_sq
#check @QuarticMaxwell.HeterogeneousCertificate.constant_norm
#print axioms QuarticMaxwell.HeterogeneousCertificate.constant_norm
#check @QuarticMaxwell.HeterogeneousCertificate.linear_norm
#print axioms QuarticMaxwell.HeterogeneousCertificate.linear_norm
#check @QuarticMaxwell.HeterogeneousCertificate.moment_norm
#print axioms QuarticMaxwell.HeterogeneousCertificate.moment_norm
#check @QuarticMaxwell.HeterogeneousCertificate.isolatedMoment0_norm
#print axioms QuarticMaxwell.HeterogeneousCertificate.isolatedMoment0_norm
#check @QuarticMaxwell.HeterogeneousCertificate.isolatedMoment1_norm
#print axioms QuarticMaxwell.HeterogeneousCertificate.isolatedMoment1_norm
#check @QuarticMaxwell.HeterogeneousCertificate.moment0_error
#print axioms QuarticMaxwell.HeterogeneousCertificate.moment0_error
#check @QuarticMaxwell.HeterogeneousCertificate.moment1_error
#print axioms QuarticMaxwell.HeterogeneousCertificate.moment1_error
#check @QuarticMaxwell.HeterogeneousCertificate.b0
#print axioms QuarticMaxwell.HeterogeneousCertificate.b0
#check @QuarticMaxwell.HeterogeneousCertificate.b1
#print axioms QuarticMaxwell.HeterogeneousCertificate.b1
#check @QuarticMaxwell.HeterogeneousCertificate.beta_left
#print axioms QuarticMaxwell.HeterogeneousCertificate.beta_left
#check @QuarticMaxwell.HeterogeneousCertificate.beta_right
#print axioms QuarticMaxwell.HeterogeneousCertificate.beta_right
#check @QuarticMaxwell.HeterogeneousCertificate.isolatedMoment0_formula
#print axioms QuarticMaxwell.HeterogeneousCertificate.isolatedMoment0_formula
#check @QuarticMaxwell.HeterogeneousCertificate.direction_leftCenter
#print axioms QuarticMaxwell.HeterogeneousCertificate.direction_leftCenter
#check @QuarticMaxwell.HeterogeneousCertificate.direction_rightCenter
#print axioms QuarticMaxwell.HeterogeneousCertificate.direction_rightCenter
#check @QuarticMaxwell.HeterogeneousCertificate.isolatedMoment1_formula
#print axioms QuarticMaxwell.HeterogeneousCertificate.isolatedMoment1_formula
#check @QuarticMaxwell.HeterogeneousCertificate.I0
#print axioms QuarticMaxwell.HeterogeneousCertificate.I0
#check @QuarticMaxwell.HeterogeneousCertificate.isolated_imaginary_moment
#print axioms QuarticMaxwell.HeterogeneousCertificate.isolated_imaginary_moment
#check @QuarticMaxwell.HeterogeneousCertificate.isolated_extinction
#print axioms QuarticMaxwell.HeterogeneousCertificate.isolated_extinction
#check @QuarticMaxwell.HeterogeneousCertificate.imaginary_moment_error
#print axioms QuarticMaxwell.HeterogeneousCertificate.imaginary_moment_error
#check @QuarticMaxwell.HeterogeneousCertificate.extinction_error
#print axioms QuarticMaxwell.HeterogeneousCertificate.extinction_error
#check @QuarticMaxwell.HeterogeneousCertificate.extinction_interval
#print axioms QuarticMaxwell.HeterogeneousCertificate.extinction_interval
#check @QuarticMaxwell.HeterogeneousCertificate.imaginary_moment_interval
#print axioms QuarticMaxwell.HeterogeneousCertificate.imaginary_moment_interval
#check @QuarticMaxwell.HeterogeneousCertificate.imaginary_moment_negative
#print axioms QuarticMaxwell.HeterogeneousCertificate.imaginary_moment_negative
#check @QuarticMaxwell.HeterogeneousCertificate.coefficient_formula
#print axioms QuarticMaxwell.HeterogeneousCertificate.coefficient_formula
#check @QuarticMaxwell.HeterogeneousCertificate.coefficient_interval
#print axioms QuarticMaxwell.HeterogeneousCertificate.coefficient_interval
#check @QuarticMaxwell.HeterogeneousRemainder.body
#print axioms QuarticMaxwell.HeterogeneousRemainder.body
#check @QuarticMaxwell.HeterogeneousRemainder.w
#print axioms QuarticMaxwell.HeterogeneousRemainder.w
#check @QuarticMaxwell.HeterogeneousRemainder.w_pos
#print axioms QuarticMaxwell.HeterogeneousRemainder.w_pos
#check @QuarticMaxwell.HeterogeneousRemainder.w_formula
#print axioms QuarticMaxwell.HeterogeneousRemainder.w_formula
#check @QuarticMaxwell.HeterogeneousRemainder.rho_eq
#print axioms QuarticMaxwell.HeterogeneousRemainder.rho_eq
#check @QuarticMaxwell.HeterogeneousRemainder.radius_eq
#print axioms QuarticMaxwell.HeterogeneousRemainder.radius_eq
#check @QuarticMaxwell.HeterogeneousRemainder.source_norm_sq
#print axioms QuarticMaxwell.HeterogeneousRemainder.source_norm_sq
#check @QuarticMaxwell.HeterogeneousRemainder.volumeRadius_cube_eq
#print axioms QuarticMaxwell.HeterogeneousRemainder.volumeRadius_cube_eq
#check @QuarticMaxwell.HeterogeneousRemainder.volumeRadius_le
#print axioms QuarticMaxwell.HeterogeneousRemainder.volumeRadius_le
#check @QuarticMaxwell.HeterogeneousRemainder.correction_le
#print axioms QuarticMaxwell.HeterogeneousRemainder.correction_le
#check @QuarticMaxwell.HeterogeneousRemainder.cosineError_le
#print axioms QuarticMaxwell.HeterogeneousRemainder.cosineError_le
#check @QuarticMaxwell.HeterogeneousRemainder.sineError_le
#print axioms QuarticMaxwell.HeterogeneousRemainder.sineError_le
#check @QuarticMaxwell.HeterogeneousRemainder.gramCorrection_eq
#print axioms QuarticMaxwell.HeterogeneousRemainder.gramCorrection_eq
#check @QuarticMaxwell.HeterogeneousRemainder.errorConstant_le
#print axioms QuarticMaxwell.HeterogeneousRemainder.errorConstant_le
#check @QuarticMaxwell.HeterogeneousRemainder.denominatorError_le
#print axioms QuarticMaxwell.HeterogeneousRemainder.denominatorError_le
#check @QuarticMaxwell.HeterogeneousRemainder.physical_errors
#print axioms QuarticMaxwell.HeterogeneousRemainder.physical_errors
#check @QuarticMaxwell.HeterogeneousAttainment.denominator_lower
#print axioms QuarticMaxwell.HeterogeneousAttainment.denominator_lower
#check @QuarticMaxwell.HeterogeneousAttainment.leading_bound
#print axioms QuarticMaxwell.HeterogeneousAttainment.leading_bound
#check @QuarticMaxwell.HeterogeneousAttainment.remainder_constant_bound
#print axioms QuarticMaxwell.HeterogeneousAttainment.remainder_constant_bound
#check @QuarticMaxwell.HeterogeneousAttainment.quotient_remainder
#print axioms QuarticMaxwell.HeterogeneousAttainment.quotient_remainder
#check @QuarticMaxwell.HeterogeneousAttainment.finite_sphere_remainder
#print axioms QuarticMaxwell.HeterogeneousAttainment.finite_sphere_remainder
#check @QuarticMaxwell.HeterogeneousAttainment.finite_sphere_lower
#print axioms QuarticMaxwell.HeterogeneousAttainment.finite_sphere_lower
#check @QuarticMaxwell.HeterogeneousAttainment.fixed_wavenumber_remainder
#print axioms QuarticMaxwell.HeterogeneousAttainment.fixed_wavenumber_remainder
#check @QuarticMaxwell.HeterogeneousAttainment.fixed_wavenumber_lower
#print axioms QuarticMaxwell.HeterogeneousAttainment.fixed_wavenumber_lower
#check @QuarticMaxwell.SphereCrossMoment.kernel_joint_integrable
#print axioms QuarticMaxwell.SphereCrossMoment.kernel_joint_integrable
#check @QuarticMaxwell.SphereCrossMoment.separated_ball_point
#print axioms QuarticMaxwell.SphereCrossMoment.separated_ball_point
#check @QuarticMaxwell.SphereCrossMoment.cross_moment
#print axioms QuarticMaxwell.SphereCrossMoment.cross_moment
#check @QuarticMaxwell.SphereCrossMoment.cross_zero_mean_bound
#print axioms QuarticMaxwell.SphereCrossMoment.cross_zero_mean_bound
#check @QuarticMaxwell.SphereCrossMoment.isolated_moment
#print axioms QuarticMaxwell.SphereCrossMoment.isolated_moment
#check @QuarticMaxwell.SphereCrossMoment.cross_constant_moment
#print axioms QuarticMaxwell.SphereCrossMoment.cross_constant_moment
#check @QuarticMaxwell.SphereCrossMoment.first_constant_cross_moment
#print axioms QuarticMaxwell.SphereCrossMoment.first_constant_cross_moment
#check @QuarticMaxwell.BlockInteractionMoments.constantSource_ball_eq
#print axioms QuarticMaxwell.BlockInteractionMoments.constantSource_ball_eq
#check @QuarticMaxwell.BlockInteractionMoments.isolated_inverse_constant
#print axioms QuarticMaxwell.BlockInteractionMoments.isolated_inverse_constant
#check @QuarticMaxwell.BlockInteractionMoments.first_constant_moment
#print axioms QuarticMaxwell.BlockInteractionMoments.first_constant_moment
#check @QuarticMaxwell.BlockInteractionMoments.oddResponse
#print axioms QuarticMaxwell.BlockInteractionMoments.oddResponse
#check @QuarticMaxwell.BlockInteractionMoments.oddResponse_mean_zero
#print axioms QuarticMaxwell.BlockInteractionMoments.oddResponse_mean_zero
#check @QuarticMaxwell.BlockInteractionMoments.homogeneous_isolated_norm
#print axioms QuarticMaxwell.BlockInteractionMoments.homogeneous_isolated_norm
#check @QuarticMaxwell.BlockInteractionMoments.homogeneous_odd_weight
#print axioms QuarticMaxwell.BlockInteractionMoments.homogeneous_odd_weight
#check @QuarticMaxwell.BlockInteractionMoments.first_odd_cross_norm
#print axioms QuarticMaxwell.BlockInteractionMoments.first_odd_cross_norm
#check @QuarticMaxwell.BlockInteractionMoments.isolated_inverse_affine
#print axioms QuarticMaxwell.BlockInteractionMoments.isolated_inverse_affine
#check @QuarticMaxwell.BlockInteractionMoments.first_affine_moment
#print axioms QuarticMaxwell.BlockInteractionMoments.first_affine_moment
#check @QuarticMaxwell.HomogeneousScalars.contrast
#print axioms QuarticMaxwell.HomogeneousScalars.contrast
#check @QuarticMaxwell.HomogeneousScalars.contrast_im
#print axioms QuarticMaxwell.HomogeneousScalars.contrast_im
#check @QuarticMaxwell.HomogeneousScalars.contrast_norm
#print axioms QuarticMaxwell.HomogeneousScalars.contrast_norm
#check @QuarticMaxwell.HomogeneousScalars.beta_formula
#print axioms QuarticMaxwell.HomogeneousScalars.beta_formula
#check @QuarticMaxwell.HomogeneousScalars.beta_im
#print axioms QuarticMaxwell.HomogeneousScalars.beta_im
#check @QuarticMaxwell.HomogeneousScalars.beta_im_pos
#print axioms QuarticMaxwell.HomogeneousScalars.beta_im_pos
#check @QuarticMaxwell.HomogeneousScalars.beta_norm_sq
#print axioms QuarticMaxwell.HomogeneousScalars.beta_norm_sq
#check @QuarticMaxwell.HomogeneousScalars.beta_norm_le_mu
#print axioms QuarticMaxwell.HomogeneousScalars.beta_norm_le_mu
#check @QuarticMaxwell.HomogeneousScalars.beta_norm_le_three
#print axioms QuarticMaxwell.HomogeneousScalars.beta_norm_le_three
#check @QuarticMaxwell.HomogeneousScalars.leading
#print axioms QuarticMaxwell.HomogeneousScalars.leading
#check @QuarticMaxwell.HomogeneousScalars.leading_pos
#print axioms QuarticMaxwell.HomogeneousScalars.leading_pos
#check @QuarticMaxwell.HomogeneousScalars.beta_leading_factor
#print axioms QuarticMaxwell.HomogeneousScalars.beta_leading_factor
#check @QuarticMaxwell.MomentPerturbation.imaginary_error
#print axioms QuarticMaxwell.MomentPerturbation.imaginary_error
#check @QuarticMaxwell.MomentPerturbation.imaginary_error_split
#print axioms QuarticMaxwell.MomentPerturbation.imaginary_error_split
#check @QuarticMaxwell.MomentPerturbation.exists_small_square
#print axioms QuarticMaxwell.MomentPerturbation.exists_small_square
#check @QuarticMaxwell.MomentPerturbation.eleventh_order_enclosure
#print axioms QuarticMaxwell.MomentPerturbation.eleventh_order_enclosure
#check @QuarticMaxwell.MomentPerturbation.positive_from_eleventh_order_error
#print axioms QuarticMaxwell.MomentPerturbation.positive_from_eleventh_order_error
#check @QuarticMaxwell.MomentPerturbation.exists_positive_from_uniform_error
#print axioms QuarticMaxwell.MomentPerturbation.exists_positive_from_uniform_error
#check @QuarticMaxwell.MomentPerturbation.higher_power_collapse
#print axioms QuarticMaxwell.MomentPerturbation.higher_power_collapse
#check @QuarticMaxwell.StaticHessian.radialProjection_normalizedComplex
#print axioms QuarticMaxwell.StaticHessian.radialProjection_normalizedComplex
#check @QuarticMaxwell.StaticHessian.newtonHessianOperator_radial
#print axioms QuarticMaxwell.StaticHessian.newtonHessianOperator_radial
#check @QuarticMaxwell.StaticHessian.newtonHessianOperator_norm
#print axioms QuarticMaxwell.StaticHessian.newtonHessianOperator_norm
#check @QuarticMaxwell.HeterogeneousAuxiliary.delta
#print axioms QuarticMaxwell.HeterogeneousAuxiliary.delta
#check @QuarticMaxwell.HeterogeneousAuxiliary.delta_nonneg
#print axioms QuarticMaxwell.HeterogeneousAuxiliary.delta_nonneg
#check @QuarticMaxwell.HeterogeneousAuxiliary.delta_lt
#print axioms QuarticMaxwell.HeterogeneousAuxiliary.delta_lt
#check @QuarticMaxwell.HeterogeneousAuxiliary.moment0_error_delta
#print axioms QuarticMaxwell.HeterogeneousAuxiliary.moment0_error_delta
#check @QuarticMaxwell.HeterogeneousAuxiliary.moment1_error_delta
#print axioms QuarticMaxwell.HeterogeneousAuxiliary.moment1_error_delta
#check @QuarticMaxwell.HeterogeneousAuxiliary.imaginary_moment_error_delta
#print axioms QuarticMaxwell.HeterogeneousAuxiliary.imaginary_moment_error_delta
#check @QuarticMaxwell.HeterogeneousAuxiliary.relative_error_lt_tenth
#print axioms QuarticMaxwell.HeterogeneousAuxiliary.relative_error_lt_tenth
#check @QuarticMaxwell.HeterogeneousAuxiliary.coefficient_decimal_outward
#print axioms QuarticMaxwell.HeterogeneousAuxiliary.coefficient_decimal_outward
#check @QuarticMaxwell.PaperSignConvention.incidentWave_plus
#print axioms QuarticMaxwell.PaperSignConvention.incidentWave_plus
#check @QuarticMaxwell.PaperSignConvention.signedScatteringPaper
#print axioms QuarticMaxwell.PaperSignConvention.signedScatteringPaper
#check @QuarticMaxwell.PaperSignConvention.leadingPaper
#print axioms QuarticMaxwell.PaperSignConvention.leadingPaper
#check @QuarticMaxwell.PaperSignConvention.leadingPaper_moment
#print axioms QuarticMaxwell.PaperSignConvention.leadingPaper_moment
#check @QuarticMaxwell.PaperSignConvention.actual_scattering_difference
#print axioms QuarticMaxwell.PaperSignConvention.actual_scattering_difference
#check @QuarticMaxwell.PaperSignConvention.contrastPaper
#print axioms QuarticMaxwell.PaperSignConvention.contrastPaper
#check @QuarticMaxwell.PaperSignConvention.contrastPaper_eq
#print axioms QuarticMaxwell.PaperSignConvention.contrastPaper_eq
#check @QuarticMaxwell.PaperSignConvention.signed_error
#print axioms QuarticMaxwell.PaperSignConvention.signed_error
#check @QuarticMaxwell.PaperSignConvention.heterogeneous_signed_error
#print axioms QuarticMaxwell.PaperSignConvention.heterogeneous_signed_error
#check @QuarticMaxwell.PaperSignConvention.coefficient_paper
#print axioms QuarticMaxwell.PaperSignConvention.coefficient_paper
#check @QuarticMaxwell.SharpnessClass.Reciprocal
#print axioms QuarticMaxwell.SharpnessClass.Reciprocal
#check @QuarticMaxwell.SharpnessClass.Admissible
#print axioms QuarticMaxwell.SharpnessClass.Admissible
#check @QuarticMaxwell.SharpnessClass.values
#print axioms QuarticMaxwell.SharpnessClass.values
#check @QuarticMaxwell.SharpnessClass.upperConstant
#print axioms QuarticMaxwell.SharpnessClass.upperConstant
#check @QuarticMaxwell.SharpnessClass.upperConstant_pos
#print axioms QuarticMaxwell.SharpnessClass.upperConstant_pos
#check @QuarticMaxwell.SharpnessClass.uniform_upper
#print axioms QuarticMaxwell.SharpnessClass.uniform_upper
#check @QuarticMaxwell.SharpnessClass.values_upper
#print axioms QuarticMaxwell.SharpnessClass.values_upper
#check @QuarticMaxwell.SharpnessClass.scaled_volume
#print axioms QuarticMaxwell.SharpnessClass.scaled_volume
#check @QuarticMaxwell.SharpnessClass.scaled_reciprocal
#print axioms QuarticMaxwell.SharpnessClass.scaled_reciprocal
#check @QuarticMaxwell.SharpnessClass.scaled_admissible
#print axioms QuarticMaxwell.SharpnessClass.scaled_admissible
#check @QuarticMaxwell.SharpnessClass.lowerScale
#print axioms QuarticMaxwell.SharpnessClass.lowerScale
#check @QuarticMaxwell.SharpnessClass.lowerScale_pos
#print axioms QuarticMaxwell.SharpnessClass.lowerScale_pos
#check @QuarticMaxwell.SharpnessClass.physical_lower
#print axioms QuarticMaxwell.SharpnessClass.physical_lower
#check @QuarticMaxwell.SharpnessClass.lower_member
#print axioms QuarticMaxwell.SharpnessClass.lower_member
#check @QuarticMaxwell.SharpnessClass.sSup_sandwich
#print axioms QuarticMaxwell.SharpnessClass.sSup_sandwich
#check @QuarticMaxwell.LorentzMaterial.denominator
#print axioms QuarticMaxwell.LorentzMaterial.denominator
#check @QuarticMaxwell.LorentzMaterial.susceptibility
#print axioms QuarticMaxwell.LorentzMaterial.susceptibility
#check @QuarticMaxwell.LorentzMaterial.pole_strictly_lower
#print axioms QuarticMaxwell.LorentzMaterial.pole_strictly_lower
#check @QuarticMaxwell.LorentzMaterial.denominator_ne_zero_real
#print axioms QuarticMaxwell.LorentzMaterial.denominator_ne_zero_real
#check @QuarticMaxwell.LorentzMaterial.positive_frequency_imaginary
#print axioms QuarticMaxwell.LorentzMaterial.positive_frequency_imaginary
#check @QuarticMaxwell.LorentzMaterial.positive_frequency_loss
#print axioms QuarticMaxwell.LorentzMaterial.positive_frequency_loss
#check @QuarticMaxwell.LorentzMaterial.operating_value
#print axioms QuarticMaxwell.LorentzMaterial.operating_value
#check @QuarticMaxwell.HomogeneousMoments.Parameters.electric
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.electric
#check @QuarticMaxwell.HomogeneousMoments.Parameters.material
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.material
#check @QuarticMaxwell.HomogeneousMoments.Parameters.body
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.body
#check @QuarticMaxwell.HomogeneousMoments.Parameters.A
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.A
#check @QuarticMaxwell.HomogeneousMoments.Parameters.C
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.C
#check @QuarticMaxwell.HomogeneousMoments.Parameters.f0
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.f0
#check @QuarticMaxwell.HomogeneousMoments.Parameters.f1
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.f1
#check @QuarticMaxwell.HomogeneousMoments.Parameters.moment
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.moment
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p0
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p0
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p1
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p1
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p0b
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p0b
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p1b
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p1b
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p0c
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p0c
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p1c
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p1c
#check @QuarticMaxwell.HomogeneousMoments.Parameters.electric_norm
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.electric_norm
#check @QuarticMaxwell.HomogeneousMoments.Parameters.body_volume
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.body_volume
#check @QuarticMaxwell.HomogeneousMoments.Parameters.center_projection_left
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.center_projection_left
#check @QuarticMaxwell.HomogeneousMoments.Parameters.center_projection_right
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.center_projection_right
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p0b_formula
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p0b_formula
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p1b_formula
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p1b_formula
#check @QuarticMaxwell.HomogeneousMoments.Parameters.transverse_hessian
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.transverse_hessian
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p0c_formula
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p0c_formula
#check @QuarticMaxwell.HomogeneousMoments.phase_moment
#print axioms QuarticMaxwell.HomogeneousMoments.phase_moment
#check @QuarticMaxwell.HomogeneousMoments.Parameters.leading_moment
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.leading_moment
#check @QuarticMaxwell.HomogeneousMoments.Parameters.cross_bound
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.cross_bound
#check @QuarticMaxwell.HomogeneousMoments.Parameters.static_norm
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.static_norm
#check @QuarticMaxwell.HomogeneousMoments.Parameters.f0_norm
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.f0_norm
#check @QuarticMaxwell.HomogeneousMoments.Parameters.f1_norm
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.f1_norm
#check @QuarticMaxwell.HomogeneousMoments.affineCoefficient
#print axioms QuarticMaxwell.HomogeneousMoments.affineCoefficient
#check @QuarticMaxwell.HomogeneousMoments.affineCoefficient_pos
#print axioms QuarticMaxwell.HomogeneousMoments.affineCoefficient_pos
#check @QuarticMaxwell.HomogeneousMoments.Parameters.center_separation
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.center_separation
#check @QuarticMaxwell.HomogeneousMoments.Parameters.reverse_separation
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.reverse_separation
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p1c_norm
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p1c_norm
#check @QuarticMaxwell.HomogeneousMoments.Parameters.resolvent_error
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.resolvent_error
#check @QuarticMaxwell.HomogeneousMoments.Parameters.moment_error
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.moment_error
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p0_error
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p0_error
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p1_error
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p1_error
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p1_norm
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p1_norm
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p0b_norm
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p0b_norm
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p0c_norm
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p0c_norm
#check @QuarticMaxwell.HomogeneousMoments.Parameters.approx0_norm
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.approx0_norm
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p1_difference
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p1_difference
#check @QuarticMaxwell.HomogeneousMoments.error11
#print axioms QuarticMaxwell.HomogeneousMoments.error11
#check @QuarticMaxwell.HomogeneousMoments.error12
#print axioms QuarticMaxwell.HomogeneousMoments.error12
#check @QuarticMaxwell.HomogeneousMoments.error14
#print axioms QuarticMaxwell.HomogeneousMoments.error14
#check @QuarticMaxwell.HomogeneousMoments.error15
#print axioms QuarticMaxwell.HomogeneousMoments.error15
#check @QuarticMaxwell.HomogeneousMoments.errorCoefficient
#print axioms QuarticMaxwell.HomogeneousMoments.errorCoefficient
#check @QuarticMaxwell.HomogeneousMoments.errorCoefficient_nonneg
#print axioms QuarticMaxwell.HomogeneousMoments.errorCoefficient_nonneg
#check @QuarticMaxwell.HomogeneousMoments.Parameters.imaginary_error
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.imaginary_error
#check @QuarticMaxwell.HomogeneousMoments.Parameters.coefficient_pos
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.coefficient_pos
#check @QuarticMaxwell.HomogeneousMoments.exists_positive_coefficient
#print axioms QuarticMaxwell.HomogeneousMoments.exists_positive_coefficient
#check @QuarticMaxwell.HomogeneousMoments.chosenRadius
#print axioms QuarticMaxwell.HomogeneousMoments.chosenRadius
#check @QuarticMaxwell.HomogeneousMoments.chosenRadius_spec
#print axioms QuarticMaxwell.HomogeneousMoments.chosenRadius_spec
#check @QuarticMaxwell.HomogeneousMoments.chosenParameters
#print axioms QuarticMaxwell.HomogeneousMoments.chosenParameters
#check @QuarticMaxwell.HomogeneousMoments.coefficientFloor
#print axioms QuarticMaxwell.HomogeneousMoments.coefficientFloor
#check @QuarticMaxwell.HomogeneousMoments.coefficientFloor_pos
#print axioms QuarticMaxwell.HomogeneousMoments.coefficientFloor_pos
#check @QuarticMaxwell.HomogeneousMoments.Parameters.denominator_upper
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.denominator_upper
#check @QuarticMaxwell.HomogeneousMoments.Parameters.coefficient_lower
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.coefficient_lower
#check @QuarticMaxwell.HomogeneousMoments.chosen_coefficient_lower
#print axioms QuarticMaxwell.HomogeneousMoments.chosen_coefficient_lower
#check @QuarticMaxwell.HomogeneousMoments.chosen_coefficient_pos
#print axioms QuarticMaxwell.HomogeneousMoments.chosen_coefficient_pos
#check @QuarticMaxwell.HomogeneousMoments.Parameters.material_constants
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.material_constants
#check @QuarticMaxwell.HomogeneousMoments.Parameters.denominator_lower
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.denominator_lower
#check @QuarticMaxwell.HomogeneousMoments.affineCoefficient_lt_two_thousand
#print axioms QuarticMaxwell.HomogeneousMoments.affineCoefficient_lt_two_thousand
#check @QuarticMaxwell.HomogeneousMoments.explicit_error_bound
#print axioms QuarticMaxwell.HomogeneousMoments.explicit_error_bound
#check @QuarticMaxwell.HomogeneousMoments.explicit_leading_lower
#print axioms QuarticMaxwell.HomogeneousMoments.explicit_leading_lower
#check @QuarticMaxwell.HomogeneousMoments.explicitParameters
#print axioms QuarticMaxwell.HomogeneousMoments.explicitParameters
#check @QuarticMaxwell.HomogeneousMoments.explicit_coefficient_pos
#print axioms QuarticMaxwell.HomogeneousMoments.explicit_coefficient_pos
#check @QuarticMaxwell.HomogeneousMoments.referenceVolume
#print axioms QuarticMaxwell.HomogeneousMoments.referenceVolume
#check @QuarticMaxwell.HomogeneousMoments.responseCorrection
#print axioms QuarticMaxwell.HomogeneousMoments.responseCorrection
#check @QuarticMaxwell.HomogeneousMoments.forwardErrorBound
#print axioms QuarticMaxwell.HomogeneousMoments.forwardErrorBound
#check @QuarticMaxwell.HomogeneousMoments.scatteringErrorBound
#print axioms QuarticMaxwell.HomogeneousMoments.scatteringErrorBound
#check @QuarticMaxwell.HomogeneousMoments.leadingBound
#print axioms QuarticMaxwell.HomogeneousMoments.leadingBound
#check @QuarticMaxwell.HomogeneousMoments.Parameters.rho_eq
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.rho_eq
#check @QuarticMaxwell.HomogeneousMoments.Parameters.input_norm_sq
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.input_norm_sq
#check @QuarticMaxwell.HomogeneousMoments.Parameters.correction_eq
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.correction_eq
#check @QuarticMaxwell.HomogeneousMoments.Parameters.forwardError_eq
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.forwardError_eq
#check @QuarticMaxwell.HomogeneousMoments.Parameters.scatteringError_eq
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.scatteringError_eq
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p0_norm
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p0_norm
#check @QuarticMaxwell.HomogeneousMoments.Parameters.leading_bound
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.leading_bound
#check @QuarticMaxwell.HomogeneousMoments.denominatorFloor
#print axioms QuarticMaxwell.HomogeneousMoments.denominatorFloor
#check @QuarticMaxwell.HomogeneousMoments.remainderBound
#print axioms QuarticMaxwell.HomogeneousMoments.remainderBound
#check @QuarticMaxwell.HomogeneousMoments.intervalFloor
#print axioms QuarticMaxwell.HomogeneousMoments.intervalFloor
#check @QuarticMaxwell.HomogeneousMoments.uniformCutoff
#print axioms QuarticMaxwell.HomogeneousMoments.uniformCutoff
#check @QuarticMaxwell.HomogeneousMoments.data_nonnegative
#print axioms QuarticMaxwell.HomogeneousMoments.data_nonnegative
#check @QuarticMaxwell.HomogeneousMoments.denominatorFloor_pos
#print axioms QuarticMaxwell.HomogeneousMoments.denominatorFloor_pos
#check @QuarticMaxwell.HomogeneousMoments.remainderBound_nonneg
#print axioms QuarticMaxwell.HomogeneousMoments.remainderBound_nonneg
#check @QuarticMaxwell.HomogeneousMoments.uniformCutoff_pos
#print axioms QuarticMaxwell.HomogeneousMoments.uniformCutoff_pos
#check @QuarticMaxwell.HomogeneousMoments.Parameters.interval_lower
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.interval_lower
#check @QuarticMaxwell.HomogeneousMoments.Parameters.remainder_nonneg
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.remainder_nonneg
#check @QuarticMaxwell.HomogeneousMoments.Parameters.remainder_upper
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.remainder_upper
#check @QuarticMaxwell.HomogeneousMoments.Parameters.electric_real
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.electric_real
#check @QuarticMaxwell.HomogeneousMoments.Parameters.electric_transverse
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.electric_transverse
#check @QuarticMaxwell.HomogeneousMoments.Parameters.uniform_physical_lower
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.uniform_physical_lower
#check @QuarticMaxwell.HomogeneousSharpness.lowerConstant
#print axioms QuarticMaxwell.HomogeneousSharpness.lowerConstant
#check @QuarticMaxwell.HomogeneousSharpness.cutoff
#print axioms QuarticMaxwell.HomogeneousSharpness.cutoff
#check @QuarticMaxwell.HomogeneousSharpness.lowerConstant_pos
#print axioms QuarticMaxwell.HomogeneousSharpness.lowerConstant_pos
#check @QuarticMaxwell.HomogeneousSharpness.cutoff_pos
#print axioms QuarticMaxwell.HomogeneousSharpness.cutoff_pos
#check @QuarticMaxwell.HomogeneousSharpness.pattern_admissible
#print axioms QuarticMaxwell.HomogeneousSharpness.pattern_admissible
#check @QuarticMaxwell.HomogeneousSharpness.pattern_homogeneous
#print axioms QuarticMaxwell.HomogeneousSharpness.pattern_homogeneous
#check @QuarticMaxwell.HomogeneousSharpness.sSup_sandwich
#print axioms QuarticMaxwell.HomogeneousSharpness.sSup_sandwich
#check @QuarticMaxwell.HomogeneousSharpness.theorem13
#print axioms QuarticMaxwell.HomogeneousSharpness.theorem13
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p1c_beta_norm
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p1c_beta_norm
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p0b_beta_norm
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p0b_beta_norm
#check @QuarticMaxwell.HomogeneousMoments.Parameters.p0c_beta_norm
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.p0c_beta_norm
#check @QuarticMaxwell.HomogeneousMoments.Parameters.approx0_beta_norm
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.approx0_beta_norm
#check @QuarticMaxwell.HomogeneousMoments.Parameters.approx1
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.approx1
#check @QuarticMaxwell.HomogeneousMoments.Parameters.first_interaction_error
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.first_interaction_error
#check @QuarticMaxwell.HomogeneousMoments.Parameters.approx0_mu_norm
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.approx0_mu_norm
#check @QuarticMaxwell.HomogeneousMoments.Parameters.remaining_interaction_error
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.remaining_interaction_error
#check @QuarticMaxwell.HomogeneousMoments.Parameters.quantitative_relative_error
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.quantitative_relative_error
#check @QuarticMaxwell.HomogeneousMoments.explicit_relative_error
#print axioms QuarticMaxwell.HomogeneousMoments.explicit_relative_error
#check @QuarticMaxwell.HomogeneousMoments.Parameters.quantitative_enclosure
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.quantitative_enclosure
#check @QuarticMaxwell.HomogeneousMoments.Parameters.quantitative_coefficient_interval
#print axioms QuarticMaxwell.HomogeneousMoments.Parameters.quantitative_coefficient_interval
#check @QuarticMaxwell.HomogeneousMoments.exists_quantitative_radius
#print axioms QuarticMaxwell.HomogeneousMoments.exists_quantitative_radius
#check @QuarticMaxwell.HomogeneousMoments.exists_quantitative_parameters
#print axioms QuarticMaxwell.HomogeneousMoments.exists_quantitative_parameters
