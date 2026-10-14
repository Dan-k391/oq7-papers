import work.PlanarMaterialInverse
namespace OQ7Prescribed
#synth TopologicalSpace (PlanarCurrentL2 1 →L[ℂ] PlanarCurrentL2 1)
#synth PseudoMetricSpace (PlanarCurrentL2 1 →L[ℂ] PlanarCurrentL2 1)
#synth IsTopologicalAddGroup (PlanarCurrentL2 1 →L[ℂ] PlanarCurrentL2 1)
#synth NormedAddCommGroup (PlanarCurrentL2 1 →L[ℂ] PlanarCurrentL2 1)
#synth ContinuousSub (PlanarCurrentL2 1 →L[ℂ] PlanarCurrentL2 1)
#synth ContinuousAdd (PlanarCurrentL2 1 →L[ℂ] PlanarCurrentL2 1)
#synth ContinuousNeg (PlanarCurrentL2 1 →L[ℂ] PlanarCurrentL2 1)
set_option trace.Meta.synthInstance true in
example (L : ℝ) : ContinuousSub (PlanarCurrentL2 L →L[ℂ] PlanarCurrentL2 L) := inferInstance
end OQ7Prescribed
