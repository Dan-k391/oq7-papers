import PrescribedExtinction.PhysicalTheorem11

open OQ7Prescribed
#print OQ7Prescribed.TwoLayerBody
#print OQ7Prescribed.MaterialAdmissible
#print OQ7Prescribed.ScatteringState
#print OQ7Prescribed.WeakMaxwell
#print OQ7Prescribed.HasWeakCurl
#print OQ7Prescribed.Outgoing
#print OQ7Prescribed.extinction
#print OQ7Prescribed.absorption
#print OQ7Prescribed.scattering
#print OQ7Prescribed.currentFarField
#print OQ7Prescribed.Theorem11Statement
#print OQ7Prescribed.PhysicalTheorem11Statement
#print OQ7Prescribed.FullPhysicalOpticalStatement
#print axioms OQ7Prescribed.theorem11_complete
#check OQ7Prescribed.outgoing_dyadic_contact_identity
#check OQ7Prescribed.compactOutgoingOperator_norm_le
#check OQ7Prescribed.vacuum_outgoing_weak_unique_zero
#check OQ7Prescribed.electricVolumeField_L2_slab_uniform_error

example : PhysicalTheorem11Statement := theorem11_complete
