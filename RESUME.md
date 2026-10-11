# Active physical Theorem 1.1 continuation

The final theorem is unproved: `Theorem11Statement` is a proposition definition, not a proof. The machine-readable verification report records this distinction. No genuine blocker has been found.

The current aperture approach uses the actual outgoing Green convolution in horizontal polar coordinates. Two radial integrations by parts, with even circular averages handling coincident heights, give an actual uniform scalar error of order `1/R`. `SlabScaledEstimate.horizontalSlabPotential_uniform_aperture_error` exports this estimate. This does not yet prove vector Maxwell aperture localization.

The smooth separated-current bridge is now proved: horizontal derivatives commute through actual Green convolution, the smooth dyadic field equals the original electric volume field almost everywhere, and contraction onto arbitrary unit horizontal axes has a uniform `C/R` aperture error times the height profile's L1 norm. `SlabPhysicalAperture.electricVolumeField_slab_uniform_aperture_error` is the physical export. This is not yet the all-L2-profile body residual or normalized-response localization.

Next: obtain the uniform body L2 residual and extend height profiles by density; use the existing aperture-independent coercive inverse to prove normalized response and power localization. Then prove the exact planar design and joint zero-angle/plate-loss limits, the first exact extinction bracket, positive isotropic loss via Woodbury/Neumann continuity, and the second bracket and final witness assembly. The exact original final target and its source hash remain guarded by `verify.ps1`.

Run `verify.ps1` and the selected `verify-milestones.ps1` using the pinned Lean path recorded in `verification/report.json`. Main verification requires access to external pinned dependency Git metadata. Preserve each completed milestone's build, declaration inventory, transitive axiom audit, statement export, and Git commit. Scratch files under ignored `work/` are not accepted proof evidence.
