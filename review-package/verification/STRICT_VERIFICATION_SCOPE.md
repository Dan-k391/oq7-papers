# Strict verification boundary

The regenerated final-theorem axiom report contains only propext, Classical.choice and Quot.sound. The exhaustive project sweep reports the same allowed set for every project constant.

The cone report explicitly flags sorryAx, Lean.ofReduceBool and Lean.trustCompiler as **present in the imported environment but outside the final theorem's dependency cone**. Their existence in Lean's imported infrastructure is not hidden. None is a dependency of the final theorem, and none occurs in the project-wide reachable-axiom set. No additional mathematical axiom, admitted proof or native-trust axiom is accepted for the strict main claim.

The new fresh replay succeeded with exit 0 for PrescribedExtinction.PhysicalTheorem11. The pinned helper loads that module and replays its import environment into an empty Lean kernel environment. This is the same Lean kernel implementation. Its native/unsafe IO driver is not an independently implemented mathematical checker and does not change the axiom census.

An independently implemented checker was not supplied or run. Human peer review is not established. The current build reused compatible objects; the preserved earlier clean build and this new fresh replay are distinct pieces of evidence.
