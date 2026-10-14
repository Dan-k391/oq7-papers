import OQ7Mission
import Lean.Util.FoldConsts
set_option maxHeartbeats 0

/- This is a read-only traversal of actual kernel types and proof/value terms.
   Every referenced imported constant is expanded, including Lean/Mathlib. -/
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let roots : Array Lean.Name := #[
    `OQ7Mission.norm_lower_bound_of_imaginary_coercivity,
    `OQ7Mission.current_error_le_residual,
    `OQ7Mission.current_error_isLittleO_of_uniform_coercivity,
    `OQ7Mission.quadraticWork_difference_bound,
    `OQ7Mission.incidentWork_difference_bound,
    `OQ7Mission.quadraticWork_difference_isLittleO_square,
    `OQ7Mission.incidentWork_difference_isLittleO_square,
    `OQ7Mission.area_normalized_work_errors_tendsto_zero,
    `OQ7Mission.RationalOverlap.exact_certificate,
    `OQ7Mission.RationalOverlap.rational_SDP_upper_bound,
    `OQ7Mission.RationalOverlap.rational_SDP_attainment,
    `OQ7Mission.RationalOverlap.rational_square_upper_bound]
  let mut seen : Lean.NameSet := {}
  let mut work := roots
  let mut nodes : Array Lean.Json := #[]
  while !work.isEmpty do
    let name := work.back!
    work := work.pop
    if !seen.contains name then
      seen := seen.insert name
      let some info := env.find? name | throwError "Missing referenced kernel constant {name}"
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "definition"
        | .opaqueInfo _ => "opaque"
        | _ => "other"
      let typeDeps := info.type.getUsedConstants
      let valueDeps := match info.value? (allowOpaque := true) with
        | some proof => proof.getUsedConstants
        | none => #[]
      nodes := nodes.push (Lean.Json.mkObj [
        ("name", Lean.Json.str name.toString),
        ("kind", Lean.Json.str kind),
        ("typeConstants", Lean.Json.arr (typeDeps.map (fun n => Lean.Json.str n.toString))),
        ("valueConstants", Lean.Json.arr (valueDeps.map (fun n => Lean.Json.str n.toString)))])
      work := work ++ typeDeps ++ valueDeps
  let result := Lean.Json.mkObj [
    ("roots", Lean.Json.arr (roots.map (fun n => Lean.Json.str n.toString))),
    ("nodes", Lean.Json.arr nodes)]
  Lean.logInfo m!"OQ7FULL-JSON {result.compress}"

