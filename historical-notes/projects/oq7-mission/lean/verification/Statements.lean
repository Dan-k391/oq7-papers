import OQ7Mission
set_option pp.universes true
set_option pp.explicit true
set_option pp.coercions true
set_option pp.notation false

run_cmd do
  let env ← Lean.getEnv
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "OQ7Mission." ||
        name.toString.startsWith "_private.OQ7Mission." then
      Lean.logInfo m!"OQ7MISSION-TYPE {name} : {info.type}"

