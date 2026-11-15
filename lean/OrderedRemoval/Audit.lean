import OrderedRemoval.Statements
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `OrderedRemoval.Statements | throwError "module not found"
  let md := env.header.moduleData[modIdx]!
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut rows : Array (Name × Array Name) := #[]
  for n in md.constNames do
    if (← getEnv).contains n then
      let axs ← Lean.collectAxioms n
      rows := rows.push (n, axs)
  let mut bad : Array Name := #[]
  for (n, axs) in rows do
    if axs.any (fun a => !standard.contains a) then bad := bad.push n
  logInfo m!"AUDIT_DECL_COUNT {rows.size}"
  logInfo m!"AUDIT_BAD_COUNT {bad.size}"
  for n in bad do
    let axs ← Lean.collectAxioms n
    logInfo m!"AUDIT_BAD {n} [{String.intercalate ", " (axs.toList.map toString)}]"
  if !bad.isEmpty then
    throwError "axiom audit failed for {bad.size} declaration(s)"
  let mut sets : Std.HashMap String (Array Name) := {}
  for (n, axs) in rows do
    let k := String.intercalate ", " (axs.toList.map toString)
    sets := sets.insert k ((sets.getD k #[]).push n)
  for (k, ns) in sets.toList do
    logInfo m!"AUDIT_SET [{k}] count={ns.size}"
