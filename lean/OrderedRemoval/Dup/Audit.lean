import OrderedRemoval.Dup.Red

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods : Array Name := #[`OrderedRemoval.Dup.Defs, `OrderedRemoval.Dup.Fact1, `OrderedRemoval.Dup.Repr, `OrderedRemoval.Dup.Fact2b, `OrderedRemoval.Dup.Main, `OrderedRemoval.Dup.Red]
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  let mut bad : Array Name := #[]
  for m in mods do
    let some modIdx := env.getModuleIdx? m | throwError "module {m} not found"
    for n in env.header.moduleData[modIdx]!.constNames do
      if env.contains n then
        count := count + 1
        let axs ← Lean.collectAxioms n
        if axs.any (fun a => !standard.contains a) then bad := bad.push n
  logInfo m!"DUP_AUDIT_DECL_COUNT {count}"
  logInfo m!"DUP_AUDIT_BAD_COUNT {bad.size}"
  if !bad.isEmpty then
    throwError "axiom audit failed: {bad}"
