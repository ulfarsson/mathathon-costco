import OrderedRemoval.Statements
import OrderedRemoval.Unconditional
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods := #[
    `OrderedRemoval.Statements, `OrderedRemoval.Unconditional,
    `OAI.Combinatorics.MatrixRemoval.AnchorFrames, `OAI.Combinatorics.MatrixRemoval.AnchorGroups, `OAI.Combinatorics.MatrixRemoval.AnchorPatternBridge,
    `OAI.Combinatorics.MatrixRemoval.AnchorPatternFixed, `OAI.Combinatorics.MatrixRemoval.AnchorProperties, `OAI.Combinatorics.MatrixRemoval.AnchorRigidity,
    `OAI.Combinatorics.MatrixRemoval.AnchorRigidityFixed, `OAI.Combinatorics.MatrixRemoval.Asymptotics, `OAI.Combinatorics.MatrixRemoval.BodyExtension,
    `OAI.Combinatorics.MatrixRemoval.BodyRoles, `OAI.Combinatorics.MatrixRemoval.CanonicalCopyBound, `OAI.Combinatorics.MatrixRemoval.CanonicalHorizontal,
    `OAI.Combinatorics.MatrixRemoval.CanonicalModeEntries, `OAI.Combinatorics.MatrixRemoval.Consequence, `OAI.Combinatorics.MatrixRemoval.CopyBound,
    `OAI.Combinatorics.MatrixRemoval.CopyBoundFixed, `OAI.Combinatorics.MatrixRemoval.DirectNonshattering, `OAI.Combinatorics.MatrixRemoval.GuardContainment,
    `OAI.Combinatorics.MatrixRemoval.GuardedFrame, `OAI.Combinatorics.MatrixRemoval.GuardedPath, `OAI.Combinatorics.MatrixRemoval.Host,
    `OAI.Combinatorics.MatrixRemoval.HostAnchorFrames, `OAI.Combinatorics.MatrixRemoval.HostAnchorGroups, `OAI.Combinatorics.MatrixRemoval.HostAnchorPinning,
    `OAI.Combinatorics.MatrixRemoval.HostAnchorRigidity, `OAI.Combinatorics.MatrixRemoval.HostBodyModes, `OAI.Combinatorics.MatrixRemoval.HostBodyOrder,
    `OAI.Combinatorics.MatrixRemoval.HostCopyBound, `OAI.Combinatorics.MatrixRemoval.HostModeIncidence, `OAI.Combinatorics.MatrixRemoval.HostNonshattering,
    `OAI.Combinatorics.MatrixRemoval.HostRepairDistance, `OAI.Combinatorics.MatrixRemoval.HostRoleExtraction, `OAI.Combinatorics.MatrixRemoval.HostRootLeaf,
    `OAI.Combinatorics.MatrixRemoval.HostSampledPath, `OAI.Combinatorics.MatrixRemoval.HostSampledSelection, `OAI.Combinatorics.MatrixRemoval.HostSampling,
    `OAI.Combinatorics.MatrixRemoval.HostSamplingCompatibility, `OAI.Combinatorics.MatrixRemoval.HostTreeOrder, `OAI.Combinatorics.MatrixRemoval.HostTwins,
    `OAI.Combinatorics.MatrixRemoval.HostVerticalLocalization, `OAI.Combinatorics.MatrixRemoval.Main, `OAI.Combinatorics.MatrixRemoval.ModeIncidence,
    `OAI.Combinatorics.MatrixRemoval.ModeLocalization, `OAI.Combinatorics.MatrixRemoval.Model, `OAI.Combinatorics.MatrixRemoval.OrderedAnchorGroups,
    `OAI.Combinatorics.MatrixRemoval.OrderedAnchorRigidity, `OAI.Combinatorics.MatrixRemoval.OrderedBodyLocalization, `OAI.Combinatorics.MatrixRemoval.OrderedHost,
    `OAI.Combinatorics.MatrixRemoval.OrderedHostCopy, `OAI.Combinatorics.MatrixRemoval.OrderedRepairDistance, `OAI.Combinatorics.MatrixRemoval.OrderedSampledSelection,
    `OAI.Combinatorics.MatrixRemoval.PathPropagation, `OAI.Combinatorics.MatrixRemoval.PinnedHostCopy, `OAI.Combinatorics.MatrixRemoval.SampledPath,
    `OAI.Combinatorics.MatrixRemoval.SampledPathOrder, `OAI.Combinatorics.MatrixRemoval.SamplingAvoidance, `OAI.Combinatorics.MatrixRemoval.SamplingDistance,
    `OAI.Combinatorics.MatrixRemoval.SelectedAnchorSparsity, `OAI.Combinatorics.MatrixRemoval.SequenceAssembly, `OAI.Combinatorics.MatrixRemoval.ThreeSeedSampling,
    `OAI.Combinatorics.MatrixRemoval.TreePositions]
  let standard : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut rows : Array (Name × Array Name) := #[]
  for modName in mods do
    let some modIdx := env.getModuleIdx? modName | throwError s!"module {modName} not found"
    let md := env.header.moduleData[modIdx]!
    for n in md.constNames do
      if (← getEnv).contains n then
        let axs ← Lean.collectAxioms n
        rows := rows.push (n, axs)
  let mut bad : Array Name := #[]
  for (n, axs) in rows do
    logInfo m!"AUDIT_DECL {n} [{String.intercalate ", " (axs.toList.map toString)}]"
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
