/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Lean
import Lean.Replay
import Lean.Util.FoldConsts

open Lean

/-- Inventory is separate from the kernel-replay result: replay accepts axioms. -/
private def reportInventory (env : Environment) (roots : Array String) : IO Unit := do
  let constants := env.constants.map₁
  let mut unsafeCount := 0
  let mut partialCount := 0
  let mut axiomNames : Array String := #[]
  let mut directSorryUsers : Array String := #[]
  for (name, info) in constants do
    if info.isUnsafe then
      unsafeCount := unsafeCount + 1
    if info.isPartial then
      partialCount := partialCount + 1
    if let .axiomInfo _ := info then
      axiomNames := axiomNames.push name.toString
    if info.getUsedConstantsAsSet.contains "sorryAx".toName then
      directSorryUsers := directSorryUsers.push name.toString
  IO.println <| Json.compress <| Json.mkObj [
    ("phase", toJson "inventory"),
    ("roots", toJson roots),
    ("loaded_modules", toJson (env.header.moduleNames.map Name.toString)),
    ("constant_count", toJson constants.size),
    ("unsafe_skipped_count", toJson unsafeCount),
    ("partial_skipped_count", toJson partialCount),
    ("axiom_names", toJson axiomNames),
    ("direct_sorry_users", toJson directSorryUsers),
    ("axiom_policy_enforced", toJson false)
  ]
  (← IO.getStdout).flush

private def importsFor (args : Array String) : IO (Array Import) := do
  if args.isEmpty then
    throw <| IO.userError "Supply one or more exact library root module names."
  args.mapM fun arg => do
    let moduleName := arg.toName
    if moduleName.isAnonymous then
      throw <| IO.userError s!"Invalid module name: {arg}"
    pure ({ module := moduleName } : Import)

private def reportArtifacts (env : Environment) (label : String) : IO Unit := do
  let files ← env.header.moduleNames.mapM fun name => do
    let base ← findOLean name
    let paths ← [base, OLeanLevel.server.adjustFileName base,
      OLeanLevel.private.adjustFileName base, base.withExtension "ir.sig",
      base.withExtension "ir"].filterM fun p => p.pathExists
    if paths.isEmpty || paths.head! != base then
      throw <| IO.userError s!"Missing base object file for {name}"
    pure <| Json.mkObj [
      ("module", toJson name.toString),
      ("files", toJson (paths.map System.FilePath.toString))]
  IO.println <| Json.compress <| Json.mkObj [
    ("phase", toJson "artifacts"), ("label", toJson label), ("modules", toJson files)]
  (← IO.getStdout).flush

/-- Verify actual proof-body identity for every declaration the unchanged
kernel replay would process in the original whole environment. -/
private unsafe def auditCoverage (plan : System.FilePath) : IO Unit := do
  let raw ← IO.FS.readFile plan
  let rows ← IO.ofExcept <| (Json.parse raw).bind fun j =>
    (fromJson? j : Except String (Array (String × Array String)))
  if rows.isEmpty then
    throw <| IO.userError "Missing replay shards"
  let mut labels : Std.HashSet String := {}
  for (label, _) in rows do
    if labels.contains label then
      throw <| IO.userError s!"Duplicate shard {label}"
    labels := labels.insert label
  let fullImports ← importsFor #["Nyll"]
  withImportModules fullImports {} (trustLevel := 0) fun full => do
    let mut covered : Std.HashSet Name := {}
    for (label, roots) in rows do
      let inputs ← importsFor roots
      let names ← withImportModules inputs {} (trustLevel := 0) fun shard => do
        reportArtifacts shard label
        let mut names := #[]
        for (name, original) in full.constants.map₁ do
          if !original.isUnsafe && !original.isPartial && !covered.contains name then
            if let some candidate := shard.constants.map₁[name]? then
              if candidate == original then
                names := names.push name
        pure names
      for name in names do
        covered := covered.insert name
    let mut required := 0
    for (name, original) in full.constants.map₁ do
      if !original.isUnsafe && !original.isPartial then
        required := required + 1
        unless covered.contains name do
          throw <| IO.userError s!"No replay shard has the exact full-environment declaration {name}"
    IO.println <| Json.compress <| Json.mkObj [
      ("phase", toJson "exactCoverage"), ("required", toJson required),
      ("matched", toJson covered.size), ("result", toJson "PASS")]

/--
Read existing oleans once at private level, then use the unchanged official
Lean 4.36.0 kernel replay in a fresh trust-level-zero environment.
No imported initializers or environment extensions are executed.
-/
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | ["--audit-coverage", path] =>
    auditCoverage ⟨path⟩
    return 0
  | "--attest" :: label :: roots =>
    let inputs ← importsFor roots.toArray
    withImportModules inputs {} (trustLevel := 0) fun env => reportArtifacts env label
    return 0
  | roots =>
    let (label, roots) := match roots with
      | "--replay-attested" :: label :: roots => (some label, roots)
      | roots => (none, roots)
    let imports ← importsFor roots.toArray
    withImportModules imports {} (trustLevel := 0) fun env => do
      reportInventory env roots.toArray
      if let some label := label then
        reportArtifacts env label
      IO.println "REPLAY_START official_Lean_4_36_0_Environment_replay trustLevel=0"
      (← IO.getStdout).flush
      let replayEnv ← mkEmptyEnvironment (trustLevel := 0)
      discard <| Lean.Kernel.Environment.replay env.constants.map₁ replayEnv.toKernelEnv
      IO.println <| Json.compress <| Json.mkObj [
        ("phase", toJson "replay"),
        ("result", toJson "PASS"),
        ("kernel", toJson "official Lean 4.36.0"),
        ("axiom_policy_enforced", toJson false)
      ]
      return 0
