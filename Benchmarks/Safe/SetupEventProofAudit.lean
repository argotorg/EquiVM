import Benchmarks.Safe.SetupEventTrace
import Benchmarks.Safe.SetupDataAllocate
import Benchmarks.Safe.SetupSource

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.safeSetupEventTrace, ``Benchmarks.Safe.safeSetupEventTraceRevert,
      ``Benchmarks.Safe.safeSetupEventStatic, ``Benchmarks.Safe.safeSetupOwnersAllocate,
      ``Benchmarks.Safe.safeSetupModulesAllocate, ``Benchmarks.Safe.safeSetupPrefix,
      ``Benchmarks.Safe.safeSetupStatic, ``Benchmarks.Safe.safeInternalSetupFallback] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
