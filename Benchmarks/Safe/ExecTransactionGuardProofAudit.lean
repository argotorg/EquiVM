import Benchmarks.Safe.ExecTransactionGuardTrace

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.safeExecTransactionGuard,
      ``Benchmarks.Safe.safeExecGuardCallTrace, ``Benchmarks.Safe.safeExecGuardEncode,
      ``Benchmarks.Safe.safeExecGuardCallEncoding, ``Benchmarks.Safe.execGuardArgsMemory_read,
      ``Benchmarks.Safe.optionalCheckedCallSuccess,
      ``Benchmarks.Safe.calldataBytesEncodedInto_read] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
