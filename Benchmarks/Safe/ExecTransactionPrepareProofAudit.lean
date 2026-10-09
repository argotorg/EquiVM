import Benchmarks.Safe.ExecTransactionPrepare

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.safeExecTransactionPrepare,
      ``Benchmarks.Safe.safeExecTransactionNoncePrefix,
      ``Benchmarks.Safe.safeExecTransactionNonceOverflow,
      ``Benchmarks.Safe.safeExecTransactionNonceStatic,
      ``Benchmarks.Safe.safeExecHashTrace, ``Benchmarks.Safe.transactionHashMemory_preserves] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
