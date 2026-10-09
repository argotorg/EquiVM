import Benchmarks.Safe.ExecTransactionFinish
import Benchmarks.Safe.ExecTransactionPaymentTrace
import Benchmarks.Safe.ExecTransactionSuccessCheck
import Benchmarks.Safe.ExecTransactionGasCheck

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.safeExecTransactionFinish,
      ``Benchmarks.Safe.safeExecTransactionPayment, ``Benchmarks.Safe.safeExecSuccessCheck,
      ``Benchmarks.Safe.safeExecGasUsed, ``Benchmarks.Safe.safeExecTransactionExecute,
      ``Benchmarks.Safe.safeExecGasCheck, ``Benchmarks.Safe.safeExecAfterGuardTrace,
      ``Benchmarks.Safe.checkedSubSourceUnderflow] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
