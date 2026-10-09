import Benchmarks.Safe.ExecuteSource
import Benchmarks.Safe.ExecuteRawTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeExecuteTrace {I g s0 σ k C aw mem rdata}
    {target value ptr operation txGas ret : UInt256} {R : List UInt256}
    (evm : EVM.State) (payload : ByteArray)
    (h : RD safeBytecode I g s0 ⟨7408⟩
      (txGas :: operation :: ptr :: value :: target :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hdata : mem.readWithPadding (ptr + UInt256.ofNat 32).toNat (memLoad ptr mem).toNat =
      payload)
    (hop : operation.toNat ≤ 1) (hov : R.length + 14 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    (RDstatic safeBytecode g s0 ∧
      ExecFuncBody config
        (executeFrame (AccountAddress.ofUInt256 target) value payload operation txGas) evm
        executeFunction.body .staticViolation) ∨
    ∃ evm' σ' z out aw' k' C',
      ExecFuncBody config
        (executeFrame (AccountAddress.ofUInt256 target) value payload operation txGas) evm
        executeFunction.body
        (.returned
          (executeFinalFrame (AccountAddress.ofUInt256 target) value payload operation txGas z out)
          evm' (some [.bool z])) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ret ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        mem aw' out σ' k' C' ∧ out.size < UInt256.size := by
  rcases safeExecuteRawTrace evm payload h hee hacc hworld hdata hop hov hret with
    ⟨hr, ho, hp, hv⟩ | ⟨evm', σ', z, out, aw', k', C', hc, he, ha, hw, hr, hs, _⟩
  · exact Or.inl ⟨hr, safeExecuteCallStaticSource ho hp hv⟩
  · refine Or.inr ⟨evm', σ', z, out, aw', k', C', ?_, he, ha, hw, hr, hs⟩
    rcases hc with ⟨ho, hc⟩ | ⟨ho, hc⟩
    · exact safeExecuteDelegateSource ho hc
    · exact safeExecuteCallSource ho hc

end Benchmarks.Safe
