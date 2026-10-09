import Benchmarks.Safe.ModuleMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeModulePreDecodedTrace (evm : EVM.State) (payload : ByteArray)
    {I g s0 σ k C aw rdata} {target value operation ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨7172⟩
      (operation :: ⟨128⟩ :: value :: target :: ret :: R)
      (memoryBytesDecoded payload) aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hn : payload.size ≤ 2 ^ 64 - 192) (ho : operation.toNat < 2)
    (hov : R.length + 30 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    (RDrev safeBytecode g s0 ∧
      ExecFuncBody config (preModuleFrame (AccountAddress.ofUInt256 target)
        value payload operation) evm preModuleExecutionFunction.body .reverted) ∨
    ∃ frame evm' σ' mem' aw' rdata' hash k' C',
      ExecFuncBody config (preModuleFrame (AccountAddress.ofUInt256 target)
        value payload operation) evm preModuleExecutionFunction.body
        (.returned frame evm' (some [.address (AccountAddress.ofUInt256 (preModuleGuardWord evm)),
          .fixedBytes bytes32Width (EVM.Word.toBytesBE hash)])) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ret (hash :: preModuleGuardWord evm :: R)
        mem' aw' rdata' σ' k' C' ∧
      modulePreMemoryForm payload target value operation (UInt256.ofNat I.source.val) mem' := by
  let words := modulePayloadWords payload
  have hwords : words.length = (payload.size + 31) / 32 := memoryWords_length _ _ _
  have he := memoryBytesInitialEnd_bound hn
  have hlarge : 160 ≤ memoryBytesInitialEnd payload.size := by unfold memoryBytesInitialEnd; omega
  exact safePreModuleTrace (src := 128) words payload evm h hee hacc hworld
    (memoryBytesDecoded_free payload) (memoryBytesDecoded_length payload)
    (memoryWords_view _ _ _) hwords (memoryBytesDecoded_words payload)
    (by rw [memoryBytesDecoded_size]; omega)
    (by rw [memoryBytesDecoded_size]; unfold memoryBytesInitialEnd ABI.paddedSize; omega)
    (by omega) (by decide)
    (by rw [memoryBytesDecoded_size, hwords]; omega)
    (by rw [hwords]; unfold memoryBytesInitialEnd ABI.paddedSize; omega)
    (by rw [hwords]; change _ < 2 ^ 256; omega)
    (by
      have hbound : 2 ^ 65 ≤ maxReturnDataSizeByGas := by decide +kernel
      rw [hwords]; omega)
    ho hov hret

end Benchmarks.Safe
