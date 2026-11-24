import Benchmarks.Safe.ViaIR.ExecTransactionAllocate
import Benchmarks.Safe.ViaIR.SetupDecodeScalars
import Benchmarks.Safe.ViaIR.Blocks.Runtime_016

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000 in
theorem safeSetupModulesAllocate {I g s0 σ k C aw mem rdata n len ptr}
    {scratch ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3401⟩
      (scratch :: UInt256.ofNat len :: UInt256.ofNat (setupDataStart I.calldata) :: ret :: R)
      mem aw rdata σ k C)
    (hb : SetupCalldataBounds I.calldata n len)
    (hf : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr)
    (hp : ptr + 64 + len < UInt256.size) (hov : R.length + 12 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    (¬ptr + 32 + ABI.paddedSize len < 2 ^ 64 ∧ RDrev fork safeBytecode g s0) ∨
      ∃ aw' k' C', ptr + 32 + ABI.paddedSize len < 2 ^ 64 ∧
      RD fork safeBytecode I g s0 ret (UInt256.ofNat ptr :: R)
        (calldataBufferMemory I.calldata mem (setupDataStart I.calldata) ptr len len
          (ptr + 32 + ABI.paddedSize len)) aw' rdata σ k' C' := by
  have h₁ := safeRuntime_block_3401 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_3401_stack] at h₁
  exact safeCalldataBufferAllocateEvidence len h₁ hf hp (by have := hb.dataLength; omega)
    hb.dataEnd (lt_size_of_lt_sign hb.small) hov hret

end Benchmarks.Safe.ViaIR
