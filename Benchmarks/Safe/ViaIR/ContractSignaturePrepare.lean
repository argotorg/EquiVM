import Benchmarks.Safe.ViaIR.ContractSignatureEncode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeContractSignaturePrepare (words : List UInt256)
    {I g s0 σ k C aw mem rdata ptr src len} {hash owner last sig : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7707⟩
      (UInt256.ofNat src :: last :: owner :: sig :: hash :: R) mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat len)
    (hw : WordArrayMemory mem (src + 32) words) (hn : words.length = (len + 31) / 32)
    (hp : 96 ≤ ptr) (hin : src + 32 + 32 * words.length ≤ mem.size)
    (ha : src + 32 + 32 * words.length ≤ ptr + 32)
    (hb : contractSignatureCallEnd ptr len + 32 < UInt256.size) (hov : R.length + 23 ≤ 1024) :
    RDrev fork safeBytecode g s0 ∨
      ∃ gas aw' k' C', contractSignatureCallEnd ptr len < 2 ^ 64 ∧
        RD fork safeBytecode I g s0 ⟨7776⟩
          (gas :: owner :: UInt256.ofNat (ptr + 32) ::
            UInt256.ofNat (contractSignatureCallLength len) :: ⟨0⟩ :: ⟨0⟩ ::
            last :: owner :: sig :: hash :: R)
          (contractSignatureCallMemory mem ptr len hash words) aw' rdata σ k' C' := by
  obtain ⟨_, _, _, h₁⟩ := safeContractSignatureArgs words h hf hl hw hn hin ha
    (by dsimp [contractSignatureCallEnd, ABI.paddedSize] at hb; rw [hn]; omega) hov
  obtain hrev | ⟨_, _, _, hsmall, h₂⟩ := safeContractSignatureEncode h₁ hn hb (by omega)
  · exact .inl hrev
  obtain ⟨aw', k', C', h₃⟩ := safeRuntime_block_7771_packed (by simp; omega) h₂
  have hload : memLoad (UInt256.ofNat ptr)
      (contractSignatureEncodedMemory mem ptr len hash words) =
      UInt256.ofNat (contractSignatureCallLength len) := by
    apply memLoad_of_wordRead
    rw [ulit_toNat' ptr (by dsimp [contractSignatureCallEnd] at hb; omega)]
    exact contractSignatureEncodedMemory_length mem ptr len hash words hn hp
  simp only [safeRuntime_block_7771_stack, hload] at h₃
  exact .inr ⟨_, aw', k', C', hsmall, h₃⟩

end Benchmarks.Safe.ViaIR
