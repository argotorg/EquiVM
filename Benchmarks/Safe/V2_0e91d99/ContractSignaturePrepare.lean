import Benchmarks.Safe.V2_0e91d99.Blocks.Runtime_030
import Benchmarks.Safe.V2_0e91d99.ContractSignatureEncode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V2_0e91d99.RuntimeBlocks

namespace Benchmarks.Safe.V2_0e91d99

set_option maxRecDepth 100000 in
theorem safeContractSignaturePrepare (words : List UInt256)
    {I g s0 σ k C aw mem rdata ptr src subptr len} {hash offset owner ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7036⟩
      (UInt256.ofNat len :: offset :: UInt256.ofNat src :: hash :: owner :: ret :: R)
      mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hsub : UInt256.ofNat 32 + (offset + UInt256.ofNat src) = UInt256.ofNat subptr)
    (hl : memLoad (UInt256.ofNat subptr) mem = UInt256.ofNat len)
    (hw : WordArrayMemory (contractSignatureHeaderMemory mem ptr hash) (subptr + 32) words)
    (hn : words.length = (len + 31) / 32) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr)
    (hin : subptr + 32 ≤ mem.size) (ha : subptr + 32 ≤ ptr)
    (hsrc : subptr + 32 + 32 * words.length ≤ ptr + 68)
    (hb : ptr + 132 + 32 * words.length < UInt256.size) (hov : R.length + 33 ≤ 1024) :
    ∃ gasArg aw' k' C', RD fork safeBytecode I g s0 ⟨7102⟩
      (gasArg :: UInt256.land owner solcAddrMask :: UInt256.ofNat ptr ::
        UInt256.ofNat (contractSignatureCallLength len) :: UInt256.ofNat ptr :: ⟨32⟩ ::
        UInt256.ofNat (contractSignatureCallEnd ptr len) :: ⟨371636862⟩ ::
        UInt256.land owner solcAddrMask :: signatureMagicWord :: UInt256.ofNat subptr ::
        UInt256.ofNat len :: offset :: UInt256.ofNat src :: hash :: owner :: ret :: R)
      (contractSignatureCallMemory mem ptr len hash words) aw' rdata σ k' C' := by
  obtain ⟨_, _, _, h₁⟩ := safeContractSignatureEncode words h hf hsub hl hw hn hin ha hsrc hb hov
  have hfree := contractSignatureArgs_free (len := len) (hash := hash) (words := words)
    hf hm hp hn
  change memLoad (UInt256.ofNat 64) _ = _ at hfree
  have hsub' : UInt256.sub (UInt256.ofNat (contractSignatureCallEnd ptr len))
      (UInt256.ofNat ptr) = UInt256.ofNat (contractSignatureCallLength len) := by
    have hadd : UInt256.ofNat ptr + UInt256.ofNat (contractSignatureCallLength len) =
        UInt256.ofNat (contractSignatureCallEnd ptr len) := by
      apply u256_inj
      have he : contractSignatureCallEnd ptr len < UInt256.size := by
        dsimp [contractSignatureCallEnd, contractSignatureCallLength, ABI.paddedSize]
        rw [hn] at hb
        omega
      rw [ulit_toNat' _ he]
      exact uadd_ofNat_toNat (by omega) (by dsimp [contractSignatureCallEnd] at he; omega) he
    rw [← hadd, word_add_sub_left]
  have h₂ := safeRuntime_block_7090 (by simp; omega) h₁
  simp only [safeRuntime_block_7090_stack, hfree, hsub'] at h₂
  exact ⟨_, _, _, _, h₂⟩

end Benchmarks.Safe.V2_0e91d99
