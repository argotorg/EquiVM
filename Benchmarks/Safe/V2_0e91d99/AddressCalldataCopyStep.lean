import Benchmarks.Safe.V2_0e91d99.Decoders
import Benchmarks.Safe.V2_0e91d99.CalldataWords
import Benchmarks.Safe.V2_0e91d99.CalldataDecodeArithmetic
import Benchmarks.Safe.V2_0e91d99.Memory
import Benchmarks.Safe.V2_0e91d99.Blocks.Runtime_050

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V2_0e91d99.RuntimeBlocks

namespace Benchmarks.Safe.V2_0e91d99

set_option maxRecDepth 100000 in
theorem safeAddressCalldataCopyStep {I g s0 σ k C aw mem rdata i n src dst}
    {scratch base fallbackHandler target threshold : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11406⟩
      (UInt256.ofNat i :: UInt256.ofNat dst :: UInt256.ofNat src :: scratch :: base ::
        fallbackHandler :: target :: threshold :: UInt256.ofNat n :: R) mem aw rdata σ k C)
    (hi : i < n) (hn : n < UInt256.size) (hsrc : src + 32 < UInt256.size)
    (hdst : dst + 32 < UInt256.size)
    (hc : (calldataWord I.calldata src).toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨11406⟩
      (UInt256.ofNat (i + 1) :: UInt256.ofNat (dst + 32) :: UInt256.ofNat (src + 32) ::
        scratch :: base :: fallbackHandler :: target :: threshold :: UInt256.ofNat n :: R)
      (writeWord mem dst (calldataWord I.calldata src)) aw' rdata σ k' C' := by
  have h₁ := safeRuntime_block_11406_fallthrough (by omega) (by
    rw [ult_one (by rw [ulit_toNat' _ (by omega), ulit_toNat' _ hn]; exact hi)]
    decide) h
  have h₂ := safeRuntime_block_11415 (by simp; omega) (by jump_dest) h₁
  have hs : (UInt256.ofNat src).toNat = src := ulit_toNat' _ (by omega)
  simp only [safeRuntime_block_11415_stack, hs] at h₂
  obtain ⟨_, _, h₃⟩ := safeValidateAddress h₂ (by simp; omega) hc (by jump_dest)
  obtain ⟨aw', k', C', h₄⟩ := safeRuntime_block_11425_packed
    (by simp; omega) (by jump_dest) h₃
  have hip : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) :=
    u256_one_add_ofNat i
  have hsp : UInt256.ofNat 32 + UInt256.ofNat src = UInt256.ofNat (src + 32) :=
    u256_32_add_ofNat src
  have hdp : UInt256.ofNat dst + UInt256.ofNat 32 = UInt256.ofNat (dst + 32) :=
    wordOfNatAdd dst 32 hdst
  simp only [safeRuntime_block_11425_stack, safeRuntime_block_11425_memory,
    safeAddressMask, solcAddrMask_clean_left hc, ulit_toNat' dst (by omega), hip, hsp, hdp] at h₄
  exact ⟨aw', k', C', h₄⟩

set_option maxRecDepth 100000 in
theorem safeAddressCalldataCopyStepRevert {I g s0 σ k C aw mem rdata i n src dst}
    {scratch base fallbackHandler target threshold : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11406⟩
      (UInt256.ofNat i :: UInt256.ofNat dst :: UInt256.ofNat src :: scratch :: base ::
        fallbackHandler :: target :: threshold :: UInt256.ofNat n :: R) mem aw rdata σ k C)
    (hi : i < n) (hn : n < UInt256.size) (hsrc : src < UInt256.size)
    (hc : ¬(calldataWord I.calldata src).toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_11406_fallthrough (by omega) (by
    rw [ult_one (by rw [ulit_toNat' _ (by omega), ulit_toNat' _ hn]; exact hi)]
    decide) h
  have h₂ := safeRuntime_block_11415 (by simp; omega) (by jump_dest) h₁
  simp only [safeRuntime_block_11415_stack, ulit_toNat' src hsrc] at h₂
  exact safeValidateAddressRevert h₂ (by simp; omega) hc

end Benchmarks.Safe.V2_0e91d99
