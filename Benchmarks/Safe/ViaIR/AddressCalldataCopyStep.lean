import Benchmarks.Safe.ViaIR.AddressCalldataRead
import Benchmarks.Safe.ViaIR.CalldataWords
import Benchmarks.Safe.ViaIR.CalldataDecodeArithmetic
import Benchmarks.Safe.ViaIR.Memory
import Benchmarks.Safe.ViaIR.Blocks.Runtime_015
import Benchmarks.Safe.ViaIR.Blocks.Runtime_016
import Benchmarks.Safe.ViaIR.Blocks.Runtime_018

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeAddressCalldataCopyStep {I g s0 σ k C aw mem rdata i n src dst}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3187⟩
      (UInt256.ofNat i :: UInt256.ofNat n :: UInt256.ofNat src :: UInt256.ofNat dst :: R)
      mem aw rdata σ k C)
    (hi : i < n) (hn : n < UInt256.size) (hsrc : src + 32 < UInt256.size)
    (hdst : dst + 32 < UInt256.size)
    (hc : (calldataWord I.calldata src).toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨3187⟩
      (UInt256.ofNat (i + 1) :: UInt256.ofNat n :: UInt256.ofNat (src + 32) ::
        UInt256.ofNat (dst + 32) :: R)
      (writeWord mem dst (calldataWord I.calldata src)) aw' rdata σ k' C' := by
  have h₁ := safeRuntime_block_3187_taken (by simp; omega) (by
    rw [ult_one (by rw [ulit_toNat' _ (by omega), ulit_toNat' _ hn]; exact hi)]
    decide) (by jump_dest) h
  have h₂ := safeRuntime_block_3859 (by omega) (by jump_dest) h₁
  have hs : (UInt256.ofNat src).toNat = src := ulit_toNat' _ (by omega)
  obtain ⟨_, _, h₃⟩ := safeReadCalldataAddress h₂ (by simpa only [hs] using hc)
    (by simp; omega) (by jump_dest)
  obtain ⟨aw', k', C', h₄⟩ := safeRuntime_block_3883_packed
    (by omega) (by jump_dest) h₃
  have hip : UInt256.ofNat i + UInt256.ofNat 1 = UInt256.ofNat (i + 1) :=
    wordOfNatAdd i 1 (by omega)
  have hsp : UInt256.ofNat src + UInt256.ofNat 32 = UInt256.ofNat (src + 32) :=
    wordOfNatAdd src 32 hsrc
  have hdp : UInt256.ofNat dst + UInt256.ofNat 32 = UInt256.ofNat (dst + 32) :=
    wordOfNatAdd dst 32 hdst
  simp only [safeRuntime_block_3883_stack, safeRuntime_block_3883_memory,
    safeAddressMask, hs] at h₄
  change RD fork safeBytecode I g s0 ⟨3187⟩
    ((UInt256.ofNat i + UInt256.ofNat 1) :: UInt256.ofNat n ::
      (UInt256.ofNat src + UInt256.ofNat 32) ::
      (UInt256.ofNat dst + UInt256.ofNat 32) :: R)
    (writeWord mem (UInt256.ofNat dst).toNat
      (UInt256.land (calldataWord I.calldata src) solcAddrMask)) aw' rdata σ k' C' at h₄
  rw [solcAddrMask_clean hc, ulit_toNat' dst (by omega), hip, hsp, hdp] at h₄
  exact ⟨aw', k', C', h₄⟩

theorem safeAddressCalldataCopyStepRevert {I g s0 σ k C aw mem rdata i n src dst}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3187⟩
      (UInt256.ofNat i :: UInt256.ofNat n :: UInt256.ofNat src :: UInt256.ofNat dst :: R)
      mem aw rdata σ k C)
    (hi : i < n) (hn : n < UInt256.size) (hsrc : src < UInt256.size)
    (hc : ¬(calldataWord I.calldata src).toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_3187_taken (by simp; omega) (by
    rw [ult_one (by rw [ulit_toNat' _ (by omega), ulit_toNat' _ hn]; exact hi)]
    decide) (by jump_dest) h
  have h₂ := safeRuntime_block_3859 (by omega) (by jump_dest) h₁
  exact safeReadCalldataAddressRevert h₂ (by simpa only [ulit_toNat' src hsrc] using hc)
    (by simp; omega)

end Benchmarks.Safe.ViaIR
