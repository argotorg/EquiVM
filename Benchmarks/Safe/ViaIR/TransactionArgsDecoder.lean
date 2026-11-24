import Benchmarks.Safe.ViaIR.Decoders
import Benchmarks.Safe.ViaIR.CalldataBytesDecoder
import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.Blocks.Runtime_007
import Benchmarks.Safe.ViaIR.Blocks.Runtime_012

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

set_option maxHeartbeats 1000000 in
theorem safeDecodeTransactionArgsStart {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2253⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      (UInt256.ofNat 320) = ⟨0⟩)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 21 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨6952⟩ (⟨2273⟩ :: ⟨0⟩ :: R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_2253_fallthrough (by simp; omega) (by
    rw [safeIRArgumentSizeSub hlong hsize]
    exact hc) h
  have h₂ := safeRuntime_block_2266 (by simp; omega) (by jump_dest) h₁
  exact ⟨_, _, h₂⟩

set_option maxHeartbeats 1000000 in
theorem safeDecodeTransactionArgsToBytes {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2273⟩
      (calldataWord I.calldata 4 :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 21 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7083⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) ::
        UInt256.ofNat I.calldata.size :: ⟨2304⟩ :: calldataWord I.calldata 4 :: ⟨0⟩ :: R)
      mem aw rdata σ k' C' := by
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_2273_fallthrough (by simp; omega) (by
    change UInt256.gt (calldataWord I.calldata 68) _ = UInt256.ofNat 0
    rw [hm, ugt_zero (by simpa only [show
      (UInt256.ofNat (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 by decide +kernel] using hoff)]
    rfl) h
  have h₂ := safeRuntime_block_2291 (by simp; omega) (by jump_dest) h₁
  change RD fork safeBytecode I g s0 ⟨7083⟩
    ((UInt256.ofNat 4 + calldataWord I.calldata 68) :: UInt256.ofNat I.calldata.size ::
      ⟨2304⟩ :: calldataWord I.calldata 4 :: ⟨0⟩ :: R) mem aw rdata σ _ _ at h₂
  have hadd : UInt256.ofNat 4 + calldataWord I.calldata 68 =
      UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) := by
    conv_lhs => rw [← u256_ofNat_toNat (calldataWord I.calldata 68)]
    exact wordOfNatAdd _ _ (by change _ < 2 ^ 256; omega)
  rw [hadd] at h₂
  exact ⟨_, _, h₂⟩

set_option maxHeartbeats 1000000 in
theorem safeDecodeTransactionArgsToToken {I g s0 σ k C aw mem rdata}
    {len off : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2304⟩
      (len :: off :: calldataWord I.calldata 4 :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (ho : (calldataWord I.calldata 100).toNat < 2) (hov : R.length + 21 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨6974⟩
      (⟨2334⟩ :: len :: off :: calldataWord I.calldata 4 :: calldataWord I.calldata 100 ::
        ⟨1055⟩ :: ⟨32⟩ :: ⟨0⟩ :: len :: off :: calldataWord I.calldata 4 ::
        calldataWord I.calldata 100 :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_2304_fallthrough (by omega) (by
    change UInt256.isZero (UInt256.lt (calldataWord I.calldata 100) ⟨2⟩) = _
    rw [ult_one (by exact ho)]
    rfl) h
  have h₂ := safeRuntime_block_2318 (by omega) (by jump_dest) h₁
  exact ⟨_, _, h₂⟩

def transactionArgsStack (I : ExecutionEnv) (len : Nat) (R : List UInt256) : List UInt256 :=
  calldataWord I.calldata 4 :: calldataWord I.calldata 36 ::
    UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat + 32) :: UInt256.ofNat len ::
    calldataWord I.calldata 100 :: calldataWord I.calldata 132 ::
    calldataWord I.calldata 164 :: calldataWord I.calldata 196 ::
    calldataWord I.calldata 228 :: calldataWord I.calldata 260 :: calldataWord I.calldata 292 ::
    ⟨1055⟩ :: ⟨32⟩ :: ⟨0⟩ :: UInt256.ofNat len ::
    UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat + 32) ::
    calldataWord I.calldata 4 :: calldataWord I.calldata 100 :: R

set_option maxHeartbeats 1000000 in
theorem safeDecodeTransactionArgsValid {I g s0 σ k C aw mem rdata len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2253⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hh : 324 ≤ I.calldata.size) (hs : I.calldata.size < 2 ^ 255)
    (hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hw : calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat) =
      UInt256.ofNat len)
    (hn : len ≤ 2 ^ 64 - 1)
    (hin : 4 + (calldataWord I.calldata 68).toNat + 32 + len ≤ I.calldata.size)
    (ho : (calldataWord I.calldata 100).toNat < 2)
    (hgas : (calldataWord I.calldata 228).toNat < EVM.addressModulus)
    (href : (calldataWord I.calldata 260).toNat < EVM.addressModulus)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨9040⟩ (transactionArgsStack I len R)
      mem aw rdata σ k' C' := by
  obtain ⟨_, _, h₁⟩ := safeDecodeTransactionArgsStart h
    (solcDecodeLenCheckOk hh (by omega) (lt_size_of_lt_sign hs) (by decide))
    (by omega) (lt_size_of_lt_sign hs) (by omega)
  obtain ⟨_, _, h₂⟩ := safeDecodeAddress h₁ (by simp; omega) hc (by jump_dest)
  obtain ⟨_, _, h₃⟩ := safeDecodeTransactionArgsToBytes h₂ hoff (by omega)
  obtain ⟨_, _, h₄⟩ := safeDecodeCalldataBytesValid h₃ hw hin hs hn (by simp; omega)
    (by jump_dest)
  obtain ⟨_, _, h₅⟩ := safeDecodeTransactionArgsToToken h₄ ho (by omega)
  have h₆ := safeRuntime_block_6974_fallthrough (by simp; omega) (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 228)
      (UInt256.land (calldataWord I.calldata 228) solcAddrMask) = ⟨0⟩
    rw [solcAddrMask_clean hgas]
    exact u256_sub_self _) h₅
  have h₇ := safeRuntime_block_6995 (by simp; omega) (by jump_dest) h₆
  have h₈ := safeRuntime_block_2334 (by simp; omega) (by jump_dest) h₇
  have h₉ := safeRuntime_block_7018_fallthrough (by simp; omega) (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 260)
      (UInt256.land (calldataWord I.calldata 260) solcAddrMask) = ⟨0⟩
    rw [solcAddrMask_clean href]
    exact u256_sub_self _) h₈
  have h₁₀ := safeRuntime_block_7040 (by simp; omega) (by jump_dest) h₉
  have h₁₁ := safeRuntime_block_2343 (by simp; omega) (by jump_dest) h₁₀
  exact ⟨_, _, h₁₁⟩

set_option maxHeartbeats 1000000 in
theorem safeDecodeTransactionArgsEvidence {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2253⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 24 ≤ 1024) :
    RDrev fork safeBytecode g s0 ∨
    ∃ len k' C', 324 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 ∧
      (calldataWord I.calldata 4).toNat < EVM.addressModulus ∧
      (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1 ∧
      calldataWord I.calldata (4 + (calldataWord I.calldata 68).toNat) =
        UInt256.ofNat len ∧ len ≤ 2 ^ 64 - 1 ∧
      4 + (calldataWord I.calldata 68).toNat + 32 + len ≤ I.calldata.size ∧
      (calldataWord I.calldata 100).toNat < 2 ∧
      (calldataWord I.calldata 228).toNat < EVM.addressModulus ∧
      (calldataWord I.calldata 260).toNat < EVM.addressModulus ∧
      RD fork safeBytecode I g s0 ⟨9040⟩ (transactionArgsStack I len R)
        mem aw rdata σ k' C' := by
  have hfail (hc : UInt256.slt
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (UInt256.ofNat 320) = ⟨1⟩) :
      RDrev fork safeBytecode g s0 := by
    have h₁ := safeRuntime_block_2253_taken (by simp; omega) (by
      rw [safeIRArgumentSizeSub hlong hsize]
      change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
        (UInt256.ofNat 320) ≠ ⟨0⟩
      rw [hc]
      decide) (by jump_dest) h
    exact safeRuntime_block_589 (by simp; omega) h₁
  by_cases hh : 324 ≤ I.calldata.size
  swap
  · exact Or.inl (hfail (solcDecodeLenCheckShort hlong (by simpa using Nat.lt_of_not_ge hh)
      hsize (by decide)))
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  swap
  · exact Or.inl (hfail (solcDecodeLenCheckHuge (by simpa using Nat.le_of_not_gt hhi)
      hsize (by decide)))
  obtain ⟨_, _, h₁⟩ := safeDecodeTransactionArgsStart h
    (solcDecodeLenCheckOk hh hhi hsize (by decide)) hlong hsize (by omega)
  by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · exact Or.inl (safeDecodeAddressNoncanon h₁ (by simp; omega) hc)
  obtain ⟨_, _, h₂⟩ := safeDecodeAddress h₁ (by simp; omega) hc (by jump_dest)
  by_cases hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1
  swap
  · have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
    have h₃ := safeRuntime_block_2273_taken (by simp; omega) (by
      change UInt256.gt (calldataWord I.calldata 68) _ ≠ UInt256.ofNat 0
      rw [hm, ugt_one (by
        change 2 ^ 64 - 1 < (calldataWord I.calldata 68).toNat; omega)]
      decide) (by jump_dest) h₂
    exact Or.inl (safeRuntime_block_973 (by simp; omega) h₃)
  obtain ⟨_, _, h₃⟩ := safeDecodeTransactionArgsToBytes h₂ hoff (by omega)
  rcases safeDecodeCalldataBytesEvidence h₃ (by omega) hsize (by simp; omega)
    (by jump_dest) with hr | ⟨len, k', C', hw, hn, hs, hin, h₄⟩
  · exact Or.inl hr
  by_cases ho : (calldataWord I.calldata 100).toNat < 2
  swap
  · have h₅ := safeRuntime_block_2304_taken (by omega) (by
      change UInt256.isZero (UInt256.lt (calldataWord I.calldata 100) ⟨2⟩) ≠ _
      rw [ult_zero (by change 2 ≤ (calldataWord I.calldata 100).toNat; omega)]
      decide) (by jump_dest) h₄
    exact Or.inl (safeRuntime_block_589 (by simp; omega) h₅)
  obtain ⟨_, _, h₅⟩ := safeDecodeTransactionArgsToToken h₄ ho (by omega)
  by_cases hgas : (calldataWord I.calldata 228).toNat < EVM.addressModulus
  swap
  · have h₆ := safeRuntime_block_6974_taken (by simp; omega) (by
      rw [safeAddressMask]
      change UInt256.sub (calldataWord I.calldata 228)
        (UInt256.land (calldataWord I.calldata 228) solcAddrMask) ≠ ⟨0⟩
      intro heq
      exact hgas ((u256_sub_eq_zero_iff_eq.mp heq) ▸ solcAddrMask_result_canonical _))
      (by jump_dest) h₅
    exact Or.inl (safeRuntime_block_111 (by
      simp [safeRuntime_block_6974_taken_stack]; omega) h₆)
  have h₆ := safeRuntime_block_6974_fallthrough (by simp; omega) (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 228)
      (UInt256.land (calldataWord I.calldata 228) solcAddrMask) = ⟨0⟩
    rw [solcAddrMask_clean hgas]
    exact u256_sub_self _) h₅
  have h₇ := safeRuntime_block_6995 (by simp; omega) (by jump_dest) h₆
  have h₈ := safeRuntime_block_2334 (by simp; omega) (by jump_dest) h₇
  by_cases href : (calldataWord I.calldata 260).toNat < EVM.addressModulus
  swap
  · have h₉ := safeRuntime_block_7018_taken (by simp; omega) (by
      rw [safeAddressMask]
      change UInt256.sub (calldataWord I.calldata 260)
        (UInt256.land (calldataWord I.calldata 260) solcAddrMask) ≠ ⟨0⟩
      intro heq
      exact href ((u256_sub_eq_zero_iff_eq.mp heq) ▸ solcAddrMask_result_canonical _))
      (by jump_dest) h₈
    exact Or.inl (safeRuntime_block_111 (by
      simp [safeRuntime_block_7018_taken_stack]; omega) h₉)
  obtain ⟨k'', C'', hdone⟩ := safeDecodeTransactionArgsValid h hh hs hc hoff hw hn hin ho
    hgas href hov
  exact Or.inr ⟨len, k'', C'', hh, hs, hc, hoff, hw, hn, hin, ho, hgas, href, hdone⟩

end Benchmarks.Safe.ViaIR
