import Benchmarks.EAS.EAS.WordArrayDecode
import Benchmarks.EAS.EAS.WordArrayGuards

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

private theorem arrayStartNat {cd : ByteArray} (ho : wordArrayOffset cd ≤ solcMaxU64) :
    (UInt256.ofNat 4 + calldataWord cd 4).toNat = 4 + wordArrayOffset cd :=
  add4_word_toNat _ ho

private theorem arrayReadLength {cd : ByteArray} (ho : wordArrayOffset cd ≤ solcMaxU64) :
    calldataWord cd (UInt256.ofNat 4 + calldataWord cd 4).toNat = UInt256.ofNat (wordArrayLength cd) := by
  rw [arrayStartNat ho]
  exact (u256_ofNat_toNat _).symm

private theorem arrayDataStart {cd : ByteArray} (ho : wordArrayOffset cd ≤ solcMaxU64) :
    (UInt256.ofNat 4 + calldataWord cd 4) + UInt256.ofNat 32 = UInt256.ofNat (wordArrayOffset cd + 36) := by
  have hb : wordArrayOffset cd + 36 < UInt256.size := by
    change wordArrayOffset cd ≤ 18446744073709551615 at ho
    change wordArrayOffset cd + 36 < 2^256
    omega
  apply u256_inj
  rw [uadd_toNat, arrayStartNat ho, ofNat_toNat_lt _ hb]
  change (4 + wordArrayOffset cd + 32) % UInt256.size = wordArrayOffset cd + 36
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The shared array decoder instantiated at the first ABI argument. -/
theorem easWordArrayDecode {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 8 ≤ 1024) (hsize : ee.calldata.size < UInt256.size)
    (ho : wordArrayOffset ee.calldata ≤ solcMaxU64)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4225⟩
      ((UInt256.ofNat 4 + calldataWord ee.calldata 4) :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata σ k C) :
    if wordArrayValid ee.calldata then
      ∃ k' C', RD fork (deployedRuntime v) ee g s0 ret
        (UInt256.ofNat (wordArrayLength ee.calldata) :: UInt256.ofNat (wordArrayOffset ee.calldata + 36) :: R)
        mem aw rdata σ k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hh : wordArrayOffset ee.calldata + 36 ≤ ee.calldata.size ∧ ee.calldata.size < 2^255
  · have hg : UInt256.isZero (UInt256.slt ((UInt256.ofNat 4 + calldataWord ee.calldata 4) + UInt256.ofNat 31)
        (UInt256.ofNat ee.calldata.size)) = ⟨0⟩ := by
      rw [arrayHeaderGuard ho hsize]
      change UInt256.fromBool (!decide (wordArrayOffset ee.calldata + 36 ≤ ee.calldata.size ∧ ee.calldata.size < 2^255)) = ⟨0⟩
      rw [decide_eq_true hh]
      rfl
    by_cases hn : wordArrayLength ee.calldata ≤ solcMaxU64
    · have hnword : (calldataWord ee.calldata (UInt256.ofNat 4 + calldataWord ee.calldata 4).toNat).toNat =
          wordArrayLength ee.calldata := by rw [arrayStartNat ho]; rfl
      have hglen : UInt256.gt (calldataWord ee.calldata (UInt256.ofNat 4 + calldataWord ee.calldata 4).toNat)
          (UInt256.ofNat 18446744073709551615) = ⟨0⟩ := by
        apply ugt_zero
        rw [hnword]
        exact hn
      have hex : (((UInt256.shiftLeft (calldataWord ee.calldata (UInt256.ofNat 4 + calldataWord ee.calldata 4).toNat)
          (UInt256.ofNat 5)) + (UInt256.ofNat 4 + calldataWord ee.calldata 4)) + UInt256.ofNat 32).toNat =
          wordArrayOffset ee.calldata + 36 + 32 * wordArrayLength ee.calldata := by
        rw [arrayExtent_toNat ho (by rwa [hnword]), hnword]
        rfl
      by_cases hp : wordArrayOffset ee.calldata + 36 + 32 * wordArrayLength ee.calldata ≤ ee.calldata.size
      · rw [if_pos (show wordArrayValid ee.calldata from ⟨ho, hh.2, hh.1, hn, hp⟩)]
        obtain ⟨k', C', rd'⟩ := easWordArrayDecode_ok v hstack hg hglen
          (ugt_zero (by rw [hex, ofNat_toNat_lt _ hsize]; exact hp)) hvalid rd
        rw [arrayReadLength ho, arrayDataStart ho] at rd'
        exact ⟨k', C', rd'⟩
      · rw [if_neg (by intro h; exact hp h.2.2.2.2)]
        exact easWordArrayDecode_revert_extent v hstack hg hglen
          (by rw [ugt_one (by rw [hex, ofNat_toNat_lt _ hsize]; omega)]; decide) rd
    · rw [if_neg (by intro h; exact hn h.2.2.2.1)]
      exact easWordArrayDecode_revert_length v (by omega) hg
        (by rw [ugt_one (by rw [arrayStartNat ho]; exact Nat.lt_of_not_ge hn)]; decide) rd
  · rw [if_neg (by intro h; exact hh ⟨h.2.2.1, h.2.1⟩)]
    exact easWordArrayDecode_revert_header v (by omega)
      (by
        rw [arrayHeaderGuard ho hsize]
        change UInt256.fromBool (!decide (wordArrayOffset ee.calldata + 36 ≤ ee.calldata.size ∧ ee.calldata.size < 2^255)) ≠ ⟨0⟩
        rw [decide_eq_false hh]
        decide) rd

end Benchmarks.EAS.EAS
