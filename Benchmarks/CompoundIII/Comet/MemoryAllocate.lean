import Benchmarks.CompoundIII.Comet.GetterCommon
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_036
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

def allocationEnd (ptr len : UInt256) : UInt256 :=
  ptr + UInt256.land (UInt256.lnot ⟨31⟩) (len + ⟨31⟩)

-- LIBRARY CANDIDATE: the solc bounded allocation guard and rounded pointer arithmetic.
theorem allocationEnd_bounded_toNat {ptr len : UInt256} {bound : Nat}
    (hlen : len.toNat ≤ 32 * bound) (hptr : ptr.toNat + 32 * bound < 2^64) :
    (allocationEnd ptr len).toNat = ptr.toNat + (len.toNat + 31) / 32 * 32 := by
  have hlenAdd : (len + (⟨31⟩ : UInt256)).toNat = len.toNat + 31 := by
    rw [uadd_toNat]
    change (len.toNat + 31) % UInt256.size = _
    exact Nat.mod_eq_of_lt (by change len.toNat + 31 < 2^256; omega)
  rw [allocationEnd, uadd_toNat, u256_land_comm, longDataCutoff_toNat, hlenAdd]
  exact Nat.mod_eq_of_lt (by change _ < 2^256; omega)

theorem allocationEnd_bounded_guard {ptr len : UInt256} {bound : Nat}
    (hlen : len.toNat ≤ 32 * bound) (hptr : ptr.toNat + 32 * bound < 2^64) :
    UInt256.lor (UInt256.lt (allocationEnd ptr len) ptr)
      (UInt256.gt (allocationEnd ptr len)
        (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨64⟩) ⟨1⟩)) = ⟨0⟩ := by
  have he := allocationEnd_bounded_toNat hlen hptr
  rw [ult_zero (by rw [he]; omega), ugt_zero (by
    rw [he]
    change _ ≤ 2^64 - 1
    omega)]
  rfl

theorem cometAllocateBounded {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr len ret : UInt256} {R : List UInt256} {bound : Nat}
    (hstack : R.length + 6 ≤ 1024) (hlen : len.toNat ≤ 32 * bound)
    (hptr : ptr.toNat + 32 * bound < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨6982⟩ (ptr :: len :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret R
      (writeWord mem 64 (allocationEnd ptr len)) aw' rdata σ k' C' := by
  have rd1 := cometWithExtendedAssetList_block_6982_fallthrough
    (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 5 ≤ 1024; omega) (allocationEnd_bounded_guard hlen hptr) h
  have rd2 := cometWithExtendedAssetList_block_7013
    (immWords := wordsOf (immStore v)) (by omega) hret rd1
  exact ⟨_, _, _, rd2⟩

theorem allocationEnd_toNat {ptr len : UInt256}
    (hlen : len.toNat ≤ 160) (hptr : ptr.toNat + 160 < 2^64) :
    (allocationEnd ptr len).toNat = ptr.toNat + (len.toNat + 31) / 32 * 32 :=
  allocationEnd_bounded_toNat (bound := 5) hlen hptr

theorem allocationEnd_guard {ptr len : UInt256}
    (hlen : len.toNat ≤ 160) (hptr : ptr.toNat + 160 < 2^64) :
    UInt256.lor (UInt256.lt (allocationEnd ptr len) ptr)
      (UInt256.gt (allocationEnd ptr len)
        (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨64⟩) ⟨1⟩)) = ⟨0⟩ :=
  allocationEnd_bounded_guard (bound := 5) hlen hptr

theorem cometAllocate160 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr len ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hlen : len.toNat ≤ 160)
    (hptr : ptr.toNat + 160 < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨6982⟩ (ptr :: len :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret R
      (writeWord mem 64 (allocationEnd ptr len)) aw' rdata σ k' C' :=
  cometAllocateBounded (bound := 5) hstack hlen hptr hret h

theorem allocationEnd_160 (ptr : UInt256) : allocationEnd ptr ⟨160⟩ = ptr + ⟨160⟩ := by
  rfl

theorem allocationEnd_256 (ptr : UInt256) : allocationEnd ptr ⟨256⟩ = ptr + ⟨256⟩ := by
  rfl

end Benchmarks.CompoundIII.Comet
