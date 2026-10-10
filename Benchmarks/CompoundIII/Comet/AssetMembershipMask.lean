import Benchmarks.CompoundIII.Comet.AssetMembershipFieldEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometCheckedSub8_ok {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {x y ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hx : x.toNat < 2^8) (hy : y.toNat < 2^8)
    (hle : y.toNat ≤ x.toNat)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨11438⟩ (x :: y :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (UInt256.sub x y :: R)
      mem aw rdata σ k' C' := by
  have hc (w : UInt256) (hw : w.toNat < 2^8) : UInt256.land (UInt256.ofNat 255) w = w := by
    rw [u256_land_comm]; exact u256LandMaskCleanOfToNat _ _ (bits := 8) rfl hw
  have r1 := cometWithExtendedAssetList_block_11438_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
    (by rw [hc x hx, hc y hy]; exact ult_zero hle) h
  dsimp only [cometWithExtendedAssetList_block_11438_fallthrough_stack] at r1
  rw [hc x hx, hc y hy] at r1
  have r2 := cometWithExtendedAssetList_block_11453
    (immWords := wordsOf (immStore v)) (by omega) hret r1
  exact ⟨_, _, r2⟩

-- LIBRARY CANDIDATE: a canonical bit position and a sufficiently wide mask preserve its bit.
theorem maskedWordBit (offset mask : UInt256) (width : Nat)
    (ho : offset.toNat < 256) (hb : offset.toNat < width)
    (hm : mask.toNat = 2^width - 1) :
    UInt256.land (UInt256.shiftLeft (UInt256.ofNat 1) offset) mask =
      UInt256.ofNat (2^offset.toNat) := by
  rw [wordBitMask offset ho]
  apply u256LandMaskCleanOfToNat _ _ hm
  rw [UInt256.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide) ho)]
  exact Nat.pow_lt_pow_right (by decide) hb

theorem cometMembershipMask16 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw offset ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (ho : offset.toNat < 16)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨14209⟩ (offset :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (UInt256.ofNat (2^offset.toNat) :: R) mem aw rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_14209
    (immWords := wordsOf (immStore v)) hstack hret h
  dsimp only [cometWithExtendedAssetList_block_14209_stack] at r1
  rw [u256LandMaskCleanOfToNat offset (UInt256.ofNat 255) (bits := 8) rfl (by change offset.toNat < 256; omega),
    u256_land_comm (UInt256.ofNat 65535),
    maskedWordBit offset (UInt256.ofNat 65535) 16 (by omega) ho rfl] at r1
  exact ⟨_, _, r1⟩

theorem cometMembershipMask8 {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw offset ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (ho : offset.toNat < 8)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨14290⟩ (offset :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (UInt256.ofNat (2^offset.toNat) :: R) mem aw rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_14290
    (immWords := wordsOf (immStore v)) hstack hret h
  dsimp only [cometWithExtendedAssetList_block_14290_stack] at r1
  rw [u256_land_comm (UInt256.ofNat 255),
    u256LandMaskCleanOfToNat offset (UInt256.ofNat 255) (bits := 8) rfl (by change offset.toNat < 256; omega),
    maskedWordBit offset (UInt256.ofNat 255) 8 (by omega) ho rfl] at r1
  exact ⟨_, _, r1⟩

end Benchmarks.CompoundIII.Comet
