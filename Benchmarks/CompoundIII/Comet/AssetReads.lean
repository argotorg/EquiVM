import Benchmarks.CompoundIII.Comet.AbiRoutines
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_018
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_031
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_036
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_037

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def assetMask64 : UInt256 := UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨64⟩) ⟨1⟩

theorem cometRead64_ok {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hc : (memLoad ptr mem).toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7126⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (memLoad ptr mem :: R)
      mem aw' rdata σ k' C' := by
  have hm : UInt256.land (memLoad ptr mem) assetMask64 = memLoad ptr mem :=
    u256LandMaskCleanOfToNat _ _ (by decide : assetMask64.toNat = 2^64 - 1) hc
  have r1 := cometWithExtendedAssetList_block_7126_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.sub (memLoad ptr mem) (UInt256.land (memLoad ptr mem) assetMask64) = ⟨0⟩
      rw [hm, u256_sub_self]) h
  have r2 := cometWithExtendedAssetList_block_7145
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 1 ≤ 1024; omega) hret r1
  exact ⟨_, _, _, r2⟩

theorem cometRead64_bad {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hc : ¬ (memLoad ptr mem).toNat < 2^64)
    (h : RD (deployedRuntime v) ee g s0 ⟨7126⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hm : memLoad ptr mem ≠ UInt256.land (memLoad ptr mem) assetMask64 := by
    intro he
    have hb := u256LandMaskToNatLtOfToNat (memLoad ptr mem) assetMask64
      (by decide : assetMask64.toNat = 2^64 - 1)
    rw [← he] at hb
    exact hc hb
  have r1 := cometWithExtendedAssetList_block_7126_taken
    (immWords := wordsOf (immStore v)) hstack (u256_sub_ne_zero_of_ne hm)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  exact cometRevert1410 (by change R.length + 2 + 2 ≤ 1024; omega) r1

def assetMask128 : UInt256 := UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨128⟩) ⟨1⟩

theorem cometRead128_ok {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hc : (memLoad ptr mem).toNat < 2^128)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7146⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (memLoad ptr mem :: R)
      mem aw' rdata σ k' C' := by
  have hm : UInt256.land (memLoad ptr mem) assetMask128 = memLoad ptr mem :=
    u256LandMaskCleanOfToNat _ _ (by decide : assetMask128.toNat = 2^128 - 1) hc
  have r1 := cometWithExtendedAssetList_block_7146_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.sub (memLoad ptr mem) (UInt256.land (memLoad ptr mem) assetMask128) = ⟨0⟩
      rw [hm, u256_sub_self]) h
  have r2 := cometWithExtendedAssetList_block_7165
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 1 ≤ 1024; omega) hret r1
  exact ⟨_, _, _, r2⟩

theorem cometRead128_bad {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hc : ¬ (memLoad ptr mem).toNat < 2^128)
    (h : RD (deployedRuntime v) ee g s0 ⟨7146⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hm : memLoad ptr mem ≠ UInt256.land (memLoad ptr mem) assetMask128 := by
    intro he
    have hb := u256LandMaskToNatLtOfToNat (memLoad ptr mem) assetMask128
      (by decide : assetMask128.toNat = 2^128 - 1)
    rw [← he] at hb
    exact hc hb
  have r1 := cometWithExtendedAssetList_block_7146_taken
    (immWords := wordsOf (immStore v)) hstack (u256_sub_ne_zero_of_ne hm)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  exact cometRevert1410 (by change R.length + 2 + 2 ≤ 1024; omega) r1

theorem cometValidate8_ok {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {w ret : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hc : w.toNat < 2^8)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨5782⟩ (w :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret R mem aw rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_5782_fallthrough
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
    (by change UInt256.sub (UInt256.land w ⟨255⟩) w = ⟨0⟩
        rw [lowByteClean hc, u256_sub_self]) h
  have r2 := cometWithExtendedAssetList_block_5792
    (immWords := wordsOf (immStore v)) (by omega) hret r1
  exact ⟨_, _, r2⟩

theorem cometValidate8_bad {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {w : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024) (hc : ¬ w.toNat < 2^8)
    (h : RD (deployedRuntime v) ee g s0 ⟨5782⟩ (w :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hn : UInt256.land w ⟨255⟩ ≠ w := fun h ↦ hc ((lowByteClean_iff w).mp h)
  have r1 := cometWithExtendedAssetList_block_5782_taken
    (immWords := wordsOf (immStore v)) hstack (u256_sub_ne_zero_of_ne hn)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  exact cometRevert1410 (by change R.length + 2 ≤ 1024; omega) r1

theorem cometRead8_ok {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hc : (memLoad ptr mem).toNat < 2^8)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7104⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (memLoad ptr mem :: R)
      mem aw' rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_7104
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨k2, C2, r2⟩ := cometValidate8_ok (v := v)
    (by change R.length + 2 + 4 ≤ 1024; omega) hc
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_3121
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 1 ≤ 1024; omega) hret r2
  exact ⟨_, _, _, r3⟩

theorem cometRead8_bad {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hc : ¬ (memLoad ptr mem).toNat < 2^8)
    (h : RD (deployedRuntime v) ee g s0 ⟨7104⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_7104
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  exact cometValidate8_bad (v := v) (by change R.length + 3 + 3 ≤ 1024; omega) hc r1

theorem cometReadAddress_ok {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hc : (memLoad ptr mem).toNat < 2^160)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7115⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (memLoad ptr mem :: R)
      mem aw' rdata σ k' C' := by
  have r1 := cometWithExtendedAssetList_block_7115
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨k2, C2, r2⟩ := cometValidateAddress_ok (v := v)
    (by change R.length + 2 + 5 ≤ 1024; omega) hc
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_3121
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 1 ≤ 1024; omega) hret r2
  exact ⟨_, _, _, r3⟩

theorem cometReadAddress_bad {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hc : ¬ (memLoad ptr mem).toNat < 2^160)
    (h : RD (deployedRuntime v) ee g s0 ⟨7115⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_7115
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  exact cometValidateAddress_bad (v := v) (by change R.length + 3 + 4 ≤ 1024; omega) hc r1

end Benchmarks.CompoundIII.Comet
