import Benchmarks.CompoundIII.Comet.AddressDecodeCost
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_016
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_075
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_076
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_077

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def absorbAccountsStack (i : Nat) (base absorber : UInt256) (n : Nat) (R : List UInt256) :=
  UInt256.ofNat i :: base :: ⟨1⟩ :: absorber :: UInt256.ofNat n :: R

def absorbAccountOffset (base : UInt256) (i : Nat) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat i) ⟨5⟩ + base

theorem cometAbsorbAccountsRead {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw base absorber : UInt256} {σ : AccountMap} {k C i n : Nat} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024) (hi : i < n) (hn : n < 2^64)
    (h : RD (deployedRuntime v) ee g s0 ⟨16695⟩
      (absorbAccountsStack i base absorber n R) mem aw rdata σ k C) :
    RD (deployedRuntime v) ee g s0 ⟨1393⟩
      (calldataWord ee.calldata (absorbAccountOffset base i).toNat :: ⟨2425⟩ ::
        calldataWord ee.calldata (absorbAccountOffset base i).toNat ::
        ⟨16966⟩ :: ⟨16972⟩ :: UInt256.ofNat i :: ⟨1⟩ ::
        base :: ⟨1⟩ :: absorber :: UInt256.ofNat n :: R)
      mem aw rdata σ (k + 39) (C + 141) := by
  have hin : (UInt256.ofNat i).toNat = i :=
    UInt256.toNat_ofNat_of_lt (by change i < 2^256; omega)
  have hnn : (UInt256.ofNat n).toNat = n :=
    UInt256.toNat_ofNat_of_lt (by change n < 2^256; omega)
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat n) = ⟨1⟩ :=
    ult_one (by rw [hin, hnn]; exact hi)
  have r1 := cometWithExtendedAssetList_block_16695_taken
    (immWords := wordsOf (immStore v)) (by omega) (by rw [hlt]; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_16942
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_16519_fallthrough
    (immWords := wordsOf (immStore v))
    (by change R.length + 9 + 4 ≤ 1024; omega) (by rw [hlt]; decide) r2
  have r4 := cometWithExtendedAssetList_block_16529
    (immWords := wordsOf (immStore v))
    (by change R.length + 8 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
  have r5 := cometWithExtendedAssetList_block_16961
    (immWords := wordsOf (immStore v))
    (by change R.length + 9 + 1 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
  have r6 := cometWithExtendedAssetList_block_16557
    (immWords := wordsOf (immStore v))
    (by change R.length + 8 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
  simpa only [Nat.add_assoc] using r6

theorem cometAbsorbAccountsEnter {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw base absorber : UInt256} {σ : AccountMap} {k C i n : Nat} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024) (hi : i < n) (hn : n < 2^64)
    (hc : (calldataWord ee.calldata (absorbAccountOffset base i).toNat).toNat <
      EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 ⟨16695⟩
      (absorbAccountsStack i base absorber n R) mem aw rdata σ k C) :
    RD (deployedRuntime v) ee g s0 ⟨16978⟩
      (absorber :: calldataWord ee.calldata (absorbAccountOffset base i).toNat ::
        ⟨16972⟩ :: UInt256.ofNat i :: ⟨1⟩ :: base :: ⟨1⟩ ::
        absorber :: UInt256.ofNat n :: R) mem aw rdata σ (k + 58) (C + 214) := by
  have r1 := cometAbsorbAccountsRead (v := v) hstack hi hn h
  have r2 := cometValidateAddress_cost (v := v)
    (by change R.length + 9 + 5 ≤ 1024; omega) hc
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_2425
    (immWords := wordsOf (immStore v))
    (by change R.length + 7 + 2 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  have r4 := cometWithExtendedAssetList_block_16966
    (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 9 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
  simpa only [Nat.add_assoc] using r4

theorem cometAbsorbAccountsIncrement {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw base absorber : UInt256} {σ : AccountMap} {k C i n : Nat} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 ⟨16972⟩
      (UInt256.ofNat i :: ⟨1⟩ :: base :: ⟨1⟩ :: absorber :: UInt256.ofNat n :: R)
      mem aw rdata σ k C) :
    RD (deployedRuntime v) ee g s0 ⟨16695⟩
      (absorbAccountsStack (i + 1) base absorber n R) mem aw rdata σ (k + 4) (C + 15) := by
  have hr := cometWithExtendedAssetList_block_16972
    (immWords := wordsOf (immStore v)) (by change R.length + 4 + 2 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simpa only [cometWithExtendedAssetList_block_16972_stack, absorbAccountsStack,
    u256_add_comm (UInt256.ofNat i) ⟨1⟩, u256_one_add_ofNat] using hr

theorem cometAbsorbAccountsExit {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw base absorber : UInt256} {σ : AccountMap} {k C i n : Nat} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hi : n ≤ i) (hi256 : i < UInt256.size)
    (hn256 : n < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 ⟨16695⟩
      (absorbAccountsStack i base absorber n R) mem aw rdata σ k C) :
    RD (deployedRuntime v) ee g s0 ⟨16703⟩
      (absorbAccountsStack i base absorber n R) mem aw rdata σ (k + 6) (C + 23) := by
  exact cometWithExtendedAssetList_block_16695_fallthrough
    (immWords := wordsOf (immStore v)) hstack
    (ult_zero (by simpa only [UInt256.toNat_ofNat_of_lt hi256,
      UInt256.toNat_ofNat_of_lt hn256] using hi)) h

end Benchmarks.CompoundIII.Comet
