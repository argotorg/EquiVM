import Benchmarks.CompoundIII.Comet.ThreeAddressUintCalldata
import Benchmarks.CompoundIII.Comet.TwoAddressUintDecode
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_015

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

theorem cometDecodeThreeAddressesUint {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ret : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024) (hsz : 4 ≤ ee.calldata.size)
    (hsize : ee.calldata.size < UInt256.size)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨2215⟩
      (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata σ k C) :
    if ThreeAddressUintCalldataValid ee then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (calldataWord ee.calldata 100 :: calldataWord ee.calldata 68 ::
          calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hlo : 132 ≤ ee.calldata.size
  · by_cases hhi : ee.calldata.size < 2^255+4
    · have r1 := cometWithExtendedAssetList_block_2215_fallthrough
        (immWords := wordsOf (immStore v)) (by omega)
        (solcCalldataStaticLenCheckOk (words := 4) hlo hhi hsize) h
      have r2 := cometWithExtendedAssetList_block_2228
        (immWords := wordsOf (immStore v)) (by omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      change RD _ _ _ _ _ (calldataWord ee.calldata 4 :: UInt256.ofNat 2238 ::
        calldataWord ee.calldata 4 :: ret :: UInt256.ofNat 4 :: R) _ _ _ _ _ _ at r2
      by_cases hc0 : (calldataWord ee.calldata 4).toNat < EVM.addressModulus
      · obtain ⟨_, _, r3⟩ := cometValidateAddress_ok (v := v) (ret := ⟨2238⟩)
          (by change R.length + 3 + 5 ≤ 1024; omega) hc0
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
        have r4 := cometWithExtendedAssetList_block_2238
          (immWords := wordsOf (immStore v)) (by omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
        change RD _ _ _ _ _ (calldataWord ee.calldata 36 :: UInt256.ofNat 2253 ::
          calldataWord ee.calldata 36 :: UInt256.ofNat 4 :: ret :: calldataWord ee.calldata 4 :: R)
          _ _ _ _ _ _ at r4
        by_cases hc1 : (calldataWord ee.calldata 36).toNat < EVM.addressModulus
        · obtain ⟨_, _, r5⟩ := cometValidateAddress_ok (v := v) (ret := ⟨2253⟩)
            (by change R.length + 4 + 5 ≤ 1024; omega) hc1
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
          have r6 := cometWithExtendedAssetList_block_2253
            (immWords := wordsOf (immStore v)) (by change R.length + 1 + 8 ≤ 1024; omega)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
          change RD _ _ _ _ _ (calldataWord ee.calldata 68 :: UInt256.ofNat 2040 ::
            calldataWord ee.calldata 68 :: UInt256.ofNat 96 :: ret :: UInt256.ofNat 4 ::
              calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: R) _ _ _ _ _ _ at r6
          by_cases hc2 : (calldataWord ee.calldata 68).toNat < EVM.addressModulus
          · rw [if_pos ⟨hlo, hhi, hc0, hc1, hc2⟩]
            obtain ⟨_, _, r7⟩ := cometValidateAddress_ok (v := v) (ret := ⟨2040⟩)
              (by change R.length + 6 + 5 ≤ 1024; omega) hc2
              (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r6
            have r8 := cometWithExtendedAssetList_block_2040
              (immWords := wordsOf (immStore v)) (by change R.length + 2 + 4 ≤ 1024; omega)
              hvalid r7
            exact ⟨_, _, r8⟩
          · rw [if_neg (fun hh ↦ hc2 hh.2.2.2.2)]
            exact cometValidateAddress_bad (v := v)
              (by change R.length + 7 + 4 ≤ 1024; omega) hc2 r6
        · rw [if_neg (fun hh ↦ hc1 hh.2.2.2.1)]
          exact cometValidateAddress_bad (v := v)
            (by change R.length + 5 + 4 ≤ 1024; omega) hc1 r4
      · rw [if_neg (fun hh ↦ hc0 hh.2.2.1)]
        exact cometValidateAddress_bad (v := v)
          (by change R.length + 4 + 4 ≤ 1024; omega) hc0 r2
    · rw [if_neg (fun hh ↦ hhi hh.2.1)]
      have r1 := cometWithExtendedAssetList_block_2215_taken
        (immWords := wordsOf (immStore v)) (by omega)
        (by rw [solcCalldataStaticLenCheckHuge (words := 4) (by omega) hsize (by decide)]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      exact cometRevert1410 (by change R.length + 2 + 2 ≤ 1024; omega) r1
  · rw [if_neg (fun hh ↦ hlo hh.1)]
    have r1 := cometWithExtendedAssetList_block_2215_taken
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [solcCalldataStaticLenCheckShort (words := 4) hsz (by omega) hsize (by decide)]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    exact cometRevert1410 (by change R.length + 2 + 2 ≤ 1024; omega) r1

end Benchmarks.CompoundIII.Comet
