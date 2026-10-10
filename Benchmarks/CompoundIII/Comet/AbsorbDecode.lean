import Benchmarks.CompoundIII.Comet.AbsorbDecodeWords
import Benchmarks.CompoundIII.Comet.AddressDecodeCost
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_030

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometDecodeAbsorb {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hsz : 4 ≤ ee.calldata.size)
    (hsize : ee.calldata.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 ⟨5508⟩ R mem aw rdata σ k C) :
    if AbsorbCalldataValid ee.calldata then
      RD (deployedRuntime v) ee g s0 ⟨16664⟩
        (calldataWord ee.calldata 4 :: (calldataWord ee.calldata 36 + UInt256.ofNat 36) ::
          calldataWord ee.calldata (4 + absorbArrayOffset ee.calldata) :: ⟨22⟩ :: R)
        mem aw rdata σ (k + 76) (C + 278)
    else RDrev (deployedRuntime v) g s0 := by
  let off := calldataWord ee.calldata 36
  let len := calldataWord ee.calldata (4 + absorbArrayOffset ee.calldata)
  have hmask : (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1)).toNat = solcMaxU64 := u64mask_toNat
  have hsizeNat : (UInt256.ofNat ee.calldata.size).toNat = ee.calldata.size :=
    UInt256.toNat_ofNat_of_lt hsize
  by_cases hhead : 68 ≤ ee.calldata.size
  · by_cases hhiHead : ee.calldata.size < 2^255 + 4
    · have r1 := cometWithExtendedAssetList_block_5508_fallthrough
        (immWords := wordsOf (immStore v)) (by omega)
        (calldataLength_ok (need := 64) (by decide) hhead hhiHead hsize) h
      have r2 := cometWithExtendedAssetList_block_5520
        (immWords := wordsOf (immStore v)) (by omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      by_cases hc : (calldataWord ee.calldata 4).toNat < EVM.addressModulus
      · have r3 := cometValidateAddress_cost (v := v)
          (by change R.length + 1 + 5 ≤ 1024; omega) hc
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
        by_cases hoff : off.toNat ≤ solcMaxU64
        · have r4 := cometWithExtendedAssetList_block_5531_fallthrough
            (immWords := wordsOf (immStore v)) (by omega)
            (ugt_zero (by rw [hmask]; exact hoff)) r3
          by_cases hhi : ee.calldata.size < 2^255
          · by_cases hword : off.toNat + 36 ≤ ee.calldata.size
            · have hslt : UInt256.slt (off + UInt256.ofNat 35)
                  (UInt256.ofNat ee.calldata.size) = ⟨1⟩ := by
                apply slt_lit_one_low hhi
                rw [absorb_offset_add35_toNat hoff]
                omega
              have r5 := cometWithExtendedAssetList_block_5552_fallthrough
                (immWords := wordsOf (immStore v)) (by omega)
                (by change UInt256.isZero (UInt256.slt (off + UInt256.ofNat 35)
                      (UInt256.ofNat ee.calldata.size)) = _
                    rw [hslt]; rfl) r4
              have hload : uInt256OfByteArray (ee.calldata.readBytes
                  ((UInt256.ofNat 4) + off).toNat 32) = len := by
                change uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + off).toNat 32) = _
                rw [add4_word_toNat off hoff]
              by_cases hn : len.toNat ≤ solcMaxU64
              · have hgt : UInt256.gt len
                    (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
                      (UInt256.ofNat 1)) = ⟨0⟩ := ugt_zero (by rw [hmask]; exact hn)
                have r6 := cometWithExtendedAssetList_block_5563_fallthrough
                  (immWords := wordsOf (immStore v)) (by omega)
                  (by change UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes
                        ((UInt256.ofNat 4) + off).toNat 32)) _ = _
                      rw [hload]; exact hgt) r5
                change RD _ _ _ _ _ (calldataWord ee.calldata 4 ::
                  uInt256OfByteArray (ee.calldata.readBytes ((UInt256.ofNat 4) + off).toNat 32) ::
                  off :: R)
                  _ _ _ _ _ _ at r6
                rw [hload] at r6
                have hend := uadd_shift5_add36_toNat off len hoff hn
                by_cases hbound : off.toNat + 36 + 32 * len.toNat ≤ ee.calldata.size
                · have hvalid : AbsorbCalldataValid ee.calldata :=
                    ⟨hhead, hhi, hc, hoff, hword, hn, hbound⟩
                  rw [if_pos hvalid]
                  have r7 := cometWithExtendedAssetList_block_5575_fallthrough
                    (immWords := wordsOf (immStore v)) hstack
                    (ugt_zero (by rw [hend, hsizeNat]; omega)) r6
                  have r8 := cometWithExtendedAssetList_block_5590
                    (immWords := wordsOf (immStore v)) (by omega)
                    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r7
                  simpa only [Nat.add_assoc] using r8
                · rw [if_neg (by intro hv; exact hbound hv.2.2.2.2.2.2)]
                  have r7 := cometWithExtendedAssetList_block_5575_taken
                    (immWords := wordsOf (immStore v)) hstack
                    (by rw [ugt_one (by rw [hend, hsizeNat]; omega)]; decide)
                    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
                  exact cometRevert1410 (by change R.length + 3 + 2 ≤ 1024; omega) r7
              · rw [if_neg (by intro hv; exact hn hv.2.2.2.2.2.1)]
                have r6 := cometWithExtendedAssetList_block_5563_taken
                  (immWords := wordsOf (immStore v)) (by omega)
                  (by change UInt256.gt (uInt256OfByteArray (ee.calldata.readBytes
                        ((UInt256.ofNat 4) + off).toNat 32)) _ ≠ _
                      rw [hload, ugt_one (by rw [hmask]; omega)]; decide)
                  (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
                exact cometRevert1410 (by change R.length + 3 + 2 ≤ 1024; omega) r6
            · rw [if_neg (by intro hv; exact hword hv.2.2.2.2.1)]
              have hslt : UInt256.slt (off + UInt256.ofNat 35)
                  (UInt256.ofNat ee.calldata.size) = ⟨0⟩ := by
                apply slt_lit_zero hhi
                · rw [absorb_offset_add35_toNat hoff]; omega
                · exact absorb_offset_add35_small hoff
              have r5 := cometWithExtendedAssetList_block_5552_taken
                (immWords := wordsOf (immStore v)) (by omega)
                (by change UInt256.isZero (UInt256.slt (off + UInt256.ofNat 35)
                      (UInt256.ofNat ee.calldata.size)) ≠ _
                    rw [hslt]; decide)
                (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
              exact cometRevert1410 (by change R.length + 3 + 2 ≤ 1024; omega) r5
          · rw [if_neg (by intro hv; exact hhi hv.2.1)]
            have hslt : UInt256.slt (off + UInt256.ofNat 35)
                (UInt256.ofNat ee.calldata.size) = ⟨0⟩ :=
              slt_zero_low_high (absorb_offset_add35_small hoff) (by rw [hsizeNat]; omega)
            have r5 := cometWithExtendedAssetList_block_5552_taken
              (immWords := wordsOf (immStore v)) (by omega)
              (by change UInt256.isZero (UInt256.slt (off + UInt256.ofNat 35)
                    (UInt256.ofNat ee.calldata.size)) ≠ _
                  rw [hslt]; decide)
              (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
            exact cometRevert1410 (by change R.length + 3 + 2 ≤ 1024; omega) r5
        · rw [if_neg (by intro hv; exact hoff hv.2.2.2.1)]
          have r4 := cometWithExtendedAssetList_block_5531_taken
            (immWords := wordsOf (immStore v)) (by omega)
            (by rw [ugt_one (by rw [hmask]; exact Nat.lt_of_not_ge hoff)]; decide)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
          exact cometRevert1410 (by change R.length + 3 + 2 ≤ 1024; omega) r4
      · rw [if_neg (by intro hv; exact hc hv.2.2.1)]
        exact cometValidateAddress_bad (v := v)
          (by change R.length + 2 + 4 ≤ 1024; omega) hc r2
    · rw [if_neg (by intro hv; have := hv.2.1; omega)]
      have r1 := cometWithExtendedAssetList_block_5508_taken
        (immWords := wordsOf (immStore v)) (by omega)
        (calldataLength_huge (need := 64) (by decide) (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      exact cometRevert1410 (by omega) r1
  · rw [if_neg (by intro hv; exact hhead hv.1)]
    have r1 := cometWithExtendedAssetList_block_5508_taken
      (immWords := wordsOf (immStore v)) (by omega)
      (calldataLength_short (need := 64) (by decide) hsz (by omega) hsize)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    exact cometRevert1410 (by omega) r1

end Benchmarks.CompoundIII.Comet
