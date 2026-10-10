import Benchmarks.CompoundIII.Comet.TwoAddressGetter
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_014

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

abbrev TwoAddressUintCalldataValid (I : ExecutionEnv) : Prop :=
  100 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
    (calldataWord I.calldata 4).toNat < EVM.addressModulus ∧
    (calldataWord I.calldata 36).toNat < EVM.addressModulus

theorem cometDecodeTwoAddressesUint {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {ret : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024) (hsz : 4 ≤ ee.calldata.size)
    (hsize : ee.calldata.size < UInt256.size)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨2001⟩
      (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata σ k C) :
    if TwoAddressUintCalldataValid ee then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (calldataWord ee.calldata 68 :: calldataWord ee.calldata 36 ::
          calldataWord ee.calldata 4 :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hlo : 100 ≤ ee.calldata.size
  · by_cases hhi : ee.calldata.size < 2 ^ 255 + 4
    · have rd1 := cometWithExtendedAssetList_block_2001_fallthrough
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (solcCalldataStaticLenCheckOk (words := 3) hlo hhi hsize) h
      have rd2 := cometWithExtendedAssetList_block_2013
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
      by_cases hc₀ : (calldataWord ee.calldata 4).toNat < EVM.addressModulus
      · obtain ⟨k₃, C₃, rd3⟩ := cometValidateAddress_ok (v := v) (ret := ⟨2023⟩)
          (by change R.length + 3 + 5 ≤ 1024; omega) hc₀
          (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd2
        have rd4 := cometWithExtendedAssetList_block_2023
          (immWords := wordsOf (immStore v)) (by omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd3
        by_cases hc₁ : (calldataWord ee.calldata 36).toNat < EVM.addressModulus
        · simp only [TwoAddressUintCalldataValid, hlo, hhi, hc₀, hc₁, and_self, if_true]
          obtain ⟨k₅, C₅, rd5⟩ := cometValidateAddress_ok (v := v) (ret := ⟨2040⟩)
            (by change R.length + 5 + 5 ≤ 1024; omega) hc₁
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd4
          have rd6 := cometWithExtendedAssetList_block_2040
            (immWords := wordsOf (immStore v))
            (by change R.length + 1 + 4 ≤ 1024; omega) hvalid rd5
          exact ⟨_, _, rd6⟩
        · simp only [TwoAddressUintCalldataValid, hc₁, and_false, if_false]
          exact cometValidateAddress_bad (v := v)
            (by change R.length + 6 + 4 ≤ 1024; omega) hc₁ rd4
      · simp only [TwoAddressUintCalldataValid, hc₀, false_and, and_false, if_false]
        exact cometValidateAddress_bad (v := v)
          (by change R.length + 4 + 4 ≤ 1024; omega) hc₀ rd2
    · simp only [TwoAddressUintCalldataValid, hhi, false_and, and_false, if_false]
      have rd1 := cometWithExtendedAssetList_block_2001_taken
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [solcCalldataStaticLenCheckHuge (words := 3) (by omega) hsize (by decide)]; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      exact cometRevert1410 (by change R.length + 2 + 2 ≤ 1024; omega) rd1
  · simp only [TwoAddressUintCalldataValid, hlo, false_and, if_false]
    have rd1 := cometWithExtendedAssetList_block_2001_taken
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [solcCalldataStaticLenCheckShort (words := 3) hsz (by omega) hsize (by decide)]
          decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    exact cometRevert1410 (by change R.length + 2 + 2 ≤ 1024; omega) rd1

end Benchmarks.CompoundIII.Comet
