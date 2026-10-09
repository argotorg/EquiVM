import Benchmarks.Morpho.MorphoBlue.MarketWordTwoAddressesABI
import Benchmarks.Morpho.MorphoBlue.Address196Decode
import Benchmarks.Morpho.MorphoBlue.CalldataBytesDecode
import Benchmarks.Morpho.MorphoBlue.CreateMarketMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def withdrawCollateralDecodeStack (cd : ByteArray) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat 128, calldataWord cd 196, solcAddrMask, calldataWord cd 228,
    calldataWord cd 164, calldataWord cd 228, UInt256.ofNat 0] ++ R

theorem morphoWithdrawCollateralDecode {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024) (hs : 4 ≤ ee.calldata.size) (hsize : ee.calldata.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5398) (UInt256.ofNat 0 :: R)
      solcFreePtrMem aw out σ k C) :
    (¬ MarketWordTwoAddressesBounds ee.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (MarketWordTwoAddressesBounds ee.calldata ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5498)
        (withdrawCollateralDecodeStack ee.calldata R)
        (createMarketDecodedMem (marketParamsFromCalldata ee.calldata)) aw' out σ k' C') := by
  have hbad (hc : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩)
      (UInt256.ofNat 256) = ⟨1⟩) : RDrev (deployedRuntime v) g s0 := by
    have rd := morphoBlocks.morpho_block_5398_taken (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 3 ≤ 1024; omega)
      (by rw [wordAddNegFour, hc]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by simp; omega) rd
  by_cases hl : 260 ≤ ee.calldata.size
  swap
  · exact .inl ⟨fun hb => hl hb.1,
      hbad (solcCalldataStaticLenCheckShort (words := 8) hs (by omega) hsize (by decide))⟩
  by_cases hh : ee.calldata.size < 2 ^ 255 + 4
  swap
  · exact .inl ⟨fun hb => by have hx := hb.2.1; omega,
      hbad (solcCalldataStaticLenCheckHuge (words := 8) (by omega) hsize (by decide))⟩
  have rd1 := morphoBlocks.morpho_block_5398_fallthrough (immWords := wordsOf (immStore v))
    (by simp; omega) (by rw [wordAddNegFour]; exact solcCalldataStaticLenCheckOk (words := 8) hl hh hsize) h
  have rd2 := morphoBlocks.morpho_block_5441 (immWords := wordsOf (immStore v))
    (by simp; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hfree : memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 := solcFreePtrMem_mload64
  obtain ⟨a3, k3, C3, rd3⟩ := morphoDecodeMarketParamsPrefix (v := v) (by simp; omega)
    hsize (by omega) hh (by rw [hfree]; decide) rd2
  by_cases hp : (marketParamsFromCalldata ee.calldata).Canonical
  swap
  · exact .inl ⟨fun hb => hp hb.2.2.1,
      morphoDecodeMarketParamsNoncanonical (v := v) (by simp; omega) hp rd3⟩
  obtain ⟨a4, k4, C4, rd4⟩ := morphoDecodeMarketParamsOk (v := v) (by simp; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hp rd3
  rw [hfree] at rd4
  have rd5 := morphoBlocks.morpho_block_5449 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 3 ≤ 1024; omega) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd4
  by_cases ha : (calldataWord ee.calldata 196).toNat < EVM.addressModulus
  swap
  · exact .inl ⟨fun hb => ha hb.2.2.2.1,
      morphoDecodeAddress196Revert (v := v) (by change R.length + 3 + 4 ≤ 1024; omega) ha rd5⟩
  obtain ⟨k6, C6, rd6⟩ := morphoDecodeAddress196Ok (v := v)
    (by change R.length + 3 + 4 ≤ 1024; omega) (by rw [morphoPatchedValidJumps v]; jump_dest) ha rd5
  by_cases hr : (calldataWord ee.calldata 228).toNat < EVM.addressModulus
  swap
  · have rd := morphoBlocks.morpho_block_5460_taken (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 8 ≤ 1024; omega) (addressMaskSub_nonzero hr)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd6
    exact .inl ⟨fun hb ↦ hr hb.2.2.2.2,
      morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v)) (by change R.length + 7 + 2 ≤ 1024; omega) rd⟩
  have rd7 := morphoBlocks.morpho_block_5460_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 8 ≤ 1024; omega) (by
      change UInt256.sub (calldataWord ee.calldata 228)
        (UInt256.land (calldataWord ee.calldata 228) solcAddrMask) = ⟨0⟩
      rw [solcAddrMask_clean hr, u256_sub_self]) rd6
  dsimp only [morphoBlocks.morpho_block_5460_fallthrough_stack] at rd7
  change RD _ _ _ _ _
    ([UInt256.ofNat 128, calldataWord ee.calldata 196, solcAddrMask,
      calldataWord ee.calldata 228, calldataWord ee.calldata 164,
      UInt256.land (calldataWord ee.calldata 228) solcAddrMask, UInt256.ofNat 0] ++ R)
    _ _ _ _ _ _ at rd7
  rw [solcAddrMask_clean hr] at rd7
  exact .inr ⟨⟨hl, hh, hp, ha, hr⟩, a4, _, _, rd7⟩

end Benchmarks.Morpho.MorphoBlue
