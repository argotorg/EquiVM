import Benchmarks.Morpho.MorphoBlue.MarketTwoWordsTwoAddressesABI
import Benchmarks.Morpho.MorphoBlue.CalldataBytesDecode
import Benchmarks.Morpho.MorphoBlue.CreateMarketMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def marketTwoWordsTwoAddressesDecodeStack (cd : ByteArray) (R : List UInt256) : List UInt256 :=
  [calldataWord cd 260, calldataWord cd 228, calldataWord cd 196,
    calldataWord cd 164, UInt256.ofNat 128] ++ R

theorem morphoMarketTwoWordsTwoAddressesDecode {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ret : UInt256} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024) (hs : 4 ≤ ee.calldata.size) (hsize : ee.calldata.size < UInt256.size)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11928) (UInt256.ofNat ee.calldata.size :: ret :: R)
      solcFreePtrMem aw out σ k C) :
    (¬ MarketTwoWordsTwoAddressesBounds ee.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (MarketTwoWordsTwoAddressesBounds ee.calldata ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 ret
        (marketTwoWordsTwoAddressesDecodeStack ee.calldata R)
        (createMarketDecodedMem (marketParamsFromCalldata ee.calldata)) aw' out σ k' C') := by
  have hbad (hc : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩)
      (UInt256.ofNat 288) = ⟨1⟩) : RDrev (deployedRuntime v) g s0 := by
    have rd := morphoBlocks.morpho_block_11928_taken (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 4 ≤ 1024; omega)
      (by rw [wordAddNegFour, hc]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    exact morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v)) (by simp; omega) rd
  by_cases hl : 292 ≤ ee.calldata.size
  swap
  · exact .inl ⟨fun hb => hl hb.1,
      hbad (solcCalldataStaticLenCheckShort (words := 9) hs (by omega) hsize (by decide))⟩
  by_cases hh : ee.calldata.size < 2 ^ 255 + 4
  swap
  · exact .inl ⟨fun hb => by have hx := hb.2.1; omega,
      hbad (solcCalldataStaticLenCheckHuge (words := 9) (by omega) hsize (by decide))⟩
  have rd1 := morphoBlocks.morpho_block_11928_fallthrough (immWords := wordsOf (immStore v))
    (by simp; omega) (by rw [wordAddNegFour]; exact solcCalldataStaticLenCheckOk (words := 9) hl hh hsize) h
  have rd2 := morphoBlocks.morpho_block_11972 (immWords := wordsOf (immStore v))
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
  by_cases ha : (calldataWord ee.calldata 228).toNat < EVM.addressModulus
  swap
  · have rd := morphoBlocks.morpho_block_11980_taken (immWords := wordsOf (immStore v))
      (by simp; omega) (addressMaskSub_nonzero ha)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd4
    exact .inl ⟨fun hb ↦ ha hb.2.2.2.1,
      morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v)) (by change R.length + 6 + 2 ≤ 1024; omega) rd⟩
  have rd5 := morphoBlocks.morpho_block_11980_fallthrough (immWords := wordsOf (immStore v))
    (by simp; omega) (by
      change UInt256.sub (calldataWord ee.calldata 228)
        (UInt256.land (calldataWord ee.calldata 228) solcAddrMask) = ⟨0⟩
      rw [solcAddrMask_clean ha, u256_sub_self]) rd4
  by_cases hr : (calldataWord ee.calldata 260).toNat < EVM.addressModulus
  swap
  · have rd := morphoBlocks.morpho_block_12024_taken (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 5 ≤ 1024; omega) (addressMaskSub_nonzero hr)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd5
    exact .inl ⟨fun hb ↦ hr hb.2.2.2.2,
      morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v)) (by change R.length + 6 + 2 ≤ 1024; omega) rd⟩
  have rd6 := morphoBlocks.morpho_block_12024_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 5 ≤ 1024; omega) (by
      change UInt256.sub (calldataWord ee.calldata 260)
        (UInt256.land (calldataWord ee.calldata 260) solcAddrMask) = ⟨0⟩
      rw [solcAddrMask_clean hr, u256_sub_self]) rd5
  have rd7 := morphoBlocks.morpho_block_12038 (immWords := wordsOf (immStore v))
    (by change R.length + 4 + 2 ≤ 1024; omega) hvalid rd6
  exact .inr ⟨⟨hl, hh, hp, ha, hr⟩, a4, _, _, rd7⟩

end Benchmarks.Morpho.MorphoBlue
