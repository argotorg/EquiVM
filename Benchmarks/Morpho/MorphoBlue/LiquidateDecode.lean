import Benchmarks.Morpho.MorphoBlue.LiquidateABI
import Benchmarks.Morpho.MorphoBlue.CalldataBytesDecode
import Benchmarks.Morpho.MorphoBlue.CreateMarketMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def liquidateDecodeStack (cd : ByteArray) (R : List UInt256) : List UInt256 :=
  [calldataWord cd (4 + (calldataWord cd 260).toNat),
    (UInt256.ofNat 4 + calldataWord cd 260) + UInt256.ofNat 32,
    UInt256.ofNat 0, UInt256.ofNat 128] ++ R

theorem morphoLiquidateDecode {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024) (hs : 4 ≤ ee.calldata.size) (hsize : ee.calldata.size < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1260) (UInt256.ofNat 0 :: R)
      solcFreePtrMem aw out σ k C) :
    (¬ LiquidateBounds ee.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (LiquidateBounds ee.calldata ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1378)
        (liquidateDecodeStack ee.calldata R)
        (createMarketDecodedMem (marketParamsFromCalldata ee.calldata)) aw' out σ k' C') := by
  have hbad (hc : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩)
      (UInt256.ofNat 288) = ⟨1⟩) : RDrev (deployedRuntime v) g s0 := by
    have rd := morphoBlocks.morpho_block_1260_taken (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 3 ≤ 1024; omega)
      (by rw [wordAddNegFour, hc]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by simp; omega) rd
  by_cases hl : 292 ≤ ee.calldata.size
  swap
  · exact .inl ⟨fun hb => hl hb.1,
      hbad (solcCalldataStaticLenCheckShort (words := 9) hs (by omega) hsize (by decide))⟩
  by_cases hh : ee.calldata.size < 2 ^ 255 + 4
  swap
  · exact .inl ⟨fun hb => by have hx := hb.2.1; omega,
      hbad (solcCalldataStaticLenCheckHuge (words := 9) (by omega) hsize (by decide))⟩
  have rd1 := morphoBlocks.morpho_block_1260_fallthrough (immWords := wordsOf (immStore v))
    (by simp; omega) (by rw [wordAddNegFour]; exact solcCalldataStaticLenCheckOk (words := 9) hl hh hsize) h
  have rd2 := morphoBlocks.morpho_block_1303 (immWords := wordsOf (immStore v))
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
  by_cases ha : (calldataWord ee.calldata 164).toNat < EVM.addressModulus
  swap
  · have rd := morphoBlocks.morpho_block_1311_taken (immWords := wordsOf (immStore v))
      (by simp; omega) (addressMaskSub_nonzero ha)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd4
    exact .inl ⟨fun hb ↦ ha hb.2.2.2.1,
      morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v)) (by change R.length + 2 + 2 ≤ 1024; omega) rd⟩
  have rd5 := morphoBlocks.morpho_block_1311_fallthrough (immWords := wordsOf (immStore v))
    (by simp; omega) (by
      change UInt256.sub (calldataWord ee.calldata 164)
        (UInt256.land (calldataWord ee.calldata 164) solcAddrMask) = ⟨0⟩
      rw [solcAddrMask_clean ha, u256_sub_self]) rd4
  by_cases ho : (calldataWord ee.calldata 260).toNat ≤ solcMaxU64
  swap
  · have rd := morphoBlocks.morpho_block_1346_taken (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 3 ≤ 1024; omega)
      (by rw [ugt_one (by change solcMaxU64 < (calldataWord ee.calldata 260).toNat; omega)]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd5
    exact .inl ⟨fun hb ↦ ho hb.2.2.2.2.1,
      morphoBlocks.morpho_block_1249 (immWords := wordsOf (immStore v)) (by change R.length + 1 + 2 ≤ 1024; omega) rd⟩
  have rd6 := morphoBlocks.morpho_block_1346_fallthrough (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 3 ≤ 1024; omega) (ugt_zero ho) rd5
  have rd8 := morphoBlocks.morpho_block_1365 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 4 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd6
  have hstart : (UInt256.ofNat 4 + calldataWord ee.calldata 260).toNat =
      4 + (calldataWord ee.calldata 260).toNat := add4_word_toNat _ ho
  rcases morphoDecodeCalldataBytes (v := v) (start := UInt256.ofNat 4 + calldataWord ee.calldata 260)
      (by change R.length + 2 + 8 ≤ 1024; omega)
      (by rw [hstart]; norm_num [solcMaxU64] at ho; omega) hsize
      (by rw [morphoPatchedValidJumps v]; jump_dest) rd8 with
    ⟨hb, hr⟩ | ⟨hh', hb, k9, C9, rd9⟩
  · rw [hstart] at hb
    exact .inl ⟨fun hh => hb ⟨hh.2.1, hh.2.2.2.2.2⟩, hr⟩
  · rw [hstart] at hb rd9
    exact .inr ⟨⟨hl, hh', hp, ha, ho, hb⟩, a4, _, _, rd9⟩

end Benchmarks.Morpho.MorphoBlue
