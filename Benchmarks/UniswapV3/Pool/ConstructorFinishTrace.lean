import Benchmarks.UniswapV3.Pool.ConstructorRuntime
import Benchmarks.UniswapV3.Pool.CreationBlocks_002

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolCreationBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem constructorFinalReadWords (original : AccountAddress) (out : ByteArray)
    (hlen : 160 ≤ out.size) :
    let mem := constructorFinalMem original out
    let words := wordsOf (immStore (constructorValuation original out))
    UInt256.shiftRight (memLoad (UInt256.ofNat 128) mem) (UInt256.ofNat 96) = words "original" ∧
    UInt256.shiftRight (memLoad (UInt256.ofNat 160) mem) (UInt256.ofNat 96) = words "factory" ∧
    UInt256.shiftRight (memLoad (UInt256.ofNat 192) mem) (UInt256.ofNat 96) = words "token0" ∧
    UInt256.shiftRight (memLoad (UInt256.ofNat 224) mem) (UInt256.ofNat 96) = words "token1" ∧
    UInt256.shiftRight (memLoad (UInt256.ofNat 256) mem) (UInt256.ofNat 232) = words "fee" ∧
    UInt256.shiftRight (memLoad (UInt256.ofNat 288) mem) (UInt256.ofNat 232) = words "tickSpacing" ∧
    UInt256.shiftRight (memLoad (UInt256.ofNat 320) mem) (UInt256.ofNat 128) =
      words "maxLiquidityPerTick" := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [constructorFinalMem_load original out hlen 128 (constructorOriginalWord original)
      (by simp [constructorStoredFields]), wordsOf_immStore_original]
    exact constructorOriginalWord_decode original
  · rw [constructorFinalMem_load original out hlen 160
      (constructorAddressStored (calldataWord out 0)) (by simp [constructorStoredFields]),
      wordsOf_immStore_factory]
    exact constructorAddressStored_decode _
  · rw [constructorFinalMem_load original out hlen 192
      (constructorAddressStored (calldataWord out 32)) (by simp [constructorStoredFields]),
      wordsOf_immStore_token0]
    exact constructorAddressStored_decode _
  · rw [constructorFinalMem_load original out hlen 224
      (constructorAddressStored (calldataWord out 64)) (by simp [constructorStoredFields]),
      wordsOf_immStore_token1]
    exact constructorAddressStored_decode _
  · rw [constructorFinalMem_load original out hlen 256
      (constructorFeeStored (calldataWord out 96)) (by simp [constructorStoredFields]),
      wordsOf_immStore_fee, wordOfInt_ofNat_toNat]
    simpa only [constructorValuation] using constructorFeeStored_decode out
  · rw [constructorFinalMem_load original out hlen 288
      (constructorSpacingStored (calldataWord out 128)) (by simp [constructorStoredFields]),
      wordsOf_immStore_tickSpacing, wordOfInt_ofNat_toNat]
    simpa only [constructorValuation] using constructorSpacingStored_decode out
  · rw [constructorFinalMem_load original out hlen 320
      (constructorLiquidityStored (EVM.wordOfInt (spacingLiquidity (constructorSpacing out))))
      (by simp [constructorStoredFields]), wordsOf_immStore_maxLiquidityPerTick, wordOfInt_ofNat_toNat]
    simpa only [constructorValuation] using constructorLiquidityStored_decode out

theorem constructorRuntimeSummaryMem (tail : ByteArray) (original : AccountAddress)
    (out : ByteArray) (hlen : 160 ≤ out.size) :
    uniswapV3PoolCreation_block_381_memory (tail := tail) (mem := constructorFinalMem original out) =
      writeCascade uniswapV3PoolBytecode
        ((constructorPatchWrites (wordsOf (immStore (constructorValuation original out)))).take 9) := by
  obtain ⟨_, _, _, _, hf, hs, hm⟩ := constructorFinalReadWords original out hlen
  unfold uniswapV3PoolCreation_block_381_memory
  rw [hm, hs, hf]
  have hcopy : (uniswapV3PoolCreationBytecode ++ tail).write (UInt256.ofNat 586).toNat
      (constructorFinalMem original out) (UInt256.ofNat 0).toNat (UInt256.ofNat 22142).toNat =
      uniswapV3PoolBytecode :=
    constructorRuntimeCopy tail _ (by rw [constructorFinalMem_size _ _ hlen]; decide)
  rw [hcopy]
  rfl

theorem constructorPatchedRuntime_read (words : String → UInt256) :
    (constructorPatchedRuntime words).readWithPadding 0 22142 = constructorPatchedRuntime words := by
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by decide)
    (by rw [constructorPatchedRuntime_size])]
  change (constructorPatchedRuntime words).extract 0 22142 = _
  rw [← constructorPatchedRuntime_size words, byteArray_extract_self]

theorem constructorFinishX {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {σ : AccountMap} {aw : UInt256} {k C : Nat} {out : ByteArray}
    (rd : RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨381⟩ []
      (constructorFinalMem ee.codeOwner out) aw out σ k C) (hlen : 160 ≤ out.size) :
    RDret (uniswapV3PoolCreationBytecode ++ tail) g s0 σ
      (deployedRuntime (constructorValuation ee.codeOwner out)) := by
  let words := wordsOf (immStore (constructorValuation ee.codeOwner out))
  obtain ⟨ho, hf, h0, h1, hfee, ht, hm⟩ := constructorFinalReadWords ee.codeOwner out hlen
  have rp := uniswapV3PoolCreation_block_381 (by decide) rd
  simp only [uniswapV3PoolCreation_block_381_stack, ho, hf, h0, h1, hfee] at rp
  rw [constructorRuntimeSummaryMem tail _ _ hlen] at rp
  have rr := uniswapV3PoolCreation_block_488 (by decide) rp
  change RDret (uniswapV3PoolCreationBytecode ++ tail) g s0 σ
    ((writeCascade (writeCascade uniswapV3PoolBytecode ((constructorPatchWrites words).take 9))
      ((constructorPatchWrites words).drop 9)).readWithPadding 0 22142) at rr
  rw [← writeCascade_append, List.take_append_drop] at rr
  change RDret (uniswapV3PoolCreationBytecode ++ tail) g s0 σ
    ((constructorPatchedRuntime words).readWithPadding 0 22142) at rr
  rw [constructorPatchedRuntime_read, constructorPatchedRuntime_eq] at rr
  exact rr

end Benchmarks.UniswapV3.Pool
