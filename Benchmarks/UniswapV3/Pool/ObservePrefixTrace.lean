import Benchmarks.UniswapV3.Pool.ObserveInputTrace
import Benchmarks.UniswapV3.Pool.OracleObserveFunctionTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem observePrefixX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {rdata : ByteArray} {k C n start : Nat} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨9436⟩
      (UInt256.ofNat n :: UInt256.ofNat start :: R) solcFreePtrMem ⟨3⟩ rdata σ k C)
    (hn : n ≤ 2 ^ 32) (hstart : start < UInt256.size) (hov : R.length + 16 ≤ 1024) :
    (ee.codeOwner ≠ v.original ∧ RDrev (deployedRuntime v) g s0) ∨
    (ee.codeOwner = v.original ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨16967⟩
      (slot0FieldWord 25 2 σ ee :: poolLiquidityWord σ ee :: slot0FieldWord 23 2 σ ee ::
        EVM.wordOfInt (slot0TickValue σ ee) :: ⟨128⟩ :: UInt256.ofNat ee.header.timestamp ::
        ⟨8⟩ :: ⟨9566⟩ :: ⟨96⟩ :: ⟨96⟩ :: UInt256.ofNat n :: UInt256.ofNat start :: R)
      (observeInputMem ee.calldata start n) (observeInputAw n) rdata σ k' C') := by
  have r1 := uniswapV3Pool_block_9436 (immWords := wordsOf (immStore v))
    (by dsimp only [List.length]; omega)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_9436_stack] at r1
  rcases noDelegateCallX (v := v) r1
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
    (by dsimp only [List.length]; omega) with ⟨hr, hs⟩ | ⟨hs, k2, C2, r2⟩
  · exact Or.inl ⟨hs, hr⟩
  · have r3 := uniswapV3Pool_block_9447 (immWords := wordsOf (immStore v))
      (by dsimp only [List.length]; omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
    simp only [uniswapV3Pool_block_9447_stack] at r3
    obtain ⟨k4, C4, r4⟩ := blockTimestampX (v := v) r3
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by dsimp only [List.length]; omega)
    exact Or.inr ⟨hs, observeInputX (v := v) r4 hn hstart hov⟩

theorem observeOracleX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {rdata : ByteArray} {k C : Nat} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨16967⟩
      (slot0FieldWord 25 2 σ ee :: poolLiquidityWord σ ee :: slot0FieldWord 23 2 σ ee ::
        EVM.wordOfInt (slot0TickValue σ ee) :: ⟨128⟩ :: UInt256.ofNat ee.header.timestamp ::
        ⟨8⟩ :: ⟨9566⟩ :: ⟨96⟩ :: ⟨96⟩ :: UInt256.ofNat (observeCount ee.calldata) ::
        UInt256.ofNat (observeDataStart ee.calldata) :: R)
      (observeInputMem ee.calldata (observeDataStart ee.calldata) (observeCount ee.calldata))
      (observeInputAw (observeCount ee.calldata)) rdata σ k C)
    (hc : ObserveCalldataValid ee.calldata) (hsize : ee.calldata.size < UInt256.size)
    (hov : R.length + 68 ≤ 1024) :
    OracleObserveOutcome v ee g s0 σ rdata ⟨9566⟩
      (⟨96⟩ :: ⟨96⟩ :: UInt256.ofNat (observeCount ee.calldata) ::
        UInt256.ofNat (observeDataStart ee.calldata) :: R)
      (blockTimestampWord ee) (observeRawAgos ee.calldata) (slot0TickValue σ ee)
      (slot0FieldWord 23 2 σ ee) (poolLiquidityWord σ ee) (slot0FieldWord 25 2 σ ee) ⟨128⟩
      (observeInputMem ee.calldata (observeDataStart ee.calldata) (observeCount ee.calldata))
      (observeInputAw (observeCount ee.calldata)) (observeInputFree (observeCount ee.calldata)) C := by
  obtain ⟨hm, ha, hcover, hbudget⟩ := observeInputMemory ee.calldata
    (observeDataStart ee.calldata) (observeCount ee.calldata) hc.count hc.payload
  have hn : (observeRawAgos ee.calldata).length = observeCount ee.calldata :=
    calldataWordList_length _ _ _
  apply oracleObserveX (v := v) rd
  · exact u256LandMaskToNatLtOfToNat _ _ (by decide)
  · exact u256LandMaskToNatLtOfToNat _ _ (by decide)
  · exact u256_land_comm _ _
  · rw [slot0TickWord, signextend_idem ⟨24, by decide⟩ _ _ (by decide) (by decide)]
  · exact poolLiquidityWord_lt _ _
  · rw [hn]; have := hc.count; omega
  · exact hm.cursor
  · exact ha
  · decide
  · rw [hn]
    have hf : (observeInputFree (observeCount ee.calldata)).toNat =
        160 + 32 * observeCount ee.calldata := ulit_toNat' _
      (by have := hc.count; change _ < 2 ^ 256; omega)
    rw [hf]
    change 128 + 32 * (observeCount ee.calldata + 1) ≤ _
    omega
  · exact hbudget.mono_cost (Nat.zero_le C)
  · exact le_refl _
  · exact hcover
  · exact hsize
  · rw [uniswapV3PoolPatchedValidJumps v]; jump_dest
  · dsimp only [List.length]; omega

end Benchmarks.UniswapV3.Pool
