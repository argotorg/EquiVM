import Benchmarks.UniswapV3.Pool.FlashProtocolTrace
import Benchmarks.UniswapV3.Pool.FlashGrowthSource
import Benchmarks.UniswapV3.Pool.FullMathTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_026

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def flashGrowthReturn (second : Bool) : UInt256 := if second then ⟨7409⟩ else ⟨7270⟩
def flashUpdateExit (second : Bool) : UInt256 := if second then ⟨7421⟩ else ⟨7282⟩

def flashUpdateRest (paid1 paid0 after1 after0 before1 before0 fee1 fee0 liquidity : UInt256)
    (R : List UInt256) : List UInt256 :=
  paid1 :: paid0 :: after1 :: after0 :: before1 :: before0 :: fee1 :: fee0 :: liquidity :: R

theorem flashGrowthBuildX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw fees divisor paid1 paid0 after1 after0 before1 before0 fee1 fee0 liquidity : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (flashGrowthEntry second)
      (fees :: divisor :: flashUpdateRest paid1 paid0 after1 after0 before1 before0 fee1 fee0 liquidity R)
      mem aw rdata σ k C) (hliquidity : liquidity.toNat < 2 ^ 128) (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨13017⟩
      (liquidity :: UInt256.ofNat (2 ^ 128) :: UInt256.sub (if second then paid1 else paid0) fees ::
        flashGrowthReturn second :: fees :: divisor ::
        flashUpdateRest paid1 paid0 after1 after0 before1 before0 fee1 fee0 liquidity R)
      mem aw rdata σ k' C' := by
  have hclean : UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) liquidity = liquidity :=
    uint128Word_clean hliquidity
  cases second
  · have rdCall := uniswapV3Pool_block_7244 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_7244_stack, solcMask128] at rdCall
    exact ⟨_, _, by simpa only [solcShift128, hclean] using rdCall⟩
  · have rdCall := uniswapV3Pool_block_7383 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_7383_stack, solcMask128] at rdCall
    exact ⟨_, _, by simpa only [solcShift128, hclean] using rdCall⟩

theorem flashGrowthStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw amount fees divisor : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (flashGrowthReturn second)
      (amount :: fees :: divisor :: R) mem aw rdata σ k C)
    (hperm : ee.perm = true) (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (flashUpdateExit second) R mem aw rdata
      (addFeeGrowthMap σ ee second amount) k' C' := by
  cases second
  · obtain ⟨k', C', rdDone⟩ := uniswapV3Pool_block_7270 (immWords := wordsOf (immStore v))
      hov hperm rd
    refine ⟨k', C', ?_⟩
    simpa only [addFeeGrowthMap, feeGrowthSlot, feeGrowthWord, Bool.false_eq_true, ↓reduceIte,
      solcSlotWordAt, solcSlotWord, u256_add_comm] using rdDone
  · obtain ⟨k', C', rdDone⟩ := uniswapV3Pool_block_7409 (immWords := wordsOf (immStore v))
      hov hperm rd
    refine ⟨k', C', ?_⟩
    simpa only [addFeeGrowthMap, feeGrowthSlot, feeGrowthWord, ↓reduceIte,
      solcSlotWordAt, solcSlotWord, u256_add_comm] using rdDone

theorem flashGrowthX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat}
    {aw fees divisor paid1 paid0 after1 after0 before1 before0 fee1 fee0 liquidity : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (locals : Store) (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (flashGrowthEntry second)
      (fees :: divisor :: flashUpdateRest paid1 paid0 after1 after0 before1 before0 fee1 fee0 liquidity R)
      mem aw rdata σ k C) (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hp : locals.get? (flashPaidName second) =
      some (.int (Int.ofNat (if second then paid1 else paid0).toNat)))
    (hf : locals.get? (flashProtocolFeesName second) = some (.int (Int.ofNat fees.toNat)))
    (hl : locals.get? "_liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (hbase : locals.get? (feeGrowthName second) = none)
    (hliquidity : liquidity.toNat < 2 ^ 128) (hov : R.length + 27 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
        (flashGrowthStmts second) .reverted) ∨
    let amount := flashGrowthResult (if second then paid1 else paid0) fees liquidity
    SourceState s0 ee (addFeeGrowthMap σ ee second amount) (addFeeGrowth evm second amount) ∧
      ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
        (flashGrowthStmts second)
        (.ok (flashGrowthFrame locals (immStore v) second
          (if second then paid1 else paid0) fees liquidity) (addFeeGrowth evm second amount)) ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 (flashUpdateExit second)
        (flashUpdateRest paid1 paid0 after1 after0 before1 before0 fee1 fee0 liquidity R)
        mem aw rdata (addFeeGrowthMap σ ee second amount) k' C' := by
  obtain ⟨_, _, rdCall⟩ := flashGrowthBuildX (v := v) second rd hliquidity (by omega)
  rcases fullMathX (v := v) rdCall
      (by rw [uniswapV3PoolPatchedValidJumps v]; cases second <;> native_decide)
      (by simpa only [flashUpdateRest, List.length_cons] using hov) with
    ⟨hbad, rdBad⟩ | ⟨hgood, _, _, _, rdReturn⟩
  · exact Or.inl ⟨rdBad, flashGrowthReverts locals (immStore v) evm second _ fees liquidity
      hp hf hl hbad⟩
  · refine Or.inr ⟨SourceState.addFeeGrowth hs second _,
      flashGrowthReturns locals (immStore v) evm second _ fees liquidity hp hf hl hbase hgood, ?_⟩
    exact flashGrowthStoreX (v := v) second rdReturn hperm
      (by simp only [flashUpdateRest, List.length_cons]; omega)

end Benchmarks.UniswapV3.Pool
