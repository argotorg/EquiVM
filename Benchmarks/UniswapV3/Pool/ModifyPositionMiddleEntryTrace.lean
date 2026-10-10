import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleModel
import Benchmarks.UniswapV3.Pool.Slot0MemoryFields
import Benchmarks.UniswapV3.Pool.OracleWriteEntryTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_053

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem modifyPositionMiddleEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free key : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ (modifyPositionUpdatedState v a evm))
    (rd : RD (deployedRuntime v) ee g s0 ⟨16536⟩
      (p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hp : Slot0Memory mem p evm.accountMap evm.executionEnv)
    (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 15 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨14801⟩
      (oracleWriteEntryWords {modifyPositionMiddleOracleArgs v a evm with
        time := UInt256.ofNat ee.header.timestamp} ++
        ⟨16595⟩ :: modifyPositionMiddleLiquidity v a evm :: p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R)
      mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free := by
  have hpw : p.toNat + 224 < UInt256.size := by change _ < 2 ^ 256; omega
  have hpadd (n : Nat) (hn : n ≤ 128) : (p + UInt256.ofNat n).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)]
    omega
  have hl : poolLiquidityWord σ ee = modifyPositionMiddleLiquidity v a evm := by
    dsimp only [modifyPositionMiddleLiquidity]
    rw [hs.accounts, ← hs.env]
  have hm1 := hm.expand32 (p + UInt256.ofNat 64) (hpadd 64 (by decide))
  obtain ⟨k1, C1, r1⟩ := uniswapV3Pool_block_16536 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_16536_stack, hp.load_index hpw, solcMask128] at r1
  have hl' : UInt256.land (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac ↦ ac.storage.getD (UInt256.ofNat 4) ⟨0⟩)) (UInt256.ofNat (2 ^ 128 - 1)) =
      modifyPositionMiddleLiquidity v a evm := hl
  rw [hl'] at r1
  obtain ⟨k2, C2, r2⟩ := blockTimestampX (v := v) r1
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
  have r3 := uniswapV3Pool_block_16567 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
  simp only [uniswapV3Pool_block_16567_stack, hp.load_tick hpw, hp.load_cardinality hpw,
    hp.load_cardinalityNext hpw] at r3
  have hm3 := ((hm1.expand32 (p + UInt256.ofNat 32) (hpadd 32 (by decide))).expand32
    (p + UInt256.ofNat 96) (hpadd 96 (by decide))).expand32
      (p + UInt256.ofNat 128) (hpadd 128 (by decide))
  simp only [oracleWriteEntryWords, modifyPositionMiddleOracleArgs,
    List.cons_append, List.nil_append]
  exact ⟨_, _, _, r3, hm3⟩

end Benchmarks.UniswapV3.Pool
