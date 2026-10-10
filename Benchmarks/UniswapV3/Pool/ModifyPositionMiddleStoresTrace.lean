import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleStoresSource
import Benchmarks.UniswapV3.Pool.ModifyPositionMemory
import Benchmarks.UniswapV3.Pool.Slot0MemoryFields
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_053

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000
attribute [local irreducible] modifyPositionUpdatedState modifyPositionMiddleOracleState
  oracleWriteResultIndex oracleWriteResultCardinality

theorem modifyPositionMiddleStoresX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free key : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ (modifyPositionMiddleOracleState v a evm))
    (rd : RD (deployedRuntime v) ee g s0 ⟨16595⟩
      (oracleWriteResultCardinality (modifyPositionMiddleOracleArgs v a evm)
          (modifyPositionUpdatedState v a evm) ::
        oracleWriteResultIndex (modifyPositionMiddleOracleArgs v a evm)
          (modifyPositionUpdatedState v a evm) ::
        modifyPositionMiddleLiquidity v a evm :: p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hq : ModifyPositionParamsMemory mem q a)
    (hp : Slot0Memory mem p evm.accountMap evm.executionEnv)
    (hpb : p.toNat + 224 ≤ 2 ^ 200) (hqb : q.toNat + 128 ≤ 2 ^ 200)
    (hperm : ee.perm = true) (hov : R.length + 13 ≤ 1024) :
    ∃ σ' aw' k' C', SourceState s0 ee σ' (modifyPositionMiddleStoresState v a evm) ∧
      RD (deployedRuntime v) ee g s0 ⟨11629⟩
        (EVM.wordOfInt a.upper :: ⟨16665⟩ :: slot0FieldWord 0 20 evm.accountMap evm.executionEnv ::
          ⟨16675⟩ :: modifyPositionMiddleLiquidity v a evm :: p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R)
        mem aw' rdata σ' k' C' ∧ HeapMemory mem aw' free := by
  have hpw : p.toNat + 224 < UInt256.size := by change _ < 2 ^ 256; omega
  have hqw : q.toNat + 128 < UInt256.size := by change _ < 2 ^ 256; omega
  have hq64 := uadd_word_ofNat_toNat q 64 (show q.toNat + 64 < UInt256.size by omega)
  have hm' := (hm.expand32 p (by omega)).expand32 (q + UInt256.ofNat 64) (by rw [hq64]; omega)
  let update := fun old ↦
    slot0ObservationWord (slot0ObservationWord old
      (oracleWriteResultCardinality (modifyPositionMiddleOracleArgs v a evm)
        (modifyPositionUpdatedState v a evm)) true)
      (oracleWriteResultIndex (modifyPositionMiddleOracleArgs v a evm)
        (modifyPositionUpdatedState v a evm)) false
  have hs' := hs.readModifyWrite ⟨0⟩ update
  change SourceState s0 ee _ (modifyStorageWord (modifyPositionMiddleOracleState v a evm) ⟨0⟩ update) at hs'
  dsimp only [update] at hs'
  rw [← storeSlot0ObservationPair_eq] at hs'
  obtain ⟨k', C', rr⟩ := uniswapV3Pool_block_16595 (immWords := wordsOf (immStore v)) hov hperm
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_16595_stack, hq.load_upper hqw, hp.load_sqrt hpw] at rr
  simp only [slot0ObservationWord_evm, Bool.false_eq_true, if_false, if_true] at hs'
  exact ⟨_, _, _, _, hs', rr, hm'⟩

end Benchmarks.UniswapV3.Pool
