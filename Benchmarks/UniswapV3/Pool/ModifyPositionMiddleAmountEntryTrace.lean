import Benchmarks.UniswapV3.Pool.ModifyPositionMemory
import Benchmarks.UniswapV3.Pool.Slot0MemoryFields
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_053

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem modifyPositionMiddleAmount0EntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q key free sqrtA sqrtB liquidity : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨16665⟩
      (sqrtB :: sqrtA :: ⟨16675⟩ :: liquidity :: p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hq : ModifyPositionParamsMemory mem q a)
    (hb : q.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 11 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨19588⟩
      (EVM.wordOfInt a.delta :: sqrtB :: sqrtA :: ⟨16675⟩ :: liquidity :: p ::
        ⟨0⟩ :: ⟨0⟩ :: key :: q :: R) mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free := by
  have hqw : q.toNat + 128 < UInt256.size := by change _ < 2 ^ 256; omega
  have hq96 := uadd_word_ofNat_toNat q 96 (show q.toNat + 96 < UInt256.size by omega)
  have hm' := hm.expand32 (q + UInt256.ofNat 96) (by rw [hq96]; omega)
  have rr := uniswapV3Pool_block_16665 (immWords := wordsOf (immStore v)) hov
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_16665_stack, u256_add_comm (UInt256.ofNat 96) q,
    hq.load_delta hqw] at rr
  exact ⟨_, _, _, rr, hm'⟩

theorem modifyPositionMiddleLowerEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q key free amount0 liquidity : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨16675⟩
      (amount0 :: liquidity :: p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hq : ModifyPositionParamsMemory mem q a)
    (hb : q.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 10 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨11629⟩
      (EVM.wordOfInt a.lower :: ⟨16693⟩ :: ⟨16705⟩ :: liquidity :: p :: ⟨0⟩ :: amount0 :: key :: q :: R)
      mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free := by
  have hqw : q.toNat + 128 < UInt256.size := by change _ < 2 ^ 256; omega
  have hq32 := uadd_word_ofNat_toNat q 32 (show q.toNat + 32 < UInt256.size by omega)
  have hm' := hm.expand32 (q + UInt256.ofNat 32) (by rw [hq32]; omega)
  have rr := uniswapV3Pool_block_16675 (immWords := wordsOf (immStore v)) hov
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_16675_stack, u256_add_comm (UInt256.ofNat 32) q,
    hq.load_lower hqw] at rr
  exact ⟨_, _, _, rr, hm'⟩

theorem modifyPositionMiddleAmount1EntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q key free sqrtA amount0 liquidity : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : ModifyPositionArgs) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨16693⟩
      (sqrtA :: ⟨16705⟩ :: liquidity :: p :: ⟨0⟩ :: amount0 :: key :: q :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hq : ModifyPositionParamsMemory mem q a)
    (hp : Slot0Memory mem p evm.accountMap evm.executionEnv)
    (hpb : p.toNat + 224 ≤ 2 ^ 200) (hqb : q.toNat + 128 ≤ 2 ^ 200)
    (hov : R.length + 11 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨19656⟩
      (EVM.wordOfInt a.delta :: slot0FieldWord 0 20 evm.accountMap evm.executionEnv :: sqrtA ::
        ⟨16705⟩ :: liquidity :: p :: ⟨0⟩ :: amount0 :: key :: q :: R)
      mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free := by
  have hpw : p.toNat + 224 < UInt256.size := by change _ < 2 ^ 256; omega
  have hqw : q.toNat + 128 < UInt256.size := by change _ < 2 ^ 256; omega
  have hq96 := uadd_word_ofNat_toNat q 96 (show q.toNat + 96 < UInt256.size by omega)
  have hm' := (hm.expand32 p (by omega)).expand32 (q + UInt256.ofNat 96) (by rw [hq96]; omega)
  have rr := uniswapV3Pool_block_16693 (immWords := wordsOf (immStore v)) hov
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_16693_stack, hp.load_sqrt hpw, hq.load_delta hqw] at rr
  exact ⟨_, _, _, rr, hm'⟩

theorem modifyPositionMiddleDeltaEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q key free amount0 amount1 liquidity : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨16705⟩
      (amount1 :: liquidity :: p :: ⟨0⟩ :: amount0 :: key :: q :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hq : ModifyPositionParamsMemory mem q a)
    (hb : q.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 10 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨13807⟩
      (EVM.wordOfInt a.delta :: liquidity :: ⟨16721⟩ :: liquidity :: p :: amount1 :: amount0 :: key :: q :: R)
      mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free := by
  have hqw : q.toNat + 128 < UInt256.size := by change _ < 2 ^ 256; omega
  have hq96 := uadd_word_ofNat_toNat q 96 (show q.toNat + 96 < UInt256.size by omega)
  have hm' := hm.expand32 (q + UInt256.ofNat 96) (by rw [hq96]; omega)
  have rr := uniswapV3Pool_block_16705 (immWords := wordsOf (immStore v)) hov
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_16705_stack, u256_add_comm (UInt256.ofNat 96) q,
    hq.load_delta hqw] at rr
  exact ⟨_, _, _, rr, hm'⟩

end Benchmarks.UniswapV3.Pool
