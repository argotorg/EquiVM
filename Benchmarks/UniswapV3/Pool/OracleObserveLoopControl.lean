import Benchmarks.UniswapV3.Pool.DynamicWordArray
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_055

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleObserveStack (i : Nat) (secondsPtr ticksPtr card liquidity index tickRaw agoPtr timeRaw ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  UInt256.ofNat i :: secondsPtr :: ticksPtr :: card :: liquidity :: index :: tickRaw :: agoPtr ::
    timeRaw :: ⟨8⟩ :: ret :: R

theorem oracleObserveLoopCallX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C i : Nat} {aw agoPtr ticksPtr secondsPtr card liquidity index : UInt256}
    {tickRaw timeRaw ret : UInt256} {mem rdata : ByteArray} {rawAgos : List UInt256}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨17172⟩
      (oracleObserveStack i secondsPtr ticksPtr card liquidity index tickRaw agoPtr timeRaw ret R)
      mem aw rdata σ k C)
    (ha : ActiveWords aw) (hm : DynamicWordArrayMemory mem agoPtr rawAgos)
    (hb : agoPtr.toNat + 32 * (rawAgos.length + 1) ≤ 2 ^ 200)
    (hi : i < rawAgos.length) (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', C + (Cₘ (M aw (wordArrayElement agoPtr i) ⟨32⟩) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨13193⟩
        (card :: liquidity :: index :: tickRaw :: rawAgos[i] :: timeRaw :: ⟨8⟩ :: ⟨17215⟩ ::
          oracleObserveStack i secondsPtr ticksPtr card liquidity index tickRaw agoPtr timeRaw ret R)
        mem (M aw (wordArrayElement agoPtr i) ⟨32⟩) rdata σ k' C' := by
  have hn : rawAgos.length < UInt256.size := by change _ < 2 ^ 256; omega
  have hiw : i < UInt256.size := by omega
  have hfit : agoPtr.toNat + 32 * (rawAgos.length + 1) < UInt256.size := by
    change _ < 2 ^ 256; omega
  have hh := hm.header hfit
  have he := hm.element i hi hfit
  have hr := wordArrayElement_raw agoPtr i (by omega)
  have hnat := wordArrayElement_toNat agoPtr i (by omega)
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat rawAgos.length) = ⟨1⟩ :=
    ult_one (by rw [ulit_toNat' i hiw, ulit_toNat' _ hn]; exact hi)
  have hrep := expandedWords32_chain ha (le_refl agoPtr.toNat) (by omega)
  change M (M aw agoPtr ⟨32⟩) agoPtr ⟨32⟩ = M aw agoPtr ⟨32⟩ at hrep
  have hex := expandedWords32_chain ha (show agoPtr.toNat ≤ (wordArrayElement agoPtr i).toNat by
    rw [hnat]; omega) (by rw [hnat]; omega)
  change M (M aw agoPtr ⟨32⟩) (wordArrayElement agoPtr i) ⟨32⟩ =
    M aw (wordArrayElement agoPtr i) ⟨32⟩ at hex
  have r1 := uniswapV3Pool_block_17172_fallthrough (immWords := wordsOf (immStore v))
    (by dsimp only [oracleObserveStack, List.length]; omega) (by rw [hh, hlt]; decide) rd
  have r2 := uniswapV3Pool_block_17182_taken (immWords := wordsOf (immStore v))
    (by dsimp only [List.length]; omega) (by rw [hh, hlt]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
  simp only [hrep] at r2
  have r3 := uniswapV3Pool_block_17198 (immWords := wordsOf (immStore v))
    (by dsimp only [uniswapV3Pool_block_17182_taken_stack, List.length]; omega)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
  simp only [uniswapV3Pool_block_17198_stack, hr, he, hex] at r3
  refine ⟨_, _, ?_, r3⟩
  dsimp only [memExpansionCost]
  rw [hex]
  omega

theorem oracleObserveLoopDoneX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C i : Nat} {aw agoPtr ticksPtr secondsPtr card liquidity index : UInt256}
    {tickRaw timeRaw ret : UInt256} {mem rdata : ByteArray} {rawAgos : List UInt256}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨17172⟩
      (oracleObserveStack i secondsPtr ticksPtr card liquidity index tickRaw agoPtr timeRaw ret R)
      mem aw rdata σ k C)
    (hm : DynamicWordArrayMemory mem agoPtr rawAgos)
    (hb : agoPtr.toNat + 32 * (rawAgos.length + 1) < UInt256.size)
    (hi : rawAgos.length ≤ i) (hiw : i < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 13 ≤ 1024) :
    RD (deployedRuntime v) ee g s0 ret (secondsPtr :: ticksPtr :: R)
      mem (M aw agoPtr ⟨32⟩) rdata σ (k + 8 + 13)
      (C + (29 + memExpansionCost aw agoPtr ⟨32⟩) + 34) := by
  have hh := hm.header hb
  have hn : rawAgos.length < UInt256.size := by omega
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat rawAgos.length) = ⟨0⟩ :=
    ult_zero (by rw [ulit_toNat' i hiw, ulit_toNat' _ hn]; exact hi)
  have r1 := uniswapV3Pool_block_17172_taken (immWords := wordsOf (immStore v))
    (by dsimp only [oracleObserveStack, List.length]; omega) (by rw [hh, hlt]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  exact uniswapV3Pool_block_17300 (immWords := wordsOf (immStore v)) (by omega) hret r1

end Benchmarks.UniswapV3.Pool
