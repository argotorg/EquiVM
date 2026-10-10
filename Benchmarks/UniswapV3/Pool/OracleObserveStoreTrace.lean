import Benchmarks.UniswapV3.Pool.OracleObserveArrays
import Benchmarks.UniswapV3.Pool.SignedWords
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_055

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleObserveLoopStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C i n : Nat} {aw ticksPtr secondsPtr tickRaw secondsRaw : UInt256}
    {tickValue secondsValue : Int} {mem rdata : ByteArray} {R : List UInt256}
    {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨17215⟩
      (secondsRaw :: tickRaw :: UInt256.ofNat i :: secondsPtr :: ticksPtr :: R) mem aw rdata σ k C)
    (ha : ActiveWords aw) (ht : memLoad ticksPtr mem = UInt256.ofNat n)
    (hs : memLoad secondsPtr mem = UInt256.ofNat n) (hi : i < n)
    (hts : ticksPtr.toNat + 32 * (n + 1) ≤ secondsPtr.toNat)
    (hsb : secondsPtr.toNat + 32 * (n + 1) ≤ 2 ^ 200)
    (htw : UInt256.signextend (UInt256.ofNat 6) tickRaw = EVM.wordOfInt tickValue)
    (hsw : UInt256.land secondsRaw (UInt256.ofNat (2 ^ 160 - 1)) = EVM.wordOfInt secondsValue)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', C + (Cₘ (M aw (wordArrayElement secondsPtr i) ⟨32⟩) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨17172⟩
        (UInt256.ofNat (i + 1) :: secondsPtr :: ticksPtr :: R)
        (oracleObserveUpdateMem mem ticksPtr secondsPtr i tickValue secondsValue)
        (M aw (wordArrayElement secondsPtr i) ⟨32⟩) rdata σ k' C' := by
  have hn : n < UInt256.size := by change _ < 2 ^ 256; omega
  have hiw : i < UInt256.size := by omega
  have hfitT : ticksPtr.toNat + 32 * (i + 1) < UInt256.size := by
    change _ < 2 ^ 256; omega
  have hfitS : secondsPtr.toNat + 32 * (i + 1) < UInt256.size := by
    change _ < 2 ^ 256; omega
  have hrawT := wordArrayElement_raw ticksPtr i hfitT
  have hrawS := wordArrayElement_raw secondsPtr i hfitS
  have hnatT := wordArrayElement_toNat ticksPtr i hfitT
  have hnatS := wordArrayElement_toNat secondsPtr i hfitS
  have hbS : (wordArrayElement secondsPtr i).toNat + 32 ≤ 2 ^ 200 := by rw [hnatS]; omega
  have hbT : (wordArrayElement ticksPtr i).toNat + 32 ≤ 2 ^ 200 := by rw [hnatT]; omega
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat n) = ⟨1⟩ :=
    ult_one (by rw [ulit_toNat' i hiw, ulit_toNat' n hn]; exact hi)
  have hheaders := expandedWords32_chain ha (show ticksPtr.toNat ≤ secondsPtr.toNat by omega)
    (by omega)
  change M (M aw ticksPtr ⟨32⟩) secondsPtr ⟨32⟩ = M aw secondsPtr ⟨32⟩ at hheaders
  have hseconds := expandedWords32_chain ha
    (show secondsPtr.toNat ≤ (wordArrayElement secondsPtr i).toNat by rw [hnatS]; omega) hbS
  change M (M aw secondsPtr ⟨32⟩) (wordArrayElement secondsPtr i) ⟨32⟩ =
    M aw (wordArrayElement secondsPtr i) ⟨32⟩ at hseconds
  have hcS := expandedWords_cover ha hbS (by decide : (⟨32⟩ : UInt256).toNat ≠ 0)
  have hticks := expandedWords32_eq_of_cover (activeWords_expand32 ha hbS) hbT
    (show (wordArrayElement ticksPtr i).toNat + 32 ≤
      (expandedWords aw (wordArrayElement secondsPtr i) ⟨32⟩).toNat * 32 by
      rw [hnatS] at hcS; rw [hnatT]; change _ + 32 ≤ _ at hcS; omega)
  change M (M aw (wordArrayElement secondsPtr i) ⟨32⟩) (wordArrayElement ticksPtr i) ⟨32⟩ =
    M aw (wordArrayElement secondsPtr i) ⟨32⟩ at hticks
  have r1 := uniswapV3Pool_block_17215_taken (immWords := wordsOf (immStore v))
    (by omega) (by rw [ht, hlt]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  have r2 := uniswapV3Pool_block_17227_taken (immWords := wordsOf (immStore v))
    (by dsimp only [uniswapV3Pool_block_17215_taken_stack, List.length]; omega)
    (by rw [hs, hlt]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
  simp only [uniswapV3Pool_block_17227_taken_stack, hrawT, hheaders] at r2
  have r3 := uniswapV3Pool_block_17246 (immWords := wordsOf (immStore v))
    (by dsimp only [List.length]; omega)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 160 - 1) := by decide
  have hmem : uniswapV3Pool_block_17246_memory (mem := mem) (x0 := UInt256.ofNat i)
      (x1 := secondsPtr) (x2 := wordArrayElement ticksPtr i) (x3 := secondsRaw) (x4 := tickRaw) =
      oracleObserveUpdateMem mem ticksPtr secondsPtr i tickValue secondsValue := by
    dsimp only [uniswapV3Pool_block_17246_memory]
    rw [hmask, hrawS, hnatS, hnatT,
      signextend_idem ⟨56, by decide⟩ _ _ (by decide) (by decide), htw,
      u256_land_comm (UInt256.ofNat (2 ^ 160 - 1)) (UInt256.land _ _),
      u256_land_comm (UInt256.ofNat (2 ^ 160 - 1)) secondsRaw, maskTwice, hsw]
    rfl
  have hinc : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) :=
    u256_one_add_ofNat i
  simp only [uniswapV3Pool_block_17246_stack, hinc,
    hmem, hrawS, hseconds, hticks] at r3
  refine ⟨_, _, ?_, r3⟩
  dsimp only [memExpansionCost]
  rw [hheaders, hseconds, hticks]
  omega

end Benchmarks.UniswapV3.Pool
