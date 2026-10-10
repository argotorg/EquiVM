import Benchmarks.UniswapV3.Pool.TickUpdateRawModel
import Benchmarks.UniswapV3.Pool.TickUpdateModel
import Benchmarks.UniswapV3.Pool.LiquidityDeltaTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_071

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def tickUpdateWords (a : TickUpdateArgs) : List UInt256 :=
  [a.maxLiquidity, a.upper.toUInt256, a.time, EVM.wordOfInt a.cumulative,
   a.secondsPerLiquidity, a.global1, a.global0, EVM.wordOfInt a.delta,
   EVM.wordOfInt a.current, EVM.wordOfInt a.tick, ⟨5⟩]

def tickUpdateMemoryWords (aw : UInt256) : UInt256 :=
  M (M (M aw ⟨0⟩ ⟨32⟩) ⟨32⟩ ⟨32⟩) ⟨0⟩ ⟨64⟩

theorem tickUpdateLiquidityRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickUpdateArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20795⟩ (tickUpdateWords a ++ ret :: R)
      mem aw rdata σ k C) (hfit : a.TraceFits) (hov : R.length + 25 ≤ 1024) :
    let before := Int.ofNat (tickGrossWord σ ee a.tick).toNat
    (RDrev (deployedRuntime v) g s0 ∧ ¬ liquidityDeltaValid before a.delta) ∨
    (liquidityDeltaValid before a.delta ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨20838⟩
      (EVM.wordOfInt (liquidityDeltaResult before a.delta) :: ⟨0⟩ :: tickGrossWord σ ee a.tick ::
        tickClearBase a.tick :: ⟨0⟩ :: tickUpdateWords a ++ ret :: R)
      (twoWordHashMem (EVM.wordOfInt a.tick) ⟨5⟩ mem) (tickUpdateMemoryWords aw) rdata σ k' C') := by
  dsimp only
  rcases hfit with ⟨htb, _, hdb, _⟩
  have ht : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt a.tick) =
      EVM.wordOfInt a.tick := by
    rw [signextend_wordOfInt ⟨24, by decide⟩ _ _ (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ htb.1 htb.2]
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 128 - 1) := by native_decide
  obtain ⟨kp, Cp, rp⟩ := uniswapV3Pool_block_20795 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 19 ≤ 1024; omega)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
  simp only [uniswapV3Pool_block_20795_stack, uniswapV3Pool_block_20795_memory, ht, hmask] at rp
  have hh : keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (EVM.wordOfInt a.tick) ⟨5⟩ mem) =
      tickClearBase a.tick := twoWordHashMem_solcMappingSlot_any _ _ _
  change RD (deployedRuntime v) ee g s0 ⟨13807⟩
    (EVM.wordOfInt a.delta ::
      uint128Word (solcSlotWordAt
        (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (EVM.wordOfInt a.tick) ⟨5⟩ mem)) σ ee) ::
      ⟨20838⟩ :: ⟨0⟩ :: uint128Word (solcSlotWordAt
        (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (EVM.wordOfInt a.tick) ⟨5⟩ mem)) σ ee) ::
      keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (EVM.wordOfInt a.tick) ⟨5⟩ mem) ::
      ⟨0⟩ :: tickUpdateWords a ++ ret :: R)
    (twoWordHashMem (EVM.wordOfInt a.tick) ⟨5⟩ mem) _ rdata σ kp Cp at rp
  rw [hh] at rp
  have hbefore : 0 ≤ Int.ofNat (tickGrossWord σ ee a.tick).toNat ∧
      Int.ofNat (tickGrossWord σ ee a.tick).toNat < 2 ^ 128 := by
    constructor
    · exact Int.ofNat_nonneg _
    · change ((tickGrossWord σ ee a.tick).toNat : Int) < 2 ^ 128
      exact_mod_cast tickGrossWord_lt σ ee a.tick
  have hrp : RD (deployedRuntime v) ee g s0 ⟨13807⟩
      (EVM.wordOfInt a.delta :: EVM.wordOfInt (Int.ofNat (tickGrossWord σ ee a.tick).toNat) ::
        ⟨20838⟩ :: ⟨0⟩ :: tickGrossWord σ ee a.tick :: tickClearBase a.tick ::
        ⟨0⟩ :: tickUpdateWords a ++ ret :: R)
      (twoWordHashMem (EVM.wordOfInt a.tick) ⟨5⟩ mem)
      (M (M (M aw ⟨0⟩ ⟨32⟩) ⟨32⟩ ⟨32⟩) ⟨0⟩ ⟨64⟩) rdata σ kp Cp := by
    simpa only [wordOfInt_ofNat_toNat] using rp
  rcases liquidityDeltaCanonicalX (v := v)
    (Int.ofNat (tickGrossWord σ ee a.tick).toNat) a.delta hrp
    hbefore.1 hbefore.2 hdb.1 hdb.2
    (by rw [uniswapV3PoolPatchedValidJumps v]; native_decide)
    (by simpa only [tickUpdateWords, List.length_cons, List.length_nil, List.length_append]
      using hov) with hb | ⟨hv, kf, Cf, rf⟩
  · exact Or.inl hb
  · exact Or.inr ⟨hv, kf, Cf, rf⟩


theorem tickUpdateLiquidityX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickUpdateArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20795⟩ (tickUpdateWords a ++ ret :: R)
      mem aw rdata σ k C) (hfit : a.TraceFits) (hov : R.length + 25 ≤ 1024) :
    let before := Int.ofNat (tickGrossWord σ ee a.tick).toNat
    (RDrev (deployedRuntime v) g s0 ∧ ¬ liquidityDeltaValid before a.delta) ∨
    (liquidityDeltaValid before a.delta ∧ ∃ k' C' aw', RD (deployedRuntime v) ee g s0 ⟨20838⟩
      (EVM.wordOfInt (liquidityDeltaResult before a.delta) :: ⟨0⟩ :: tickGrossWord σ ee a.tick ::
        tickClearBase a.tick :: ⟨0⟩ :: tickUpdateWords a ++ ret :: R)
      (twoWordHashMem (EVM.wordOfInt a.tick) ⟨5⟩ mem) aw' rdata σ k' C') := by
  rcases tickUpdateLiquidityRawX (v := v) a rd hfit hov with hb | ⟨hv, k', C', r'⟩
  · exact Or.inl hb
  · exact Or.inr ⟨hv, k', C', _, r'⟩

end Benchmarks.UniswapV3.Pool
