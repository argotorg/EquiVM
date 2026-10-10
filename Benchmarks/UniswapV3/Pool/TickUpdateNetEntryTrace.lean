import Benchmarks.UniswapV3.Pool.TickUpdateRawModel
import Benchmarks.UniswapV3.Pool.TickUpdateBranchTrace
import Benchmarks.UniswapV3.Pool.TickUpdateStorage
import Benchmarks.UniswapV3.Pool.SafeSignedMathTrace
import Benchmarks.UniswapV3.Pool.SafeCast128Trace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem tickNetValue_word (σ : AccountMap) (ee : ExecutionEnv) (tick : Int) :
    EVM.wordOfInt (tickNetValue σ ee tick) =
      UInt256.signextend (UInt256.ofNat 15) (UInt256.div
        (solcSlotWordAt (tickClearBase tick) σ ee)
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))) := by
  have hp : UInt256.ofNat (256 ^ 16) = UInt256.ofNat (2 ^ 128) := by native_decide
  simpa only [tickNetValue, tickSignedFieldValue, tickFieldSlot, tickClearBase,
    show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero, hp, solcShift128] using
    (signextend_normalizeSint ⟨128, by decide⟩ (UInt256.ofNat 15)
      (UInt256.div (solcSlotWordAt (tickClearBase tick) σ ee) (UInt256.ofNat (2 ^ 128)))
      (by decide) (by decide)).symm

def tickUpdateNetReturnPC (upper : Bool) : UInt256 := if upper then ⟨21236⟩ else ⟨21198⟩

theorem tickUpdateNetEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickUpdateArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ (tickUpdateGrossState a evm))
    (rd : RD (deployedRuntime v) ee g s0 (if a.upper then ⟨21203⟩ else ⟨21161⟩)
      (tickUpdateWorkingWords a evm ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.TraceFits) (hov : R.length + 21 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat (if a.upper then 12967 else 12995))
      (EVM.wordOfInt a.delta :: EVM.wordOfInt (tickUpdateNetBefore a evm) :: ⟨21193⟩ ::
        tickUpdateNetReturnPC a.upper :: tickUpdateWorkingWords a evm ++ ret :: R)
      mem aw rdata σ k' C' := by
  have hd : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt a.delta) =
      EVM.wordOfInt a.delta := by
    rw [signextend_wordOfInt ⟨128, by decide⟩ _ _ (by decide) (by decide),
      normalizeSint_eq_self ⟨128, by decide⟩ _ hfit.2.2.1.1 hfit.2.2.1.2]
  have hn : UInt256.signextend (UInt256.ofNat 15) (UInt256.signextend (UInt256.ofNat 15)
      (UInt256.div (solcSlotWordAt (tickClearBase a.tick) σ ee)
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)))) =
      EVM.wordOfInt (tickUpdateNetBefore a evm) := by
    rw [signextend_idem ⟨128, by decide⟩ _ _ (by decide) (by decide), ← tickNetValue_word]
    simp only [tickUpdateNetBefore, hs.accounts, hs.env]
  cases hu : a.upper
  · simp only [hu, Bool.false_eq_true, if_false] at rd ⊢
    obtain ⟨kf, Cf, rf⟩ := uniswapV3Pool_block_21161 (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 17 ≤ 1024; omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    simp only [uniswapV3Pool_block_21161_stack] at rf
    change RD (deployedRuntime v) ee g s0 ⟨12995⟩
      (UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt a.delta) ::
        UInt256.signextend (UInt256.ofNat 15) (UInt256.signextend (UInt256.ofNat 15)
          (UInt256.div (solcSlotWordAt (tickClearBase a.tick) σ ee)
            (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)))) ::
        ⟨21193⟩ :: ⟨21198⟩ :: tickUpdateWorkingWords a evm ++ ret :: R)
      mem aw rdata σ kf Cf at rf
    rw [hd, hn] at rf
    exact ⟨kf, Cf, rf⟩
  · simp only [hu, if_true] at rd ⊢
    obtain ⟨kf, Cf, rf⟩ := uniswapV3Pool_block_21203 (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 17 ≤ 1024; omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    simp only [uniswapV3Pool_block_21203_stack] at rf
    change RD (deployedRuntime v) ee g s0 ⟨12967⟩
      (UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt a.delta) ::
        UInt256.signextend (UInt256.ofNat 15) (UInt256.signextend (UInt256.ofNat 15)
          (UInt256.div (solcSlotWordAt (tickClearBase a.tick) σ ee)
            (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)))) ::
        ⟨21193⟩ :: ⟨21236⟩ :: tickUpdateWorkingWords a evm ++ ret :: R)
      mem aw rdata σ kf Cf at rf
    rw [hd, hn] at rf
    exact ⟨kf, Cf, rf⟩

end Benchmarks.UniswapV3.Pool
