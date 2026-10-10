import Benchmarks.UniswapV3.Pool.FlashPrefixTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem flashStartX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : FlashArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨6440⟩ R mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hov : R.length + 6 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecTransitionBody config contract evm (flashLocals a) flashTransition.body .reverted
        (immStore v)) ∨
    (RDstatic (deployedRuntime v) g s0 ∧
      ExecTransitionBody config contract evm (flashLocals a) flashTransition.body .staticViolation
        (immStore v)) ∨
    (ee.perm = true ∧ ∃ k' C',
      SourceState s0 ee (storeSlot0Unlocked evm false).accountMap (storeSlot0Unlocked evm false) ∧
      ExecBlock config (flashFrame v a) evm (flashTransition.body.take 6)
        (.ok (flashReadyFrame v a (poolLiquidityWord (storeSlot0Unlocked evm false).accountMap ee))
          (storeSlot0Unlocked evm false)) ∧
      RD (deployedRuntime v) ee g s0 ⟨6595⟩
        (poolLiquidityWord (storeSlot0Unlocked evm false).accountMap ee :: R)
        mem aw rdata (storeSlot0Unlocked evm false).accountMap k' C') := by
  rcases flashReadLockX (v := v) rd (by omega) with
    ⟨rdBad, hlocked⟩ | ⟨hunlocked, kLock, CLock, rdLock⟩
  · rw [hs.accounts, ← hs.env] at hlocked
    exact Or.inl ⟨rdBad, flashRevertsLocked v evm a hwv hlocked⟩
  · have hunlockedSource : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩ := by
      rw [← hs.accounts, hs.env]
      exact hunlocked
    by_cases hp : ee.perm = true
    · obtain ⟨hsLocked, kDelegate, CDelegate, rdDelegate⟩ := flashLockX (v := v) rdLock hs hp (by omega)
      rcases noDelegateCallX (v := v) rdDelegate
          (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by omega) with
        ⟨rdBad, hdelegate⟩ | ⟨hself, kLiq, CLiq, rdLiq⟩
      · exact Or.inl ⟨rdBad, flashRevertsDelegate v evm a hwv hunlockedSource
          (by rw [hs.env]; exact hdelegate)⟩
      · have hselfSource : evm.executionEnv.codeOwner = v.original := by rw [hs.env]; exact hself
        rcases flashReadLiquidityX (v := v) rdLiq hov with
          ⟨rdBad, hliq⟩ | ⟨hliq, kReady, CReady, rdReady⟩
        · exact Or.inl ⟨rdBad, flashRevertsLiquidity v evm a hwv hunlockedSource hselfSource
            (by rw [hsLocked.env, hliq]; omega)⟩
        · have hsource := flashReadyPrefix v evm a hwv hunlockedSource hselfSource
            (by rw [hsLocked.env]; exact hliq)
          dsimp only at hsource
          rw [hsLocked.env] at hsource
          exact Or.inr (Or.inr ⟨hp, kReady, CReady, hsLocked, hsource, rdReady⟩)
    · have hp' : ee.perm = false := Bool.eq_false_of_not_eq_true hp
      exact Or.inr (Or.inl ⟨flashLockStaticX (v := v) rdLock hp' (by omega),
        flashStatic v evm a hwv hunlockedSource (by rw [hs.env]; exact hp')⟩)

end Benchmarks.UniswapV3.Pool
