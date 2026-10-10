import Benchmarks.UniswapV4PoolManager.PoolSwapLoopInvariant
import Benchmarks.UniswapV4PoolManager.PoolSwapSavedLocals
import Benchmarks.UniswapV4PoolManager.PoolSwapOriginalAccounts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapIterationCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {p : PoolSwapParamsWords} {q : PoolSwapLoopWords}
    {aw step state params id tag x1 fee protocol : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+36 ≤ 1024) (hI : evm.executionEnv = I)
    (hinv : PoolSwapLoopInvariant f mem id step state params fee protocol p q)
    (hspacing : int24Canonical p.tickSpacing) (hlimit : p.priceLimit.toNat < 2^160)
    (hfee : fee.toNat < 2^24) (hprotocol : protocol.toNat < 2^16)
    (h : RD (deployedRuntime v) I g s0 ⟨19169⟩
      (poolSwapLoopStack q p id step state params x1 tag fee protocol R) mem aw rdata evm.accountMap k C) :
    ∃ result, ExecBlock config f evm poolSwapLoopBody result ∧
      blockResultTrace (deployedRuntime v) g s0
        (fun ff post => ∃ q' mem' aw' k' C', C < C' ∧ post.executionEnv = I ∧ post.σ₀ = evm.σ₀ ∧
          RD (deployedRuntime v) I g s0 ⟨19155⟩
            (poolSwapLoopStack q' p id step state params x1 tag fee protocol R) mem' aw' rdata post.accountMap k' C' ∧
          PoolSwapLoopInvariant ff mem' id step state params fee protocol p q' ∧
          MemoryWindowEq mem mem' 64 (min step.toNat state.toNat) ∧ PoolSwapSavedLocals f ff ∧
          (PoolSwapActiveWords aw step state params → aw' = aw))
        (fun _ _ => False) result := by
  let result := poolSwapIterationResult f evm id q.step q.result p q.remaining q.calculated fee protocol q.amountToProtocol
  have hl := hinv.locals
  have hs := poolSwapIterationSource (evm := evm) hl.contract
    (by have := int24Canonical_natAbs_le hinv.tick; omega) hinv.price hlimit
    hl.step hl.result hl.params hl.self hl.direction hl.remaining hl.calculated hl.fee hl.protocol hl.amount
  have ht := poolSwapIterationTrace (f := f) v hstack hI hinv.memory hinv.tick hspacing
    hinv.price hlimit hinv.liquidity hfee hprotocol h
  refine ⟨result, hs, ?_⟩
  apply blockResultTrace_mono ht
  intro ff post he hnormal
  obtain ⟨mem', aw', k', C', hC', rd', hm', hw', ha'⟩ := hnormal
  obtain ⟨hl', henv, hp', ht', hliq'⟩ :=
    poolSwapIterationPost hl hinv.tick hinv.price hlimit hinv.liquidity he
  exact ⟨⟨_, _, _, _, _⟩, mem', aw', k', C', hC', henv.trans hI, poolSwapIterationResult_σ₀ he,
    rd', ⟨hl', hm', hp', ht', hliq'⟩,
    hw', poolSwapIterationResult_saved hl he, ha'⟩

end Benchmarks.UniswapV4PoolManager
