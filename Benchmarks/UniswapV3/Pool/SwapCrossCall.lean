import Benchmarks.UniswapV3.Pool.SwapCrossLoad
import Benchmarks.UniswapV3.Pool.HashMemoryPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapCrossCallFrame (frame : Frame) (evm : EVM.State) (a : TickCrossArgs) : Frame :=
  resumeAfterInternalCall frame "liquidityNet" (some [.int (tickCrossResult evm a)])

theorem swapCrossCallX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw p q free exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData)
    (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3775⟩
      (q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hsource : SourceState s0 ee σ evm)
    (hf : frame = {contract := contract, locals := frame.locals, immutables := immStore v})
    (hz : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hcget : frame.locals.get? "cache" = some c.value)
    (hsget : frame.locals.get? "state" = some s.value)
    (hdget : frame.locals.get? "step" = some d.value)
    (hg : ∀ b, frame.locals.get? (feeGrowthName b) = none)
    (hm : HeapMemory mem aw free) (hc : SwapCacheMemory mem cache c)
    (hs : SwapStateMemory mem p s) (hd : SwapIterationMemory mem q d)
    (ht : -(2 ^ 23 : Int) ≤ d.tickNext ∧ d.tickNext < 2 ^ 23)
    (hperm : ee.perm = true) (hcache : 96 ≤ cache.toNat)
    (hcp : cache.toNat + 192 ≤ p.toNat) (hpq : p.toNat + 224 ≤ q.toNat)
    (hbq : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 28 ≤ 1024) :
    let ca := swapCrossArgs a.zeroForOne c s d σ ee
    let m := twoWordHashMem (EVM.wordOfInt d.tickNext) ⟨5⟩ mem
    ExecStmt config frame evm swapInitializedBody[1]!
        (.ok (swapCrossCallFrame frame evm ca) (tickCrossState evm ca)) ∧
      SourceState s0 ee (tickCrossMap ca σ ee) (tickCrossState evm ca) ∧
      ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
        RD (deployedRuntime v) ee g s0 ⟨3851⟩
          ([EVM.wordOfInt (tickCrossResult evm ca), ⟨0⟩, q] ++
            swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
          m aw' rdata (tickCrossMap ca σ ee) k' C' ∧ HeapMemory m aw' free ∧
        SwapCacheMemory m cache c ∧ SwapStateMemory m p s ∧ SwapIterationMemory m q d ∧
        MemoryPrefix mem m cache.toNat ∧ aw.toNat ≤ aw'.toNat := by
  dsimp only
  obtain ⟨aw1, k1, C1, hC1, r1, hm1, hmono⟩ :=
    swapCrossLoadX (v := v) a c s d rd hm hc hs hd (by omega) (by omega) hbq (by omega)
  have he := evalSwapCrossCallArgs (evm := evm) a.zeroForOne c s d
    (congrArg Frame.contract hf) hz hcget hsget hdget hg
  rw [← hsource.accounts, hsource.env] at he
  obtain ⟨hex, hsrc, k2, C2, hC2, r2, hm2⟩ :=
    tickCrossInternalMonoX (v := v) (swapCrossArgs a.zeroForOne c s d σ ee)
      frame evm swapCrossCallArgs "liquidityNet" hf he hsource r1 ht hperm hm1
      (by rw [uniswapV3PoolPatchedValidJumps v]; native_decide)
      (by change R.length + 15 + 13 ≤ 1024; omega)
  have hpre := twoWordHashMem_prefix mem (EVM.wordOfInt d.tickNext) ⟨5⟩ (q.toNat + 224)
  refine ⟨hex, hsrc, aw1, k2, C2, by omega, r2, hm2, ?_, ?_, ?_,
    twoWordHashMem_prefix _ _ _ _, hmono⟩
  · exact MemoryPrefix.wordArray hpre hc hcache (by change cache.toNat + 192 ≤ _; omega)
  · exact MemoryPrefix.wordArray hpre hs (by omega) (by change p.toNat + 224 ≤ _; omega)
  · exact MemoryPrefix.wordArray hpre hd (by omega) (by change q.toNat + 224 ≤ _; omega)

end Benchmarks.UniswapV3.Pool
