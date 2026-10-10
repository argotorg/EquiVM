import Benchmarks.UniswapV3.Pool.SwapTransferBuild
import Benchmarks.UniswapV3.Pool.SafeTransfer
import Benchmarks.UniswapV3.Pool.SourceFrame

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapTransferX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p free exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (second : Bool) (a : SwapArgs) (amount0 amount1 : Int) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 (swapTransferEntry second)
      (swapPaymentWords a p exactWord cache snap dataStart dataLength ret amount0 amount1 R)
      mem aw rdata σ k C)
    (hsource : SourceState s0 ee σ evm) (hf : frame.contract = contract)
    (hi : frame.immutables = immStore v) (hperm : ee.perm = true)
    (hr : frame.locals.get? "recipient" = some (.address a.recipient))
    (ha : frame.locals.get? (poolAmountName second) =
      some (.int (if second then amount1 else amount0)))
    (hfit : -(2 ^ 255 : Int) ≤ (if second then amount1 else amount0) ∧
      (if second then amount1 else amount0) < 2 ^ 255)
    (hm : HeapMemory mem aw free) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : free.toNat + 2 ^ 138 + 195 ≤ 2 ^ 200) (hov : R.length + 33 ≤ 1024) :
    (ExecStmt config frame evm (swapTransferStmt second) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ evm' σ' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecStmt config frame evm (swapTransferStmt second)
        (.ok (swapTransferFrame frame second (if second then amount1 else amount0)) evm') ∧
      RD (deployedRuntime v) ee g s0 (swapTransferExit second)
        (swapPaymentWords a p exactWord cache snap dataStart dataLength ret amount0 amount1 R)
        mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ MemoryPrefix mem mem' free.toNat ∧
      128 ≤ mem'.size ∧ memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧
      free.toNat ≤ next.toNat ∧ next.toNat ≤ free.toNat + 2 ^ 138 + 163 := by
  rcases swapTransferBuildX (v := v) second a amount0 amount1 rd hfit (by omega) with
    ⟨hskip, k1, C1, r1⟩ | ⟨hneg, k1, C1, r1⟩
  · refine Or.inr ⟨evm, σ, rdata, mem, aw, free, k1, C1, hsource, ?_, r1, hm,
      MemoryPrefix.refl _ _, hmem, hzero, le_refl _, by omega⟩
    rw [swapTransferFrame, if_neg hskip]
    exact ExecStmt.iteFalse
      (by
        simpa only [hskip, decide_false] using
          evalSwapTransferGuard (evm := evm) second (if second then amount1 else amount0) ha) .nil
  · have hret : (D_J (deployedRuntime v) 0).contains (swapTransferExit second) = true := by
      rw [uniswapV3PoolPatchedValidJumps v]; cases second <;> native_decide
    rcases safeTransferGrowingX (v := v) (immStore v) (poolToken v second) a.recipient
        r1 hsource hperm hm hmem hzero hb hret
        (by change R.length + 13 + 20 ≤ 1024; omega) with
      ⟨rr, hex⟩ | ⟨evm', σ', out, mem', aw', next, k', C', hsrc, hex, rr, hm', hpref, hlo, hhi⟩
    · have hx := swapTransferReverts v frame.locals evm second a.recipient
        (if second then amount1 else amount0) hr ha hneg hex
      rw [← frame_eq_of_parts hf hi] at hx
      exact Or.inl ⟨hx, rr⟩
    · have hx := swapTransferReturns v frame.locals evm evm' second a.recipient
        (if second then amount1 else amount0) _ hr ha hneg hex
      rw [← frame_eq_of_parts hf hi] at hx
      refine Or.inr ⟨evm', σ', out, mem', aw', next, k', C', hsrc, hx, rr, hm', hpref,
        le_trans hmem hpref.size, ?_, hlo, hhi⟩
      rw [MemoryPrefix.memLoad hpref (UInt256.ofNat 96) (by decide) hm.lower hmem, hzero]

end Benchmarks.UniswapV3.Pool
