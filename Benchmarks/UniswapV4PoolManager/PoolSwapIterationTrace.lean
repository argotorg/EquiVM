import Benchmarks.UniswapV4PoolManager.PoolSwapIterationSource
import Benchmarks.UniswapV4PoolManager.PoolSwapScanComputeTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapAccountingWindow
import Benchmarks.UniswapV4PoolManager.PoolSwapActiveWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapIterationTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}
    {aw step state params id remaining calculated tag x1 fee protocol amount : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+36 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : PoolSwapMemoryView mem step state params s r p)
    (htc : int24Canonical r.tick) (hspacing : int24Canonical p.tickSpacing)
    (hprice : r.price.toNat < 2^160) (hlimit : p.priceLimit.toNat < 2^160)
    (hliq : r.liquidity.toNat < 2^128) (hfee : fee.toNat < 2^24) (hprotocol : protocol.toNat < 2^16)
    (h : RD (deployedRuntime v) I g s0 ⟨19169⟩
      ([remaining, x1, params, calculated, tag, fee, protocol, amount, UInt256.fromBool (!p.zeroForOne),
        step, poolSlot id, state] ++ R) mem aw rdata evm.accountMap k C) :
    let scan := poolSwapScanStep s evm id r p
    let next := tickSqrtPrice (EVM.signed (tickClampWord scan.tickNext))
    let w := swapStepWord r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee
    let computed := poolSwapComputeStep {scan with tickNext := tickClampWord scan.tickNext} next w
    let result := {r with price := w.next}
    let fees := poolSwapAccountingStep computed result fee protocol
    blockResultTrace (deployedRuntime v) g s0
      (fun _ post => ∃ mem' aw' k' C', C < C' ∧
        RD (deployedRuntime v) I g s0 ⟨19155⟩
          ([poolSwapRemainingAfter computed p.amountSpecified remaining, x1, params,
            poolSwapCalculatedAfter computed p.amountSpecified calculated, tag, fee, protocol,
            poolSwapProtocolAmount computed fee protocol amount, UInt256.fromBool (!p.zeroForOne), step, poolSlot id, state] ++ R)
          mem' aw' rdata post.accountMap k' C' ∧
        PoolSwapMemoryView mem' step state params fees (poolSwapTickResultWords evm id fees result p.zeroForOne) p ∧
        MemoryWindowEq mem mem' 64 (min step.toNat state.toNat) ∧
        (PoolSwapActiveWords aw step state params → aw' = aw))
      (fun _ _ => False) (poolSwapIterationResult f evm id s r p remaining calculated fee protocol amount) := by
  dsimp only
  let scan := poolSwapScanStep s evm id r p
  let next := tickSqrtPrice (EVM.signed (tickClampWord scan.tickNext))
  let clamped := {scan with tickNext := tickClampWord scan.tickNext}
  let w := swapStepWord r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee
  let computed := poolSwapComputeStep clamped next w
  let result := {r with price := w.next}
  let f1 := poolSwapComputeFrame (tickClampPriceFrame (poolSwapScanFrame f s evm id r p) scan)
    clamped r p next remaining fee
  have hpre := poolSwapScanComputeTrace v hstack hI hm htc hspacing hprice hlimit hliq hfee h
  dsimp only at hpre
  have hnext : next.toNat < 2^160 := tickSqrtPrice_lt_160 (tickClampWord_natAbs scan.tickNext)
  unfold poolSwapIterationResult
  dsimp only
  by_cases hfit : swapStepFits r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee
  · rw [if_pos hfit]
    obtain ⟨mem2, k2, C2, hC2, rd2, hmComputed, hwComputed⟩ := hpre.1 hfit
    have hnewprice : result.price.toNat < 2^160 :=
      swapStepWord_next_canonical hprice (swapTargetWord_canonical hnext hlimit) hfit
    have haccount := poolSwapAccountingTrace (f := f1) (s := computed) (r := result)
      v (by omega) hI hmComputed hfee hprotocol hliq (tickClampWord_canonical scan.tickNext)
      hnewprice hnext hprice rd2
    apply blockResultTrace_mono haccount
    intro ff post _ hnormal
    obtain ⟨k3, C3, hC3, rd3⟩ := hnormal
    have rd4 := poolManagerBlocks.poolManager_block_19964
      (by change R.length+7+6 ≤ 1024; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
    simp only [poolManagerBlocks.poolManager_block_19964_stack] at rd4
    have hmFinal := hmComputed.accounting evm id fee protocol
    refine ⟨_, _, _, _, by omega, rd4, hmFinal,
      hwComputed.trans (hmComputed.accounting_window evm id fee protocol), ?_⟩
    intro ha
    change poolSwapAccountingAW (poolSwapScanComputeAW aw step state params)
      step state p.amountSpecified computed result fee protocol = aw
    rw [ha.scan_compute, ha.accounting]
  · rw [if_neg hfit]
    exact hpre.2 hfit

end Benchmarks.UniswapV4PoolManager
