import Benchmarks.UniswapV4PoolManager.ProtocolSwapFeeSource
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_053
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_063

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem protocolFeeDirectionTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw packed x0 x1 x2 x3 x4 x5 x6 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (zeroForOne : Bool) (hstack : R.length+11 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 (if zeroForOne then ⟨18833⟩ else ⟨22261⟩)
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: packed :: R) mem aw rdata σ k C) :
    RD (deployedRuntime v) I g s0 ⟨18842⟩
      (x4 :: x0 :: x1 :: x2 :: x3 ::
        (if zeroForOne then protocolFeeZeroWord (slot0FeeField packed 184)
          else protocolFeeOneWord (slot0FeeField packed 184)) :: x5 :: x6 :: packed :: R)
      mem aw rdata σ (k + if zeroForOne then 6 else 9) (C + if zeroForOne then 18 else 30) := by
  cases zeroForOne with
  | false =>
    simpa only [Bool.false_eq_true, if_false, protocolFeeOneWord_packed,
      poolManagerBlocks.poolManager_block_22261_stack] using
      poolManagerBlocks.poolManager_block_22261 hstack
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  | true =>
    simpa only [if_true, protocolFeeZeroWord_packed, poolManagerBlocks.poolManager_block_18833_stack] using
      poolManagerBlocks.poolManager_block_18833 hstack h

theorem slot0GetLPFeeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw packed x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+12 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨22246⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: packed :: R) mem aw rdata σ k C) :
    RD (deployedRuntime v) I g s0 ⟨18941⟩
      (slot0FeeField packed 208 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: packed :: R)
      mem aw rdata σ (k+9) (C+29) := by
  simpa only [poolManagerBlocks.poolManager_block_22246_stack,
    u256_land_comm (UInt256.ofNat 16777215) _, slot0FeeField] using
    poolManagerBlocks.poolManager_block_22246 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h

theorem protocolSwapFeeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw fee lpFee x1 x2 x3 x4 x5 x6 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+12 ≤ 1024) (hl : lpFee.toNat < 2^24)
    (h : RD (deployedRuntime v) I g s0 ⟨22219⟩
      (lpFee :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: fee :: R) mem aw rdata σ k C) :
    RD (deployedRuntime v) I g s0 ⟨18951⟩
      (protocolSwapFeeWord fee lpFee :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: fee :: R)
      mem aw rdata σ (k+17) (C+58) := by
  have hclean : UInt256.land lpFee (UInt256.ofNat 16777215) = lpFee :=
    u256LandMaskCleanOfToNat _ _ rfl hl
  have rd := poolManagerBlocks.poolManager_block_22219 hstack
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simpa only [poolManagerBlocks.poolManager_block_22219_stack, hclean,
    protocolSwapFeeWord_eq_raw fee hl, protocolSwapFeeRaw, protocolFeeZeroWord] using rd

end Benchmarks.UniswapV4PoolManager
