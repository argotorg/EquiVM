import Benchmarks.UniswapV4PoolManager.PoolModifyRegionAmount
import Benchmarks.UniswapV4PoolManager.PoolModifyCheckedAmountTrace
import Benchmarks.UniswapV4PoolManager.TickSqrtCanonicalTrace
import Benchmarks.UniswapV4PoolManager.Signed128Range

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolModifyRegionAmount0Trace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw sqrtPrice : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+23 ≤ 1024)
    (hu : int24Canonical p.upper) (ht : poolTicksValid p.lower p.upper)
    (hp : sqrtPrice.toNat < 2^160) (hd : signedFits ⟨128, by decide⟩ p.delta)
    (h : RD (deployedRuntime v) I g s0 ⟨6410⟩
      (p.upper :: p.lower :: sqrtPrice :: EVM.wordOfInt p.delta :: R) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post => post = evm ∧ ∃ k' C',
      RD (deployedRuntime v) I g s0 ⟨6442⟩
        (poolModifyRegionWord false p sqrtPrice :: p.lower :: ⟨6381⟩ :: ⟨6461⟩ :: sqrtPrice ::
          EVM.wordOfInt p.delta :: R) mem aw rdata post.accountMap k' C') (fun _ _ => False)
      (poolModifyRegionAmountResult f evm false p sqrtPrice) := by
  have hs : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt p.delta) = EVM.wordOfInt p.delta :=
    signextend128_wordOfInt hd.1 hd.2
  have rd1 := poolManagerBlocks.poolManager_block_6410 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_6410_stack, hs] at rd1
  obtain ⟨k2, C2, rd2⟩ := tickSqrtCanonicalTrace v (by simp only [List.length_cons]; omega)
    hu (poolTicksValid_bounds ht).2 (by rw [deployedRuntime_jumps]; jump_dest) rd1
  have rd3 := poolManagerBlocks.poolManager_block_6436 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact poolModifyCheckedAmountTrace (wordLocal f "__c21" (tickSqrtPrice (EVM.signed p.upper)))
    "__c22" "__c23" false v (by simp only [List.length_cons]; omega)
    hp (tickSqrtPrice_lt_160 (poolTicksValid_bounds ht).2) hd
    (by rw [deployedRuntime_jumps]; jump_dest) rd3

theorem poolModifyRegionAmount1EntryTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw sqrtPrice amount0 : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} 
    (v : PoolManagerImmutables) (hstack : R.length+20 ≤ 1024)
    (hl : int24Canonical p.lower) (ht : poolTicksValid p.lower p.upper)
    (hp : sqrtPrice.toNat < 2^160) (hd : signedFits ⟨128, by decide⟩ p.delta)
    (h : RD (deployedRuntime v) I g s0 ⟨6442⟩
      (amount0 :: p.lower :: ⟨6381⟩ :: ⟨6461⟩ :: sqrtPrice :: EVM.wordOfInt p.delta :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨17610⟩
      (tickSqrtPrice (EVM.signed p.lower) :: sqrtPrice :: EVM.wordOfInt p.delta :: ⟨6381⟩ :: ⟨6461⟩ ::
        amount0 :: EVM.wordOfInt p.delta :: R) mem aw rdata evm.accountMap k' C'  := by
  have hs : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt p.delta) = EVM.wordOfInt p.delta :=
    signextend128_wordOfInt hd.1 hd.2
  have rd1 := poolManagerBlocks.poolManager_block_6442 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_6442_stack, hs] at rd1
  obtain ⟨k2, C2, rd2⟩ := tickSqrtCanonicalTrace v (by simp only [List.length_cons]; omega)
    hl (poolTicksValid_bounds ht).1 (by rw [deployedRuntime_jumps]; jump_dest) rd1
  have rd3 := poolManagerBlocks.poolManager_block_6456 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨_, _, rd3⟩

theorem poolModifyRegionAmount1Trace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw sqrtPrice amount0 : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+20 ≤ 1024)
    (hl : int24Canonical p.lower) (ht : poolTicksValid p.lower p.upper)
    (hp : sqrtPrice.toNat < 2^160) (hd : signedFits ⟨128, by decide⟩ p.delta)
    (h : RD (deployedRuntime v) I g s0 ⟨6442⟩
      (amount0 :: p.lower :: ⟨6381⟩ :: ⟨6461⟩ :: sqrtPrice :: EVM.wordOfInt p.delta :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post => post = evm ∧ ∃ k' C',
      RD (deployedRuntime v) I g s0 ⟨6461⟩
        (poolModifyRegionWord true p sqrtPrice :: amount0 :: EVM.wordOfInt p.delta :: R)
        mem aw rdata post.accountMap k' C') (fun _ _ => False)
      (poolModifyRegionAmountResult f evm true p sqrtPrice) := by
  obtain ⟨k1, C1, rd1⟩ := poolModifyRegionAmount1EntryTrace v hstack hl ht hp hd h
  simpa only [poolModifyRegionAmountResult, poolModifyRegionWord, poolModifyRegionA, poolModifyRegionB,
    poolModifyRegionPrice, poolModifyRegionTick, poolModifyRegionSqrtRet, poolModifyRegionAmountRet,
    poolModifyRegionCastRet, ↓reduceIte] using
    poolModifyCheckedAmountTrace (wordLocal f "__c24" (tickSqrtPrice (EVM.signed p.lower)))
      "__c25" "__c26" true v (by simp only [List.length_cons]; omega)
      (tickSqrtPrice_lt_160 (poolTicksValid_bounds ht).1) hp hd
      (by rw [deployedRuntime_jumps]; jump_dest) rd1

end Benchmarks.UniswapV4PoolManager
