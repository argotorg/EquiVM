import Benchmarks.UniswapV4PoolManager.ModifyLiquidityEventMemory
import Benchmarks.UniswapV4PoolManager.ModifyLiquidityEventStatic
import Benchmarks.UniswapV4PoolManager.MemoryAccessCost
import Benchmarks.UniswapV4PoolManager.BalanceDeltaSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem modifyLiquidityEventTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw free keyPtr paramsPtr a0 a1 id fees src len junk : UInt256}
    {key : PoolKeyWords} {p : ModifyLiquidityWords} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024)
    (hk : PoolKeyView mem keyPtr key)
    (hp : MemorySlice mem paramsPtr.toNat (wordBytes (modifyLiquidityWords p)))
    (hc : key.hooks.toNat < 2^160) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hkb : keyPtr.toNat+160 ≤ free.toNat) (hpb : paramsPtr.toNat+128 ≤ free.toNat)
    (hf : free.toNat+128 < UInt256.size) (hfree : memLoad (UInt256.ofNat 64) mem = free)
    (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ⟨6084⟩
      ([a1, a0, paramsPtr, id, fees, src, len, ⟨6222⟩, ⟨6240⟩, fees, keyPtr, UInt256.ofNat 64, junk] ++ R)
      mem aw rdata σ k C) :
    (I.perm = false ∧ RDstatic (deployedRuntime v) g s0) ∨ ∃ aw' k' C', Cₘ aw' ≤ C' ∧
      RD (deployedRuntime v) I g s0 ⟨14427⟩
        ([key.hooks, keyPtr, paramsPtr, balanceDeltaWord a0 a1, fees, src, len,
          ⟨6222⟩, ⟨6240⟩, fees, keyPtr, UInt256.ofNat 64, junk] ++ R)
        (modifyLiquidityEventMemory mem free p) aw' rdata σ k' C' := by
  by_cases hperm : I.perm = true
  · have hm : poolManagerBlocks.poolManager_block_6084_memory (mem := mem)
        (x2 := paramsPtr) (x11 := UInt256.ofNat 64) = modifyLiquidityEventMemory mem free p :=
      modifyLiquidityEventMemory_compiled hp hl hu hpb hf hfree
    have hk' : PoolKeyView (modifyLiquidityEventMemory mem free p) keyPtr key :=
      ⟨hk.slice.modifyLiquidityEvent free p (by
        simpa only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil] using hkb), hk.fits⟩
    have hhook := hk'.load (i := 4) rfl
    have hclean : UInt256.land key.hooks (UInt256.ofNat 1461501637330902918203684832716283019655932542975) =
        key.hooks := solcAddrMask_clean hc
    have hs : poolManagerBlocks.poolManager_block_6084_stack (mem := mem)
        (x0 := a1) (x1 := a0) (x2 := paramsPtr) (x4 := fees) (x5 := src) (x6 := len)
        (x7 := ⟨6222⟩) (x8 := ⟨6240⟩) (x9 := fees) (x10 := keyPtr) (x11 := UInt256.ofNat 64)
        (R := junk :: R) =
        [key.hooks, keyPtr, paramsPtr, balanceDeltaWord a0 a1, fees, src, len,
          ⟨6222⟩, ⟨6240⟩, fees, keyPtr, UInt256.ofNat 64, junk] ++ R := by
      change UInt256.land (memLoad (keyPtr+UInt256.ofNat 128)
        (poolManagerBlocks.poolManager_block_6084_memory (mem := mem) (x2 := paramsPtr) (x11 := UInt256.ofNat 64)))
        (UInt256.ofNat 1461501637330902918203684832716283019655932542975) :: _ = _
      rw [hm, hhook, hclean]
      rfl
    have rd := poolManagerBlocks.poolManager_block_6084 (R := junk :: R)
      (x11 := UInt256.ofNat 64) (by simp only [List.length_cons]; omega)
      hperm (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    rw [hs, hm, hfree] at rd
    have hcost := memoryAccessCost_covers aw
      [(paramsPtr, ⟨32⟩), (paramsPtr+UInt256.ofNat 32, ⟨32⟩), (paramsPtr+UInt256.ofNat 64, ⟨32⟩),
       (paramsPtr+UInt256.ofNat 96, ⟨32⟩), (UInt256.ofNat 64, ⟨32⟩), (free, ⟨32⟩),
       (free+UInt256.ofNat 32, ⟨32⟩), (free+UInt256.ofNat 64, ⟨32⟩), (free+UInt256.ofNat 96, ⟨32⟩),
       (free, UInt256.ofNat 128), (keyPtr+UInt256.ofNat 128, ⟨32⟩)]
    simp only [memoryAccessWords, memoryAccessCost] at hcost
    refine .inr ⟨_, _, _, ?_, rd⟩
    omega (config := { splitNatSub := false })
  · exact .inl ⟨Bool.eq_false_iff.mpr hperm,
      modifyLiquidityEventStatic (R := junk :: R) (by simp only [List.length_cons]; omega)
        (Bool.eq_false_iff.mpr hperm) h⟩

end Benchmarks.UniswapV4PoolManager
