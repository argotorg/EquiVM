import Benchmarks.UniswapV4PoolManager.PoolModifyAfterPreludeTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyStartTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyAllocationMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyAllocatedMemory (mem : ByteArray) (ptr id : UInt256) (p : PoolModifyParams) (evm : State) : ByteArray :=
  poolModifyAfterPreludeMemory (poolModifyAllocationMemory mem ptr) (ptr+UInt256.ofNat 128) ptr id p evm

theorem poolModifyAllocatedTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {σ₀ : AccountMap}
    {mem rdata : ByteArray} {aw id params ptr x1 x2 x4 x5 x9 extra : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+34 ≤ 1024) (hI : evm.executionEnv = I) (hσ : evm.σ₀ = σ₀)
    (hc : int24Canonical p.spacing) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (ht : poolTicksValid p.lower p.upper) (hd : signedFits ⟨128, by decide⟩ p.delta)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (ha : UInt256.land (memLoad params mem) solcAddrMask = accountWord p.owner)
    (hs : memLoad (params+UInt256.ofNat 160) mem = p.salt)
    (hsp : memLoad (params+UInt256.ofNat 128) mem = p.spacing)
    (hp : 160 ≤ params.toNat) (hps : params.toNat+192 ≤ mem.size) (hpb : params.toNat+192 ≤ ptr.toNat)
    (hptr : 160 ≤ ptr.toNat) (hfit : ptr.toNat+128 ≤ solcMaxU64)
    (h : RD (deployedRuntime v) I g s0 ⟨5680⟩
      (x1 :: x2 :: ⟨0⟩ :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: extra :: R)
      mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (poolModifyReturnTrace v I g s0 σ₀ (poolModifyAllocatedMemory mem ptr id p evm)
        rdata x1 x2 x4 x5 x9 extra R)
      (poolModifyAfterPreludeResult (poolModifyPreludeFrame f p) evm id p) := by
  have hfit256 : ptr.toNat+128 < UInt256.size := by
    change ptr.toNat+128 < 2^256
    change ptr.toNat+128 ≤ 2^64-1 at hfit
    omega
  have h128 : (ptr+UInt256.ofNat 128).toNat = ptr.toNat+128 := uadd_word_ofNat_toNat ptr 128 hfit256
  have hp128 := uadd_word_ofNat_toNat params 128 (by omega)
  have hp160 := uadd_word_ofNat_toNat params 160 (by omega)
  obtain ⟨aw1, k1, C1, rd1⟩ := poolModifyAllocateTrace v (by simp only [List.length_cons]; omega) hfree hfit h
  obtain ⟨aw2, k2, C2, rd2⟩ := poolModifyInitialTrace v (by simp only [List.length_cons]; omega) hfit256 hd rd1
  have hm1 := (poolModifyAllocationMemory_load_before mem ptr (UInt256.ofNat 128) (by decide) hmem hptr).trans hm
  have hs1 := (poolModifyAllocationMemory_load_before mem ptr (params+UInt256.ofNat 160)
    (by omega) (by omega) (by omega)).trans hs
  have hsp1 := (poolModifyAllocationMemory_load_before mem ptr (params+UInt256.ofNat 128)
    (by omega) (by omega) (by omega)).trans hsp
  have ha1 : UInt256.land (memLoad params (poolModifyAllocationMemory mem ptr)) solcAddrMask = accountWord p.owner := by
    rw [poolModifyAllocationMemory_load_before mem ptr params (by omega) (by omega) (by omega)]
    exact ha
  exact poolModifyAfterPreludeTrace (poolModifyPreludeFrame f p) v hstack hI hσ hc hl hu ht hd hm1
    (poolModifyAllocationMemory_free mem ptr (by omega))
    (by rw [h128]; change ptr.toNat+128+64 < 2^256; change ptr.toNat+128 ≤ 2^64-1 at hfit; omega)
    ha1 hs1 hsp1 (by omega) hpb hptr
    (by rw [poolModifyAllocationMemory_size]; omega) hfit256 (by rw [h128])
    (poolModifyAllocationMemory_lowerZero mem ptr hfit256)
    (poolModifyAllocationMemory_upperZero mem ptr hfit256) rd2

end Benchmarks.UniswapV4PoolManager
