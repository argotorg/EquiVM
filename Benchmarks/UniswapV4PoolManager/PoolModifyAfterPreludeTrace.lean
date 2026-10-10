import Benchmarks.UniswapV4PoolManager.PoolModifyAccountingTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyTicksMemory
import Benchmarks.UniswapV4PoolManager.PoolModifySource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyAfterPreludeMemory (mem : ByteArray) (free ptr id : UInt256) (p : PoolModifyParams) (evm : State) : ByteArray :=
  poolModifyAccountingMemory (poolModifyTicksMemory mem ptr id p evm) free id p
    (poolModifyTicksFlipped evm id p false) (poolModifyTicksFlipped evm id p true)

theorem poolModifyAfterPreludeTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {σ₀ : AccountMap}
    {mem rdata : ByteArray} {aw free id params ptr x1 x2 x4 x5 x9 extra : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+34 ≤ 1024) (hI : evm.executionEnv = I) (hσ : evm.σ₀ = σ₀)
    (hc : int24Canonical p.spacing) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (ht : poolTicksValid p.lower p.upper) (hd : signedFits ⟨128, by decide⟩ p.delta)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hfree : memLoad (UInt256.ofNat 64) mem = free) (hfh : free.toNat+64 < UInt256.size)
    (ha : UInt256.land (memLoad params mem) solcAddrMask = accountWord p.owner)
    (hs : memLoad (params+UInt256.ofNat 160) mem = p.salt)
    (hsp : memLoad (params+UInt256.ofNat 128) mem = p.spacing)
    (hp : 64 ≤ params.toNat) (hpb : params.toNat+192 ≤ ptr.toNat)
    (hptr : 160 ≤ ptr.toNat) (hspan : ptr.toNat+128 ≤ mem.size) (hfit : ptr.toNat+128 < UInt256.size)
    (hstatefree : ptr.toNat+128 ≤ free.toNat)
    (hlzero : memLoad ptr mem = ⟨0⟩) (huzero : memLoad (ptr+UInt256.ofNat 64) mem = ⟨0⟩)
    (h : RD (deployedRuntime v) I g s0 (if p.delta ≠ 0 then ⟨6949⟩ else ⟨5722⟩)
      (⟨0⟩ :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: extra :: R)
      mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (poolModifyReturnTrace v I g s0 σ₀ (poolModifyAfterPreludeMemory mem free ptr id p evm)
        rdata x1 x2 x4 x5 x9 extra R)
      (poolModifyAfterPreludeResult f evm id p) := by
  have h128 := uadd_word_ofNat_toNat params 128 (by omega)
  have h160 := uadd_word_ofNat_toNat params 160 (by omega)
  have hticks := poolModifyTicksTrace f v (by simp only [List.length_cons]; omega) hI hc hl hu ht hd
    hm (by omega) hsp (by omega) (by omega) (by omega) hptr hfit h
  apply functionResultTrace_continueBlock hticks
  intro f1 post _ ht1
  obtain ⟨hIpost, hσpost, aw1, k1, C1, rd1⟩ := ht1
  have hsize := poolModifyTicksMemory_size_ge mem ptr id p evm (by omega)
  have hm1 := (poolModifyTicksMemory_load_before mem ptr id p evm (UInt256.ofNat 128)
    (by decide) (by change 160 ≤ mem.size; omega) hptr hfit).trans hm
  have hfree1 := (poolModifyTicksMemory_load_before mem ptr id p evm (UInt256.ofNat 64)
    (by decide) (by change 96 ≤ mem.size; omega) (by change 96 ≤ ptr.toNat; omega) hfit).trans hfree
  have ha1 : UInt256.land (memLoad params (poolModifyTicksMemory mem ptr id p evm)) solcAddrMask = accountWord p.owner := by
    rw [poolModifyTicksMemory_load_before mem ptr id p evm params hp (by omega) (by omega) hfit]
    exact ha
  have hs1 := (poolModifyTicksMemory_load_before mem ptr id p evm (params+UInt256.ofNat 160)
    (by omega) (by omega) (by omega) hfit).trans hs
  exact poolModifyAccountingTrace f1 v hstack hIpost (hσpost.trans hσ) hm1 (by omega) hl hu ht hd
    hfree1 (by omega) hfh ha1 hs1 hp (by omega) (by omega) (by omega) (by omega) hfit hstatefree
    (poolModifyTicksMemory_lowerFlipped mem ptr id p evm (by omega) hfit hlzero)
    (poolModifyTicksMemory_upperFlipped mem ptr id p evm (by omega) hfit huzero) rd1

end Benchmarks.UniswapV4PoolManager
