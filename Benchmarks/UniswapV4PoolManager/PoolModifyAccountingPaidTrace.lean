import Benchmarks.UniswapV4PoolManager.PoolModifyAfterFeesPaidTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyFeesPaidTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolModifyAccountingPaidTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {σ₀ : AccountMap}
    {mem rdata : ByteArray} {aw free id params ptr x1 x2 x4 x5 x9 extra : UInt256} {p : PoolModifyParams}
    {fl fu : Bool} {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+34 ≤ 1024) (hI : evm.executionEnv = I) (hσ : evm.σ₀ = σ₀)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper) (ht : poolTicksValid p.lower p.upper)
    (hd : signedFits ⟨128, by decide⟩ p.delta)
    (hfree : memLoad (UInt256.ofNat 64) mem = free) (hfl : 160 ≤ free.toNat)
    (hfh : free.toNat+64 < UInt256.size)
    (ha : UInt256.land (memLoad params mem) solcAddrMask = accountWord p.owner)
    (hs : memLoad (params+UInt256.ofNat 160) mem = p.salt)
    (hp : 64 ≤ params.toNat) (hps : params.toNat+192 ≤ mem.size) (hpf : params.toNat+160 < UInt256.size)
    (hptr : 64 ≤ ptr.toNat) (hspan : ptr.toNat+96 ≤ mem.size) (hfit : ptr.toNat+128 < UInt256.size)
    (hstatefree : ptr.toNat+128 ≤ free.toNat)
    (hlflip : memLoad ptr mem = UInt256.fromBool fl)
    (huflip : memLoad (ptr+UInt256.ofNat 64) mem = UInt256.fromBool fu)
    (h5 : 5 ≤ aw.toNat) (hactive : ptr.toNat+128 ≤ aw.toNat*32) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ⟨5722⟩
      (⟨0⟩ :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: extra :: R)
      mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (poolModifyReturnPaidTrace v I g s0 σ₀ (poolModifyAccountingMemory mem free id p fl fu)
        rdata x1 x2 x4 x5 x9 extra R)
      (poolModifyAccountingResult f evm id p fl fu) := by
  have hfees := poolModifyFeesPaidTrace f v (by simp only [List.length_cons]; omega) hI hm hmem hl hu
    hd.1 hd.2 hfree hfl hfh ha hs hp hps hpf h5 hpaid h
  apply functionResultTrace_continueBlock hfees
  intro f1 post _ ht1
  obtain ⟨hIpost, hσpost, aw1, k1, C1, hpaid1, haw1, rd1⟩ := ht1
  have hsize := poolModifyFeesMemory_size mem free id p (by omega)
  have hm1 := (poolModifyFeesMemory_load_before mem free id p (UInt256.ofNat 128) (by decide) hmem hfl).trans hm
  have hl1 := (poolModifyFeesMemory_load_before mem free id p ptr hptr (by omega) (by omega)).trans hlflip
  have h64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have hu1 := (poolModifyFeesMemory_load_before mem free id p (ptr+UInt256.ofNat 64)
    (by omega) (by omega) (by omega)).trans huflip
  exact poolModifyAfterFeesPaidTrace f1 v hstack hIpost (hσpost.trans hσ) hl hu ht hd hm1
    (by omega) hptr (by omega) hfit hl1 hu1 (by omega) (by omega) hpaid1 rd1

end Benchmarks.UniswapV4PoolManager
