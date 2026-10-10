import Benchmarks.UniswapV4PoolManager.PoolModifyFees
import Benchmarks.UniswapV4PoolManager.PoolFeeInsideTrace
import Benchmarks.UniswapV4PoolManager.PositionGetTrace
import Benchmarks.UniswapV4PoolManager.PositionLiquidityTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyFeesMemory (mem : ByteArray) (free id : UInt256) (p : PoolModifyParams) : ByteArray :=
  positionGetMemory (poolFeeInsideMemory mem id p.lower p.upper) free id p.owner p.lower p.upper p.salt

theorem poolModifyFeesPreludeTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw free id params x0 x1 x2 ptr x4 x5 x9 : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hfree : memLoad (UInt256.ofNat 64) mem = free) (hfl : 160 ≤ free.toNat)
    (hfh : free.toNat+64 < UInt256.size)
    (ha : UInt256.land (memLoad params mem) solcAddrMask = accountWord p.owner)
    (hs : memLoad (params+UInt256.ofNat 160) mem = p.salt)
    (hp : 64 ≤ params.toNat) (hps : params.toNat+192 ≤ mem.size) (hpf : params.toNat+160 < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨5722⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨5915⟩
      (positionUpdateInputStack evm id (poolModifyPositionKey p) p.delta (poolModifyFeeWord evm id p false)
        p.upper x0 x1 x2 ptr x4 x5 p.lower x9 (poolModifyFeeWord evm id p true) R)
      (poolModifyFeesMemory mem free id p) aw' rdata evm.accountMap k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := poolFeeInsideTrace v hstack hI hm hmem hl hu h
  have hm1 := (poolFeeInsideMemory_load id p.lower p.upper (UInt256.ofNat 128) (by decide) hmem).trans hm
  have hmem1 : 160 ≤ (poolFeeInsideMemory mem id p.lower p.upper).size := by
    rw [poolFeeInsideMemory_size _ _ _ (by omega)]
    exact hmem
  have hfree1 := (poolFeeInsideMemory_load (mem := mem) id p.lower p.upper (UInt256.ofNat 64) (by decide)
    (by change 96 ≤ mem.size; omega)).trans hfree
  have ha1 : UInt256.land (memLoad params (poolFeeInsideMemory mem id p.lower p.upper)) solcAddrMask = accountWord p.owner := by
    rw [poolFeeInsideMemory_load _ _ _ params hp (by omega)]
    exact ha
  have h160 := uadd_word_ofNat_toNat params 160 hpf
  have hs1 := (poolFeeInsideMemory_load id p.lower p.upper (params+UInt256.ofNat 160)
    (by omega) (by omega)).trans hs
  exact positionGetTrace v hstack hI hm1 hmem1 hfree1 hfl hfh ha1 hs1 rd1

end Benchmarks.UniswapV4PoolManager
