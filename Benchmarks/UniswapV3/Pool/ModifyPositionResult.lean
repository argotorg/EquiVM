import Benchmarks.UniswapV3.Pool.ModifyPositionGuardTrace
import Benchmarks.UniswapV3.Pool.ModifyPositionUpdateSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def ModifyPositionSuccess (v : UniswapV3PoolImmutables) (a : ModifyPositionArgs)
    (evm s0 : EVM.State) (ee : ExecutionEnv) (g : Sat256) (ret : UInt256)
    (R : List UInt256) (mem : ByteArray) (p : UInt256) (rdata : ByteArray) : Prop :=
  ∃ frame evm' amount0 amount1 mem' free aw σ k C,
    ExecFuncBody config (modifyPositionFrame (immStore v) a) evm modifyPositionFunction.body
      (.returned frame evm' (some [modifyPositionKeyValue a, .int amount0, .int amount1])) ∧
    (-(2 ^ 255 : Int) ≤ amount0 ∧ amount0 < 2 ^ 255) ∧
    (-(2 ^ 255 : Int) ≤ amount1 ∧ amount1 < 2 ^ 255) ∧
    SourceState s0 ee σ evm' ∧
    RD (deployedRuntime v) ee g s0 ret
      (EVM.wordOfInt amount1 :: EVM.wordOfInt amount0 :: solcMappingSlot ⟨7⟩ (modifyPositionKey a) :: R)
      mem' aw rdata σ k C ∧ HeapMemory mem' aw free ∧ free.toNat ≤ p.toNat + 1210 ∧
    MemoryPrefix mem mem' p.toNat

theorem modifyPositionFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free ret : UInt256} {mem mem' rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs)
    (evm evm' : EVM.State) (frame : Frame) (amount0 amount1 : Int)
    (hprefix : ExecBlock config (modifyPositionFrame (immStore v) a) evm
      (modifyPositionFunction.body.take 8)
      (.ok (modifyPositionUpdatedFrame (immStore v) a evm) (modifyPositionUpdatedState v a evm)))
    (htail : ExecBlock config (modifyPositionUpdatedFrame (immStore v) a evm)
      (modifyPositionUpdatedState v a evm) (modifyPositionFunction.body.drop 8)
      (.returned frame evm' (some [modifyPositionKeyValue a, .int amount0, .int amount1])))
    (hs : SourceState s0 ee σ evm')
    (rd : RD (deployedRuntime v) ee g s0 ⟨16801⟩
      (p :: EVM.wordOfInt amount1 :: EVM.wordOfInt amount0 :: solcMappingSlot ⟨7⟩ (modifyPositionKey a) ::
        q :: ret :: R) mem' aw rdata σ k C)
    (h0 : -(2 ^ 255 : Int) ≤ amount0 ∧ amount0 < 2 ^ 255)
    (h1 : -(2 ^ 255 : Int) ≤ amount1 ∧ amount1 < 2 ^ 255)
    (hm : HeapMemory mem' aw free) (hfree : free.toNat ≤ p.toNat + 1210)
    (hmem : MemoryPrefix mem mem' p.toNat)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    ModifyPositionSuccess v a evm s0 ee g ret R mem p rdata := by
  have rr := modifyPositionReturnX (v := v) rd hret hov
  refine ⟨frame, evm', amount0, amount1, mem', free, aw, σ, k + 8, C + 25,
    ?_, h0, h1, hs, rr, hm, hfree, hmem⟩
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 8 modifyPositionFunction.body]
  exact execBlock_append_ok hprefix htail

end Benchmarks.UniswapV3.Pool
