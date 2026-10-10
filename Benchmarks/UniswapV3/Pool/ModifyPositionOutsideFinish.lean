import Benchmarks.UniswapV3.Pool.ModifyPositionResult
import Benchmarks.UniswapV3.Pool.ModifyPositionOutsideTrace
import Benchmarks.UniswapV3.Pool.ModifyPositionOutsideChoice

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000
attribute [local irreducible] modifyPositionUpdatedState

theorem modifyPositionOutsideFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free ret : UInt256} {mem mem' rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs) (evm : EVM.State)
    (second : Bool)
    (hprefix : ExecBlock config (modifyPositionFrame (immStore v) a) evm
      (modifyPositionFunction.body.take 8)
      (.ok (modifyPositionUpdatedFrame (immStore v) a evm) (modifyPositionUpdatedState v a evm)))
    (hs : SourceState s0 ee σ (modifyPositionUpdatedState v a evm))
    (rd : RD (deployedRuntime v) ee g s0 (modifyPositionOutsideEntry second)
      (p :: ⟨0⟩ :: ⟨0⟩ :: solcMappingSlot ⟨7⟩ (modifyPositionKey a) :: q :: ret :: R)
      mem' aw rdata σ k C)
    (ha : a.Fits) (ht : validTicks a.lower a.upper) (hz : a.delta ≠ 0)
    (hrange : if second then a.upper ≤ slot0TickValue evm.accountMap evm.executionEnv
      else slot0TickValue evm.accountMap evm.executionEnv < a.lower)
    (hm : HeapMemory mem' aw free) (hq : ModifyPositionParamsMemory mem' q a)
    (hb : q.toNat + 128 ≤ 2 ^ 200) (hfree : free.toNat ≤ p.toNat + 1210)
    (hmem : MemoryPrefix mem mem' p.toNat)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 42 ≤ 1024) :
    (ExecFuncBody config (modifyPositionFrame (immStore v) a) evm modifyPositionFunction.body .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    ModifyPositionSuccess v a evm s0 ee g ret R mem p rdata := by
  rcases modifyPositionOutsideX (v := v) a evm (modifyPositionUpdatedState v a evm) second
    rd ha ht hm hq hb (by evm_ov) with ⟨hsrc, rr⟩ | ⟨hsrc, hv, aw', kr, Cr, rr, hm'⟩
  · have hchoice := modifyPositionOutsideChoiceSource (immStore v) a evm
      (modifyPositionUpdatedState v a evm) second .reverted hz hrange ht hsrc
    refine Or.inl ⟨?_, rr⟩
    apply ExecFuncBody.execBlockRevert
    rw [← List.take_append_drop 8 modifyPositionFunction.body]
    exact execBlock_append_ok hprefix (ExecBlock.consRevert hchoice)
  · have hchoice := modifyPositionOutsideChoiceSource (immStore v) a evm
      (modifyPositionUpdatedState v a evm) second _ hz hrange ht hsrc
    have htail := ExecBlock.consNormal hchoice (ExecBlock.consReturn
      (modifyPositionOutsideReturnSource (immStore v) a evm (modifyPositionUpdatedState v a evm) second)
      (stmts := []))
    have hbounds := signedAmountDeltaResult_bounds second (modifyPositionOutsideArgs a)
      (modifyPositionOutsideArgs_fits a ha) hv
    have h0 : -(2 ^ 255 : Int) ≤ (if second then 0 else signedAmountDeltaResult second (modifyPositionOutsideArgs a)) ∧
        (if second then 0 else signedAmountDeltaResult second (modifyPositionOutsideArgs a)) < 2 ^ 255 := by
      cases second
      · exact hbounds
      · norm_num
    have h1 : -(2 ^ 255 : Int) ≤ (if second then signedAmountDeltaResult second (modifyPositionOutsideArgs a) else 0) ∧
        (if second then signedAmountDeltaResult second (modifyPositionOutsideArgs a) else 0) < 2 ^ 255 := by
      cases second
      · norm_num
      · exact hbounds
    apply Or.inr
    have rr' : RD (deployedRuntime v) ee g s0 ⟨16801⟩
        (p :: EVM.wordOfInt (if second then signedAmountDeltaResult second (modifyPositionOutsideArgs a) else 0) ::
          EVM.wordOfInt (if second then 0 else signedAmountDeltaResult second (modifyPositionOutsideArgs a)) ::
          solcMappingSlot ⟨7⟩ (modifyPositionKey a) :: q :: ret :: R) mem' aw' rdata σ kr Cr := by
      simpa only [apply_ite EVM.wordOfInt, show EVM.wordOfInt 0 = (⟨0⟩ : UInt256) from rfl] using rr
    exact modifyPositionFinishX (v := v) a evm (modifyPositionUpdatedState v a evm)
      (modifyPositionOutsideFinalFrame (immStore v) a evm second)
      (if second then 0 else signedAmountDeltaResult second (modifyPositionOutsideArgs a))
      (if second then signedAmountDeltaResult second (modifyPositionOutsideArgs a) else 0)
      hprefix htail hs rr' h0 h1 hm' hfree hmem hret (by omega)

end Benchmarks.UniswapV3.Pool
