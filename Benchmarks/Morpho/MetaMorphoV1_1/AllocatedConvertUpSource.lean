import Benchmarks.Morpho.MetaMorphoV1_1.AllocatedConvertSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConvertSharesUpSource

/-! Upward conversion after the shared fee-accrual and supply prefix. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem allocatedConvertUpTailSource (v : MetaMorphoV1_1Immutables) {locals : Store} {evm : State}
    {assets total shares supply ptr : UInt256}
    (hl : AllocatedConvertLocals
      { contract := contract, locals := locals, immutables := immStore v }
      assets total shares supply ptr ⟨1⟩)
    (hs : supply.toNat + shares.toNat < UInt256.size)
    (hc : convertSharesUpFits v.DECIMALS_OFFSET assets (supply + shares) total) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (allocatedConvertToSharesFunction.body.drop 6)
      (.returned
        { contract := contract
          locals := locals.insert "__c2"
            (uint256Value (convertSharesUpWord v.DECIMALS_OFFSET assets (supply + shares) total))
          immutables := immStore v } evm
        [uint256Value (convertSharesUpWord v.DECIMALS_OFFSET assets (supply + shares) total),
          uint256Value ptr]) := by
  rw [allocatedConvertToSharesFunction_tail]
  apply ExecBlock.consNormal (convertSharesUpCall v (allocatedConvertArgsSource hl hs) hc)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, store_get_self,
    store_get_ne _ _ (by decide : ("__c2" == cursorName) = false), hl.cursor,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem allocatedConvertUpTailReverts (v : MetaMorphoV1_1Immutables) {locals : Store} {evm : State}
    {assets total shares supply ptr : UInt256}
    (hl : AllocatedConvertLocals
      { contract := contract, locals := locals, immutables := immStore v }
      assets total shares supply ptr ⟨1⟩)
    (hbad : ¬ (supply.toNat + shares.toNat < UInt256.size ∧
      convertSharesUpFits v.DECIMALS_OFFSET assets (supply + shares) total)) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (allocatedConvertToSharesFunction.body.drop 6) .reverted := by
  rw [allocatedConvertToSharesFunction_tail]
  by_cases hs : supply.toNat + shares.toNat < UInt256.size
  · exact ExecBlock.consRevert (convertSharesUpCallReverts v
      (allocatedConvertArgsSource hl hs) (fun hc ↦ hbad ⟨hs, hc⟩))
  · exact ExecBlock.consRevert (ExecStmt.internalCallArgsRevert
      (allocatedConvertArgsRevert hl (Nat.le_of_not_gt hs)))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
