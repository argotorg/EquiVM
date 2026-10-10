import Benchmarks.Morpho.MetaMorphoV1_1.AllocatedAssetsSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConvertAssetsUpSource

/-! Upward conversion after the shared fee-accrual and supply prefix. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem allocatedAssetsUpTailSource (v : MetaMorphoV1_1Immutables) {locals : Store} {evm : State}
    {assets total shares supply ptr : UInt256}
    (hl : AllocatedAssetsLocals
      { contract := contract, locals := locals, immutables := immStore v }
      assets total shares supply ptr ⟨1⟩)
    (hs : supply.toNat + shares.toNat < UInt256.size)
    (hc : convertAssetsUpFits v.DECIMALS_OFFSET assets (supply + shares) total) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (allocatedConvertToAssetsFunction.body.drop 6)
      (.returned
        { contract := contract
          locals := locals.insert "__c2"
            (uint256Value (convertAssetsUpWord v.DECIMALS_OFFSET assets (supply + shares) total))
          immutables := immStore v } evm
        [uint256Value (convertAssetsUpWord v.DECIMALS_OFFSET assets (supply + shares) total),
          uint256Value ptr]) := by
  rw [allocatedConvertToAssetsFunction_tail]
  apply ExecBlock.consNormal (convertAssetsUpCall v (allocatedAssetsArgsSource hl hs) hc)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, store_get_self,
    store_get_ne _ _ (by decide : ("__c2" == cursorName) = false), hl.cursor,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem allocatedAssetsUpTailReverts (v : MetaMorphoV1_1Immutables) {locals : Store} {evm : State}
    {assets total shares supply ptr : UInt256}
    (hl : AllocatedAssetsLocals
      { contract := contract, locals := locals, immutables := immStore v }
      assets total shares supply ptr ⟨1⟩)
    (hbad : ¬ (supply.toNat + shares.toNat < UInt256.size ∧
      convertAssetsUpFits v.DECIMALS_OFFSET assets (supply + shares) total)) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (allocatedConvertToAssetsFunction.body.drop 6) .reverted := by
  rw [allocatedConvertToAssetsFunction_tail]
  by_cases hs : supply.toNat + shares.toNat < UInt256.size
  · exact ExecBlock.consRevert (convertAssetsUpCallReverts v
      (allocatedAssetsArgsSource hl hs) (fun hc ↦ hbad ⟨hs, hc⟩))
  · exact ExecBlock.consRevert (ExecStmt.internalCallArgsRevert
      (allocatedAssetsArgsRevert hl (Nat.le_of_not_gt hs)))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
