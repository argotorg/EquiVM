import Benchmarks.Morpho.MetaMorphoV1_1.AccruedFeeGuard
import Benchmarks.Morpho.MetaMorphoV1_1.ConvertSharesSource

/-! The fee-charging branch after asset totals have been computed. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def accruedFeeAssets (interest fee : UInt256) : UInt256 :=
  fullMulDivWord interest fee ⟨1000000000000000000⟩

def accruedFeeShares (offset interest fee supply total : UInt256) : UInt256 :=
  convertSharesWord offset (accruedFeeAssets interest fee) supply
    (UInt256.sub total (accruedFeeAssets interest fee))

def accruedFeeFits (offset interest fee supply total : UInt256) : Prop :=
  fullMulDivFits interest fee ⟨1000000000000000000⟩ ∧
    (accruedFeeAssets interest fee).toNat ≤ total.toNat ∧
    convertSharesFits offset (accruedFeeAssets interest fee) supply
      (UInt256.sub total (accruedFeeAssets interest fee))

def accruedFeeAmountFrame (frame : Frame) (interest fee : UInt256) : Frame :=
  { frame with
    locals := frame.locals.insert "feeAssets" (uint256Value (accruedFeeAssets interest fee)) }

def accruedFeeSupplyFrame (frame : Frame) (interest fee supply : UInt256) : Frame :=
  { accruedFeeAmountFrame frame interest fee with
    locals := (accruedFeeAmountFrame frame interest fee).locals.insert "__c3"
      (uint256Value supply) }

def accruedFeeConversionFrame (frame : Frame) (offset interest fee supply total : UInt256) :
    Frame :=
  { accruedFeeSupplyFrame frame interest fee supply with
    locals := (accruedFeeSupplyFrame frame interest fee supply).locals.insert "__c4"
      (uint256Value (accruedFeeShares offset interest fee supply total)) }

def accruedFeeFinalFrame (frame : Frame) (offset interest fee supply total : UInt256) : Frame :=
  { accruedFeeConversionFrame frame offset interest fee supply total with
    locals := (accruedFeeConversionFrame frame offset interest fee supply total).locals.insert
      "feeShares" (uint256Value (accruedFeeShares offset interest fee supply total)) }

theorem totalSupplyInternalCall (locals imms : Store) (evm : State) (ret : Ident) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "totalSupply_body" [] ret)
      (.ok
        { contract := contract
          locals := locals.insert ret
            (uint256Value (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩))
          immutables := imms } evm) := by
  exact internalCallReturnExpr rfl (evalStorage_totalSupply evm ∅ imms (by simp))

theorem accruedFeeAmountArgs {frame : Frame} {evm : State} {interest fee : UInt256}
    (hi : frame.locals.get? "totalInterest" = some (uint256Value interest))
    (hf : evalExpr? config frame evm (.storage ⟨"fee", []⟩) = .ok (uint256Value fee)) :
    evalExprs? config frame evm
      [.var "totalInterest", .storage ⟨"fee", []⟩, .intLit 1000000000000000000] =
      .ok [uint256Value interest, uint256Value fee, uint256Value ⟨1000000000000000000⟩] := by
  have he : evalExpr? config frame evm (.var "totalInterest") =
      .ok (uint256Value interest) := by simp only [evalExpr?, hi, EvalResult.ofOption]
  simp only [evalExprs?, he, hf, bind, EvalResult.bind, evalExpr?, pure]
  rfl

theorem accruedFeeConversionValues {frame : Frame} {evm : State}
    {interest fee supply total : UInt256}
    (ht : frame.locals.get? "newTotalAssets" = some (uint256Value total)) :
    let f := accruedFeeSupplyFrame frame interest fee supply
    evalExpr? config f evm (.var "feeAssets") = .ok (uint256Value (accruedFeeAssets interest fee)) ∧
    evalExpr? config f evm (.var "__c3") = .ok (uint256Value supply) ∧
    evalExpr? config f evm (.var "newTotalAssets") = .ok (uint256Value total) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp only [evalExpr?, accruedFeeSupplyFrame, accruedFeeAmountFrame,
      store_get_ne _ _ (by decide : ("__c3" == "feeAssets") = false),
      store_get_ne _ _ (by decide : ("__c3" == "newTotalAssets") = false),
      store_get_ne _ _ (by decide : ("feeAssets" == "newTotalAssets") = false),
      store_get_self, ht, EvalResult.ofOption]

def accruedFeeConversionArgs : List Expr :=
  [.var "feeAssets", .var "__c3",
    .inRange (.uint ⟨256, by decide⟩)
      (.binary .sub (.var "newTotalAssets") (.var "feeAssets")), .intLit 0]

theorem accruedFeeConversionArgsSource {frame : Frame} {evm : State}
    {interest fee supply total : UInt256}
    (ht : frame.locals.get? "newTotalAssets" = some (uint256Value total))
    (hfit : (accruedFeeAssets interest fee).toNat ≤ total.toNat) :
    evalExprs? config (accruedFeeSupplyFrame frame interest fee supply) evm
      accruedFeeConversionArgs = .ok
      [uint256Value (accruedFeeAssets interest fee), uint256Value supply,
        uint256Value (UInt256.sub total (accruedFeeAssets interest fee)), uint256Value ⟨0⟩] := by
  obtain ⟨ha, hs, htotal⟩ := accruedFeeConversionValues (interest := interest) (fee := fee)
    (supply := supply) ht (evm := evm)
  have hsub := evalExpr_uint256_sub htotal ha hfit
  simp only [accruedFeeConversionArgs, evalExprs?, ha, hs, hsub,
    bind, EvalResult.bind, evalExpr?, pure]
  rfl

theorem accruedFeeConversionArgsRevert {frame : Frame} {evm : State}
    {interest fee supply total : UInt256}
    (ht : frame.locals.get? "newTotalAssets" = some (uint256Value total))
    (hbad : total.toNat < (accruedFeeAssets interest fee).toNat) :
    evalExprs? config (accruedFeeSupplyFrame frame interest fee supply) evm
      accruedFeeConversionArgs = .revert := by
  obtain ⟨ha, hs, htotal⟩ := accruedFeeConversionValues (interest := interest) (fee := fee)
    (supply := supply) ht (evm := evm)
  have hsub := checkedSubSourceUnderflow htotal ha hbad
  simp only [accruedFeeConversionArgs, evalExprs?, ha, hs, hsub, bind, EvalResult.bind]

theorem accruedFeeBodySource (v : MetaMorphoV1_1Immutables) (locals : Store) (evm : State)
    (interest fee supply total : UInt256)
    (hi : locals.get? "totalInterest" = some (uint256Value interest))
    (hf : evalExpr? config { contract := contract, locals := locals, immutables := immStore v }
      evm (.storage ⟨"fee", []⟩) = .ok (uint256Value fee))
    (ht : locals.get? "newTotalAssets" = some (uint256Value total))
    (hsh : locals.get? "feeShares" = some (uint256Value ⟨0⟩))
    (hs : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = supply)
    (hfit : accruedFeeFits v.DECIMALS_OFFSET interest fee supply total) :
    let frame : Frame := { contract := contract, locals := locals, immutables := immStore v }
    ExecBlock config frame evm accruedFeeBody
      (.ok (accruedFeeFinalFrame frame v.DECIMALS_OFFSET interest fee supply total) evm) := by
  dsimp only
  have hfirst := fullMulDivCall (accruedFeeAmountArgs hi hf) hfit.1 (ret := "feeAssets")
  have hsecond := totalSupplyInternalCall
    (locals.insert "feeAssets" (uint256Value (accruedFeeAssets interest fee))) (immStore v)
    evm "__c3"
  rw [hs] at hsecond
  apply ExecBlock.consNormal hfirst
  apply ExecBlock.consNormal hsecond
  apply ExecBlock.consNormal (convertSharesCall v
    (accruedFeeConversionArgsSource
      (frame := { contract := contract, locals := locals, immutables := immStore v })
      (supply := supply) ht hfit.2.1) hfit.2.2 (ret := "__c4"))
  refine ExecBlock.consNormal (ExecStmt.assign
    (value := uint256Value (accruedFeeShares v.DECIMALS_OFFSET interest fee supply total))
    ?_ ?_) ExecBlock.nil
  · simp only [evalExpr?, store_get_self, EvalResult.ofOption, accruedFeeShares]
  · simp only [assignStorageRef?, accruedFeeAmountFrame,
      store_get_ne _ _ (by decide : ("__c4" == "feeShares") = false),
      store_get_ne _ _ (by decide : ("__c3" == "feeShares") = false),
      store_get_ne _ _ (by decide : ("feeAssets" == "feeShares") = false),
      hsh, updateLocalPath?, bind, EvalResult.bind, pure]
    rfl

theorem accruedFeeBodyReverts (v : MetaMorphoV1_1Immutables) (locals : Store) (evm : State)
    (interest fee supply total : UInt256)
    (hi : locals.get? "totalInterest" = some (uint256Value interest))
    (hf : evalExpr? config { contract := contract, locals := locals, immutables := immStore v }
      evm (.storage ⟨"fee", []⟩) = .ok (uint256Value fee))
    (ht : locals.get? "newTotalAssets" = some (uint256Value total))
    (hs : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = supply)
    (hbad : ¬ accruedFeeFits v.DECIMALS_OFFSET interest fee supply total) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v }
      evm accruedFeeBody .reverted := by
  by_cases hm : fullMulDivFits interest fee ⟨1000000000000000000⟩
  · apply ExecBlock.consNormal (fullMulDivCall (accruedFeeAmountArgs hi hf) hm)
    have hsecond := totalSupplyInternalCall
      (locals.insert "feeAssets" (uint256Value (accruedFeeAssets interest fee))) (immStore v)
      evm "__c3"
    rw [hs] at hsecond
    apply ExecBlock.consNormal hsecond
    by_cases htfit : (accruedFeeAssets interest fee).toNat ≤ total.toNat
    · exact ExecBlock.consRevert (convertSharesCallReverts v
        (accruedFeeConversionArgsSource
          (frame := { contract := contract, locals := locals, immutables := immStore v })
          (supply := supply) ht htfit) (fun hc ↦ hbad ⟨hm, htfit, hc⟩))
    · exact ExecBlock.consRevert (ExecStmt.internalCallArgsRevert
        (accruedFeeConversionArgsRevert
          (frame := { contract := contract, locals := locals, immutables := immStore v })
          (supply := supply) ht (Nat.lt_of_not_ge htfit)))
  · exact ExecBlock.consRevert (fullMulDivCallReverts (accruedFeeAmountArgs hi hf) hm)

theorem accruedFeeFinalFrame_preserves (frame : Frame) (offset interest fee supply total : UInt256)
    (name : Ident) (h0 : ("feeAssets" == name) = false) (h1 : ("__c3" == name) = false)
    (h2 : ("__c4" == name) = false) (h3 : ("feeShares" == name) = false) :
    (accruedFeeFinalFrame frame offset interest fee supply total).locals.get? name =
      frame.locals.get? name := by
  simp only [accruedFeeFinalFrame, accruedFeeConversionFrame, accruedFeeSupplyFrame,
    accruedFeeAmountFrame, store_get_ne _ _ h0, store_get_ne _ _ h1,
    store_get_ne _ _ h2, store_get_ne _ _ h3]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
