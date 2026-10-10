import Benchmarks.Morpho.MetaMorphoV1_1.MarketInterestSource
import Benchmarks.Morpho.MetaMorphoV1_1.CastFieldSource

/-! Source continuations for the two interest casts and asset balance updates. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def marketAssetsFits (ptr interest : UInt256) (market : ByteArray) : Prop :=
  castAddFits ptr interest (calldataWord market 64) ∧
    castAddFits (nextCursor ptr ⟨64⟩) interest (calldataWord market 0)

instance (ptr interest : UInt256) (market : ByteArray) :
    Decidable (marketAssetsFits ptr interest market) := inferInstanceAs (Decidable (_ ∧ _))

def marketBorrowFrame (frame : Frame) (market : ByteArray) (ptr interest : UInt256) : Frame :=
  marketUpdateFrame (cursorCastFrame frame "__c5" interest ptr)
    (marketUpdatedValue market (calldataWord market 0) (calldataWord market 32)
      (calldataWord market 64 + interest))

def marketAssetsFrame (frame : Frame) (market : ByteArray) (ptr interest : UInt256) : Frame :=
  marketUpdateFrame
    (cursorCastFrame (marketBorrowFrame frame market ptr interest)
      "__c6" interest (nextCursor ptr ⟨64⟩))
    (marketUpdatedValue market (calldataWord market 0 + interest) (calldataWord market 32)
      (calldataWord market 64 + interest))

set_option maxRecDepth 2000 in
theorem marketAssetStatements :
    marketAccrualBody.drop 4 =
      cursorCall allocatedToUint128Function.name [.var "interest"] "__c5" ++
      [marketFieldAdd "totalBorrowAssets" "__c5"] ++
      cursorCall allocatedToUint128Function.name [.var "interest"] "__c6" ++
      [marketFieldAdd "totalSupplyAssets" "__c6"] ++ marketAccrualBody.drop 12 := by
  let reserves := fun name ↦
    if name == "market" then 384 else if name == "borrowRateView" then 32 else 0
  let taylor := Stmt.internalCall "MathLib_wTaylorCompounded"
    [.var "borrowRate", .var "elapsed"] "__c3"
  let interest := Stmt.internalCall "MathLib_wMulDown"
    [.field (.var "market") "totalBorrowAssets", .var "__c3"] "interest"
  have hsplit (tail : List Stmt) :
      allocationBody marketBalancesAllocationCalls reserves
        (borrowRateStatement :: taylor :: interest ::
          .internalCall "UtilsLib_toUint128" [.var "interest"] "__c5" ::
          marketFieldAdd "totalBorrowAssets" "__c5" ::
          .internalCall "UtilsLib_toUint128" [.var "interest"] "__c6" ::
          marketFieldAdd "totalSupplyAssets" "__c6" :: tail) =
      [borrowRateStatement, reserveBytes 32, taylor, interest] ++
        cursorCall allocatedToUint128Function.name [.var "interest"] "__c5" ++
        [marketFieldAdd "totalBorrowAssets" "__c5"] ++
        cursorCall allocatedToUint128Function.name [.var "interest"] "__c6" ++
        [marketFieldAdd "totalSupplyAssets" "__c6"] ++
        allocationBody marketBalancesAllocationCalls reserves tail := by
    simp [allocationBody, allocationStatement, marketBalancesAllocationCalls, marketFieldAdd,
      borrowRateStatement, reserves, taylor, interest, List.append_assoc]
  have hb := hsplit (marketAccrualSourceBody.drop 7)
  change marketAccrualBody = _ at hb
  rw [hb]
  rfl

theorem marketBorrowFrame_cursor (frame : Frame) (market : ByteArray) (ptr interest : UInt256) :
    (marketBorrowFrame frame market ptr interest).locals.get? cursorName =
      some (uint256Value (nextCursor ptr ⟨64⟩)) := by
  rw [marketBorrowFrame, marketUpdateFrame, store_get_ne _ _ (by decide)]
  exact cursorCastFrame_cursor _ _ _ _

theorem marketBorrowFrame_interest {frame : Frame} (market : ByteArray) (ptr interest : UInt256)
    (hi : frame.locals.get? "interest" = some (uint256Value interest)) :
    (marketBorrowFrame frame market ptr interest).locals.get? "interest" =
      some (uint256Value interest) := by
  rw [marketBorrowFrame, marketUpdateFrame, store_get_ne _ _ (by decide),
    cursorCastFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
  exact hi

theorem marketAssetsSourcePrefix {frame : Frame} {evm : State}
    {market : ByteArray} {ptr interest : UInt256} (hcontract : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (marketValue market))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hi : frame.locals.get? "interest" = some (uint256Value interest))
    (hfit : marketAssetsFits ptr interest market) :
    ABlock config evm frame (marketAccrualBody.drop 4)
      (marketAssetsFrame frame market ptr interest) (marketAccrualBody.drop 12) := by
  constructor
  intro result htail
  rw [marketAssetStatements]
  apply (cursorCastSourcePrefix "__c5" _ hcontract (by decide)
    (by simp only [evalExpr?, hi, EvalResult.ofOption]) hp hfit.1.1 hfit.1.2.1).run
  apply ExecBlock.consNormal (marketFieldAddSource
    (by rw [cursorCastFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]; exact hm)
    (by rfl) (by rfl) (cursorCastFrame_value _ _ _ _ (by decide)) hfit.1.2.2)
  apply (cursorCastSourcePrefix "__c6" _ (show
      (marketBorrowFrame frame market ptr interest).contract = contract from hcontract)
    (by decide) (by simp only [evalExpr?, marketBorrowFrame_interest market ptr interest hi,
      EvalResult.ofOption]) (marketBorrowFrame_cursor frame market ptr interest)
      hfit.2.1 hfit.2.2.1).run
  apply ExecBlock.consNormal (marketFieldAddSource
    (by rw [cursorCastFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
        exact store_get_self _ _ _)
    (by rfl) (by rfl) (cursorCastFrame_value _ _ _ _ (by decide)) hfit.2.2.2) htail

theorem marketAssetsSourceReverts {frame : Frame} {evm : State}
    {market : ByteArray} {ptr interest : UInt256} (hcontract : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (marketValue market))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hi : frame.locals.get? "interest" = some (uint256Value interest))
    (hbad : ¬ marketAssetsFits ptr interest market) :
    ExecBlock config frame evm (marketAccrualBody.drop 4) .reverted := by
  rw [marketAssetStatements]
  by_cases hb : castAddFits ptr interest (calldataWord market 64)
  · apply (castFieldSourcePrefix (updated := marketUpdatedValue market
      (calldataWord market 0) (calldataWord market 32) (calldataWord market 64 + interest))
      "totalBorrowAssets" "__c5" _ hcontract (by decide) (by decide) (by decide)
      hm rfl rfl (by simp only [evalExpr?, hi, EvalResult.ofOption]) hp hb).run
    exact castFieldSourceReverts "totalSupplyAssets" "__c6" _
      (show (marketBorrowFrame frame market ptr interest).contract = contract from hcontract)
      (by decide) (by decide) (by decide) (store_get_self _ _ _) rfl
      (by change evalExpr? config (marketBorrowFrame frame market ptr interest) evm _ = _
          simp only [evalExpr?, marketBorrowFrame_interest market ptr interest hi,
            EvalResult.ofOption]) (marketBorrowFrame_cursor frame market ptr interest)
      (fun hs ↦ hbad ⟨hb, hs⟩)
  · exact castFieldSourceReverts "totalBorrowAssets" "__c5" _ hcontract
      (by decide) (by decide) (by decide) hm rfl
      (by simp only [evalExpr?, hi, EvalResult.ofOption]) hp hb

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
