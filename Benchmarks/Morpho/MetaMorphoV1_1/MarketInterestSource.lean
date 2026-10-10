import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateSource
import Benchmarks.Morpho.MetaMorphoV1_1.TaylorSource
import Benchmarks.Morpho.MetaMorphoV1_1.WadMultiply

/-! The two source calls that compute accrued interest after reading the borrow rate. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def marketInterest (assets rate elapsed : UInt256) : UInt256 :=
  wadMulWord assets (taylorSum (UInt256.mul rate elapsed))

def marketInterestFits (assets rate elapsed : UInt256) : Prop :=
  taylorFits rate elapsed ∧
    assets.toNat * (taylorSum (UInt256.mul rate elapsed)).toNat < UInt256.size

instance (assets rate elapsed : UInt256) : Decidable (marketInterestFits assets rate elapsed) :=
  inferInstanceAs (Decidable (_ ∧ _))

def marketTaylorFrame (frame : Frame) (rate elapsed : UInt256) : Frame :=
  { frame with
    locals := frame.locals.insert "__c3" (uint256Value (taylorSum (UInt256.mul rate elapsed))) }

def marketInterestFrame (frame : Frame) (assets rate elapsed : UInt256) : Frame :=
  { marketTaylorFrame frame rate elapsed with
    locals := (marketTaylorFrame frame rate elapsed).locals.insert "interest"
      (uint256Value (marketInterest assets rate elapsed)) }

set_option maxRecDepth 2000 in
theorem marketInterestStatements :
    marketAccrualBody.drop 2 =
      .internalCall "MathLib_wTaylorCompounded" [.var "borrowRate", .var "elapsed"] "__c3" ::
      .internalCall "MathLib_wMulDown"
        [.field (.var "market") "totalBorrowAssets", .var "__c3"] "interest" ::
      marketAccrualBody.drop 4 := by
  let reserves := fun name ↦
    if name == "market" then 384 else if name == "borrowRateView" then 32 else 0
  let taylor := Stmt.internalCall "MathLib_wTaylorCompounded"
    [.var "borrowRate", .var "elapsed"] "__c3"
  let interest := Stmt.internalCall "MathLib_wMulDown"
    [.field (.var "market") "totalBorrowAssets", .var "__c3"] "interest"
  have hsplit (tail : List Stmt) :
      allocationBody marketBalancesAllocationCalls reserves
        (borrowRateStatement :: taylor :: interest :: tail) =
      [borrowRateStatement, reserveBytes 32, taylor, interest] ++
        allocationBody marketBalancesAllocationCalls reserves tail := by
    simp [allocationBody, allocationStatement, marketBalancesAllocationCalls,
      borrowRateStatement, reserves, taylor, interest]
  have hb := hsplit (marketAccrualSourceBody.drop 3)
  change marketAccrualBody = _ at hb
  rw [hb]
  rfl

theorem marketInterestSourcePrefix {frame : Frame} {evm : State}
    {market : ByteArray} {rate elapsed : UInt256} (hcontract : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (marketValue market))
    (hr : frame.locals.get? "borrowRate" = some (uint256Value rate))
    (he : frame.locals.get? "elapsed" = some (uint256Value elapsed))
    (hfit : marketInterestFits (calldataWord market 64) rate elapsed) :
    ABlock config evm frame (marketAccrualBody.drop 2)
      (marketInterestFrame frame (calldataWord market 64) rate elapsed)
      (marketAccrualBody.drop 4) := by
  rcases frame with ⟨c, locals, imms⟩
  cases hcontract
  constructor
  intro result htail
  rw [marketInterestStatements]
  apply ExecBlock.consNormal (taylorCall evm locals imms rate elapsed "__c3" _ _ hfit.1
    (by simp only [evalExpr?, hr, EvalResult.ofOption])
    (by simp only [evalExpr?, he, EvalResult.ofOption]))
  apply ExecBlock.consNormal (wadMulCall evm _ imms (calldataWord market 64)
    (taylorSum (UInt256.mul rate elapsed)) "interest" _ _ hfit.2 ?_
    (by simp only [evalExpr?, marketTaylorFrame, store_get_self, EvalResult.ofOption])) htail
  apply marketFieldSource (out := market) ?_ rfl
  rw [marketTaylorFrame, store_get_ne _ _ (by decide)]
  exact hm

theorem marketInterestSourceReverts {frame : Frame} {evm : State}
    {market : ByteArray} {rate elapsed : UInt256} (hcontract : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (marketValue market))
    (hr : frame.locals.get? "borrowRate" = some (uint256Value rate))
    (he : frame.locals.get? "elapsed" = some (uint256Value elapsed))
    (hbad : ¬ marketInterestFits (calldataWord market 64) rate elapsed) :
    ExecBlock config frame evm (marketAccrualBody.drop 2) .reverted := by
  rcases frame with ⟨c, locals, imms⟩
  cases hcontract
  rw [marketInterestStatements]
  by_cases ht : taylorFits rate elapsed
  · apply ExecBlock.consNormal (taylorCall evm locals imms rate elapsed "__c3" _ _ ht
      (by simp only [evalExpr?, hr, EvalResult.ofOption])
      (by simp only [evalExpr?, he, EvalResult.ofOption]))
    apply ExecBlock.consRevert (wadMulCallReverts evm _ imms (calldataWord market 64)
      (taylorSum (UInt256.mul rate elapsed)) "interest" _ _
      (Nat.le_of_not_lt (fun hp ↦ hbad ⟨ht, hp⟩)) ?_
      (by simp only [evalExpr?, store_get_self, EvalResult.ofOption]))
    apply marketFieldSource (out := market) ?_ rfl
    rw [store_get_ne _ _ (by decide)]
    exact hm
  · exact ExecBlock.consRevert (taylorCallReverts evm locals imms rate elapsed "__c3" _ _ ht
      (by simp only [evalExpr?, hr, EvalResult.ofOption])
      (by simp only [evalExpr?, he, EvalResult.ofOption]))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
