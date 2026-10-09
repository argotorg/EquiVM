import Benchmarks.Morpho.MorphoBlue.AccrueSourceCall
import Benchmarks.Morpho.MorphoBlue.WadSource
import Benchmarks.Morpho.MorphoBlue.Uint128Arithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def accrueTaylorLocals (locals : Store) (rate elapsed : UInt256) : Store :=
  locals.insert "__c1" (.int (Int.ofNat (taylorWord rate elapsed).toNat))

def accrueCalcLocals (locals : Store) (rate elapsed assets : UInt256) : Store :=
  (accrueTaylorLocals locals rate elapsed).insert "interest"
    (.int (Int.ofNat (wMulDownResult assets (taylorWord rate elapsed)).toNat))

theorem morphoAccrueTaylorStep (locals imms : Store) (rate elapsed : UInt256) (evm : EVM.State)
    (hr : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "borrowRate") = .ok (.int (Int.ofNat rate.toNat)))
    (he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "elapsed") = .ok (.int (Int.ofNat elapsed.toNat))) (hfit : TaylorFits rate elapsed) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm accrueIrmBody[3]!
      (.ok { contract := contract, locals := accrueTaylorLocals locals rate elapsed, immutables := imms } evm) :=
  morphoTaylorCallOk rate elapsed evm locals imms _ _ _ hr he hfit

theorem morphoAccrueTaylorReverts (locals imms : Store) (rate elapsed : UInt256) (evm : EVM.State)
    (hr : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "borrowRate") = .ok (.int (Int.ofNat rate.toNat)))
    (he : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "elapsed") = .ok (.int (Int.ofNat elapsed.toNat))) (hbad : ¬ TaylorFits rate elapsed) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm accrueIrmBody[3]! .reverted :=
  morphoTaylorCallReverts rate elapsed evm locals imms _ _ _ hr he hbad

theorem accrueTaylorLocals_market (p : MarketParamsWords) (locals : Store) (rate elapsed : UInt256)
    (h : MarketLocals p locals) : MarketLocals p (accrueTaylorLocals locals rate elapsed) :=
  h.insert "__c1" _ (by decide)

theorem accrueTaylorLocals_eval (locals imms : Store) (rate elapsed : UInt256) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := accrueTaylorLocals locals rate elapsed, immutables := imms }
      evm (.var "__c1") = .ok (.int (Int.ofNat (taylorWord rate elapsed).toNat)) := by
  simp only [evalExpr?, accrueTaylorLocals, store_get_self, EvalResult.ofOption]

theorem morphoAccrueInterestStep (p : MarketParamsWords) (locals imms : Store) (rate elapsed : UInt256)
    (evm : EVM.State) (hl : MarketLocals p locals)
    (hfit : (marketFieldWord evm.accountMap evm.executionEnv p.id 2).toNat *
      (taylorWord rate elapsed).toNat < UInt256.size) :
    ExecStmt config { contract := contract, locals := accrueTaylorLocals locals rate elapsed, immutables := imms }
      evm accrueIrmBody[4]!
      (.ok { contract := contract, locals := (accrueCalcLocals locals rate elapsed
        (marketFieldWord evm.accountMap evm.executionEnv p.id 2)), immutables := imms } evm) :=
  morphoWMulDownCallOk _ _ evm _ imms _ _ _
    ((accrueTaylorLocals_market p locals rate elapsed hl).evalField imms evm ⟨2, by decide⟩)
    (accrueTaylorLocals_eval locals imms rate elapsed evm) hfit

theorem morphoAccrueInterestReverts (p : MarketParamsWords) (locals imms : Store) (rate elapsed : UInt256)
    (evm : EVM.State) (hl : MarketLocals p locals)
    (hover : UInt256.size ≤ (marketFieldWord evm.accountMap evm.executionEnv p.id 2).toNat *
      (taylorWord rate elapsed).toNat) :
    ExecStmt config { contract := contract, locals := accrueTaylorLocals locals rate elapsed, immutables := imms }
      evm accrueIrmBody[4]! .reverted :=
  morphoWMulDownCallReverts _ _ evm _ imms _ _ _
    ((accrueTaylorLocals_market p locals rate elapsed hl).evalField imms evm ⟨2, by decide⟩)
    (accrueTaylorLocals_eval locals imms rate elapsed evm) hover

theorem accrueCalcLocals_market (p : MarketParamsWords) (locals : Store) (rate elapsed assets : UInt256)
    (h : MarketLocals p locals) : MarketLocals p (accrueCalcLocals locals rate elapsed assets) :=
  (accrueTaylorLocals_market p locals rate elapsed h).insert "interest" _ (by decide)

theorem accrueCalcLocals_eval (locals imms : Store) (rate elapsed assets : UInt256) (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := accrueCalcLocals locals rate elapsed assets, immutables := imms }
      evm (.var "interest") = .ok (.int (Int.ofNat (wMulDownResult assets (taylorWord rate elapsed)).toNat)) := by
  simp only [evalExpr?, accrueCalcLocals, store_get_self, EvalResult.ofOption]

-- Both asset additions use the same checked uint128 operation, but the second reloads storage.
theorem morphoAccrueAssetsAssign (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (i : Fin 6) (name : Ident) (interest : UInt256) (hl : MarketLocals p locals)
    (hi : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var name) = .ok (.int (Int.ofNat interest.toNat)))
    (hfit : (marketFieldWord evm.accountMap evm.executionEnv p.id i).toNat + interest.toNat < 2 ^ 128) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.assign .storage ⟨"market", [.mindex (.var "id"), .field (marketFieldName i)]⟩
        (.inRange (.uint ⟨128, by decide⟩) (.binary .add
          (.storage ⟨"market", [.mindex (.var "id"), .field (marketFieldName i)]⟩) (.var name))))
      (.ok { contract := contract, locals := locals, immutables := imms }
        (storeMarketField evm p.id i (marketFieldWord evm.accountMap evm.executionEnv p.id i + interest))) := by
  apply ExecStmt.assign (evalCheckedUint128AddOk (hl.evalField imms evm i) hi hfit)
  apply assignMarketField evm locals imms (.var "id") p.id i _ _ hl.market (hl.evalId imms evm)
  rw [uadd_toNat, Nat.mod_eq_of_lt (show
    (marketFieldWord evm.accountMap evm.executionEnv p.id i).toNat + interest.toNat < UInt256.size by
      change _ < 2 ^ 256; omega)]
  exact hfit

theorem morphoAccrueAssetsAssignReverts (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (i : Fin 6) (name : Ident) (interest : UInt256) (hl : MarketLocals p locals)
    (hi : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var name) = .ok (.int (Int.ofNat interest.toNat)))
    (hover : 2 ^ 128 ≤ (marketFieldWord evm.accountMap evm.executionEnv p.id i).toNat + interest.toNat) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.assign .storage ⟨"market", [.mindex (.var "id"), .field (marketFieldName i)]⟩
        (.inRange (.uint ⟨128, by decide⟩) (.binary .add
          (.storage ⟨"market", [.mindex (.var "id"), .field (marketFieldName i)]⟩) (.var name)))) .reverted :=
  ExecStmt.assignExprRevert (evalCheckedUint128AddReverts (hl.evalField imms evm i) hi hover)

end Benchmarks.Morpho.MorphoBlue
