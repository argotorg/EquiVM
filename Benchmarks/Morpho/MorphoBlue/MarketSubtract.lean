import Benchmarks.Morpho.MorphoBlue.Uint128Subtraction
import Benchmarks.Morpho.MorphoBlue.AccrueSourceMath

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoMarketSubtractAssign (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (i : Fin 6) (name : Ident) (amount : UInt256) (hl : MarketLocals p locals)
    (hi : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var name) = .ok (.int (Int.ofNat amount.toNat)))
    (hfit : amount.toNat ≤ (marketFieldWord evm.accountMap evm.executionEnv p.id i).toNat) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.assign .storage ⟨"market", [.mindex (.var "id"), .field (marketFieldName i)]⟩
        (.inRange (.uint ⟨128, by decide⟩) (.binary .sub
          (.storage ⟨"market", [.mindex (.var "id"), .field (marketFieldName i)]⟩) (.var name))))
      (.ok { contract := contract, locals := locals, immutables := imms }
        (storeMarketField evm p.id i (UInt256.sub (marketFieldWord evm.accountMap evm.executionEnv p.id i) amount))) := by
  have hb : (marketFieldWord evm.accountMap evm.executionEnv p.id i).toNat < 2 ^ 128 := halfWord_bound _ _
  apply ExecStmt.assign (evalCheckedUint128SubOk (hl.evalField imms evm i) hi hb hfit)
  apply assignMarketField evm locals imms (.var "id") p.id i _ _ hl.market (hl.evalId imms evm)
  rw [usub_toNat hfit]
  omega

theorem morphoMarketSubtractAssignReverts (p : MarketParamsWords) (locals imms : Store) (evm : EVM.State)
    (i : Fin 6) (name : Ident) (amount : UInt256) (hl : MarketLocals p locals)
    (hi : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var name) = .ok (.int (Int.ofNat amount.toNat)))
    (hunder : (marketFieldWord evm.accountMap evm.executionEnv p.id i).toNat < amount.toNat) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.assign .storage ⟨"market", [.mindex (.var "id"), .field (marketFieldName i)]⟩
        (.inRange (.uint ⟨128, by decide⟩) (.binary .sub
          (.storage ⟨"market", [.mindex (.var "id"), .field (marketFieldName i)]⟩) (.var name)))) .reverted :=
  ExecStmt.assignExprRevert (evalCheckedUint128SubReverts (hl.evalField imms evm i) hi hunder)

end Benchmarks.Morpho.MorphoBlue
