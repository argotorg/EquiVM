import Benchmarks.Morpho.MetaMorphoV1_1.BodyCommon

/-! The internal timelock range check, shared by submission and construction. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

abbrev timelockBoundsFunction : FunctionDecl := contract.functions[1]!

abbrev timelockInBounds (value : UInt256) : Prop :=
  value.toNat ≤ 1209600 ∧ 86400 ≤ value.toNat

def timelockBoundsFrame (imms : Store) (value : UInt256) : Frame :=
  ⟨contract, (∅ : Store).insert "newTimelock" (uint256Value value), imms⟩

theorem timelockUpperSource (evm : EVM.State) (imms : Store) (value : UInt256) :
    evalExpr? config (timelockBoundsFrame imms value) evm
      (.binary .le (.var "newTimelock") (.intLit 1209600)) =
      .ok (.bool (decide (value.toNat ≤ 1209600))) := by
  apply naturalLeSource
  · simp only [evalExpr?, timelockBoundsFrame, store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, pure]
    rfl

theorem timelockLowerSource (evm : EVM.State) (imms : Store) (value : UInt256) :
    evalExpr? config (timelockBoundsFrame imms value) evm
      (.binary .ge (.var "newTimelock") (.intLit 86400)) =
      .ok (.bool (decide (86400 ≤ value.toNat))) := by
  apply naturalGeSource
  · simp only [evalExpr?, timelockBoundsFrame, store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, pure]
    rfl

theorem timelockBoundsBody (evm : EVM.State) (imms : Store) (value : UInt256)
    (hgood : timelockInBounds value) :
    ExecFuncBody config (timelockBoundsFrame imms value) evm timelockBoundsFunction.body
      (.returned (timelockBoundsFrame imms value) evm none) := by
  apply ExecFuncBody.execBlockOK
  apply ((ABlock.start.requireStep (by
    simp only [timelockUpperSource, hgood.1, decide_true])).requireStep (by
      simp only [timelockLowerSource, hgood.2, decide_true])).run
  exact ExecBlock.nil

theorem timelockBoundsBodyReverts (evm : EVM.State) (imms : Store) (value : UInt256)
    (hbad : ¬ timelockInBounds value) :
    ExecFuncBody config (timelockBoundsFrame imms value) evm timelockBoundsFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  by_cases hhi : value.toNat ≤ 1209600
  · apply (ABlock.start.requireStep (by
      simp only [timelockUpperSource, hhi, decide_true])).requireRevert
    have hlo : ¬ 86400 ≤ value.toNat := fun hlo ↦ hbad ⟨hhi, hlo⟩
    simp only [timelockLowerSource, hlo, decide_false]
  · exact ABlock.start.requireRevert (by simp only [timelockUpperSource, hhi, decide_false])

theorem timelockBoundsCall (evm : EVM.State) (locals imms : Store) (value : UInt256)
    (arg : Expr) (retVar : Ident) (hgood : timelockInBounds value)
    (heval : evalExpr? config ⟨contract, locals, imms⟩ evm arg = .ok (uint256Value value)) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_checkTimelockBounds" [arg] retVar)
      (.ok ⟨contract, locals.insert retVar .unit, imms⟩ evm) := by
  exact internalCallFunctionReturn (caller := ⟨contract, locals, imms⟩)
    (callee := timelockBoundsFunction) (argVals := [uint256Value value]) (value := none)
    (by simp only [evalExprs?, heval, bind, EvalResult.bind, pure]) rfl rfl
    (timelockBoundsBody evm imms value hgood)

theorem timelockBoundsCallReverts (evm : EVM.State) (locals imms : Store) (value : UInt256)
    (arg : Expr) (retVar : Ident) (hbad : ¬ timelockInBounds value)
    (heval : evalExpr? config ⟨contract, locals, imms⟩ evm arg = .ok (uint256Value value)) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_checkTimelockBounds" [arg] retVar)
      .reverted := by
  exact internalCallFunctionRevert (callee := timelockBoundsFunction)
    (argVals := [uint256Value value])
    (by simp only [evalExprs?, heval, bind, EvalResult.bind, pure]) rfl rfl
    (timelockBoundsBodyReverts evm imms value hbad)

end Benchmarks.Morpho.MetaMorphoV1_1
