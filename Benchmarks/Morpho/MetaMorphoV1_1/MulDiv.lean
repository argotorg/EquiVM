import Benchmarks.Morpho.MetaMorphoV1_1.Arithmetic

/-! Source proofs for Morpho's checked multiplication and rounded division. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

def mulDivDownFunction : FunctionDecl := contract.functions[76]!

def mulDivUpFunction : FunctionDecl := contract.functions[82]!

def mulDivFrame (imms : Store) (a b d : UInt256) : Frame :=
  { contract := contract
    locals := (((∅ : Store).insert "d" (uint256Value d)).insert "y" (uint256Value b)).insert
      "x" (uint256Value a)
    immutables := imms }

theorem mulDivFrame_x (evm : EVM.State) (imms : Store) (a b d : UInt256) :
    evalExpr? config (mulDivFrame imms a b d) evm (.var "x") = .ok (uint256Value a) := by
  simp only [evalExpr?, mulDivFrame, store_get_self, EvalResult.ofOption]

theorem mulDivFrame_y (evm : EVM.State) (imms : Store) (a b d : UInt256) :
    evalExpr? config (mulDivFrame imms a b d) evm (.var "y") = .ok (uint256Value b) := by
  simp only [evalExpr?, mulDivFrame,
    store_get_ne _ _ (show ("x" == "y") = false from by decide),
    store_get_self, EvalResult.ofOption]

theorem mulDivFrame_d (evm : EVM.State) (imms : Store) (a b d : UInt256) :
    evalExpr? config (mulDivFrame imms a b d) evm (.var "d") = .ok (uint256Value d) := by
  simp only [evalExpr?, mulDivFrame,
    store_get_ne _ _ (show ("x" == "d") = false from by decide),
    store_get_ne _ _ (show ("y" == "d") = false from by decide),
    store_get_self, EvalResult.ofOption]

theorem mulDivDownBody (evm : EVM.State) (imms : Store) (a b d : UInt256)
    (hprod : a.toNat * b.toNat < UInt256.size) (hden : d ≠ ⟨0⟩) :
    ExecFuncBody config (mulDivFrame imms a b d) evm mulDivDownFunction.body
      (.returned (mulDivFrame imms a b d) evm
        (some [uint256Value (UInt256.div (UInt256.mul a b) d)])) := by
  exact ExecFuncBody.execBlockRet (ABlock.start.returns (divSourceOk
    (checkedMulSourceOk (mulDivFrame_x evm imms a b d) (mulDivFrame_y evm imms a b d) hprod)
    (mulDivFrame_d evm imms a b d) hden))

theorem mulDivDownBodyReverts (evm : EVM.State) (imms : Store) (a b d : UInt256)
    (hfail : ¬ (a.toNat * b.toNat < UInt256.size ∧ d ≠ ⟨0⟩)) :
    ExecFuncBody config (mulDivFrame imms a b d) evm mulDivDownFunction.body .reverted := by
  apply scalarReturnReverts
  by_cases hprod : a.toNat * b.toNat < UInt256.size
  · have hd : d = ⟨0⟩ := Classical.not_not.mp (fun hn ↦ hfail ⟨hprod, hn⟩)
    subst d
    exact divSourceZero
      (checkedMulSourceOk (mulDivFrame_x evm imms a b ⟨0⟩)
        (mulDivFrame_y evm imms a b ⟨0⟩) hprod)
      (mulDivFrame_d evm imms a b ⟨0⟩)
  · exact binarySourceRevertLeft (by decide) (by decide)
      (checkedMulSourceOverflow (mulDivFrame_x evm imms a b d) (mulDivFrame_y evm imms a b d)
        (Nat.le_of_not_gt hprod))

def mulDivUpFits (a b d : UInt256) : Prop :=
  a.toNat * b.toNat < UInt256.size ∧ d ≠ ⟨0⟩ ∧
    (UInt256.mul a b).toNat + (UInt256.sub d ⟨1⟩).toNat < UInt256.size

def mulDivUpWord (a b d : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul a b + UInt256.sub d ⟨1⟩) d

theorem mulDivUpBody (evm : EVM.State) (imms : Store) (a b d : UInt256)
    (hfit : mulDivUpFits a b d) :
    ExecFuncBody config (mulDivFrame imms a b d) evm mulDivUpFunction.body
      (.returned (mulDivFrame imms a b d) evm (some [uint256Value (mulDivUpWord a b d)])) := by
  have hden : (⟨1⟩ : UInt256).toNat ≤ d.toNat := by
    change 1 ≤ d.toNat
    exact Nat.pos_of_ne_zero (fun hz ↦ hfit.2.1 (uint256_toNat_eq_zero hz))
  exact ExecFuncBody.execBlockRet (ABlock.start.returns (divSourceOk
    (checkedAddSourceOk
      (checkedMulSourceOk (mulDivFrame_x evm imms a b d) (mulDivFrame_y evm imms a b d) hfit.1)
      (evalExpr_uint256_sub (mulDivFrame_d evm imms a b d)
        (by simp only [evalExpr?, uint256Value, pure]; rfl) hden) hfit.2.2)
    (mulDivFrame_d evm imms a b d) hfit.2.1))

theorem mulDivUpBodyReverts (evm : EVM.State) (imms : Store) (a b d : UInt256)
    (hfail : ¬ mulDivUpFits a b d) :
    ExecFuncBody config (mulDivFrame imms a b d) evm mulDivUpFunction.body .reverted := by
  apply scalarReturnReverts
  apply binarySourceRevertLeft (by decide) (by decide)
  by_cases hprod : a.toNat * b.toNat < UInt256.size
  · have hm := checkedMulSourceOk (mulDivFrame_x evm imms a b d)
      (mulDivFrame_y evm imms a b d) hprod
    by_cases hd : d = ⟨0⟩
    · apply rangeSourceRevert
      apply binarySourceRevertRight (by decide) (by decide) hm
      apply checkedSubSourceUnderflow (b := ⟨1⟩) (mulDivFrame_d evm imms a b d)
        (by simp only [evalExpr?, uint256Value, pure]; rfl)
      rw [hd]
      decide
    · have hden : (⟨1⟩ : UInt256).toNat ≤ d.toNat := by
        change 1 ≤ d.toNat
        exact Nat.pos_of_ne_zero (fun hz ↦ hd (uint256_toNat_eq_zero hz))
      have hover : UInt256.size ≤ (UInt256.mul a b).toNat + (UInt256.sub d ⟨1⟩).toNat := by
        exact Nat.le_of_not_gt (fun hsum ↦ hfail ⟨hprod, hd, hsum⟩)
      exact checkedAddSourceOverflow hm
        (evalExpr_uint256_sub (mulDivFrame_d evm imms a b d)
          (by simp only [evalExpr?, uint256Value, pure]; rfl) hden) hover
  · exact rangeSourceRevert (binarySourceRevertLeft (by decide) (by decide)
      (checkedMulSourceOverflow (mulDivFrame_x evm imms a b d) (mulDivFrame_y evm imms a b d)
        (Nat.le_of_not_gt hprod)))

theorem mulDivUpCall (evm : EVM.State) (locals imms : Store) (a b d : UInt256)
    (retVar : Ident) (lhs rhs den : Expr) (hfit : mulDivUpFits a b d)
    (ha : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm lhs = .ok (uint256Value a))
    (hb : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm rhs = .ok (uint256Value b))
    (hd : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm den = .ok (uint256Value d)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MathLib_mulDivUp" [lhs, rhs, den] retVar)
      (.ok
        { contract := contract
          locals := locals.insert retVar (uint256Value (mulDivUpWord a b d))
          immutables := imms } evm) := by
  exact internalCallFunctionReturn
    (caller := { contract := contract, locals := locals, immutables := imms })
    (callee := mulDivUpFunction) (value := some [uint256Value (mulDivUpWord a b d)])
    (argVals := [uint256Value a, uint256Value b, uint256Value d])
    (by simp [evalExprs?, ha, hb, hd, bind, EvalResult.bind, pure]) rfl rfl
    (mulDivUpBody evm imms a b d hfit)

theorem mulDivUpCallReverts (evm : EVM.State) (locals imms : Store) (a b d : UInt256)
    (retVar : Ident) (lhs rhs den : Expr) (hfail : ¬ mulDivUpFits a b d)
    (ha : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm lhs = .ok (uint256Value a))
    (hb : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm rhs = .ok (uint256Value b))
    (hd : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm den = .ok (uint256Value d)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "MathLib_mulDivUp" [lhs, rhs, den] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := mulDivUpFunction)
    (argVals := [uint256Value a, uint256Value b, uint256Value d])
    (by simp [evalExprs?, ha, hb, hd, bind, EvalResult.bind, pure]) rfl rfl
    (mulDivUpBodyReverts evm imms a b d hfail)


end Benchmarks.Morpho.MetaMorphoV1_1
