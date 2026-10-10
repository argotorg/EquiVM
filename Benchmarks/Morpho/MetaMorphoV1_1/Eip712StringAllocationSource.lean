import Benchmarks.Morpho.MetaMorphoV1_1.Eip712StringSource

/-! Allocation checks after evaluating either EIP-712 domain string. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

set_option maxRecDepth 2000

def domainStringSize (word : UInt256) (bytes : ByteArray) : UInt256 :=
  if word = ⟨255⟩ then UInt256.ofNat (bytes.size + 32) else ⟨64⟩

theorem domainStringSizeSource (evm : State) (v : MetaMorphoV1_1Immutables)
    (locals : Store) (value : Ident) (bytes : ByteArray)
    (hvalue : locals.get? value = some (.bytes bytes)) (hsize : bytes.size + 32 < UInt256.size) :
    evalExpr? config (domainFrame v locals) evm
      (.binary .add (.arrayLength .localVar ⟨value, []⟩) (.intLit 32)) =
      .ok (uint256Value (UInt256.ofNat (bytes.size + 32))) := by
  have hl : evalExpr? config (domainFrame v locals) evm
      (.arrayLength .localVar ⟨value, []⟩) = .ok (.int (Int.ofNat bytes.size)) := by
    simp only [evalExpr?, domainFrame, hvalue, readLocalPath?, bind, EvalResult.bind, pure]
  have hr : evalExpr? config (domainFrame v locals) evm (.intLit 32) =
      .ok (.int (Int.ofNat 32)) := by simp only [evalExpr?, pure]; rfl
  simpa only [uint256Value, UInt256.toNat_ofNat_of_lt hsize] using naturalAddSource hl hr

theorem domainStringAllocationReturns (evm : State) (v : MetaMorphoV1_1Immutables)
    (version : Bool) (locals : Store) (cursor : Expr) (free : UInt256)
    (value ret : Ident) (bytes : ByteArray)
    (hcursor : evalExpr? config (domainFrame v locals) evm cursor = .ok (uint256Value free))
    (hvalue : locals.get? value = some (.bytes bytes)) (hsize : bytes.size + 32 < UInt256.size)
    (hfit : allocationFits free (domainStringSize (domainStringImmutable v version) bytes)) :
    ExecStmt config (domainFrame v locals) evm (domainStringAllocation version cursor value ret)
      (.ok (domainFrame v (locals.insert ret (uint256Value
        (nextCursor free (domainStringSize (domainStringImmutable v version) bytes))))) evm) := by
  have hc := evalExpr_wordEq (domainStringImmutableSource evm v version locals)
    (show evalExpr? config (domainFrame v locals) evm (.intLit 255) =
      .ok (uint256Value ⟨255⟩) by simp only [evalExpr?, pure]; rfl)
  by_cases hf : domainStringImmutable v version = ⟨255⟩
  · simp only [domainStringSize, if_pos hf] at hfit ⊢
    apply ExecStmt.iteTrue (by simpa only [hf, decide_true] using hc)
    exact ExecBlock.consNormal (allocateCallReturns ret rfl hcursor
      (domainStringSizeSource evm v locals value bytes hvalue hsize) hfit) ExecBlock.nil
  · simp only [domainStringSize, if_neg hf] at hfit ⊢
    apply ExecStmt.iteFalse (by simpa only [hf, decide_false] using hc)
    exact ExecBlock.consNormal (allocateCallReturns ret rfl hcursor
      (by simp only [evalExpr?, pure]; rfl) hfit) ExecBlock.nil

theorem domainStringAllocationReverts (evm : State) (v : MetaMorphoV1_1Immutables)
    (version : Bool) (locals : Store) (cursor : Expr) (free : UInt256)
    (value ret : Ident) (bytes : ByteArray)
    (hcursor : evalExpr? config (domainFrame v locals) evm cursor = .ok (uint256Value free))
    (hvalue : locals.get? value = some (.bytes bytes)) (hsize : bytes.size + 32 < UInt256.size)
    (hbad : ¬ allocationFits free (domainStringSize (domainStringImmutable v version) bytes)) :
    ExecStmt config (domainFrame v locals) evm
      (domainStringAllocation version cursor value ret) .reverted := by
  have hc := evalExpr_wordEq (domainStringImmutableSource evm v version locals)
    (show evalExpr? config (domainFrame v locals) evm (.intLit 255) =
      .ok (uint256Value ⟨255⟩) by simp only [evalExpr?, pure]; rfl)
  by_cases hf : domainStringImmutable v version = ⟨255⟩
  · simp only [domainStringSize, if_pos hf] at hbad
    apply ExecStmt.iteTrue (by simpa only [hf, decide_true] using hc)
    exact ExecBlock.consRevert (allocateCallReverts ret rfl hcursor
      (domainStringSizeSource evm v locals value bytes hvalue hsize) hbad)
  · simp only [domainStringSize, if_neg hf] at hbad
    apply ExecStmt.iteFalse (by simpa only [hf, decide_false] using hc)
    exact ExecBlock.consRevert (allocateCallReverts ret rfl hcursor
      (by simp only [evalExpr?, pure]; rfl) hbad)

end Benchmarks.Morpho.MetaMorphoV1_1
