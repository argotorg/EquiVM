import Benchmarks.Morpho.MorphoBlue.OraclePriceABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- A typed oracle call preserves the same opaque external-call witness in each caller.
theorem oraclePriceSourceOk {frame : Frame} {evm evm' : EVM.State} {target : Expr}
    {oracle : AccountAddress} (retVar : Ident) (out : ByteArray)
    (ht : evalExpr? config frame evm target = .ok (.address oracle))
    (hcall : typedCallViaEVM config evm oracle "price" 0 [] (true, evm', out) false)
    (hlen : 32 ≤ out.size) (hout : out.size < 2 ^ 138) :
    ExecStmt config frame evm (.externalCall target "price" (.intLit 0) [] retVar false)
      (.ok { frame with locals := frame.locals.insert retVar (.int (Int.ofNat (calldataWord out 0).toNat)) } evm') := by
  have htarget : EVM.address oracle.val = oracle := by apply Fin.ext; exact Nat.mod_eq_of_lt oracle.isLt
  rw [← htarget] at hcall
  exact ExecStmt.externalCallSuccess (value := [.int (Int.ofNat (calldataWord out 0).toNat)])
    ht (by simp only [evalExpr?, pure]) rfl hcall (decodeOraclePrice_word hlen (by omega))

theorem oraclePriceSourceReverts {frame : Frame} {evm evm' : EVM.State} {target : Expr}
    {oracle : AccountAddress} (retVar : Ident) (z : Bool) (out : ByteArray)
    (ht : evalExpr? config frame evm target = .ok (.address oracle))
    (hcall : typedCallViaEVM config evm oracle "price" 0 [] (z, evm', out) false)
    (hbad : ¬ (z = true ∧ 32 ≤ out.size)) :
    ExecStmt config frame evm (.externalCall target "price" (.intLit 0) [] retVar false) .reverted := by
  have htarget : EVM.address oracle.val = oracle := by apply Fin.ext; exact Nat.mod_eq_of_lt oracle.isLt
  rw [← htarget] at hcall
  cases z
  · exact ExecStmt.externalCallFailure ht (by simp only [evalExpr?, pure]) rfl hcall
  · exact ExecStmt.externalCallReturnDecodeRevert ht (by simp only [evalExpr?, pure]) rfl hcall
      (decodeOraclePrice_short (by simp only [true_and] at hbad; omega))

end Benchmarks.Morpho.MorphoBlue
