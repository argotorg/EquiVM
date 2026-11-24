import Benchmarks.CurveVault.MemoryActive
import Benchmarks.CurveVault.Arithmetic
import Benchmarks.CurveVault.RuntimeBlocks_002
import Benchmarks.CurveVault.RuntimeBlocks_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: the compiler's base-ten exponent guard bounds a finite table.
theorem u256_exp10_toNat (exponent : UInt256) (hbound : exponent.toNat ≤ 77) :
    (UInt256.exp ⟨10⟩ exponent).toNat = 10 ^ exponent.toNat := by
  have htable : ∀ n : Fin 78, (UInt256.exp ⟨10⟩ (UInt256.ofNat n.val)).toNat = 10 ^ n.val := by
    native_decide
  simpa only [u256_ofNat_toNat] using htable ⟨exponent.toNat, by omega⟩

-- LIBRARY CANDIDATE: checked exponentiation for nonnegative integer operands.
theorem evalExpr_checkedExp256_nat {cfg : Config} {contract : ContractDecl} {evm : State}
    {locals : Store} {base exponent : Expr} {a b : Nat}
    (ha : evalExpr? cfg {contract := contract, locals := locals} evm base = .ok (.int (Int.ofNat a)))
    (hb : evalExpr? cfg {contract := contract, locals := locals} evm exponent = .ok (.int (Int.ofNat b)))
    (hfit : a ^ b < UInt256.size) :
    evalExpr? cfg {contract := contract, locals := locals} evm
      (sourceCheckedUint256 (.binary .exp base exponent)) = .ok (.int (Int.ofNat (a ^ b))) := by
  apply uint256RangeSourceOk ?_ hfit
  rw [evalExpr_binary_nonshort (by decide +kernel) (by decide +kernel), ha, hb]
  simp only [EvalResult.bind, bind, evalBinaryOp?, Int.ofNat_eq_natCast,
    Int.toNat_natCast, Int.natCast_pow]
  rw [if_neg (Int.not_lt.mpr (Int.natCast_nonneg b))]

def vaultInitializePrecisionExpr : Expr :=
  sourceCheckedUint256 (.binary .exp (.intLit 10) (sourceCheckedSub256 (.intLit 18) (.var "__c0")))

theorem vaultInitializePrecision {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {decimals x1 x2 : UInt256} {R : List UInt256} {locals : Store}
    (hd : locals.get? "__c0" = some (.int (Int.ofNat decimals.toNat)))
    (haw : aw.toNat ≤ 10) (hstack : R.length + 4 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 294) (decimals :: x1 :: x2 :: R) mem aw rdata σ k C) :
    (decimals.toNat ≤ 18 ∧ ∃ aw' k' C', aw'.toNat ≤ 10 ∧
      ExecStmt fork config {contract := contract, locals := locals} evm initializeTransition.body[4]!
        (.ok {contract := contract, locals := (locals.insert "borrowed_precision"
          (.int (Int.ofNat (UInt256.exp ⟨10⟩ (UInt256.sub ⟨18⟩ decimals)).toNat)))} evm) ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat 327) (UInt256.sub ⟨18⟩ decimals :: R)
        (decimals.toByteArray.write 0 mem 288 32) aw' rdata σ k' C') ∨
    (ExecStmt fork config {contract := contract, locals := locals} evm initializeTransition.body[4]! .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  let prepared := decimals.toByteArray.write 0 mem 288 32
  have hmd : memLoad (UInt256.ofNat 288) prepared = decimals :=
    memLoad_write_back _ _ 288 (by decide +kernel) (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 288 (by omega)))
  have hevalD := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) hd
  have heval18 : evalExpr? config {contract := contract, locals := locals} evm (.intLit 18) =
      .ok (.int (Int.ofNat (⟨18⟩ : UInt256).toNat)) := by rw [evalExpr?]; rfl
  by_cases hsub : decimals.toNat ≤ 18
  swap
  · have hover : (⟨18⟩ : UInt256).toNat < decimals.toNat := by exact Nat.lt_of_not_ge hsub
    obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_294_taken_packed hstack
      (by
        change UInt256.gt (UInt256.sub ⟨18⟩ (memLoad (UInt256.ofNat 288) prepared)) ⟨18⟩ ≠ _
        rw [hmd, u256_sub_underflow_gt _ _ hover]; decide +kernel) (by native_decide) h
    have hrev := vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_294_taken_stack, List.length_cons]; omega) rdFail
    refine Or.inr ⟨ExecStmt.letDeclRevert ?_, hrev⟩
    change evalExpr? config {contract := contract, locals := locals} evm vaultInitializePrecisionExpr = .revert
    rw [vaultInitializePrecisionExpr, evalExpr?]
    rw [evalExpr_binary_nonshort (by decide +kernel) (by decide +kernel), evalExpr?]
    simp only [evalExpr_checkedSub256_revert heval18 hevalD hover, EvalResult.bind, bind]
  obtain ⟨k0, C0, rd317⟩ := RD.pack (vaultBlocks.vault_block_294_fallthrough hstack
    (by
      change UInt256.gt (UInt256.sub ⟨18⟩ (memLoad (UInt256.ofNat 288) prepared)) ⟨18⟩ = _
      rw [hmd]
      exact ugt_zero (by rw [usub_toNat hsub]; change 18 - decimals.toNat ≤ 18; omega)) h)
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 317)
    (UInt256.sub ⟨18⟩ (memLoad (UInt256.ofNat 288) prepared) :: memLoad (UInt256.ofNat 288) prepared :: R)
    prepared _ rdata σ k0 C0 at rd317
  rw [hmd] at rd317
  have hdiff : (UInt256.sub ⟨18⟩ decimals).toNat = 18 - decimals.toNat := usub_toNat hsub
  have hbound : (UInt256.sub ⟨18⟩ decimals).toNat ≤ 77 := by rw [hdiff]; omega
  obtain ⟨k1, C1, rd327⟩ := RD.pack (vaultBlocks.vault_block_317_fallthrough (by omega)
    (ugt_zero hbound) rd317)
  refine Or.inl ⟨hsub, _, k1, C1, memoryActive_le (memoryActive_le haw (by decide +kernel)) (by decide +kernel),
    ExecStmt.letDecl ?_, rd327⟩
  change evalExpr? config {contract := contract, locals := locals} evm vaultInitializePrecisionExpr = _
  rw [u256_exp10_toNat _ hbound]
  apply evalExpr_checkedExp256_nat (by rw [evalExpr?]; rfl) (evalExpr_checkedSub256_ok heval18 hevalD rfl hsub)
  exact lt_of_le_of_lt (pow_le_pow_right' (by decide +kernel : 1 ≤ (10 : Nat))
    (by rw [hdiff]; omega : (UInt256.sub ⟨18⟩ decimals).toNat ≤ 18)) (by decide +kernel)

end Benchmarks.CurveVault
