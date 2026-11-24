import Benchmarks.CurveVault.Common
import Benchmarks.CurveVault.Arithmetic
import Benchmarks.CurveVault.RuntimeBlocks_025
import Benchmarks.CurveVault.RuntimeBlocks_026

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultCeilDivFunction : FunctionDecl := contract.functions[27]!

def vaultCeilDivWord (x y : UInt256) : UInt256 :=
  if x = ⟨0⟩ then ⟨0⟩ else UInt256.div (UInt256.sub x ⟨1⟩) y + ⟨1⟩

theorem vaultCeilDivSource {evm : EVM.State} {locals : Store} {x y : UInt256}
    (hx : locals.get? "x" = some (.int (Int.ofNat x.toNat)))
    (hy : locals.get? "y" = some (.int (Int.ofNat y.toNat))) (hy0 : y ≠ ⟨0⟩) :
    ExecFuncBody fork config {contract := contract, locals := locals} evm vaultCeilDivFunction.body
      (.returned {contract := contract, locals := locals} evm
        (some [.int (Int.ofNat (vaultCeilDivWord x y).toNat)])) := by
  have hevalX := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) hx
  have hevalY := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) hy
  have hzero : evalExpr? config {contract := contract, locals := locals} evm (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hone : evalExpr? config {contract := contract, locals := locals} evm (.intLit 1) =
      .ok (.int (Int.ofNat (⟨1⟩ : UInt256).toNat)) := by simp [evalExpr?, pure]; rfl
  have hyNat := intOfNat_toNat_ne_zero_of_u256_ne_zero y hy0
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_ne_int_true hevalY hzero hyNat))
  apply ExecBlock.consReturn
  apply ExecStmt.return
  apply evalExprs?_singleton
  by_cases hx0 : x = ⟨0⟩
  · simp only [vaultCeilDivWord, hx0, if_true]
    exact evalExpr_ite_true (evalExpr_eq_int_true hevalX hzero (by rw [hx0]; rfl)) hzero
  · have hxNat := intOfNat_toNat_ne_zero_of_u256_ne_zero x hx0
    change (x.toNat : Int) ≠ 0 at hxNat
    have hpos : (⟨1⟩ : UInt256).toNat ≤ x.toNat := by change 1 ≤ x.toNat; omega
    have hpred := evalExpr_checkedSub256_ok hevalX hone rfl hpos
    have hdiv := evalExpr_div_uint256_ok hpred hevalY hy0 rfl
    have hquot := evalExpr_ite_false (thenExpr := .intLit 0) (evalExpr_eq_int_false hevalY hzero hyNat) hdiv
    have hresult := evalExpr_castAdd256 hquot hone
    simp only [vaultCeilDivWord, hx0, if_false]
    exact evalExpr_ite_false (evalExpr_eq_int_false hevalX hzero hxNat) hresult

theorem vaultCeilDivSourceRevert {evm : EVM.State} {locals : Store}
    (hy : locals.get? "y" = some (.int 0)) :
    ExecFuncBody fork config {contract := contract, locals := locals} evm vaultCeilDivFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  exact evalExpr_ne_int_false (evalExpr_varInt hy) (by simp [evalExpr?, pure]) rfl

theorem vaultCeilDivReach {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {dest returnPc x y : UInt256} {R : List UInt256}
    (hx : memLoad (UInt256.ofNat 64) mem = x)
    (hy : memLoad (UInt256.ofNat 96) mem = y) (hy0 : y ≠ ⟨0⟩)
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 6946) (dest :: returnPc :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 returnPc R
      ((vaultCeilDivWord x y).toByteArray.write 0 mem dest.toNat 32) aw' rdata σ k' C' := by
  have rd7066 := vaultBlocks.vault_block_6946_taken
    (by simp only [List.length_cons]; omega) (by rw [hy]; exact hy0) (by native_decide) h
  by_cases hx0 : x = ⟨0⟩
  · have rd7074 := vaultBlocks.vault_block_7066_fallthrough
      (by simp only [List.length_cons]; omega) (by rw [hx, hx0]; rfl) rd7066
    have rd7103 := vaultBlocks.vault_block_7074
      (by simp only [List.length_cons]; omega) (by native_decide) rd7074
    have rdRet := vaultBlocks.vault_block_7103 (by omega) hvalid rd7103
    rw [vaultCeilDivWord, if_pos hx0]
    exact ⟨_, _, _, rdRet⟩
  · have hpos : (UInt256.ofNat 1).toNat ≤ x.toNat := by
      change 1 ≤ x.toNat
      have hn : x.toNat ≠ 0 := fun hz => hx0 (uint256_toNat_eq_zero hz)
      omega
    have rd7079 := vaultBlocks.vault_block_7066_taken
      (by simp only [List.length_cons]; omega) (by rw [hx]; exact hx0) (by native_decide) rd7066
    have rd7099 := vaultBlocks.vault_block_7079_fallthrough
      (by simp only [List.length_cons]; omega)
      (by rw [hx]; exact ugt_zero (by rw [usub_toNat hpos]; omega)) rd7079
    have rd7103 := vaultBlocks.vault_block_7099
      (by simp only [List.length_cons]; omega) rd7099
    have rdRet := vaultBlocks.vault_block_7103 (by omega) hvalid rd7103
    change RD fork vaultBytecode I g s0 returnPc R
      ((UInt256.div (UInt256.sub (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 1))
        (memLoad (UInt256.ofNat 96) mem) + UInt256.ofNat 1).toByteArray.write 0 mem dest.toNat 32)
      _ rdata σ _ _ at rdRet
    rw [hx, hy] at rdRet
    rw [vaultCeilDivWord, if_neg hx0]
    exact ⟨_, _, _, rdRet⟩

theorem vaultCeilDivReachRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (hy : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) (hstack : R.length + 8 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 6946) R mem aw rdata σ k C) :
    RDrev fork vaultBytecode g s0 := by
  have rd6954 := vaultBlocks.vault_block_6946_fallthrough (by omega) hy h
  exact vaultBlocks.vault_block_6954 hstack rd6954
end Benchmarks.CurveVault
