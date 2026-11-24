import Benchmarks.CurveVault.DebitAllowancePrepare
import Benchmarks.CurveVault.AllowanceSpend
import Benchmarks.CurveVault.DebitSource

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultDebitAllowanceRetVar (isWithdraw : Bool) : Ident := if isWithdraw then "__c2" else "__c0"

def vaultDebitAllowanceBody (isWithdraw : Bool) : List Stmt :=
  [.letDecl "allowance_" (some (.elem (.int (.uint ⟨256, by decide⟩))))
      (.storage {base := "allowance", steps := [.mindex (.var "_owner"), .mindex (.env .caller)]}),
    .ite (.binary .ne (.var "allowance_") (.intLit (UInt256.size - 1)))
      [.internalCall "_approve" [.var "_owner", .env .caller,
        sourceCheckedSub256 (.var "allowance_") (.var (vaultDebitSharesName isWithdraw))]
        (vaultDebitAllowanceRetVar isWithdraw)] []]

theorem vaultDebitAllowance (isWithdraw : Bool) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner shares : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : (if isWithdraw then 704 else 640) ≤ mem.size)
    (hmo : memLoad (UInt256.ofNat 608) mem = owner)
    (hmv : (vaultDebitAllowanceFlow isWithdraw).amount I mem = shares)
    (hcanon : owner.toNat < EVM.addressModulus)
    (hbase : locals.get? "allowance" = none)
    (ho : locals.get? "_owner" = some (.address (AccountAddress.ofNat owner.toNat)))
    (hv : locals.get? (vaultDebitSharesName isWithdraw) = some (.int (Int.ofNat shares.toNat)))
    (hperm : I.perm = true) (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat (if isWithdraw then 4431 else 5104)) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (mem' : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecBlock fork config {contract := contract, locals := locals} evm (vaultDebitAllowanceBody isWithdraw)
        (.ok {contract := contract, locals := locals'} evm') ∧
      SourceState s0 I σ' evm' ∧
      WordMemoryRange mem mem' 192 (vaultDebitAllowanceFlow isWithdraw).allowanceOffset ∧
      (∀ name, ("allowance_" == name) = false → ((vaultDebitAllowanceRetVar isWithdraw) == name) = false →
        locals'.get? name = locals.get? name) ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultDebitAllowanceFlow isWithdraw).next) R mem' aw' rdata σ' k' C') ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm (vaultDebitAllowanceBody isWithdraw) .reverted ∧
      RDrev fork vaultBytecode g s0) := by
  let old := codeOwnerStorageWord I σ (vaultAllowanceSlot (AccountAddress.ofNat owner.toNat) I.source)
  let locals0 := locals.insert "allowance_" (.int (Int.ofNat old.toNat))
  have hread := vaultAllowanceEvalAt evm locals (.var "_owner") (.env .caller)
    (AccountAddress.ofNat owner.toNat) I.source hbase
    (by rw [evalExpr?]; simp only [ho, EvalResult.ofOption])
    (by simp only [evalExpr?, envValue, hs.env, pure])
  rw [hs.storageRead] at hread
  have hlet : ExecStmt fork config {contract := contract, locals := locals} evm (vaultDebitAllowanceBody isWithdraw)[0]!
      (.ok {contract := contract, locals := locals0} evm) := ExecStmt.letDecl hread
  have ha0 : locals0.get? "allowance_" = some (.int (Int.ofNat old.toNat)) := store_get_self _ _ _
  have ho0 : locals0.get? "_owner" = some (.address (AccountAddress.ofNat owner.toNat)) := by
    rw [store_get_ne _ _ (by decide +kernel)]; exact ho
  have hv0 : locals0.get? (vaultDebitSharesName isWithdraw) = some (.int (Int.ofNat shares.toNat)) := by
    rw [store_get_ne _ _ (by cases isWithdraw <;> decide +kernel)]; exact hv
  have hevalOld := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) ha0
  have hevalMax : evalExpr? config {contract := contract, locals := locals0} evm (.intLit (UInt256.size - 1)) =
      .ok (.int (Int.ofNat (UInt256.ofNat (UInt256.size - 1)).toNat)) := by simp [evalExpr?, pure]; rfl
  obtain ⟨mem0, aw0, k0, C0, hsize0, hframe0, hma0, rdNext⟩ := vaultDebitAllowancePrepare isWithdraw
    (by cases isWithdraw <;> exact le_trans (by decide +kernel) hsize) hmo hcanon rfl (by omega) h
  by_cases hmax : old = UInt256.ofNat (UInt256.size - 1)
  · rw [if_pos hmax] at rdNext
    refine Or.inl ⟨evm, σ, locals0, mem0, aw0, k0, C0, ?_, hs, hframe0, ?_, rdNext⟩
    · exact ExecBlock.consNormal hlet (ExecBlock.consNormal (ExecStmt.iteFalse
        (evalExpr_ne_int_false hevalOld hevalMax (by rw [hmax])) ExecBlock.nil) ExecBlock.nil)
    · intro name hname _
      exact store_get_ne _ _ hname
  rw [if_neg hmax] at rdNext
  have hcond := evalExpr_ne_int_true hevalOld hevalMax (fun hn => hmax (u256_inj (Int.ofNat.inj hn)))
  have howner : memLoad (UInt256.ofNat (vaultDebitAllowanceFlow isWithdraw).ownerOffset) mem0 = owner := by
    have hoff : (vaultDebitAllowanceFlow isWithdraw).ownerOffset = 608 := by cases isWithdraw <;> rfl
    rw [hoff, hframe0.load 608 (by omega) (by cases isWithdraw <;> decide +kernel)
      (by cases isWithdraw <;> exact le_trans (by decide +kernel) hsize) (by decide +kernel), hmo]
  have hvalue : (vaultDebitAllowanceFlow isWithdraw).amount I mem0 = shares := by
    cases isWithdraw
    · exact hmv
    · exact (hframe0.load 672 (by omega) (by decide +kernel) hsize (by decide +kernel)).trans hmv
  rcases vaultAllowanceSpend (vaultDebitAllowanceFlow isWithdraw) (retVar := vaultDebitAllowanceRetVar isWithdraw)
    (ownerExpr := .var "_owner") (oldExpr := .var "allowance_") (valueExpr := .var (vaultDebitSharesName isWithdraw))
    hs hsize0 howner hma0 hvalue hcanon
    (by rw [evalExpr?]; simp only [ho0, EvalResult.ofOption]) hevalOld (evalExpr_varUInt256 hv0) hperm hstack rdNext with
    ⟨evm1, σ1, mem1, aw1, k1, C1, hcall, hs1, hframe1, rdDone⟩ | ⟨hcall, hrev⟩
  swap
  · exact Or.inr ⟨ExecBlock.consNormal hlet
      (ExecBlock.consRevert (ExecStmt.iteTrue hcond (ExecBlock.consRevert hcall))), hrev⟩
  refine Or.inl ⟨evm1, σ1, locals0.insert (vaultDebitAllowanceRetVar isWithdraw) .unit, mem1, aw1, k1, C1,
    ExecBlock.consNormal hlet (ExecBlock.consNormal
      (ExecStmt.iteTrue hcond (ExecBlock.consNormal hcall ExecBlock.nil)) ExecBlock.nil), hs1,
    hframe0.trans (hframe1.mono (le_refl _) (by cases isWithdraw <;> decide +kernel)), ?_, rdDone⟩
  intro name ha hc
  exact store_get_ne2 _ _ _ ha hc

end Benchmarks.CurveVault
