import Benchmarks.CurveVault.BalanceStorage
import Benchmarks.CurveVault.AddressWord
import Benchmarks.CurveVault.RuntimeBlocks_030
import Benchmarks.CurveVault.RuntimeBlocks_031
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultTransferFunction : FunctionDecl := contract.functions[35]!
abbrev vaultTransferGuardExpr : Expr := .binary .and
  (.binary .ne (.var "_to") (.env .this))
  (.binary .ne (.var "_to") (.cast (.intLit 0) (.elem .address)))

def vaultTransferLocals (sender recipient : AccountAddress) (value : UInt256) : Store :=
  (((∅ : Store).insert "_value" (.int (Int.ofNat value.toNat))).insert "_to" (.address recipient)).insert "_from" (.address sender)

theorem vaultTransferGuardSource (evm : State) (locals : Store) (recipient : AccountAddress)
    (hto : locals.get? "_to" = some (.address recipient)) :
    evalExpr? config {contract := contract, locals := locals} evm vaultTransferGuardExpr =
      .ok (.bool (decide (recipient ≠ evm.executionEnv.codeOwner) && decide (recipient ≠ 0))) := by
  have heval : evalExpr? config {contract := contract, locals := locals} evm (.var "_to") = .ok (.address recipient) := by
    rw [evalExpr?]
    simp only [hto, EvalResult.ofOption]
  by_cases hself : recipient = evm.executionEnv.codeOwner <;>
    simp [vaultTransferGuardExpr, evalExpr?, heval, envValue, evalBinaryOp?, castValue?,
      EvalResult.ofOption, EvalResult.bind, pure, bind, value_address_beq, AccountAddress.ofNat, hself]

theorem vaultTransferGuard {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {locals : Store} {recipient : UInt256} {R : List UInt256}
    (hs : SourceState s0 I σ evm)
    (hto : locals.get? "_to" = some (.address (AccountAddress.ofNat recipient.toNat)))
    (hmto : memLoad (UInt256.ofNat 96) mem = recipient) (hcanon : recipient.toNat < EVM.addressModulus)
    (hstack : R.length + 4 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 8133) R mem aw rdata σ k C) :
    (evalExpr? config {contract := contract, locals := locals} evm vaultTransferGuardExpr = .ok (.bool true) ∧
      ∃ aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat 8161) R mem aw' rdata σ k' C') ∨
    (evalExpr? config {contract := contract, locals := locals} evm vaultTransferGuardExpr = .ok (.bool false) ∧
      RDrev fork vaultBytecode g s0) := by
  have heval := vaultTransferGuardSource evm locals (AccountAddress.ofNat recipient.toNat) hto
  rw [hs.env] at heval
  by_cases hself : recipient = UInt256.ofNat I.codeOwner.val
  · have rd8151 := vaultBlocks.vault_block_8133_taken (by omega)
      (by rw [hmto, hself, u256_eq_refl]; decide +kernel) (by native_decide) h
    have rd8153 := vaultBlocks.vault_block_8151
      (by simp only [vaultBlocks.vault_block_8133_taken_stack, List.length_cons]; omega) rd8151
    have rdFail := vaultBlocks.vault_block_8153_taken (by omega) (by decide +kernel) (by native_decide) rd8153
    have hrev := vaultBlocks.vault_block_8284 (by simp only [vaultBlocks.vault_block_8153_taken_stack]; omega) rdFail
    refine Or.inr ⟨?_, hrev⟩
    rw [heval, hself, addressWord_roundtrip]
    simp
  have rd8144 := vaultBlocks.vault_block_8133_fallthrough (by omega)
    (by rw [hmto]; exact u256_eq_of_ne hself) h
  have rd8153 := vaultBlocks.vault_block_8144 (by omega) (by native_decide) rd8144
  change RD fork vaultBytecode I g s0 (UInt256.ofNat 8153)
    (UInt256.isZero (UInt256.isZero (memLoad (UInt256.ofNat 96) mem)) :: memLoad (UInt256.ofNat 96) mem :: R)
    mem _ rdata σ _ _ at rd8153
  rw [hmto] at rd8153
  have haself : AccountAddress.ofNat recipient.toNat ≠ I.codeOwner := fun he => hself ((addressOfWord_eq_iff hcanon _).mp he)
  by_cases hz : recipient = ⟨0⟩
  · have rdFail := vaultBlocks.vault_block_8153_taken (by omega) (by rw [hz]; decide +kernel) (by native_decide) rd8153
    have hrev := vaultBlocks.vault_block_8284 (by simp only [vaultBlocks.vault_block_8153_taken_stack]; omega) rdFail
    refine Or.inr ⟨?_, hrev⟩
    rw [heval, hz]
    simp [AccountAddress.ofNat]
  · have rdNext := vaultBlocks.vault_block_8153_fallthrough (by omega)
      (by rw [isZero_eq_zero_of_ne hz]; rfl) rd8153
    refine Or.inl ⟨?_, _, _, _, rdNext⟩
    rw [heval]
    have haz : AccountAddress.ofNat recipient.toNat ≠ 0 := fun he => hz ((addressOfWord_eq_iff hcanon _).mp he)
    simp [haself, haz]

end Benchmarks.CurveVault
