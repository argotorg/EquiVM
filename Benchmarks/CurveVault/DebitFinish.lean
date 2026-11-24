import Benchmarks.CurveVault.DebitSource
import Benchmarks.CurveVault.SaveRateCalls
import Benchmarks.CurveVault.MutationReturn

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultDebitFinish (isWithdraw : Bool) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver owner controller assets shares : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 736 ≤ mem.size)
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (ho : locals.get? "_owner" = some (.address (AccountAddress.ofNat owner.toNat)))
    (hc : locals.get? "controller" = some (.address (AccountAddress.ofUInt256 controller)))
    (ha : locals.get? (vaultDebitAssetsName isWithdraw) = some (.int (Int.ofNat assets.toNat)))
    (hv : locals.get? (vaultDebitSharesName isWithdraw) = some (.int (Int.ofNat shares.toNat)))
    (hmc : memLoad (UInt256.ofNat 704) mem = controller)
    (hmv : memLoad (UInt256.ofNat 672) mem = vaultDebitResult isWithdraw assets shares)
    (hperm : I.perm = true) (hstack : R.length + 8 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultDebitFlow isWithdraw).saveEntry) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store),
      ExecBlock fork config {contract := contract, locals := locals} evm (vaultDebitFinishBody isWithdraw)
        (.returned {contract := contract, locals := locals'} evm'
          (some [.int (Int.ofNat (vaultDebitResult isWithdraw assets shares).toNat)])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩)
        (vaultDebitResult isWithdraw assets shares).toByteArray) ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm (vaultDebitFinishBody isWithdraw)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  have hmc0 : memLoad (UInt256.ofNat (vaultDebitFlow isWithdraw).controllerOffset) mem = controller := by
    cases isWithdraw <;> exact hmc
  rcases vaultSaveRateCall (vaultDebitFlow isWithdraw) (retVar := "__c4") hs hc hmc0 hstack h with
    ⟨evm1, σ1, out, aw1, k1, C1, hsave, hs1, rdReturn⟩ | ⟨hsave, hrev⟩
  swap
  · exact Or.inr ⟨execBlock_reverted_append hsave, hrev⟩
  let mem1 := vaultSaveRateMemory (vaultDebitFlow isWithdraw) mem
  have hframe : WordMemoryRange mem mem1 0 736 := by
    have hoff : (vaultDebitFlow isWithdraw).callOffset = 736 := by cases isWithdraw <;> rfl
    dsimp only [mem1, vaultSaveRateMemory]
    rw [hoff]
    exact wordMemoryRange_write _ _ 736 0 736
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 736 (by omega))) (Or.inl (by omega))
  have hvalue : memLoad (UInt256.ofNat 672) mem1 = vaultDebitResult isWithdraw assets shares :=
    (hframe.load 672 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmv
  have hret := vaultMutationReturn (vaultDebitFlow isWithdraw) (le_trans (by omega) hframe.size)
    hvalue hperm (by omega) rdReturn
  refine Or.inl ⟨evm1, σ1, locals.insert "__c4" .unit, execBlock_append hsave ?_, hs1, hret⟩
  apply vaultDebitReturnSource (hperm := by assumption) isWithdraw hs1
  · rw [store_get_ne _ _ (by decide +kernel), hr]
  · rw [store_get_ne _ _ (by decide +kernel), ho]
  · rw [store_get_ne _ _ (by cases isWithdraw <;> decide +kernel), ha]
  · rw [store_get_ne _ _ (by cases isWithdraw <;> decide +kernel), hv]

end Benchmarks.CurveVault
