import Benchmarks.CurveVault.CreditFinish
import Benchmarks.CurveVault.MutationTransfer

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultCreditTailBody_eq (isDeposit : Bool) :
    (vaultCreditFunction isDeposit).body.drop 8 =
      vaultMutationTransferBody (vaultCreditFlow isDeposit) (vaultCreditAssetsName isDeposit) ++
        vaultCreditFinishBody isDeposit := by
  cases isDeposit <;> rfl

theorem vaultCreditTail (isDeposit : Bool) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver controller assets shares : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 704 ≤ mem.size)
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (hc : locals.get? "controller" = some (.address (AccountAddress.ofUInt256 controller)))
    (hw : locals.get? "controller_word" = some (.int (Int.ofNat controller.toNat)))
    (hb : locals.get? "_borrowed_token" = none)
    (ha : locals.get? (vaultCreditAssetsName isDeposit) = some (.int (Int.ofNat assets.toNat)))
    (hv : locals.get? (vaultCreditSharesName isDeposit) = some (.int (Int.ofNat shares.toNat)))
    (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hmc : memLoad (UInt256.ofNat 608) mem = controller)
    (hmv : memLoad (UInt256.ofNat 672) mem = vaultCreditResult isDeposit assets shares)
    (hinput : calldataWord I.calldata 4 = vaultCreditInput isDeposit assets shares)
    (hcanon : receiver.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hstack : R.length + 9 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultCreditFlow isDeposit).hookEntry) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store),
      ExecBlock fork config {contract := contract, locals := locals} evm ((vaultCreditFunction isDeposit).body.drop 8)
        (.returned {contract := contract, locals := locals'} evm'
          (some [.int (Int.ofNat (vaultCreditResult isDeposit assets shares).toNat)])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩)
        (vaultCreditResult isDeposit assets shares).toByteArray) ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm ((vaultCreditFunction isDeposit).body.drop 8)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  rw [vaultCreditTailBody_eq]
  rcases vaultMutationTransfer (vaultCreditFlow isDeposit) hs hsize hr hc hw hb ha
    (by cases isDeposit <;> decide +kernel) hmr (by cases isDeposit <;> exact hmc)
    (by cases isDeposit <;> exact le_trans (by decide +kernel) hsize)
    (by cases isDeposit; exact hmv; exact hinput) hcanon hperm hstack h with
    ⟨evm1, σ1, mem1, out1, aw1, k1, C1, htransfer, hs1, hsize1, hframe, rdFinish⟩ | ⟨htransfer, hrev⟩
  swap
  · exact Or.inr ⟨execBlock_reverted_append htransfer, hrev⟩
  have hframe1 : WordMemoryRange mem mem1 352 704 := by cases isDeposit <;> exact hframe
  rcases vaultCreditFinish isDeposit hs1 (by omega)
    (by rw [vaultMutationCallLocals_get _ _ (by decide +kernel), hr])
    (by rw [vaultMutationCallLocals_get _ _ (by decide +kernel), hc])
    (by rw [vaultMutationCallLocals_get _ _ (by cases isDeposit <;> decide +kernel), ha])
    (by rw [vaultMutationCallLocals_get _ _ (by cases isDeposit <;> decide +kernel), hv])
    ((hframe1.load 576 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmr)
    ((hframe1.load 608 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmc)
    ((hframe1.load 672 (by omega) (by omega) hsize (by decide +kernel)).trans hmv)
    hinput hcanon hperm (by omega) rdFinish with
    ⟨evm2, σ2, locals2, hfinish, hs2, hret⟩ | ⟨hfinish, hrev⟩
  · exact Or.inl ⟨evm2, σ2, locals2, execBlock_append htransfer hfinish, hs2, hret⟩
  · exact Or.inr ⟨execBlock_append htransfer hfinish, hrev⟩

end Benchmarks.CurveVault
