import Benchmarks.CurveVault.DebitFinish
import Benchmarks.CurveVault.MutationTransfer

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultDebitTailBody_eq (isWithdraw : Bool) :
    (vaultDebitFunction isWithdraw).body.drop 7 =
      vaultMutationTransferBody (vaultDebitFlow isWithdraw) (vaultDebitAssetsName isWithdraw) ++
        vaultDebitFinishBody isWithdraw := by
  cases isWithdraw <;> rfl

theorem vaultDebitTail (isWithdraw : Bool) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver owner controller assets shares : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 704 ≤ mem.size)
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (ho : locals.get? "_owner" = some (.address (AccountAddress.ofNat owner.toNat)))
    (hc : locals.get? "controller" = some (.address (AccountAddress.ofUInt256 controller)))
    (hw : locals.get? "controller_word" = some (.int (Int.ofNat controller.toNat)))
    (hb : locals.get? "_borrowed_token" = none)
    (ha : locals.get? (vaultDebitAssetsName isWithdraw) = some (.int (Int.ofNat assets.toNat)))
    (hv : locals.get? (vaultDebitSharesName isWithdraw) = some (.int (Int.ofNat shares.toNat)))
    (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hmc : memLoad (UInt256.ofNat 704) (vaultHookCachedMemory (vaultDebitFlow isWithdraw) I σ mem) = controller)
    (hcachedSize : 736 ≤ (vaultHookCachedMemory (vaultDebitFlow isWithdraw) I σ mem).size)
    (hmv : memLoad (UInt256.ofNat 672) mem = vaultDebitResult isWithdraw assets shares)
    (hinput : calldataWord I.calldata 4 = vaultDebitInput isWithdraw assets shares)
    (hcanon : receiver.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hstack : R.length + 9 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultDebitFlow isWithdraw).hookEntry) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store),
      ExecBlock fork config {contract := contract, locals := locals} evm ((vaultDebitFunction isWithdraw).body.drop 7)
        (.returned {contract := contract, locals := locals'} evm'
          (some [.int (Int.ofNat (vaultDebitResult isWithdraw assets shares).toNat)])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩)
        (vaultDebitResult isWithdraw assets shares).toByteArray) ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm ((vaultDebitFunction isWithdraw).body.drop 7)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  rw [vaultDebitTailBody_eq]
  rcases vaultMutationTransfer (vaultDebitFlow isWithdraw) hs hsize hr hc hw hb ha
    (by cases isWithdraw <;> decide +kernel) hmr (by cases isWithdraw <;> exact hmc)
    (by cases isWithdraw <;> exact hcachedSize)
    (by cases isWithdraw; exact hmv; exact hinput) hcanon hperm hstack h with
    ⟨evm1, σ1, mem1, out1, aw1, k1, C1, htransfer, hs1, hsize1, hframe, rdFinish⟩ | ⟨htransfer, hrev⟩
  swap
  · exact Or.inr ⟨execBlock_reverted_append htransfer, hrev⟩
  have hframe1 : WordMemoryRange (vaultHookCachedMemory (vaultDebitFlow isWithdraw) I σ mem) mem1 352 736 := by
    cases isWithdraw <;> exact hframe
  have hframe0 := vaultHookCachedMemory_frame (vaultDebitFlow isWithdraw) I σ mem
  have hvalue : memLoad (UInt256.ofNat 672) mem1 = vaultDebitResult isWithdraw assets shares := by
    rw [hframe1.load 672 (by omega) (by omega) (by omega) (by decide +kernel),
      hframe0.load 672 (by omega) (by omega) hsize (by decide +kernel), hmv]
  have hnext : (vaultDebitFlow isWithdraw).tokenNext = (vaultDebitFlow isWithdraw).saveEntry := by
    cases isWithdraw <;> rfl
  rw [hnext] at rdFinish
  rcases vaultDebitFinish isWithdraw hs1 hsize1
    (by rw [vaultMutationCallLocals_get _ _ (by decide +kernel), hr])
    (by rw [vaultMutationCallLocals_get _ _ (by decide +kernel), ho])
    (by rw [vaultMutationCallLocals_get _ _ (by decide +kernel), hc])
    (by rw [vaultMutationCallLocals_get _ _ (by cases isWithdraw <;> decide +kernel), ha])
    (by rw [vaultMutationCallLocals_get _ _ (by cases isWithdraw <;> decide +kernel), hv])
    ((hframe1.load 704 (by omega) (by omega) hcachedSize (by decide +kernel)).trans hmc)
    hvalue hperm (by omega) rdFinish with
    ⟨evm2, σ2, locals2, hfinish, hs2, hret⟩ | ⟨hfinish, hrev⟩
  · exact Or.inl ⟨evm2, σ2, locals2, execBlock_append htransfer hfinish, hs2, hret⟩
  · exact Or.inr ⟨execBlock_append htransfer hfinish, hrev⟩

end Benchmarks.CurveVault
