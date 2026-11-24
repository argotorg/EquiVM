import Benchmarks.CurveVault.AllowanceAdjustFinish
import Benchmarks.CurveVault.MutatingLock

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultAdjustLocals (increase : Bool) (spender : AccountAddress) (delta : UInt256) : Store :=
  ((∅ : Store).insert (vaultAdjustDeltaName increase) (.int (Int.ofNat delta.toNat))).insert "_spender" (.address spender)

theorem vaultAdjustStatic (increase : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hperm : I.perm = false) (hstack : R.length + 2 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (vaultAdjustEntryPc increase) R mem aw rdata σ k C) :
    RDstatic fork vaultBytecode g s0 := by
  have r1 := h.push1 (UInt256.ofNat 1) (by cases increase <;> native_decide) (by omega)
  have r2 := r1.push0 (by cases increase <;> native_decide) (by simp only [List.length_cons]; omega)
  exact tstoreStaticReach r2 hperm (by cases increase <;> native_decide) (by omega)

theorem vaultAdjustRoutine (increase : Bool) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {locals : Store} {spender : UInt256} {R : List UInt256}
    (hs : SourceState s0 I σ evm) (hsize : 224 ≤ mem.size)
    (hbase : locals.get? "allowance" = none)
    (hsp : locals.get? "_spender" = some (.address (AccountAddress.ofNat spender.toNat)))
    (hdelta : locals.get? (vaultAdjustDeltaName increase) = some (.int (Int.ofNat (calldataWord I.calldata 36).toNat)))
    (hms : memLoad (UInt256.ofNat 192) mem = spender)
    (hcanon : spender.toNat < EVM.addressModulus) (hperm : I.perm = true) (hstack : R.length + 6 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (vaultAdjustEntryPc increase) R mem aw rdata σ k C) :
    ∃ (evm' : State) (σ' : AccountMap) (locals' : Store),
      ExecFuncBody fork config {contract := contract, locals := locals} (vaultSetLock evm ⟨1⟩) (vaultAdjustFunction increase).body
        (.returned {contract := contract, locals := locals'} evm' (some [.bool true])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) (⟨1⟩ : UInt256).toByteArray := by
  let evm0 := vaultSetLock evm ⟨1⟩
  let σ0 := tstoreAccountMap I.codeOwner σ ⟨0⟩ ⟨1⟩
  let old := codeOwnerStorageWord I σ0 (vaultAllowanceSlot I.source (AccountAddress.ofNat spender.toNat))
  have hs0 : SourceState s0 I σ0 evm0 := by
    unfold evm0 vaultSetLock
    rw [hs.env]
    exact sourceStateTransientWrite hs ⟨0⟩ ⟨1⟩
  have hread : Stele.EVM.storageLoad evm0 evm0.executionEnv.codeOwner
      (vaultAllowanceSlot evm0.executionEnv.source (AccountAddress.ofNat spender.toNat)) = old := by
    simpa only [hs0.env] using hs0.storageRead (vaultAllowanceSlot I.source (AccountAddress.ofNat spender.toNat))
  have hprefix := vaultAdjustPrefixSource (fork := fork) increase evm0 locals (AccountAddress.ofNat spender.toNat)
    old (calldataWord I.calldata 36) hbase hsp hdelta hread
  obtain ⟨mem', aw', k', C', hsize', hms', hmc', hmv', rdFinish⟩ :=
    vaultAdjustPrepare increase hsize hms hcanon (show codeOwnerStorageWord I σ0
      (vaultAllowanceSlot I.source (AccountAddress.ofNat spender.toNat)) = old from rfl) hperm hstack h
  obtain ⟨evm', σ', locals', hfinish, hs', hret⟩ := vaultAdjustFinish increase hs0 hsize'
    (locals := vaultAdjustPrefixLocals locals increase old (calldataWord I.calldata 36))
    (by rw [vaultAdjustPrefixLocals_other _ _ _ _ _ (by decide +kernel) (by decide +kernel)]; exact hsp)
    (vaultAdjustPrefixLocals_cached _ _ _ _) (vaultAdjustPrefixLocals_value _ _ _ _)
    hms' hmc' hmv' hcanon hperm hstack rdFinish
  refine ⟨evm', σ', locals', ExecFuncBody.execBlockRet ?_, hs', hret⟩
  have hbody : (vaultAdjustFunction increase).body = (vaultAdjustFunction increase).body.take 3 ++ vaultAdjustFinishBody := by
    cases increase <;> rfl
  rw [hbody]
  exact execBlock_append hprefix hfinish

end Benchmarks.CurveVault
