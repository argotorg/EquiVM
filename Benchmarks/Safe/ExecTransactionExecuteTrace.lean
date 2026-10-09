import Benchmarks.Safe.ExecTransactionExecutePrepare
import Benchmarks.Safe.ExecuteTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def execDataMemory (p : ExecTransactionInput) (cd mem : ByteArray) (src ptr : Nat) : ByteArray :=
  calldataBufferMemory cd mem src ptr p.tx.payload.size p.tx.payload.size
    (ptr + 32 + ABI.paddedSize p.tx.payload.size)

def execAfterExecute (locals : Store) (before gasLeft : UInt256) (z : Bool) : Frame :=
  { contract := contract
    locals := (execExecuteFrame locals before gasLeft).locals.insert "success" (.bool z) }

theorem execAfterExecute_locals {p : ExecTransactionInput} {locals : Store}
    (hl : ExecTransactionLocals p locals) (before gasLeft : UInt256) (z : Bool) :
    ExecTransactionLocals p (execAfterExecute locals before gasLeft z).locals :=
  (execExecuteFrame_locals hl before gasLeft).set _ _ (by decide)

set_option maxRecDepth 100000 in
theorem safeExecTransactionExecute (p : ExecTransactionInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata src ptr locals} {sigPtr guard hash : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3830⟩ (execGuardSaved p src sigPtr guard hash R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hl : ExecTransactionLocals p locals)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 96 ≤ mem.size)
    (hp : ptr + 64 + p.tx.payload.size < UInt256.size) (hs : src < UInt256.size)
    (hd : src + p.tx.payload.size ≤ I.calldata.size)
    (hdata : I.calldata.extract src (src + p.tx.payload.size) = p.tx.payload)
    (ho : p.tx.operation.toNat < 2) (hov : R.length + 36 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧ ExecBlock config { contract := contract, locals := locals }
      evm (exectransactionTransition.body.drop 10) .reverted) ∨
    (RDstatic safeBytecode g s0 ∧ ExecBlock config { contract := contract, locals := locals }
      evm (exectransactionTransition.body.drop 10) .staticViolation) ∨
    ∃ before gasLeft z evm' σ' out aw' k' C',
      (∀ result, ExecBlock config (execAfterExecute locals before gasLeft z) evm'
        (exectransactionTransition.body.drop 13) result →
        ExecBlock config { contract := contract, locals := locals } evm
          (exectransactionTransition.body.drop 10) result) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ⟨3940⟩
        (z.toUInt256 :: before :: execGuardSaved p src sigPtr guard hash R)
        (execDataMemory p I.calldata mem src ptr) aw' out σ' k' C' ∧
      out.size < UInt256.size := by
  let before := (g.subNat (C + 3 + 2)).toUInt256
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeExecAllocate p h hf hp hs (by omega)
  obtain ⟨hr, hz, gasLeft, hlow⟩ | ⟨gasLeft, k₂, C₂, hfit, h₂⟩ :=
    safeExecExecutePrepare p h₁ hov
  · have hg : (execExecuteFrame locals before gasLeft).locals["txGasLeft"]? =
        some (uint256Value gasLeft) := by
      simp [execExecuteFrame, Std.HashMap.getElem_insert]
    have hs := safeExecExecuteArgsRevert p evm (execExecuteFrame_locals hl before gasLeft)
      (safeExecCallGasRevert p evm (execExecuteFrame_locals hl before gasLeft) hg hz hlow)
    exact .inl ⟨hr, .consNormal (.letGas before)
      (.consNormal (.letGas gasLeft) (.consRevert hs))⟩
  have hg : (execExecuteFrame locals before gasLeft).locals["txGasLeft"]? =
      some (uint256Value gasLeft) := by
    simp [execExecuteFrame, Std.HashMap.getElem_insert]
  have hgas := safeExecCallGas p evm (execExecuteFrame_locals hl before gasLeft) hg hfit
  have hb := calldataBufferMemory_bytes I.calldata mem src ptr p.tx.payload.size
    (ptr + 32 + ABI.paddedSize p.tx.payload.size) hm hd (by omega)
  rw [hdata] at hb
  have hslice : (execDataMemory p I.calldata mem src ptr).readWithPadding
      (UInt256.ofNat ptr + UInt256.ofNat 32).toNat
      (memLoad (UInt256.ofNat ptr) (execDataMemory p I.calldata mem src ptr)).toNat =
      p.tx.payload := by
    rw [execDataMemory, hb.length, wordOfNatAdd _ _ (by omega), ulit_toNat' _ (by omega),
      ulit_toNat' _ (by omega)]
    exact hb.payload
  have ht : AccountAddress.ofUInt256 (UInt256.ofNat p.tx.target.val) = p.tx.target :=
    AccountAddress.ofUInt256_ofNat p.tx.target
  rcases safeExecuteTrace evm p.tx.payload h₂ hee hacc hworld hslice (by omega)
    (by simp [execGuardSaved]; omega) (by jump_dest) with
    ⟨hr, hbody⟩ | ⟨evm', σ', z, out, aw', k', C', hbody, he', ha', hw', h₃, hout⟩
  · rw [ht] at hbody
    have hs := safeExecExecuteCall p evm (execExecuteFrame_locals hl before gasLeft) hgas hbody
    exact .inr (.inl ⟨hr, .consNormal (.letGas before)
      (.consNormal (.letGas gasLeft) (.consStatic hs))⟩)
  rw [ht] at hbody
  have hs := safeExecExecuteCall p evm (execExecuteFrame_locals hl before gasLeft) hgas hbody
  have hbool : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = z.toUInt256 := by cases z <;> rfl
  rw [hbool] at h₃
  exact .inr (.inr ⟨before, gasLeft, z, evm', σ', out, aw', k', C',
    fun _ ht ↦ .consNormal (.letGas before)
      (.consNormal (.letGas gasLeft) (.consNormal hs ht)), he', ha', hw', h₃, hout⟩)

end Benchmarks.Safe
