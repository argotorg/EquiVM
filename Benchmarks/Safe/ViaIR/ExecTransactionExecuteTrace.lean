import Benchmarks.Safe.ViaIR.ExecTransactionExecutePrepare
import Benchmarks.Safe.ViaIR.ExecuteTrace

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def execDataMemory (p : ExecTransactionInput) (cd mem : ByteArray) (src ptr : Nat) : ByteArray :=
  calldataBufferMemory cd mem src ptr p.tx.payload.size p.tx.payload.size
    (ptr + 32 + ABI.paddedSize p.tx.payload.size)

def execAfterExecute (locals : Store) (before gasLeft : UInt256) (z : Bool) : Frame :=
  { contract := contract
    locals := (execExecuteFrame locals before gasLeft).locals.insert "success" (.bool z) }

def execExecutedStack (p : ExecTransactionInput) (before guard hash : UInt256)
    (z : Bool) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat p.tx.gasToken.val, UInt256.isZero p.tx.gasPrice,
    UInt256.ofNat p.tx.refundReceiver.val, UInt256.land guard solcAddrMask,
    z.toUInt256, hash, before, ⟨0⟩] ++ R

theorem execAfterExecute_locals {p : ExecTransactionInput} {locals : Store}
    (hl : ExecTransactionLocals p locals) (before gasLeft : UInt256) (z : Bool) :
    ExecTransactionLocals p (execAfterExecute locals before gasLeft z).locals :=
  (execExecuteFrame_locals hl before gasLeft).set _ _ (by decide)

set_option maxRecDepth 2000

theorem safeExecTransactionCall (p : ExecTransactionInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr} {before gasLeft guard hash : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4689⟩
      (execAllocatedStack p ptr before gasLeft guard hash R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hcFields : ExecTransactionCalldataFields I.calldata p)
    (hdata : mem.readWithPadding (UInt256.ofNat ptr + UInt256.ofNat 32).toNat
      (memLoad (UInt256.ofNat ptr) mem).toNat = p.tx.payload)
    (hov : R.length + 20 ≤ 1024) :
    (RDstatic fork safeBytecode g s0 ∧ ExecFuncBody fork config
      (executeFrame p.tx.target p.tx.value p.tx.payload p.tx.operation (execCallGas p gasLeft))
      evm executeFunction.body .staticViolation) ∨
    ∃ evm' σ' z out aw' k' C', ExecFuncBody fork config
      (executeFrame p.tx.target p.tx.value p.tx.payload p.tx.operation (execCallGas p gasLeft))
      evm executeFunction.body
      (.returned (executeFinalFrame p.tx.target p.tx.value p.tx.payload p.tx.operation
        (execCallGas p gasLeft) z out) evm' (some [.bool z])) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD fork safeBytecode I g s0 ⟨4710⟩ (execExecutedStack p before guard hash z R)
        mem aw' out σ' k' C' ∧ out.size < UInt256.size := by
  have ht : AccountAddress.ofUInt256 (UInt256.ofNat p.tx.target.val) = p.tx.target :=
    AccountAddress.ofUInt256_ofNat p.tx.target
  have hop : uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 100).toNat 32) =
      p.tx.operation := hcFields.operation
  by_cases hd : p.tx.operation = ⟨1⟩
  · have h₁ := safeRuntime_block_4689_fallthrough
      (by simp [execCallSaved]; omega) (by rw [hop, hd]; rfl) h
    have h₂ := safeRuntime_block_4701 (by simp [execCallSaved]; omega) h₁
    obtain ⟨evm', σ', z, out, aw', k', C', hc, he, ha, hw, h₃, hs⟩ :=
      rawDelegateCallTraceFrom evm h₂ hee hacc hworld (by native_decide)
        (by simp [execCallSaved]; omega)
    rw [callOutputMem_zero] at h₃
    have h₄ := safeRuntime_block_4709 (by simp; omega) h₃
    have hbool : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = z.toUInt256 := by cases z <;> rfl
    refine .inr ⟨evm', σ', z, out, aw', k' + 1, C' + 3, safeExecuteDelegateSource hd ?_,
      he, ha, hw, ?_, hs⟩
    · simpa only [addressOfAddress, ht, hdata] using hc
    · simpa only [safeRuntime_block_4709_stack, execExecutedStack, hbool] using h₄
  · have h₁ := safeRuntime_block_4689_taken
      (by simp [execCallSaved]; omega)
      (by rw [hop]; exact u256_sub_ne_zero_of_ne (fun hh ↦ hd hh.symm)) (by jump_dest) h
    have h₂ := safeRuntime_block_5325 (by simp [execCallSaved]; omega) h₁
    simp only [safeRuntime_block_5325_stack,
      show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 36).toNat 32) =
        p.tx.value from hcFields.value] at h₂
    by_cases hp : I.perm = true ∨ p.tx.value = ⟨0⟩
    · obtain ⟨evm', σ', z, out, aw', k', C', hc, he, ha, hw, h₃, hs, _⟩ :=
        rawValueCallTraceFrom evm h₂ hee hacc hworld (by native_decide)
          (by simp [execCallSaved]; omega) hp
      rw [callOutputMem_zero] at h₃
      have h₄ := safeRuntime_block_5339 (by simp; omega) (by jump_dest) h₃
      have hbool : (if z then (⟨1⟩ : UInt256) else ⟨0⟩) = z.toUInt256 := by cases z <;> rfl
      refine .inr ⟨evm', σ', z, out, aw', k' + 3, C' + 14, safeExecuteCallSource (hperm := by simpa only [hee, or_comm] using hp) hd ?_,
        he, ha, hw, ?_, hs⟩
      · simpa only [addressOfAddress, ht, hdata] using hc
      · simpa only [safeRuntime_block_5339_stack, execExecutedStack, hbool] using h₄
    · have hperm : I.perm = false := Bool.eq_false_iff.mpr (fun he ↦ hp (.inl he))
      have hv : p.tx.value ≠ ⟨0⟩ := fun hz ↦ hp (.inr hz)
      exact .inl ⟨RD.callValueStatic h₂ hperm hv (by native_decide)
        (by simp [execCallSaved]; omega),
        safeExecuteCallStaticSource hd (by simpa only [hee] using hperm) hv⟩

set_option maxRecDepth 100000 in
theorem safeExecTransactionExecute (p : ExecTransactionInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata src ptr locals} {guard hash : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4639⟩ (execGasSaved p src guard hash (⟨0⟩ :: R))
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hcFields : ExecTransactionCalldataFields I.calldata p)
    (hl : ExecTransactionLocals p locals)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 96 ≤ mem.size)
    (hp : ptr + 64 + p.tx.payload.size < UInt256.size) (hn : p.tx.payload.size < 2 ^ 64)
    (hd : src + p.tx.payload.size ≤ I.calldata.size) (hcd : I.calldata.size < UInt256.size)
    (hdata : I.calldata.extract src (src + p.tx.payload.size) = p.tx.payload)
    (hov : R.length + 36 ≤ 1024) :
    RDrev fork safeBytecode g s0 ∨
    (RDstatic fork safeBytecode g s0 ∧ ExecBlock fork config { contract := contract, locals := locals }
      evm (exectransactionTransition.body.drop 10) .staticViolation) ∨
    ∃ before gasLeft z evm' σ' out aw' k' C',
      (∀ result, ExecBlock fork config (execAfterExecute locals before gasLeft z) evm'
        (exectransactionTransition.body.drop 13) result →
        ExecBlock fork config { contract := contract, locals := locals } evm
          (exectransactionTransition.body.drop 10) result) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD fork safeBytecode I g s0 ⟨4710⟩ (execExecutedStack p before guard hash z R)
        (execDataMemory p I.calldata mem src ptr) aw' out σ' k' C' ∧
      out.size < UInt256.size ∧ ptr + 32 + ABI.paddedSize p.tx.payload.size < 2 ^ 64 := by
  obtain ⟨hr, _⟩ | ⟨before, gasLeft, k₁, C₁, hfit, h₁⟩ :=
    safeExecExecutePrepare p h hcFields hov
  · exact .inl hr
  obtain hr | ⟨aw₂, k₂, C₂, hcap, h₂⟩ :=
    safeExecAllocate p h₁ hf hp hn hd hcd (by simp [execCallSaved]; omega) (by jump_dest)
  · exact .inl hr
  have hg : (execExecuteFrame locals before gasLeft).locals["txGasLeft"]? =
      some (uint256Value gasLeft) := by
    simp [execExecuteFrame]
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
  obtain ⟨hr, hbody⟩ | ⟨evm', σ', z, out, aw', k', C', hbody, he', ha', hw', h₃, hout⟩ :=
    safeExecTransactionCall p evm h₂ hee hacc hworld hcFields hslice (by omega)
  · have hs := safeExecExecuteCall p evm (execExecuteFrame_locals hl before gasLeft) hgas hbody
    exact .inr (.inl ⟨hr, .consNormal (.letGas before)
      (.consNormal (.letGas gasLeft) (.consStatic hs))⟩)
  have hs := safeExecExecuteCall p evm (execExecuteFrame_locals hl before gasLeft) hgas hbody
  exact .inr (.inr ⟨before, gasLeft, z, evm', σ', out, aw', k', C',
    fun _ ht ↦ .consNormal (.letGas before)
      (.consNormal (.letGas gasLeft) (.consNormal hs ht)), he', ha', hw', h₃, hout, hcap⟩)

end Benchmarks.Safe.ViaIR
