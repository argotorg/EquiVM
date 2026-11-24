import Benchmarks.Safe.ViaIR.ExecTransactionSourcePrefix
import Benchmarks.Safe.ViaIR.ExecTransactionDecodeSteps
import Benchmarks.Safe.ViaIR.CheckedIncrement
import Benchmarks.Safe.ViaIR.Blocks.Runtime_021

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def execHashSaved (cd : ByteArray) (len : Nat) (ptr : UInt256)
    (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat (execTransactionDataStart cd), calldataWord cd 260, ptr,
    calldataWord cd 228, calldataWord cd 4, UInt256.ofNat len] ++ R

def execHashStack (cd : ByteArray) (len : Nat) (ptr nonce : UInt256)
    (R : List UInt256) : List UInt256 :=
  [calldataWord cd 4, calldataWord cd 36, UInt256.ofNat (execTransactionDataStart cd),
    UInt256.ofNat len, calldataWord cd 100, calldataWord cd 132, calldataWord cd 164,
    calldataWord cd 196, calldataWord cd 228, calldataWord cd 260, nonce,
    ⟨4522⟩] ++ execHashSaved cd len ptr R

set_option maxRecDepth 2000

theorem safeExecNonceStart (evm : EVM.State) {I g s0 σ k C aw mem rdata len}
    {ptr : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4469⟩ (execTransactionDecodedStack I.calldata len ptr R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hov : R.length + 36 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7497⟩
      (execNonce evm :: ⟨4485⟩ :: execNonce evm :: ⟨4522⟩ ::
        execHashSaved I.calldata len ptr R) mem aw rdata σ k' C' := by
  have hload : (σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac ↦ ac.storage.getD (UInt256.ofNat 5) ⟨0⟩)) = execNonce evm := by
    simp only [execNonce, Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      hee, hacc]
    rfl
  obtain ⟨k', C', h₁⟩ := safeRuntime_block_4469 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_4469_stack, hload] at h₁
  exact ⟨k', C', h₁⟩

theorem safeExecNonceStore (evm : EVM.State) {I g s0 σ k C aw mem rdata len}
    {ptr : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4485⟩
      ((execNonce evm + ⟨1⟩) :: execNonce evm :: ⟨4522⟩ ::
        execHashSaved I.calldata len ptr R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hp : I.perm = true) (hc : (calldataWord I.calldata 260).toNat < EVM.addressModulus)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨9040⟩
      (execHashStack I.calldata len ptr (execNonce evm) R)
      mem aw rdata (execNonceState evm).accountMap k' C' := by
  obtain ⟨k', C', h₁⟩ := safeRuntime_block_4485 (by simp; omega) hp (by jump_dest) h
  simp only [safeRuntime_block_4485_stack, safeAddressMask] at h₁
  simpa only [execNonceState, storageStore_accountMap, hee, hacc, solcAddrMask_clean hc] using
    (show ∃ k' C', RD fork safeBytecode I g s0 ⟨9040⟩
      (execHashStack I.calldata len ptr (execNonce evm) R)
      mem aw rdata (sstoreAccountMap I.codeOwner σ ⟨5⟩ (execNonce evm + ⟨1⟩)) k' C' from
        ⟨k', C', by simpa only [solcAddrMask_clean hc] using h₁⟩)

theorem safeExecNonceStatic {I g s0 σ k C aw mem rdata} {value : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4485⟩ (value :: R) mem aw rdata σ k C)
    (hp : I.perm = false) (hov : R.length + 2 ≤ 1024) : RDstatic fork safeBytecode g s0 := by
  have h₁ := h.jumpdest (by native_decide) (by simp; omega)
  have h₂ := h₁.push1 ⟨5⟩ (by native_decide) (by simp; omega)
  exact h₂.sstoreStatic hp (by native_decide) (by omega)

end Benchmarks.Safe.ViaIR
