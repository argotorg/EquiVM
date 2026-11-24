import Benchmarks.Safe.V0_cdb2eb5.ExecTransactionSourcePrefix
import Benchmarks.Safe.V0_cdb2eb5.ExecTransactionDecodeSteps
import Benchmarks.Safe.V0_cdb2eb5.CheckedIncrement
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_019

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

def execHashSaved (cd : ByteArray) (len : Nat) (ptr : UInt256)
    (R : List UInt256) : List UInt256 :=
  ⟨0⟩ :: ⟨0⟩ :: execTransactionDecodedStack cd len ptr R

def execHashStack (cd : ByteArray) (len : Nat) (ptr nonce : UInt256)
    (R : List UInt256) : List UInt256 :=
  [nonce, calldataWord cd 260, calldataWord cd 228, calldataWord cd 196, calldataWord cd 164,
    calldataWord cd 132, calldataWord cd 100, UInt256.ofNat len,
    UInt256.ofNat (execTransactionDataStart cd), calldataWord cd 36, calldataWord cd 4,
    ⟨3481⟩] ++ execHashSaved cd len ptr R

set_option maxRecDepth 100000

theorem safeExecNonceStart (evm : EVM.State) {I g s0 σ k C aw mem rdata len}
    {ptr : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3439⟩ (execTransactionDecodedStack I.calldata len ptr R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hov : R.length + 36 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨11030⟩
      (execNonce evm :: ⟨3472⟩ :: ⟨0⟩ :: ⟨5⟩ ::
        execHashStack I.calldata len ptr (execNonce evm) R) mem aw rdata σ k' C' := by
  have hload : (σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac ↦ ac.storage.getD (UInt256.ofNat 5) ⟨0⟩)) = execNonce evm := by
    simp only [execNonce, Stele.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      hee, hacc]
    rfl
  obtain ⟨k', C', h₁⟩ := safeRuntime_block_3439 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_3439_stack, hload] at h₁
  exact ⟨k', C', h₁⟩

theorem safeExecNonceStore (evm : EVM.State) {I g s0 σ k C aw mem rdata}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3472⟩ ((execNonce evm + ⟨1⟩) :: ⟨0⟩ :: ⟨5⟩ :: R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hp : I.perm = true) (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨5217⟩ R
      mem aw rdata (execNonceState evm).accountMap k' C' := by
  obtain ⟨k', C', h₁⟩ := safeRuntime_block_3472 hov hp (by jump_dest) h
  exact ⟨k', C', by simpa only [execNonceState, storageStore_accountMap, hee, hacc] using h₁⟩

theorem safeExecNonceStatic {I g s0 σ k C aw mem rdata} {value : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3472⟩ (value :: ⟨0⟩ :: ⟨5⟩ :: R) mem aw rdata σ k C)
    (hp : I.perm = false) (hov : R.length + 3 ≤ 1024) : RDstatic fork safeBytecode g s0 := by
  have h₁ := h.jumpdest (by native_decide) (by simp; omega)
  have h₂ := h₁.swap2 (by native_decide) (by simp; omega)
  have h₃ := h₂.swap1 (by native_decide) (by simp; omega)
  have h₄ := h₃.pop (by native_decide) (by simp; omega)
  exact h₄.sstoreStatic hp (by native_decide) (by omega)

end Benchmarks.Safe.V0_cdb2eb5
