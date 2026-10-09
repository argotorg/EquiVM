import Examples.OpenZeppelinBench.Pausable.Bytecode
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Pausable

/-!
# Pausable storage helpers

The benchmark has one packed `bool` in slot `0`, byte offset `0`.  Most low-byte storage facts are
reused from `Reasoning.Storage` / packed scalar storage.
-/

def pausedRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.get? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.getD ⟨0⟩ ⟨0⟩)

def pausedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (pausedRawWord σ I) ⟨255⟩

def pausedSetTrueWord (w : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land w (UInt256.lnot ⟨255⟩)) ⟨1⟩

def pausedSetFalseWord (w : UInt256) : UInt256 :=
  UInt256.land w (UInt256.lnot ⟨255⟩)

def pausePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨0⟩ (pausedSetTrueWord (pausedRawWord σ I))

def unpausePostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨0⟩ (pausedSetFalseWord (pausedRawWord σ I))

def pausePostState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (pausedSetTrueWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩))

def unpausePostState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (pausedSetFalseWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩))


theorem pausePostState_accountMap (evm : EVM.State) :
    (pausePostState evm).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩
        (pausedSetTrueWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)) := by
  simp [pausePostState, storageStore_accountMap]

theorem unpausePostState_accountMap (evm : EVM.State) :
    (unpausePostState evm).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap ⟨0⟩
        (pausedSetFalseWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)) := by
  simp [unpausePostState, storageStore_accountMap]

end OpenZeppelinBench.Pausable
