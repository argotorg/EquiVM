import Reasoning.PackedStorage
import Benchmarks.Auction.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def initializingWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (solcSlotWord σ I ⟨0⟩) ⟨256⟩) ⟨255⟩

def initializedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWord σ I ⟨0⟩) ⟨255⟩


def InitializerReady (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  initializingWord σ I ≠ ⟨0⟩ ∨ σ.get? I.codeOwner = none

-- A nested initializer's saved top-level flag permits its final cleanup to be a no-op.
def InitializerNestedFlag (σ : AccountMap) (I : ExecutionEnv) (top : UInt256) : Prop :=
  top = ⟨0⟩ ∨ σ.get? I.codeOwner = none


theorem initializerReady_sstore {σ : AccountMap} {I : ExecutionEnv}
    (hr : InitializerReady σ I) (slot value : UInt256) (hs : (⟨0⟩ : UInt256) ≠ slot) :
    InitializerReady (sstoreAccountMap I.codeOwner σ slot value) I := by
  rcases hr with hi | ha
  · left
    simpa only [initializingWord, solcSlotWord_sstore_ne σ I ⟨0⟩ slot value hs] using hi
  · rw [sstoreAccountMap_absent_same ha]
    exact Or.inr ha

theorem initializerNestedFlag_of_ready {σ : AccountMap} {I : ExecutionEnv}
    (hr : InitializerReady σ I) :
    InitializerNestedFlag σ I (UInt256.isZero (initializingWord σ I)) := by
  rcases hr with hi | ha
  · exact Or.inl (isZero_eq_zero_of_ne hi)
  · exact Or.inr ha

theorem initializerNestedFlag_sstore {σ : AccountMap} {I : ExecutionEnv} {top : UInt256}
    (hf : InitializerNestedFlag σ I top) (slot value : UInt256) :
    InitializerNestedFlag (sstoreAccountMap I.codeOwner σ slot value) I top := by
  rcases hf with ht | ha
  · exact Or.inl ht
  · rw [sstoreAccountMap_absent_same ha]
    exact Or.inr ha

end Auction
