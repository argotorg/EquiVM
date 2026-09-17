import Benchmarks.Auction.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def initializingWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (storedWord σ I ⟨0⟩) ⟨256⟩) ⟨255⟩

def initializedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (storedWord σ I ⟨0⟩) ⟨255⟩

def initializerBeginWord (old : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land old (UInt256.lnot ⟨65535⟩)) ⟨257⟩

def initializerEndWord (old : UInt256) : UInt256 :=
  UInt256.land old (UInt256.lnot ⟨65280⟩)

def InitializerReady (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  initializingWord σ I ≠ ⟨0⟩ ∨ σ.find? I.codeOwner = none

-- A nested initializer's saved top-level flag permits its final cleanup to be a no-op.
def InitializerNestedFlag (σ : AccountMap) (I : ExecutionEnv) (top : UInt256) : Prop :=
  top = ⟨0⟩ ∨ σ.find? I.codeOwner = none

theorem storedWord_absent {σ : AccountMap} {I : ExecutionEnv}
    (ha : σ.find? I.codeOwner = none) (slot : UInt256) : storedWord σ I slot = ⟨0⟩ := by
  simp [storedWord, ha, Option.option]

theorem storedWord_sstore_ne (σ : AccountMap) (I : ExecutionEnv)
    (readSlot writeSlot value : UInt256) (hne : readSlot ≠ writeSlot) :
    storedWord (sstoreAccountMap I.codeOwner σ writeSlot value) I readSlot =
      storedWord σ I readSlot :=
  sstoreAccountMap_storage_findD_ne σ I.codeOwner readSlot writeSlot value hne

theorem initializerReady_sstore {σ : AccountMap} {I : ExecutionEnv}
    (hr : InitializerReady σ I) (slot value : UInt256) (hs : (⟨0⟩ : UInt256) ≠ slot) :
    InitializerReady (sstoreAccountMap I.codeOwner σ slot value) I := by
  rcases hr with hi | ha
  · left
    simpa only [initializingWord, storedWord_sstore_ne σ I ⟨0⟩ slot value hs] using hi
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
