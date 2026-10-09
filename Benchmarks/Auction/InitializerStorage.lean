import Reasoning.PackedStorage
import Reasoning.EVMWord
import Benchmarks.Auction.InitializerBegin

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction


theorem initializerEntered_ready (σ : AccountMap) (I : ExecutionEnv) :
    InitializerReady (initializerEntered σ I) I := by
  by_cases hi : initializingWord σ I = ⟨0⟩
  · rw [initializerEntered, if_pos hi]
    cases ha : σ.get? I.codeOwner with
    | none =>
      rw [sstoreAccountMap_absent_same ha]
      exact Or.inr ha
    | some acc =>
      left
      rw [initializingWord, solcSlotWord_sstore_present σ I ha, initializingBeginWord]
      decide
  · rw [initializerEntered, if_neg hi]
    exact Or.inl hi

end Auction
