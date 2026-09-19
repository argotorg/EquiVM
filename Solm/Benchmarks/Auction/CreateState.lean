import Solm.Benchmarks.Auction.CreateStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def createdScalarState (evm : EVM.State) (noun start finish : UInt256) : EVM.State :=
  Solm.EVM.storageStore
    (Solm.EVM.storageStore
      (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨207⟩ noun)
        evm.executionEnv.codeOwner ⟨208⟩ ⟨0⟩)
      evm.executionEnv.codeOwner ⟨209⟩ start)
    evm.executionEnv.codeOwner ⟨210⟩ finish

def createdScalarAccounts (σ : AccountMap) (I : ExecutionEnv)
    (noun start finish : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨207⟩ noun) ⟨208⟩ ⟨0⟩) ⟨209⟩ start) ⟨210⟩ finish

def createdAuctionState (evm : EVM.State) (noun start finish : UInt256) : EVM.State :=
  clearAuctionPackedState (createdScalarState evm noun start finish)

def createdAuctionAccounts (σ : AccountMap) (I : ExecutionEnv)
    (noun start finish : UInt256) : AccountMap :=
  let σ' := createdScalarAccounts σ I noun start finish
  sstoreAccountMap I.codeOwner σ' ⟨211⟩ (clearAuctionPackedWord (storedWord σ' I ⟨211⟩))

theorem SourceState.createdScalars {s0 I cA σ evm} (hs : SourceState s0 I cA σ evm)
    (noun start finish : UInt256) :
    SourceState s0 I cA (createdScalarAccounts σ I noun start finish)
      (createdScalarState evm noun start finish) := by
  unfold createdScalarState createdScalarAccounts
  rw [hs.env]
  exact (((hs.storageWrite ⟨207⟩ noun).storageWrite ⟨208⟩ ⟨0⟩).storageWrite ⟨209⟩
    start).storageWrite
    ⟨210⟩ finish

theorem SourceState.createdAuction {s0 I cA σ evm} (hs : SourceState s0 I cA σ evm)
    (noun start finish : UInt256) :
    SourceState s0 I cA (createdAuctionAccounts σ I noun start finish)
      (createdAuctionState evm noun start finish) :=
  (hs.createdScalars noun start finish).clearAuctionPacked

theorem createStorePrefix {I g s0 noun start finish ret R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨3240⟩
      (⟨0⟩ :: ⟨32⟩ :: ⟨64⟩ :: finish :: ⟨0⟩ :: start :: noun :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true) (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨3274⟩
      (⟨32⟩ :: ⟨64⟩ :: finish :: ⟨0⟩ :: start :: noun :: ret :: R)
      mem aw rdata (cA, createdAuctionAccounts σ I noun start finish) k' C' := by
  have rd3244 := evm_run h with [push1 ⟨207⟩, dup8, swap1]
  obtain ⟨_, _, rd3245⟩ := rd3244.sstore hperm (by native_decide) (by evm_ov)
  have rd3247 := evm_run rd3245 with [push1 ⟨208⟩]
  obtain ⟨_, _, rd3248⟩ := rd3247.sstore hperm (by native_decide) (by evm_ov)
  have rd3252 := evm_run rd3248 with [push1 ⟨209⟩, dup6, swap1]
  obtain ⟨_, _, rd3253⟩ := rd3252.sstore hperm (by native_decide) (by evm_ov)
  have rd3257 := evm_run rd3253 with [push1 ⟨210⟩, dup4, swap1]
  obtain ⟨_, _, rd3258⟩ := rd3257.sstore hperm (by native_decide) (by evm_ov)
  have rd3261 := evm_run rd3258 with [push1 ⟨211⟩, dup1]
  obtain ⟨_, _, rd3262⟩ := rd3261.sload (by native_decide) (by evm_ov)
  have rd3273 := evm_run rd3262 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨168⟩, shl, sub,
    not, and, swap1]
  have hmask : UInt256.lnot (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨168⟩) ⟨1⟩) =
      UInt256.lnot ⟨2 ^ 168 - 1⟩ := by native_decide
  rw [hmask, u256_land_comm (UInt256.lnot ⟨2 ^ 168 - 1⟩)] at rd3273
  exact rd3273.sstore hperm (by native_decide) (by evm_ov)

end Auction
