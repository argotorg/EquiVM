import Benchmarks.Auction.InitializeAbsentEntry

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

theorem auctionInitializerAbsentClearReturn3884 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat} (hR : R.length ≤ 1000) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g s0 ⟨3884⟩ (⟨1⟩ :: ret :: R) mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g s0 ret R mem aw rdata (cA, σ) k C := by
  have h2 := evm_run h with [push0, dup1]
  obtain ⟨_, _, h3⟩ := auctionSloadAbsent h2 hmissing (by native_decide) (by evm_ov)
  have h9 := evm_run h3 with [push2 ⟨65280⟩, not, and, swap1]
  obtain ⟨_, _, h10⟩ := auctionSstoreAbsent h9 hmissing hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run h10 with [pop, jump hret]⟩

theorem auctionInitializerAbsentClearReturn4981 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat} (hR : R.length ≤ 1000) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g s0 ⟨4981⟩ (⟨1⟩ :: ret :: R) mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g s0 ret R mem aw rdata (cA, σ) k C := by
  have h2 := evm_run h with [push0, dup1]
  obtain ⟨_, _, h3⟩ := auctionSloadAbsent h2 hmissing (by native_decide) (by evm_ov)
  have h9 := evm_run h3 with [push2 ⟨65280⟩, not, and, swap1]
  obtain ⟨_, _, h10⟩ := auctionSstoreAbsent h9 hmissing hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run h10 with [pop, jump hret]⟩

theorem auctionInitializerAbsentClearReturn5093 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat} (hR : R.length ≤ 1000) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g s0 ⟨5093⟩ (⟨1⟩ :: ret :: R) mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g s0 ret R mem aw rdata (cA, σ) k C := by
  have h2 := evm_run h with [push0, dup1]
  obtain ⟨_, _, h3⟩ := auctionSloadAbsent h2 hmissing (by native_decide) (by evm_ov)
  have h9 := evm_run h3 with [push2 ⟨65280⟩, not, and, swap1]
  obtain ⟨_, _, h10⟩ := auctionSstoreAbsent h9 hmissing hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run h10 with [pop, jump hret]⟩

theorem auctionInitializerAbsentClearReturn5200 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat} (hR : R.length ≤ 1000) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g s0 ⟨5200⟩ (⟨1⟩ :: ret :: R) mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g s0 ret R mem aw rdata (cA, σ) k C := by
  have h2 := evm_run h with [push0, dup1]
  obtain ⟨_, _, h3⟩ := auctionSloadAbsent h2 hmissing (by native_decide) (by evm_ov)
  have h9 := evm_run h3 with [push2 ⟨65280⟩, not, and, swap1]
  obtain ⟨_, _, h10⟩ := auctionSstoreAbsent h9 hmissing hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run h10 with [pop, jump hret]⟩

theorem auctionInitializerAbsentExit3877 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat} (hR : R.length ≤ 1000) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g s0 ⟨3877⟩ (⟨1⟩ :: ret :: R) mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g s0 ret R mem aw rdata (cA, σ) k C := by
  have h3884 := evm_run h with [jumpdest, dup1, iszero, push2 ⟨2850⟩, jumpiNT (by decide)]
  exact auctionInitializerAbsentClearReturn3884 hR hmissing hperm hret h3884

theorem auctionInitializeNoop_absent {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat} (hR : R.length ≤ 980) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g s0 ⟨4892⟩ (ret :: R) mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g s0 ret R mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, h4975⟩ := auctionInitializerAbsentEnter4892 (by evm_ov) hmissing hperm h
  have h4981 := evm_run h4975 with [dup1, iszero, push2 ⟨2850⟩, jumpiNT (by decide)]
  exact auctionInitializerAbsentClearReturn4981 (by omega) hmissing hperm hret h4981

theorem auctionInitializePausableUnchained_absent {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat} (hR : R.length ≤ 980) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g s0 ⟨4993⟩ (ret :: R) mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g s0 ret R mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, h5076⟩ := auctionInitializerAbsentEnter4993 (by evm_ov) hmissing hperm h
  have h5080 := evm_run h5076 with [jumpdest, push1 ⟨51⟩, dup1]
  obtain ⟨_, _, h5081⟩ := auctionSloadAbsent h5080 hmissing (by native_decide) (by evm_ov)
  have h5086 := evm_run h5081 with [push1 ⟨255⟩, not, and, swap1]
  obtain ⟨_, _, h5087⟩ := auctionSstoreAbsent h5086 hmissing hperm (by native_decide) (by evm_ov)
  have h5093 := evm_run h5087 with [dup1, iszero, push2 ⟨2850⟩, jumpiNT (by decide)]
  exact auctionInitializerAbsentClearReturn5093 (by omega) hmissing hperm hret h5093

theorem auctionInitializeReentrancyGuardUnchained_absent {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat} (hR : R.length ≤ 980) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g s0 ⟨5105⟩ (ret :: R) mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g s0 ret R mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, h5188⟩ := auctionInitializerAbsentEnter5105 (by evm_ov) hmissing hperm h
  have h5193 := evm_run h5188 with [jumpdest, push1 ⟨1⟩, push1 ⟨101⟩]
  obtain ⟨_, _, h5194⟩ := auctionSstoreAbsent h5193 hmissing hperm (by native_decide) (by evm_ov)
  have h5200 := evm_run h5194 with [dup1, iszero, push2 ⟨2850⟩, jumpiNT (by decide)]
  exact auctionInitializerAbsentClearReturn5200 (by omega) hmissing hperm hret h5200

theorem auctionInitializePausable_absent {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat} (hR : R.length ≤ 970) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g s0 ⟨3778⟩ (ret :: R) mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g s0 ret R mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, h3861⟩ := auctionInitializerAbsentEnter3778 (by evm_ov) hmissing hperm h
  have h4892 := evm_run h3861 with [
    jumpdest, push2 ⟨3869⟩, push2 ⟨4892⟩, jump (by jump_dest)]
  obtain ⟨_, _, h3869⟩ := auctionInitializeNoop_absent
    (by evm_ov) hmissing hperm (by jump_dest) h4892
  have h4993 := evm_run h3869 with [
    jumpdest, push2 ⟨3877⟩, push2 ⟨4993⟩, jump (by jump_dest)]
  obtain ⟨_, _, h3877⟩ := auctionInitializePausableUnchained_absent
    (by evm_ov) hmissing hperm (by jump_dest) h4993
  exact auctionInitializerAbsentExit3877 (by omega) hmissing hperm hret h3877

theorem auctionInitializeReentrancyGuard_absent {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat} (hR : R.length ≤ 970) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (h : RD auctionBytecode I g s0 ⟨3896⟩ (ret :: R) mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g s0 ret R mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, h3979⟩ := auctionInitializerAbsentEnter3896 (by evm_ov) hmissing hperm h
  have h5105 := evm_run h3979 with [
    jumpdest, push2 ⟨3877⟩, push2 ⟨5105⟩, jump (by jump_dest)]
  obtain ⟨_, _, h3877⟩ := auctionInitializeReentrancyGuardUnchained_absent
    (by evm_ov) hmissing hperm (by jump_dest) h5105
  exact auctionInitializerAbsentExit3877 (by omega) hmissing hperm hret h3877

end Auction
