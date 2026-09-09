import Benchmarks.Auction.InitializeMaps

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

theorem auctionSloadAbsent {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc aw slot : UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat}
    (h : RD auctionBytecode I g s0 pc (slot :: R) mem aw rdata (cA, σ) k C)
    (hmissing : σ.find? I.codeOwner = none)
    (hdec : decode auctionBytecode pc = some (.SLOAD, none))
    (hR : R.length + 1 ≤ 1024) :
    ∃ k C, RD auctionBytecode I g s0 (pc + ⟨1⟩) (⟨0⟩ :: R) mem aw rdata (cA, σ) k C := by
  obtain ⟨k', C', h'⟩ := h.sload hdec hR
  exact ⟨k', C', by simpa only [hmissing, Option.option] using h'⟩

theorem auctionSstoreAbsent {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc aw slot val : UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat}
    (h : RD auctionBytecode I g s0 pc (slot :: val :: R) mem aw rdata (cA, σ) k C)
    (hmissing : σ.find? I.codeOwner = none) (hperm : I.perm = true)
    (hdec : decode auctionBytecode pc = some (.SSTORE, none))
    (hR : R.length ≤ 1024) :
    ∃ k C, RD auctionBytecode I g s0 (pc + ⟨1⟩) R mem aw rdata (cA, σ) k C := by
  obtain ⟨k', C', h'⟩ := h.sstore hperm hdec hR
  rw [sstoreAccountMap_absent_same hmissing] at h'
  exact ⟨k', C', h'⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializerAbsentEnter3778 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat} (hR : R.length ≤ 1000) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true)
    (h : RD auctionBytecode I g s0 ⟨3778⟩ R mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g s0 ⟨3861⟩ (⟨1⟩ :: R) mem aw rdata (cA, σ) k C := by
  have h2 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, h3⟩ := auctionSloadAbsent h2 hmissing (by native_decide) (by evm_ov)
  have h18 := evm_run h3 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1,
    push2 ⟨3801⟩, jumpiNT (by decide), pop, push0]
  obtain ⟨_, _, h19⟩ := auctionSloadAbsent h18 hmissing (by native_decide) (by evm_ov)
  have h53 := evm_run h19 with [push1 ⟨255⟩, and, iszero, jumpdest,
    push2 ⟨3829⟩, jumpiT (by decide) (by jump_dest), jumpdest, push0]
  obtain ⟨_, _, h54⟩ := auctionSloadAbsent h53 hmissing (by native_decide) (by evm_ov)
  have h71 := evm_run h54 with [push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and,
    iszero, dup1, iszero, push2 ⟨3861⟩, jumpiNT (by decide), push0, dup1]
  obtain ⟨_, _, h72⟩ := auctionSloadAbsent h71 hmissing (by native_decide) (by evm_ov)
  have h79 := evm_run h72 with [push2 ⟨65535⟩, not, and, push2 ⟨257⟩]
  have h80 := RD.lor h79 (by native_decide) (by evm_ov)
  have h82 := evm_run h80 with [swap1]
  obtain ⟨_, _, h83⟩ := auctionSstoreAbsent h82 hmissing hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, h83⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializerAbsentEnter3896 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat} (hR : R.length ≤ 1000) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true)
    (h : RD auctionBytecode I g s0 ⟨3896⟩ R mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g s0 ⟨3979⟩ (⟨1⟩ :: R) mem aw rdata (cA, σ) k C := by
  have h2 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, h3⟩ := auctionSloadAbsent h2 hmissing (by native_decide) (by evm_ov)
  have h18 := evm_run h3 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1,
    push2 ⟨3919⟩, jumpiNT (by decide), pop, push0]
  obtain ⟨_, _, h19⟩ := auctionSloadAbsent h18 hmissing (by native_decide) (by evm_ov)
  have h53 := evm_run h19 with [push1 ⟨255⟩, and, iszero, jumpdest,
    push2 ⟨3947⟩, jumpiT (by decide) (by jump_dest), jumpdest, push0]
  obtain ⟨_, _, h54⟩ := auctionSloadAbsent h53 hmissing (by native_decide) (by evm_ov)
  have h71 := evm_run h54 with [push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and,
    iszero, dup1, iszero, push2 ⟨3979⟩, jumpiNT (by decide), push0, dup1]
  obtain ⟨_, _, h72⟩ := auctionSloadAbsent h71 hmissing (by native_decide) (by evm_ov)
  have h79 := evm_run h72 with [push2 ⟨65535⟩, not, and, push2 ⟨257⟩]
  have h80 := RD.lor h79 (by native_decide) (by evm_ov)
  have h82 := evm_run h80 with [swap1]
  obtain ⟨_, _, h83⟩ := auctionSstoreAbsent h82 hmissing hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, h83⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializerAbsentEnter3987 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat} (hR : R.length ≤ 1000) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true)
    (h : RD auctionBytecode I g s0 ⟨3987⟩ R mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g s0 ⟨4070⟩ (⟨1⟩ :: R) mem aw rdata (cA, σ) k C := by
  have h2 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, h3⟩ := auctionSloadAbsent h2 hmissing (by native_decide) (by evm_ov)
  have h18 := evm_run h3 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1,
    push2 ⟨4010⟩, jumpiNT (by decide), pop, push0]
  obtain ⟨_, _, h19⟩ := auctionSloadAbsent h18 hmissing (by native_decide) (by evm_ov)
  have h53 := evm_run h19 with [push1 ⟨255⟩, and, iszero, jumpdest,
    push2 ⟨4038⟩, jumpiT (by decide) (by jump_dest), jumpdest, push0]
  obtain ⟨_, _, h54⟩ := auctionSloadAbsent h53 hmissing (by native_decide) (by evm_ov)
  have h71 := evm_run h54 with [push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and,
    iszero, dup1, iszero, push2 ⟨4070⟩, jumpiNT (by decide), push0, dup1]
  obtain ⟨_, _, h72⟩ := auctionSloadAbsent h71 hmissing (by native_decide) (by evm_ov)
  have h79 := evm_run h72 with [push2 ⟨65535⟩, not, and, push2 ⟨257⟩]
  have h80 := RD.lor h79 (by native_decide) (by evm_ov)
  have h82 := evm_run h80 with [swap1]
  obtain ⟨_, _, h83⟩ := auctionSstoreAbsent h82 hmissing hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, h83⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializerAbsentEnter4892 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat} (hR : R.length ≤ 1000) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true)
    (h : RD auctionBytecode I g s0 ⟨4892⟩ R mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g s0 ⟨4975⟩ (⟨1⟩ :: R) mem aw rdata (cA, σ) k C := by
  have h2 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, h3⟩ := auctionSloadAbsent h2 hmissing (by native_decide) (by evm_ov)
  have h18 := evm_run h3 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1,
    push2 ⟨4915⟩, jumpiNT (by decide), pop, push0]
  obtain ⟨_, _, h19⟩ := auctionSloadAbsent h18 hmissing (by native_decide) (by evm_ov)
  have h53 := evm_run h19 with [push1 ⟨255⟩, and, iszero, jumpdest,
    push2 ⟨4943⟩, jumpiT (by decide) (by jump_dest), jumpdest, push0]
  obtain ⟨_, _, h54⟩ := auctionSloadAbsent h53 hmissing (by native_decide) (by evm_ov)
  have h71 := evm_run h54 with [push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and,
    iszero, dup1, iszero, push2 ⟨3877⟩, jumpiNT (by decide), push0, dup1]
  obtain ⟨_, _, h72⟩ := auctionSloadAbsent h71 hmissing (by native_decide) (by evm_ov)
  have h79 := evm_run h72 with [push2 ⟨65535⟩, not, and, push2 ⟨257⟩]
  have h80 := RD.lor h79 (by native_decide) (by evm_ov)
  have h82 := evm_run h80 with [swap1]
  obtain ⟨_, _, h83⟩ := auctionSstoreAbsent h82 hmissing hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, h83⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializerAbsentEnter4993 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat} (hR : R.length ≤ 1000) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true)
    (h : RD auctionBytecode I g s0 ⟨4993⟩ R mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g s0 ⟨5076⟩ (⟨1⟩ :: R) mem aw rdata (cA, σ) k C := by
  have h2 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, h3⟩ := auctionSloadAbsent h2 hmissing (by native_decide) (by evm_ov)
  have h18 := evm_run h3 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1,
    push2 ⟨5016⟩, jumpiNT (by decide), pop, push0]
  obtain ⟨_, _, h19⟩ := auctionSloadAbsent h18 hmissing (by native_decide) (by evm_ov)
  have h53 := evm_run h19 with [push1 ⟨255⟩, and, iszero, jumpdest,
    push2 ⟨5044⟩, jumpiT (by decide) (by jump_dest), jumpdest, push0]
  obtain ⟨_, _, h54⟩ := auctionSloadAbsent h53 hmissing (by native_decide) (by evm_ov)
  have h71 := evm_run h54 with [push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and,
    iszero, dup1, iszero, push2 ⟨5076⟩, jumpiNT (by decide), push0, dup1]
  obtain ⟨_, _, h72⟩ := auctionSloadAbsent h71 hmissing (by native_decide) (by evm_ov)
  have h79 := evm_run h72 with [push2 ⟨65535⟩, not, and, push2 ⟨257⟩]
  have h80 := RD.lor h79 (by native_decide) (by evm_ov)
  have h82 := evm_run h80 with [swap1]
  obtain ⟨_, _, h83⟩ := auctionSstoreAbsent h82 hmissing hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, h83⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializerAbsentEnter5105 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat} (hR : R.length ≤ 1000) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true)
    (h : RD auctionBytecode I g s0 ⟨5105⟩ R mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g s0 ⟨5188⟩ (⟨1⟩ :: R) mem aw rdata (cA, σ) k C := by
  have h2 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, h3⟩ := auctionSloadAbsent h2 hmissing (by native_decide) (by evm_ov)
  have h18 := evm_run h3 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1,
    push2 ⟨5128⟩, jumpiNT (by decide), pop, push0]
  obtain ⟨_, _, h19⟩ := auctionSloadAbsent h18 hmissing (by native_decide) (by evm_ov)
  have h53 := evm_run h19 with [push1 ⟨255⟩, and, iszero, jumpdest,
    push2 ⟨5156⟩, jumpiT (by decide) (by jump_dest), jumpdest, push0]
  obtain ⟨_, _, h54⟩ := auctionSloadAbsent h53 hmissing (by native_decide) (by evm_ov)
  have h71 := evm_run h54 with [push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and,
    iszero, dup1, iszero, push2 ⟨5188⟩, jumpiNT (by decide), push0, dup1]
  obtain ⟨_, _, h72⟩ := auctionSloadAbsent h71 hmissing (by native_decide) (by evm_ov)
  have h79 := evm_run h72 with [push2 ⟨65535⟩, not, and, push2 ⟨257⟩]
  have h80 := RD.lor h79 (by native_decide) (by evm_ov)
  have h82 := evm_run h80 with [swap1]
  obtain ⟨_, _, h83⟩ := auctionSstoreAbsent h82 hmissing hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, h83⟩

set_option maxHeartbeats 1000000 in
theorem auctionInitializerAbsentEnter5212 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {R : List UInt256}
    {k C : Nat} (hR : R.length ≤ 1000) (hmissing : σ.find? I.codeOwner = none)
    (hperm : I.perm = true)
    (h : RD auctionBytecode I g s0 ⟨5212⟩ R mem aw rdata (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g s0 ⟨5295⟩ (⟨1⟩ :: R) mem aw rdata (cA, σ) k C := by
  have h2 := evm_run h with [jumpdest, push0]
  obtain ⟨_, _, h3⟩ := auctionSloadAbsent h2 hmissing (by native_decide) (by evm_ov)
  have h18 := evm_run h3 with [
    push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and, dup1,
    push2 ⟨5235⟩, jumpiNT (by decide), pop, push0]
  obtain ⟨_, _, h19⟩ := auctionSloadAbsent h18 hmissing (by native_decide) (by evm_ov)
  have h53 := evm_run h19 with [push1 ⟨255⟩, and, iszero, jumpdest,
    push2 ⟨5263⟩, jumpiT (by decide) (by jump_dest), jumpdest, push0]
  obtain ⟨_, _, h54⟩ := auctionSloadAbsent h53 hmissing (by native_decide) (by evm_ov)
  have h71 := evm_run h54 with [push2 ⟨256⟩, swap1, div, push1 ⟨255⟩, and,
    iszero, dup1, iszero, push2 ⟨5295⟩, jumpiNT (by decide), push0, dup1]
  obtain ⟨_, _, h72⟩ := auctionSloadAbsent h71 hmissing (by native_decide) (by evm_ov)
  have h79 := evm_run h72 with [push2 ⟨65535⟩, not, and, push2 ⟨257⟩]
  have h80 := RD.lor h79 (by native_decide) (by evm_ov)
  have h82 := evm_run h80 with [swap1]
  obtain ⟨_, _, h83⟩ := auctionSstoreAbsent h82 hmissing hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, h83⟩

end Auction
