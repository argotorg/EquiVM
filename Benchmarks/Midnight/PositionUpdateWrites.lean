import Benchmarks.Midnight.PositionUpdateStorage
import Benchmarks.Midnight.PositionUpdateDecrease
import Benchmarks.Midnight.MappingMemory

variable {fork : Ethereum.Fork}

/-! The four ordered field writes in the internal position update. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightPositionUpdateWrites {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id user credit pending fee creditDecrease pendingDecrease ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024) (hmem : 64 ≤ mem.size) (hperm : I.perm = true)
    (rd : RD fork midnightBytecode I g s0 ⟨23723⟩
      ([pendingDecrease, ⟨23855⟩, positionSlot id user, user, solcAddrMask, ⟨96⟩,
        updatePositionTopic, id, creditDecrease, credit, ret, fee, pending] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ⟨23855⟩
      ([pendingDecrease, user, solcAddrMask, ⟨96⟩, updatePositionTopic, id, creditDecrease,
        credit, ret, fee, pending] ++ R)
      (twoWordHashMem id (UInt256.ofNat 1) mem) aw' rdata
      (positionUpdateAccounts σ I id user credit pending) k' C' := by
  change RD fork midnightBytecode I g s0 ⟨23723⟩
    (pendingDecrease :: ⟨23855⟩ :: positionSlot id user :: user :: solcAddrMask :: ⟨96⟩ ::
      updatePositionTopic :: id :: creditDecrease :: credit :: ret :: fee :: pending :: R)
    mem aw rdata σ k C at rd
  obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_23723 hstack hperm rd
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 1) mem) =
      solcMappingSlot ⟨1⟩ id := twoWordHashMem_mapSlot_of_ge64 id (UInt256.ofNat 1) hmem
  simp only [midnightBlocks.midnight_block_23723_stack, midnightBlocks.midnight_block_23723_memory,
    uint128Mask_computed, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold, hh] at rd1
  obtain ⟨k2, C2, rd2⟩ := midnightBlocks.midnight_block_23809
    (by simp only [List.length_cons]; omega) hperm (by jump_dest) rd1
  simp only [midnightBlocks.midnight_block_23809_stack, shiftLeft128_highMask] at rd2
  obtain ⟨k3, C3, rd3⟩ := midnightBlocks.midnight_block_23825
    (by simp only [List.length_cons]; omega) hperm (by jump_dest) rd2
  simp only [midnightBlocks.midnight_block_23825_stack, uint128Mask_computed,
    u256_land_comm (UInt256.lnot uint128Mask), shiftLeft128_highMask,
    u256_land_comm uint128Mask, u256_lor_comm (UInt256.shiftLeft (UInt256.ofNat I.header.timestamp)
      (UInt256.ofNat 128))] at rd3
  exact ⟨_, _, _, rd3⟩

theorem midnightPositionUpdateStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id user credit pending fee creditDecrease pendingDecrease ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024) (hperm : I.perm = false)
    (rd : RD fork midnightBytecode I g s0 ⟨23723⟩
      ([pendingDecrease, ⟨23855⟩, positionSlot id user, user, solcAddrMask, ⟨96⟩,
        updatePositionTopic, id, creditDecrease, credit, ret, fee, pending] ++ R) mem aw rdata σ k C) :
    RDstatic fork midnightBytecode g s0 := by
  change RD fork midnightBytecode I g s0 ⟨23723⟩
    (pendingDecrease :: ⟨23855⟩ :: positionSlot id user :: user :: solcAddrMask :: ⟨96⟩ ::
      updatePositionTopic :: id :: creditDecrease :: credit :: ret :: fee :: pending :: R)
    mem aw rdata σ k C at rd
  have r1 := rd.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.dup11 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r13 := r12.shl (by native_decide) (by evm_ov)
  have r14 := r13.sub (by native_decide) (by evm_ov)
  have r15 := r14.not (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r17⟩ := RD.sload r16 (by native_decide) (by evm_ov)
  have r18 := r17.and (by native_decide) (by evm_ov)
  have r19 := r18.or (by native_decide) (by evm_ov)
  have r20 := r19.dup2 (by native_decide) (by evm_ov)
  exact r20.sstoreStatic hperm (by native_decide) (by evm_ov)

end Benchmarks.Midnight
