import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.Authorization
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.ScratchMemory

variable {fork : Ethereum.Fork}

/-! The same caller-or-delegate bytecode sequence at the two setter entry points. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def onBehalfGuardPC (consumed : Bool) : UInt256 := if consumed then ⟨1754⟩ else ⟨3118⟩
def onBehalfReadPC (consumed : Bool) : UInt256 := if consumed then ⟨1963⟩ else ⟨3240⟩
def onBehalfCheckPC (consumed : Bool) : UInt256 := if consumed then ⟨1766⟩ else ⟨3130⟩

theorem onBehalfSelfStep (consumed : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {arg0 arg1 user : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : UInt256.isZero (UInt256.eq (UInt256.land user solcAddrMask) (solcSourceWord I)) = ⟨0⟩)
    (rd : RD fork midnightBytecode I g s0 (onBehalfGuardPC consumed)
      (user :: solcAddrMask :: arg1 :: arg0 :: R) mem aw rdata σ k C) :
    RD fork midnightBytecode I g s0 (onBehalfCheckPC consumed)
      (UInt256.eq (UInt256.land user solcAddrMask) (solcSourceWord I) :: arg0 :: arg1 ::
        UInt256.land user solcAddrMask :: R) mem aw rdata σ (k + 10) (C + 34) := by
  cases consumed
  · exact midnightBlocks.midnight_block_3118_fallthrough (by simp; omega) hcond rd
  · exact midnightBlocks.midnight_block_1754_fallthrough (by simp; omega) hcond rd

theorem onBehalfDelegateStep (consumed : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {arg0 arg1 user : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hcond : UInt256.isZero (UInt256.eq (UInt256.land user solcAddrMask) (solcSourceWord I)) ≠ ⟨0⟩)
    (rd : RD fork midnightBytecode I g s0 (onBehalfGuardPC consumed)
      (user :: solcAddrMask :: arg1 :: arg0 :: R) mem aw rdata σ k C) :
    RD fork midnightBytecode I g s0 (onBehalfReadPC consumed)
      (UInt256.eq (UInt256.land user solcAddrMask) (solcSourceWord I) :: arg0 :: arg1 ::
        UInt256.land user solcAddrMask :: R) mem aw rdata σ (k + 10) (C + 34) := by
  cases consumed
  · exact midnightBlocks.midnight_block_3118_taken (by simp; omega) hcond (by jump_dest) rd
  · exact midnightBlocks.midnight_block_1754_taken (by simp; omega) hcond (by jump_dest) rd

theorem onBehalfReadStep (consumed : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {arg0 arg1 user : UInt256} {R : List UInt256}
    {check : UInt256} (hstack : R.length + 8 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 (onBehalfReadPC consumed)
      (check :: arg0 :: arg1 :: user :: R) mem aw rdata σ k C) :
    ∃ k' C', RD fork midnightBytecode I g s0 (onBehalfCheckPC consumed)
      (midnightBlocks.midnight_block_3240_stack (ee := I) (mem := mem) (σ := σ)
        (x1 := arg0) (x2 := arg1) (x3 := user) (R := R))
      (midnightBlocks.midnight_block_3240_memory (ee := I) (mem := mem) (x3 := user))
      (M (M (M (M (M (M (M (M aw (UInt256.ofNat 800) ⟨32⟩)
        (memLoad (UInt256.ofNat 800) mem) ⟨32⟩) (UInt256.ofNat 32) ⟨32⟩)
        (UInt256.ofNat 800) ⟨32⟩)
        (memLoad (UInt256.ofNat 800) ((UInt256.ofNat 3).toByteArray.write 0
          (user.toByteArray.write 0 mem (memLoad (UInt256.ofNat 800) mem).toNat 32)
          (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 64)) ⟨0⟩ ⟨32⟩)
        (UInt256.ofNat 32) ⟨32⟩) ⟨0⟩ (UInt256.ofNat 64)) rdata σ k' C' := by
  cases consumed
  · exact midnightBlocks.midnight_block_3240 (by simp; omega) (by jump_dest) rd
  · exact midnightBlocks.midnight_block_1963 (by simp; omega) (by jump_dest) rd

theorem onBehalfTraceGuard (consumed : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {arg0 arg1 user : UInt256} {R : List UInt256}
    (hm : EntryScratch mem) (hstack : R.length + 8 ≤ 1024)
    (hcanon : user.toNat < EVM.addressModulus)
    (rd : RD fork midnightBytecode I g s0 (onBehalfGuardPC consumed) (user :: solcAddrMask :: arg1 :: arg0 :: R)
      mem aw rdata σ k C) :
    ∃ check mem' aw' k' C', EntryScratch mem' ∧
      (check ≠ ⟨0⟩ ↔ user = solcSourceWord I ∨
        UInt256.land (solcSlotWordAt (authorizationSlot user (solcSourceWord I)) σ I) ⟨255⟩ ≠ ⟨0⟩) ∧
      RD fork midnightBytecode I g s0 (onBehalfCheckPC consumed) (check :: arg0 :: arg1 :: user :: R)
        mem' aw' rdata σ k' C' := by
  by_cases hself : user = solcSourceWord I
  · have heq : UInt256.eq user (solcSourceWord I) = ⟨1⟩ := by
      rw [hself, uInt256_eq_self]
    have rd1 := onBehalfSelfStep consumed hstack
      (by rw [solcAddrMask_clean hcanon, heq]; decide) rd
    simp only [solcAddrMask_clean hcanon, heq] at rd1
    exact ⟨⟨1⟩, mem, aw, _, _, hm, by simp [hself, UInt256.size], rd1⟩
  · have heq : UInt256.eq user (solcSourceWord I) = ⟨0⟩ := u256_eq_of_ne hself
    have rd1 := onBehalfDelegateStep consumed hstack
      (by rw [solcAddrMask_clean hcanon, heq]; decide) rd
    simp only [solcAddrMask_clean hcanon] at rd1
    obtain ⟨k2, C2, rd2⟩ := onBehalfReadStep consumed hstack rd1
    have hm1 := hm.hash user (UInt256.ofNat 3)
    have hm2 := hm1.hash (solcSourceWord I) (solcMappingSlot (UInt256.ofNat 3) user)
    simp only [midnightBlocks.midnight_block_3240_stack, midnightBlocks.midnight_block_3240_memory,
      addressMask_computed, solcAddrMask_clean (solcSourceWord_canonical I), hm.zero,
      show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
      hm1.zero, hm.hashValue user (UInt256.ofNat 3),
      hm1.hashValue (solcSourceWord I) (solcMappingSlot (UInt256.ofNat 3) user)] at rd2
    exact ⟨_, _, _, _, _, hm2, by simp only [hself, false_or]; rfl, rd2⟩

end Benchmarks.Midnight
