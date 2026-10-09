import Benchmarks.Morpho.MorphoBlue.SenderAuthorizedSource
import Benchmarks.Morpho.MorphoBlue.AccrueMemoryAdvance

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def senderAuthorizedMem (ee : ExecutionEnv) (account : UInt256) (mem : ByteArray) : ByteArray :=
  if solcSourceWord ee = account then mem else
    twoWordHashMem (solcSourceWord ee) (solcMappingSlot (UInt256.ofNat 6) account)
      (twoWordHashMem account (UInt256.ofNat 6) mem)

theorem morphoSenderAuthorized {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw account ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (hc : account.toNat < EVM.addressModulus)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13096) (account :: ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (senderAuthorizedWord σ ee account :: R)
      (senderAuthorizedMem ee account mem) aw' out σ k' C' := by
  have hm : UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) account = account := by
    rw [u256_land_comm]
    exact solcAddrMask_clean hc
  by_cases heq : solcSourceWord ee = account
  · have he : UInt256.eq (UInt256.ofNat ee.source.val) account = UInt256.ofNat 1 := by
      change UInt256.eq (solcSourceWord ee) account = _
      rw [heq]; exact uInt256_eq_self _
    obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_13096_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (by rw [hm, he]; rfl) h
    dsimp only [morphoBlocks.morpho_block_13096_fallthrough_stack] at rd1
    rw [hm, he] at rd1
    simp only [senderAuthorizedWord, senderAuthorizedMem, if_pos heq]
    exact morphoBlocks.morpho_block_13129_packed (immWords := wordsOf (immStore v))
      (by omega) hvalid rd1
  · have he : UInt256.eq (UInt256.ofNat ee.source.val) account = UInt256.ofNat 0 :=
      uInt256_eq_zero_of_ne (fun he => heq (uInt256_eq_one_eq he))
    obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_13096_taken_packed
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 4 ≤ 1024; omega)
      (by rw [hm, he]; decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    dsimp only [morphoBlocks.morpho_block_13096_taken_stack] at rd1
    rw [hm, he] at rd1
    obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_13132_packed
      (immWords := wordsOf (immStore v)) (by omega) hvalid rd1
    dsimp only [morphoBlocks.morpho_block_13132_stack, morphoBlocks.morpho_block_13132_memory] at rd2
    have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem account (UInt256.ofNat 6) mem) = solcMappingSlot (UInt256.ofNat 6) account :=
      twoWordHashMem_solcMappingSlot_any _ _ _
    change RD _ _ _ _ _
      (UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem (solcSourceWord ee) (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          (twoWordHashMem account (UInt256.ofNat 6) mem)) (twoWordHashMem account (UInt256.ofNat 6) mem)))
        σ ee) (UInt256.ofNat 255) :: R)
      (twoWordHashMem (solcSourceWord ee) (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem account (UInt256.ofNat 6) mem)) (twoWordHashMem account (UInt256.ofNat 6) mem))
      _ _ _ _ _ at rd2
    rw [hh] at rd2
    have hh2 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem (solcSourceWord ee) (solcMappingSlot (UInt256.ofNat 6) account)
          (twoWordHashMem account (UInt256.ofNat 6) mem)) = authorizationSlot account (solcSourceWord ee) :=
      twoWordHashMem_solcMappingSlot_any _ _ _
    rw [hh2] at rd2
    simp only [senderAuthorizedWord, senderAuthorizedMem, if_neg heq]
    exact ⟨a2, k2, C2, rd2⟩

theorem senderAuthorizedMem_heap {mem : ByteArray} {fp : UInt256} {spare : Nat}
    (hm : MorphoHeap mem fp spare) (ee : ExecutionEnv) (account : UInt256) :
    MorphoHeap (senderAuthorizedMem ee account mem) fp spare ∧
    MemoryPrefix mem (senderAuthorizedMem ee account mem) fp.toNat := by
  unfold senderAuthorizedMem
  split
  · exact ⟨hm, MemoryPrefix.refl _ _⟩
  · exact ⟨(hm.hash account (UInt256.ofNat 6)).hash _ _,
      (twoWordHashMem_prefix _ _ _ _).trans (twoWordHashMem_prefix _ _ _ _)⟩

end Benchmarks.Morpho.MorphoBlue
