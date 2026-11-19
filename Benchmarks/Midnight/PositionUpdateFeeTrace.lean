import Benchmarks.Midnight.PositionUpdateWrites
import Benchmarks.Midnight.CheckedUint128Add
import Benchmarks.Midnight.MemoryWords

/-! Checked fee-credit accumulation and the update event at the end of a position update. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightPositionUpdateFee {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root id user credit pending fee creditDecrease pendingDecrease ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 21 ≤ 1024) (hmem : 96 ≤ mem.size) (hperm : I.perm = true)
    (hroot : root.toNat < 2^64) (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hfee : fee.toNat < 2^128) (hcd : creditDecrease.toNat < 2^128) (hpd : pendingDecrease.toNat < 2^128)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 ⟨23855⟩
      ([pendingDecrease, user, solcAddrMask, ⟨96⟩, updatePositionTopic, id, creditDecrease,
        credit, ret, fee, pending] ++ R) mem aw rdata σ k C) :
    let oldFeeCredit := UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨1⟩) σ I)
      (UInt256.ofNat 128)
    (2^128 ≤ oldFeeCredit.toNat + fee.toNat ∧ RDrev midnightBytecode g s0) ∨
    (oldFeeCredit.toNat + fee.toNat < 2^128 ∧ ∃ aw' k' C',
      RD midnightBytecode I g s0 ret (fee :: pending :: credit :: R)
        (writeWordArray (twoWordHashMem id (UInt256.ofNat 1) mem) root.toNat
          [creditDecrease, pendingDecrease, fee]) aw' rdata
        (storeHigh128Accounts σ I (solcMappingSlot ⟨1⟩ id + ⟨1⟩) (oldFeeCredit + fee)) k' C') := by
  let oldFeeCredit := UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨1⟩) σ I)
    (UInt256.ofNat 128)
  change RD midnightBytecode I g s0 ⟨23855⟩
    (pendingDecrease :: user :: solcAddrMask :: ⟨96⟩ :: updatePositionTopic :: id :: creditDecrease ::
      credit :: ret :: fee :: pending :: R) mem aw rdata σ k C at rd
  have rd1 := midnightBlocks.midnight_block_23855 (by simp only [List.length_cons]; omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_23855_stack, uint128Mask_computed,
    uint128Mask_clean hfee] at rd1
  obtain ⟨k2, C2, rd2⟩ := midnightToUint128 (by simp only [List.length_cons]; omega) hfee (by jump_dest) rd1
  obtain ⟨k3, C3, rd3⟩ := midnightBlocks.midnight_block_23879
    (by simp only [List.length_cons]; omega) (by jump_dest) rd2
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 1) mem) =
      solcMappingSlot ⟨1⟩ id := twoWordHashMem_mapSlot_of_ge64 id (UInt256.ofNat 1) (by omega)
  simp only [midnightBlocks.midnight_block_23879_stack, midnightBlocks.midnight_block_23879_memory,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (UInt256.ofNat 32).toNat = 32 from rfl,
    wordAt0_fold, twoWordHash_fold, hh] at rd3
  simp only [show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl] at rd3
  change RD _ _ _ _ _ (oldFeeCredit :: _) _ _ _ _ _ _ at rd3
  by_cases hsum : oldFeeCredit.toNat + fee.toNat < 2^128
  · obtain ⟨k4, C4, rd4⟩ := midnightCheckedAdd128 (by simp only [List.length_cons]; omega)
      (shiftRight128_lt _) hfee hsum (by jump_dest) rd3
    obtain ⟨k5, C5, rd5⟩ := midnightBlocks.midnight_block_23908
      (by simp only [List.length_cons]; omega) hperm (by jump_dest) rd4
    have hcomm := u256_lor_comm (UInt256.shiftLeft (oldFeeCredit + fee) (UInt256.ofNat 128))
    dsimp only [oldFeeCredit] at hcomm
    simp only [midnightBlocks.midnight_block_23908_stack, uint128Mask_computed,
      u256_land_comm (UInt256.lnot uint128Mask), shiftLeft128_highMask,
      u256_land_comm uint128Mask, hcomm] at rd5
    have rd6 := midnightBlocks.midnight_block_23940 (by omega)
      hperm hret rd5
    have hf : memLoad (UInt256.ofNat 64) (twoWordHashMem id ⟨1⟩ mem) = root := by
      rw [memLoad_twoWordHashMem id ⟨1⟩ (UInt256.ofNat 64) (by decide) hmem, hfree]
    have h32 : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
      uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
    have h64 : (root + UInt256.ofNat 64).toNat = root.toNat + 64 :=
      uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
    have hm : midnightBlocks.midnight_block_23940_memory
        (mem := twoWordHashMem id ⟨1⟩ mem)
        (x0 := pendingDecrease) (x1 := uint128Mask) (x2 := fee) (x8 := creditDecrease) =
        writeWordArray (twoWordHashMem id ⟨1⟩ mem) root.toNat
          [creditDecrease, pendingDecrease, fee] := by
      simp only [midnightBlocks.midnight_block_23940_memory, uint128Mask_clean hcd,
        uint128Mask_clean hpd, hf, h32, h64]
      simp only [writeWordArray, Reasoning.Theory.writeWord, Nat.add_assoc]
    rw [hm] at rd6
    exact Or.inr ⟨hsum, _, _, _, rd6⟩
  · exact Or.inl ⟨Nat.le_of_not_lt hsum,
      midnightCheckedAdd128Revert (by simp only [List.length_cons]; omega)
        (shiftRight128_lt _) hfee (Nat.le_of_not_lt hsum) rd3⟩

end Benchmarks.Midnight
