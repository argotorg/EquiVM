import Benchmarks.Midnight.MulticallTailDecode
import Benchmarks.Midnight.CalldataIndex
import Benchmarks.Midnight.RuntimeBlocks_017

/-! The three direct-calldata checks at the head of a multicall iteration. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMulticallTail {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw base index : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 8 ≤ 1024)
    (hi : index.toNat < 2^64) (hspan : base.toNat + 32 * index.toNat < UInt256.size)
    (rd : RD midnightBytecode I g s0 ⟨3614⟩
      (index :: base :: multicallTailBound I.calldata base :: R) mem aw rdata σ k C) :
    (¬ MulticallTailValid I.calldata base index.toNat ∧ RDrev midnightBytecode g s0) ∨
    (MulticallTailValid I.calldata base index.toNat ∧ ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ⟨3662⟩
        (multicallTailLength I.calldata base index.toNat ::
          multicallTailPointer I.calldata base index.toNat :: index :: base ::
          multicallTailBound I.calldata base :: R) mem aw rdata σ k' C') := by
  have hslot : (base + UInt256.shiftLeft index (UInt256.ofNat 5)).toNat =
      base.toNat + 32 * index.toNat := by
    rw [u256_add_comm]
    exact calldataIndex_toNat hi hspan
  by_cases ho : UInt256.sltBool (multicallTailOffset I.calldata base index.toNat)
      (multicallTailBound I.calldata base) = true
  · have hc : UInt256.isZero (UInt256.slt
        (uInt256OfByteArray (I.calldata.readBytes
          (base + UInt256.shiftLeft index (UInt256.ofNat 5)).toNat 32))
        (multicallTailBound I.calldata base)) = UInt256.ofNat 0 := by
      rw [hslot]
      change UInt256.isZero (UInt256.fromBool
        (UInt256.sltBool (multicallTailOffset I.calldata base index.toNat)
          (multicallTailBound I.calldata base))) = _
      rw [ho]
      rfl
    have rd1 := midnightBlocks.midnight_block_3614_fallthrough (by omega) hc rd
    simp only [midnightBlocks.midnight_block_3614_fallthrough_stack, hslot] at rd1
    change RD _ _ _ _ _ (multicallTailOffset I.calldata base index.toNat :: index :: base ::
      multicallTailBound I.calldata base :: R) _ _ _ _ _ _ at rd1
    by_cases hn : (multicallTailLength I.calldata base index.toNat).toNat < 2^64
    · have hc2 : UInt256.gt (multicallTailLength I.calldata base index.toNat)
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
            (UInt256.ofNat 1)) = ⟨0⟩ := ugt_zero (by change _ ≤ 2^64 - 1; omega)
      have rd2 := midnightBlocks.midnight_block_3630_fallthrough (by simp only [List.length_cons]; omega) hc2 rd1
      change RD _ _ _ _ _ (multicallTailHead I.calldata base index.toNat ::
        multicallTailLength I.calldata base index.toNat :: index :: base ::
        multicallTailBound I.calldata base :: R) _ _ _ _ _ _ at rd2
      by_cases he : UInt256.sgtBool (multicallTailPointer I.calldata base index.toNat)
          (UInt256.sub (UInt256.ofNat I.calldata.size)
            (multicallTailLength I.calldata base index.toNat)) = false
      · have hc3 : UInt256.sgt (multicallTailPointer I.calldata base index.toNat)
            (UInt256.sub (UInt256.ofNat I.calldata.size)
              (multicallTailLength I.calldata base index.toNat)) = ⟨0⟩ := by
          rw [UInt256.sgt, he]
          rfl
        have rd3 := midnightBlocks.midnight_block_3649_fallthrough (by simp only [List.length_cons]; omega) hc3 rd2
        exact Or.inr ⟨⟨ho, hn, he⟩, _, _, by omega, rd3⟩
      · have hc3 : UInt256.sgt (multicallTailPointer I.calldata base index.toNat)
            (UInt256.sub (UInt256.ofNat I.calldata.size)
              (multicallTailLength I.calldata base index.toNat)) ≠ ⟨0⟩ := by
          rw [UInt256.sgt, Bool.eq_true_of_not_eq_false he]
          decide
        have rr := midnightBlocks.midnight_block_3649_taken (by simp only [List.length_cons]; omega) hc3 (by jump_dest) rd2
        exact Or.inl ⟨fun h ↦ he h.2.2,
          midnightBlocks.midnight_block_712 (by change R.length + 5 + 2 ≤ 1024; omega) rr⟩
    · have hc2 : UInt256.gt (multicallTailLength I.calldata base index.toNat)
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
            (UInt256.ofNat 1)) ≠ ⟨0⟩ := by
        rw [ugt_one (by change 2^64 - 1 < _; omega)]
        decide
      have rr := midnightBlocks.midnight_block_3630_taken (by simp only [List.length_cons]; omega) hc2 (by jump_dest) rd1
      exact Or.inl ⟨fun h ↦ hn h.2.1,
        midnightBlocks.midnight_block_712 (by change R.length + 5 + 2 ≤ 1024; omega) rr⟩
  · have hc : UInt256.isZero (UInt256.slt
        (uInt256OfByteArray (I.calldata.readBytes
          (base + UInt256.shiftLeft index (UInt256.ofNat 5)).toNat 32))
        (multicallTailBound I.calldata base)) ≠ UInt256.ofNat 0 := by
      rw [hslot]
      change UInt256.isZero (UInt256.fromBool
        (UInt256.sltBool (multicallTailOffset I.calldata base index.toNat)
          (multicallTailBound I.calldata base))) ≠ _
      rw [Bool.eq_false_iff.mpr ho]
      decide
    have rr := midnightBlocks.midnight_block_3614_taken (by omega) hc (by jump_dest) rd
    exact Or.inl ⟨fun h ↦ ho h.1,
      midnightBlocks.midnight_block_712 (by change R.length + 4 + 2 ≤ 1024; omega) rr⟩

end Benchmarks.Midnight
