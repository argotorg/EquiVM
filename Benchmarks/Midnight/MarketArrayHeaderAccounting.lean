import Benchmarks.Midnight.MarketCalldataFirstFields
import Benchmarks.Midnight.CalldataScalarAccounting

/-! The bounds and length checks for a market's collateral calldata array. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMarketCalldataArrayHeader_accounted {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw head : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 10 ≤ 1024)
    (hsize : I.calldata.size < 2^255) (hhead : head.toNat < 2^127)
    (hoff : (calldataWord I.calldata (head.toNat + 96)).toNat < 2^64)
    (ha : MemoryAccounting mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨18661⟩
      (calldataWord I.calldata (head.toNat + 96) :: UInt256.ofNat I.calldata.size :: head :: R)
      mem aw rdata σ k C) :
    (decodeMarketData I.calldata head.toNat = none ∧ RDrev midnightBytecode g s0) ∨
    (head.toNat + (calldataWord I.calldata (head.toNat + 96)).toNat + 32 ≤ I.calldata.size ∧
      (calldataWord I.calldata
        (head.toNat + (calldataWord I.calldata (head.toNat + 96)).toNat)).toNat < 2^64 ∧
      ∃ k' C', MemoryAccounting mem aw C' ∧ RD midnightBytecode I g s0 ⟨18684⟩
        (UInt256.ofNat (pointerArrayAllocation (calldataWord I.calldata
            (head.toNat + (calldataWord I.calldata (head.toNat + 96)).toNat)).toNat) ::
          calldataWord I.calldata (head.toNat + (calldataWord I.calldata (head.toNat + 96)).toNat) ::
          (head + calldataWord I.calldata (head.toNat + 96)) ::
          UInt256.ofNat I.calldata.size :: head :: R) mem aw rdata σ k' C') := by
  let relative := calldataWord I.calldata (head.toNat + 96)
  let target := head + relative
  have ht : target.toNat = head.toNat + relative.toNat := by
    rw [uadd_toNat]
    apply Nat.mod_eq_of_lt
    change _ < 2^256
    change relative.toNat < 2^64 at hoff
    omega
  have ht31 : (target + UInt256.ofNat 31).toNat = head.toNat + relative.toNat + 31 := by
    rw [uadd_word_ofNat_toNat _ _ (by
      rw [ht]
      change _ < 2^256
      change relative.toNat < 2^64 at hoff
      omega), ht]
  by_cases hh : head.toNat + relative.toNat + 32 ≤ I.calldata.size
  · have hs : UInt256.slt (target + UInt256.ofNat 31) (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
      slt_lit_one_low hsize (by rw [ht31]; omega)
    have rd1 := midnightBlocks.midnight_block_18661_fallthrough (by omega)
      (by change UInt256.isZero (UInt256.slt (target + UInt256.ofNat 31) _) = _;
          rw [hs]; rfl) rd
    have rd2 := midnightBlocks.midnight_block_18674 (by
      simp only [List.length_cons]; omega) (by jump_dest) rd1
    change RD midnightBytecode I g s0 ⟨18477⟩
      (calldataWord I.calldata target.toNat :: ⟨18684⟩ :: calldataWord I.calldata target.toNat ::
        target :: UInt256.ofNat I.calldata.size :: head :: R) mem aw rdata σ _ _ at rd2
    rw [ht] at rd2
    have ha2 := memoryAccountingAt rd2 (by memory_account ha)
    by_cases hn : (calldataWord I.calldata (head.toNat + relative.toNat)).toNat < 2^64
    · right
      refine ⟨hh, hn, ?_⟩
      exact midnightPointerArraySize_accounted hn (by simp only [List.length_cons]; omega)
        (by jump_dest) ha2 rd2
    · left
      refine ⟨?_, ?_⟩
      · have hread := readNat_bytes hh
        have hcap : solcMaxU64 < (calldataWord I.calldata (head.toNat + relative.toNat)).toNat := by
          change 18446744073709551615 < _; omega
        simp only [decodeMarketData]
        split
        · rfl
        · split
          · rfl
          · rw [hread]
            dsimp only [bind, Option.bind]
            exact if_pos hcap
      · exact midnightPointerArrayLengthTooLarge (by omega)
          (by simp only [List.length_cons]; omega) rd2
  · left
    refine ⟨?_, ?_⟩
    · have hread := readNat_bytes_short (bytes := I.calldata)
        (off := head.toNat + relative.toNat) (by omega)
      simp [decodeMarketData, show readNat? I.calldata.toList
        (head.toNat + (calldataWord I.calldata (head.toNat + 96)).toNat) = none from hread]
    · have hs : UInt256.slt (target + UInt256.ofNat 31) (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
        slt_lit_zero hsize (by rw [ht31]; omega)
          (by rw [ht31]; change relative.toNat < 2^64 at hoff; omega)
      have rd1 := midnightBlocks.midnight_block_18661_taken (by omega)
        (by change UInt256.isZero (UInt256.slt (target + UInt256.ofNat 31) _) ≠ _;
            rw [hs]; decide) (by jump_dest) rd
      exact midnightBlocks.midnight_block_6350 (by
        simp only [midnightBlocks.midnight_block_18661_taken_stack, List.length_cons]; omega) rd1

end Benchmarks.Midnight
