import Benchmarks.Midnight.LiquidateEligibilityTrace
import Benchmarks.Midnight.ZeroFloorSub
import Benchmarks.Midnight.RuntimeBlocks_029

/-! The recovery-threshold comparison and the shared continuation after it succeeds. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem decodeCalldataMarket_rcfThreshold {bytes : ByteArray} {m : MarketData}
    (hd : decodeCalldataMarket bytes 4 = some m) :
    calldataWord bytes (calldataWord bytes 4 + UInt256.ofNat 164).toNat = m.rcfThreshold := by
  obtain ⟨hr, _, hdata⟩ := decodeCalldataMarket_data hd
  obtain ⟨_, _, _, _, _, cs, _, he⟩ := decodeMarketData_success hdata
  rw [he, uadd_word_ofNat_toNat _ 164 (by change _ < 2^256; omega)]
  change calldataWord bytes ((calldataWord bytes 4).toNat + 164) =
    calldataWord bytes (4 + (calldataWord bytes 4).toNat + 160)
  exact congrArg (calldataWord bytes) (by omega)

theorem midnightLiquidateRcfFinish {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw d0 d1 d2 flag pos dp dl borrower badDebt receiver mode selector : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 13 ≤ 1024)
    (hnz : flag ≠ ⟨0⟩)
    (rd : RD midnightBytecode I g s0 ⟨7150⟩
      ([d0, d1, d2, flag, pos, dp, dl, borrower, badDebt, receiver, mode, selector] ++ R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD midnightBytecode I g s0 ⟨6744⟩
      ([selector, selector, selector, selector, pos, dp, dl, borrower, badDebt, receiver,
        mode, selector] ++ R) mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_7150_fallthrough
    (R := [pos, dp, dl, borrower, badDebt, receiver, mode, selector] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (isZero_eq_zero_of_ne hnz) rd
  have rd2 := midnightBlocks.midnight_block_7159 (R := R) hstack (by jump_dest) rd1
  exact ⟨_, _, by omega, rd2⟩

theorem midnightLiquidateThreshold {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw repayable cap pos dp dl borrower badDebt receiver mode selector : UInt256}
    {m : MarketData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 13 ≤ 1024) (hd : decodeCalldataMarket I.calldata 4 = some m)
    (rd : RD midnightBytecode I g s0 ⟨7253⟩
      ([repayable, cap, pos, dp, dl, borrower, badDebt, receiver, mode, selector] ++ R)
      mem aw rdata σ k C) :
    (¬ (zeroFloorSubWord repayable cap).toNat < m.rcfThreshold.toNat ∧
      RDrev midnightBytecode g s0) ∨
    ((zeroFloorSubWord repayable cap).toNat < m.rcfThreshold.toNat ∧ ∃ k' C', C ≤ C' ∧
      RD midnightBytecode I g s0 ⟨6744⟩
        ([selector, selector, selector, selector, pos, dp, dl, borrower, badDebt, receiver,
          mode, selector] ++ R) mem aw rdata σ k' C') := by
  have rd1 := midnightBlocks.midnight_block_7253 (R := R) hstack (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_7253_stack, zeroFloorSubWord_eq,
    show (UInt256.ofNat 4).toNat = 4 from rfl] at rd1
  have ht := decodeCalldataMarket_rcfThreshold hd
  simp only [calldataWord] at ht
  rw [ht] at rd1
  by_cases hlt : (zeroFloorSubWord repayable cap).toNat < m.rcfThreshold.toNat
  · obtain ⟨k2, C2, hc2, rd2⟩ := midnightLiquidateRcfFinish (R := R) hstack
      (by rw [ult_one hlt]; decide) rd1
    exact Or.inr ⟨hlt, k2, C2, by omega, rd2⟩
  · have rr := midnightBlocks.midnight_block_7150_taken
      (R := [pos, dp, dl, borrower, badDebt, receiver, mode, selector] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by rw [ult_zero (Nat.le_of_not_gt hlt)]; decide) (by jump_dest) rd1
    exact Or.inl ⟨hlt, midnightBlocks.midnight_block_7167
      (by simp only [midnightBlocks.midnight_block_7150_taken_stack,
        List.length_append, List.length_cons, List.length_nil]; omega) rr⟩

end Benchmarks.Midnight
