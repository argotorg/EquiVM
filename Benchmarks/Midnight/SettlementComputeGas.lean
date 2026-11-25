import Benchmarks.Midnight.SettlementIntervalTrace
import Benchmarks.Midnight.SettlementInterpolationGas

variable {fork : Ethereum.Fork}

/-! Settlement-fee interval branches with cumulative execution costs. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

-- GENERALIZES settlementComputeTrace by retaining the accumulated cost.
theorem settlementComputeTrace_mono {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {word time ret : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I g s0 ⟨21863⟩ (word :: time :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD fork midnightBytecode I g s0 ret
      (settlementFeeValue word time :: R) mem aw rdata σ k' C' := by
  by_cases hlast : 31104000 ≤ time.toNat
  · have hc : UInt256.isZero (UInt256.lt time (UInt256.ofNat 31104000)) ≠ ⟨0⟩ := by
      rw [ult_zero (a := time) (b := UInt256.ofNat 31104000) hlast]; decide
    have rd1 := midnightBlocks.midnight_block_21863_taken
      (by first | omega | (simp only [List.length_cons]; omega)) hc (by jump_dest) rd
    have rd2 := midnightBlocks.midnight_block_22689_fallthrough
      (by first | omega | (simp only [List.length_cons]; omega))
      (checkedMulGuardInline (scaledSettlementFee_noOverflow word 6)) rd1
    simp only [midnightBlocks.midnight_block_22689_fallthrough_stack] at rd2
    have rd3 := midnightBlocks.midnight_block_22726
      (by first | omega | (simp only [List.length_cons]; omega)) hret rd2
    rw [settlementFeeValue, if_pos hlast]
    exact ⟨_, _, by omega, rd3⟩
  have hc : UInt256.isZero (UInt256.lt time (UInt256.ofNat 31104000)) = ⟨0⟩ := by
    rw [ult_one (a := time) (b := UInt256.ofNat 31104000)
      (by change time.toNat < 31104000; omega)]; rfl
  have rd := midnightBlocks.midnight_block_21863_fallthrough
    (by first | omega | (simp only [List.length_cons]; omega)) hc rd
  by_cases h0 : time.toNat < 86400
  · have hc : UInt256.isZero (UInt256.lt time (UInt256.ofNat 86400)) = ⟨0⟩ := by
      rw [ult_one (a := time) (b := UInt256.ofNat 86400) h0]; rfl
    have rd0 := midnightBlocks.midnight_block_21875_fallthrough
      (by first | omega | (simp only [List.length_cons]; omega)) hc rd
    have rd1 := midnightBlocks.midnight_block_21886_fallthrough
      (by first | omega | (simp only [List.length_cons]; omega))
      (by simpa only [settlementFeeWord_zero] using
        checkedMulGuardInline (scaledSettlementFee_noOverflow word 0)) rd0
    simp only [midnightBlocks.midnight_block_21886_fallthrough_stack] at rd1
    rw [← settlementFeeWord_zero word] at rd1
    have rd2 := midnightBlocks.midnight_block_21919_fallthrough
      (by first | omega | (simp only [List.length_cons]; omega))
      (checkedMulGuardInline (scaledSettlementFee_noOverflow word 1)) rd1
    simp only [midnightBlocks.midnight_block_21919_fallthrough_stack] at rd2
    have rd3 := midnightBlocks.midnight_block_21955
      (by first | omega | (simp only [List.length_cons]; omega)) rd2
    simp only [midnightBlocks.midnight_block_21955_stack] at rd3
    rw [settlementFeeValue, if_neg hlast, settlementFeeInterpolated, if_pos h0]
    obtain ⟨kf, Cf, hCf, rdf⟩ := settlementInterpolationTrace_mono
      (lower := scaledSettlementFee word 0) (upper := scaledSettlementFee word 1) hstack
      (scaledSettlementFee_lt word _)
      (scaledSettlementFee_lt word _) (by decide) (by decide)
      (by change 0 ≤ time.toNat; omega)
      (by change time.toNat ≤ 86400; omega) (by decide) hret rd3
    exact ⟨kf, Cf, by omega, rdf⟩
  have hc : UInt256.isZero (UInt256.lt time (UInt256.ofNat 86400)) ≠ ⟨0⟩ := by
    rw [ult_zero (a := time) (b := UInt256.ofNat 86400)
      (by change 86400 ≤ time.toNat; omega)]; decide
  have rd := midnightBlocks.midnight_block_21875_taken
    (by first | omega | (simp only [List.length_cons]; omega)) hc (by jump_dest) rd
  by_cases h1 : time.toNat < 604800
  · have hc : UInt256.isZero (UInt256.lt time (UInt256.ofNat 604800)) = ⟨0⟩ := by
      rw [ult_one (a := time) (b := UInt256.ofNat 604800) h1]; rfl
    have rd0 := midnightBlocks.midnight_block_22036_fallthrough
      (by first | omega | (simp only [List.length_cons]; omega)) hc rd
    have rd1 := midnightBlocks.midnight_block_22048_fallthrough
      (by first | omega | (simp only [List.length_cons]; omega))
      (checkedMulGuardInline (scaledSettlementFee_noOverflow word 1)) rd0
    simp only [midnightBlocks.midnight_block_22048_fallthrough_stack] at rd1
    have rd2 := midnightBlocks.midnight_block_22084_fallthrough
      (by first | omega | (simp only [List.length_cons]; omega))
      (checkedMulGuardInline (scaledSettlementFee_noOverflow word 2)) rd1
    simp only [midnightBlocks.midnight_block_22084_fallthrough_stack] at rd2
    have rd3 := midnightBlocks.midnight_block_22120
      (by first | omega | (simp only [List.length_cons]; omega)) rd2
    simp only [midnightBlocks.midnight_block_22120_stack] at rd3
    have rd4 := midnightBlocks.midnight_block_22161
      (by first | omega | (simp only [List.length_cons]; omega)) (by jump_dest) rd3
    simp only [midnightBlocks.midnight_block_22161_stack] at rd4
    rw [settlementFeeValue, if_neg hlast, settlementFeeInterpolated, if_neg h0, if_pos h1]
    obtain ⟨kf, Cf, hCf, rdf⟩ := settlementInterpolationTrace_mono
      (lower := scaledSettlementFee word 1) (upper := scaledSettlementFee word 2) hstack
      (scaledSettlementFee_lt word _)
      (scaledSettlementFee_lt word _) (by decide) (by decide)
      (by change 86400 ≤ time.toNat; omega)
      (by change time.toNat ≤ 604800; omega) (by decide) hret rd4
    exact ⟨kf, Cf, by omega, rdf⟩
  have hc : UInt256.isZero (UInt256.lt time (UInt256.ofNat 604800)) ≠ ⟨0⟩ := by
    rw [ult_zero (a := time) (b := UInt256.ofNat 604800)
      (by change 604800 ≤ time.toNat; omega)]; decide
  have rd := midnightBlocks.midnight_block_22036_taken
    (by first | omega | (simp only [List.length_cons]; omega)) hc (by jump_dest) rd
  by_cases h2 : time.toNat < 2592000
  · have hc : UInt256.isZero (UInt256.lt time (UInt256.ofNat 2592000)) = ⟨0⟩ := by
      rw [ult_one (a := time) (b := UInt256.ofNat 2592000) h2]; rfl
    have rd0 := midnightBlocks.midnight_block_22170_fallthrough
      (by first | omega | (simp only [List.length_cons]; omega)) hc rd
    have rd1 := midnightBlocks.midnight_block_22182_fallthrough
      (by first | omega | (simp only [List.length_cons]; omega))
      (checkedMulGuardInline (scaledSettlementFee_noOverflow word 2)) rd0
    simp only [midnightBlocks.midnight_block_22182_fallthrough_stack] at rd1
    have rd2 := midnightBlocks.midnight_block_22218_fallthrough
      (by first | omega | (simp only [List.length_cons]; omega))
      (checkedMulGuardInline (scaledSettlementFee_noOverflow word 3)) rd1
    simp only [midnightBlocks.midnight_block_22218_fallthrough_stack] at rd2
    have rd3 := midnightBlocks.midnight_block_22253
      (by first | omega | (simp only [List.length_cons]; omega)) rd2
    simp only [midnightBlocks.midnight_block_22253_stack] at rd3
    have rd4 := midnightBlocks.midnight_block_22293
      (by first | omega | (simp only [List.length_cons]; omega)) (by jump_dest) rd3
    simp only [midnightBlocks.midnight_block_22293_stack] at rd4
    have rd5 := midnightBlocks.midnight_block_22161
      (by first | omega | (simp only [List.length_cons]; omega)) (by jump_dest) rd4
    simp only [midnightBlocks.midnight_block_22161_stack] at rd5
    rw [settlementFeeValue, if_neg hlast, settlementFeeInterpolated, if_neg h0, if_neg h1,
      if_pos h2]
    obtain ⟨kf, Cf, hCf, rdf⟩ := settlementInterpolationTrace_mono
      (lower := scaledSettlementFee word 2) (upper := scaledSettlementFee word 3) hstack
      (scaledSettlementFee_lt word _)
      (scaledSettlementFee_lt word _) (by decide) (by decide)
      (by change 604800 ≤ time.toNat; omega)
      (by change time.toNat ≤ 2592000; omega) (by decide) hret rd5
    exact ⟨kf, Cf, by omega, rdf⟩
  have hc : UInt256.isZero (UInt256.lt time (UInt256.ofNat 2592000)) ≠ ⟨0⟩ := by
    rw [ult_zero (a := time) (b := UInt256.ofNat 2592000)
      (by change 2592000 ≤ time.toNat; omega)]; decide
  have rd := midnightBlocks.midnight_block_22170_taken
    (by first | omega | (simp only [List.length_cons]; omega)) hc (by jump_dest) rd
  by_cases h3 : time.toNat < 7776000
  · have hc : UInt256.isZero (UInt256.lt time (UInt256.ofNat 7776000)) = ⟨0⟩ := by
      rw [ult_one (a := time) (b := UInt256.ofNat 7776000) h3]; rfl
    have rd0 := midnightBlocks.midnight_block_22302_fallthrough
      (by first | omega | (simp only [List.length_cons]; omega)) hc rd
    have rd1 := midnightBlocks.midnight_block_22314_fallthrough
      (by first | omega | (simp only [List.length_cons]; omega))
      (checkedMulGuardInline (scaledSettlementFee_noOverflow word 3)) rd0
    simp only [midnightBlocks.midnight_block_22314_fallthrough_stack] at rd1
    have rd2 := midnightBlocks.midnight_block_22350_fallthrough
      (by first | omega | (simp only [List.length_cons]; omega))
      (checkedMulGuardInline (scaledSettlementFee_noOverflow word 4)) rd1
    simp only [midnightBlocks.midnight_block_22350_fallthrough_stack] at rd2
    have rd3 := midnightBlocks.midnight_block_22386
      (by first | omega | (simp only [List.length_cons]; omega)) rd2
    simp only [midnightBlocks.midnight_block_22386_stack] at rd3
    have rd4 := midnightBlocks.midnight_block_22427
      (by first | omega | (simp only [List.length_cons]; omega)) (by jump_dest) rd3
    simp only [midnightBlocks.midnight_block_22427_stack] at rd4
    have rd5 := midnightBlocks.midnight_block_22293
      (by first | omega | (simp only [List.length_cons]; omega)) (by jump_dest) rd4
    simp only [midnightBlocks.midnight_block_22293_stack] at rd5
    have rd6 := midnightBlocks.midnight_block_22161
      (by first | omega | (simp only [List.length_cons]; omega)) (by jump_dest) rd5
    simp only [midnightBlocks.midnight_block_22161_stack] at rd6
    rw [settlementFeeValue, if_neg hlast, settlementFeeInterpolated, if_neg h0, if_neg h1,
      if_neg h2, if_pos h3]
    obtain ⟨kf, Cf, hCf, rdf⟩ := settlementInterpolationTrace_mono
      (lower := scaledSettlementFee word 3) (upper := scaledSettlementFee word 4) hstack
      (scaledSettlementFee_lt word _)
      (scaledSettlementFee_lt word _) (by decide) (by decide)
      (by change 2592000 ≤ time.toNat; omega)
      (by change time.toNat ≤ 7776000; omega) (by decide) hret rd6
    exact ⟨kf, Cf, by omega, rdf⟩
  have hc : UInt256.isZero (UInt256.lt time (UInt256.ofNat 7776000)) ≠ ⟨0⟩ := by
    rw [ult_zero (a := time) (b := UInt256.ofNat 7776000)
      (by change 7776000 ≤ time.toNat; omega)]; decide
  have rd := midnightBlocks.midnight_block_22302_taken
    (by first | omega | (simp only [List.length_cons]; omega)) hc (by jump_dest) rd
  by_cases h4 : time.toNat < 15552000
  · have hc : UInt256.isZero (UInt256.lt time (UInt256.ofNat 15552000)) = ⟨0⟩ := by
      rw [ult_one (a := time) (b := UInt256.ofNat 15552000) h4]; rfl
    have rd0 := midnightBlocks.midnight_block_22436_fallthrough
      (by first | omega | (simp only [List.length_cons]; omega)) hc rd
    have rd1 := midnightBlocks.midnight_block_22448_fallthrough
      (by first | omega | (simp only [List.length_cons]; omega))
      (checkedMulGuardInline (scaledSettlementFee_noOverflow word 4)) rd0
    simp only [midnightBlocks.midnight_block_22448_fallthrough_stack] at rd1
    have rd2 := midnightBlocks.midnight_block_22484_fallthrough
      (by first | omega | (simp only [List.length_cons]; omega))
      (checkedMulGuardInline (scaledSettlementFee_noOverflow word 5)) rd1
    simp only [midnightBlocks.midnight_block_22484_fallthrough_stack] at rd2
    have rd3 := midnightBlocks.midnight_block_22520
      (by first | omega | (simp only [List.length_cons]; omega)) rd2
    simp only [midnightBlocks.midnight_block_22520_stack] at rd3
    have rd4 := midnightBlocks.midnight_block_22561
      (by first | omega | (simp only [List.length_cons]; omega)) (by jump_dest) rd3
    simp only [midnightBlocks.midnight_block_22561_stack] at rd4
    have rd5 := midnightBlocks.midnight_block_22427
      (by first | omega | (simp only [List.length_cons]; omega)) (by jump_dest) rd4
    simp only [midnightBlocks.midnight_block_22427_stack] at rd5
    have rd6 := midnightBlocks.midnight_block_22293
      (by first | omega | (simp only [List.length_cons]; omega)) (by jump_dest) rd5
    simp only [midnightBlocks.midnight_block_22293_stack] at rd6
    have rd7 := midnightBlocks.midnight_block_22161
      (by first | omega | (simp only [List.length_cons]; omega)) (by jump_dest) rd6
    simp only [midnightBlocks.midnight_block_22161_stack] at rd7
    rw [settlementFeeValue, if_neg hlast, settlementFeeInterpolated, if_neg h0, if_neg h1,
      if_neg h2, if_neg h3, if_pos h4]
    obtain ⟨kf, Cf, hCf, rdf⟩ := settlementInterpolationTrace_mono
      (lower := scaledSettlementFee word 4) (upper := scaledSettlementFee word 5) hstack
      (scaledSettlementFee_lt word _)
      (scaledSettlementFee_lt word _) (by decide) (by decide)
      (by change 7776000 ≤ time.toNat; omega)
      (by change time.toNat ≤ 15552000; omega) (by decide) hret rd7
    exact ⟨kf, Cf, by omega, rdf⟩
  have hc : UInt256.isZero (UInt256.lt time (UInt256.ofNat 15552000)) ≠ ⟨0⟩ := by
    rw [ult_zero (a := time) (b := UInt256.ofNat 15552000)
      (by change 15552000 ≤ time.toNat; omega)]; decide
  have rd := midnightBlocks.midnight_block_22436_taken
    (by first | omega | (simp only [List.length_cons]; omega)) hc (by jump_dest) rd
  have rd0 := rd
  have rd1 := midnightBlocks.midnight_block_22570_fallthrough
    (by first | omega | (simp only [List.length_cons]; omega))
    (checkedMulGuardInline (scaledSettlementFee_noOverflow word 5)) rd0
  simp only [midnightBlocks.midnight_block_22570_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_22607_fallthrough
    (by first | omega | (simp only [List.length_cons]; omega))
    (checkedMulGuardInline (scaledSettlementFee_noOverflow word 6)) rd1
  simp only [midnightBlocks.midnight_block_22607_fallthrough_stack] at rd2
  have rd3 := midnightBlocks.midnight_block_22643
    (by first | omega | (simp only [List.length_cons]; omega)) (by jump_dest) rd2
  simp only [midnightBlocks.midnight_block_22643_stack] at rd3
  have rd4 := midnightBlocks.midnight_block_22561
    (by first | omega | (simp only [List.length_cons]; omega)) (by jump_dest) rd3
  simp only [midnightBlocks.midnight_block_22561_stack] at rd4
  have rd5 := midnightBlocks.midnight_block_22427
    (by first | omega | (simp only [List.length_cons]; omega)) (by jump_dest) rd4
  simp only [midnightBlocks.midnight_block_22427_stack] at rd5
  have rd6 := midnightBlocks.midnight_block_22293
    (by first | omega | (simp only [List.length_cons]; omega)) (by jump_dest) rd5
  simp only [midnightBlocks.midnight_block_22293_stack] at rd6
  have rd7 := midnightBlocks.midnight_block_22161
    (by first | omega | (simp only [List.length_cons]; omega)) (by jump_dest) rd6
  simp only [midnightBlocks.midnight_block_22161_stack] at rd7
  rw [settlementFeeValue, if_neg hlast, settlementFeeInterpolated, if_neg h0, if_neg h1,
    if_neg h2, if_neg h3, if_neg h4]
  obtain ⟨kf, Cf, hCf, rdf⟩ := settlementInterpolationTrace_mono
    (lower := scaledSettlementFee word 5) (upper := scaledSettlementFee word 6) hstack
    (scaledSettlementFee_lt word _)
    (scaledSettlementFee_lt word _) (by decide) (by decide)
    (by change 15552000 ≤ time.toNat; omega)
    (by change time.toNat ≤ 31104000; omega) (by decide) hret rd7
  exact ⟨kf, Cf, by omega, rdf⟩


end Benchmarks.Midnight
