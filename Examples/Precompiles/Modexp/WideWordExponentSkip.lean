import Examples.Precompiles.Modexp.WideWordExponentSetup

/-! # Exact leading-zero exponent scan -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxHeartbeats 0
set_option maxRecDepth 500000
set_option Elab.async false

def wideExponentByteAt (mem : ByteArray) (aw : UInt256)
    (baseSize start : Nat) : UInt256 :=
  UInt256.byteAt ⟨0⟩
    (wideLoadWord mem aw (UInt256.ofNat (wideExponentDataPtr baseSize + start)))

def wideExponentByte (I : ExecutionEnv)
    (baseSize exponentSize modulusSize start : Nat) : UInt256 :=
  wideExponentByteAt (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize) baseSize start

def wideSkipExponentZerosAt (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize : Nat) (start : Nat) : Nat :=
  if h : start < exponentSize then
    if wideExponentByteAt mem aw baseSize start = ⟨0⟩ then
      wideSkipExponentZerosAt mem aw baseSize exponentSize (start + 1)
    else start
  else start
termination_by exponentSize - start
decreasing_by omega

def wideSkipExponentZeros (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) (start : Nat) : Nat :=
  wideSkipExponentZerosAt (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize)
    baseSize exponentSize start

def wideSkipExponentStepsAt (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize : Nat) (start : Nat) : Nat :=
  if h : start < exponentSize then
    if wideExponentByteAt mem aw baseSize start = ⟨0⟩ then
      27 + wideSkipExponentStepsAt mem aw baseSize exponentSize (start + 1)
    else 25
  else 25
termination_by exponentSize - start
decreasing_by omega

def wideSkipExponentSteps (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) (start : Nat) : Nat :=
  wideSkipExponentStepsAt (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize)
    baseSize exponentSize start

def wideSkipExponentGasAt (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize : Nat) (start : Nat) : Nat :=
  if h : start < exponentSize then
    if wideExponentByteAt mem aw baseSize start = ⟨0⟩ then
      95 + wideSkipExponentGasAt mem aw baseSize exponentSize (start + 1)
    else 84
  else 84
termination_by exponentSize - start
decreasing_by omega

def wideSkipExponentGas (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) (start : Nat) : Nat :=
  wideSkipExponentGasAt (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize)
    baseSize exponentSize start

theorem wideSkipExponentZerosAt_bounds (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize start : Nat) (hstart : start ≤ exponentSize) :
    start ≤ wideSkipExponentZerosAt mem aw baseSize exponentSize start ∧
      wideSkipExponentZerosAt mem aw baseSize exponentSize start ≤ exponentSize := by
  by_cases hlt : start < exponentSize
  · by_cases hz : wideExponentByteAt mem aw baseSize start = ⟨0⟩
    · rw [wideSkipExponentZerosAt, dif_pos hlt, if_pos hz]
      have ih := wideSkipExponentZerosAt_bounds mem aw baseSize exponentSize (start + 1)
        (by omega)
      omega
    · rw [wideSkipExponentZerosAt, dif_pos hlt, if_neg hz]
      exact ⟨le_rfl, hstart⟩
  · rw [wideSkipExponentZerosAt, dif_neg hlt]
    exact ⟨le_rfl, hstart⟩
termination_by exponentSize - start
decreasing_by omega

private theorem skipHeaderDecodes :
    [decode runtimeBytecode ⟨2658⟩, decode runtimeBytecode ⟨2659⟩,
     decode runtimeBytecode ⟨2662⟩] =
    [some (.JUMPDEST,.none), some (.Push .PUSH2, some (⟨2748⟩,2)),
     some (.JUMPI,.none)] := by
  native_decide

private theorem skipConditionDecodes :
    [decode runtimeBytecode ⟨2748⟩, decode runtimeBytecode ⟨2749⟩,
     decode runtimeBytecode ⟨2750⟩, decode runtimeBytecode ⟨2751⟩,
     decode runtimeBytecode ⟨2752⟩, decode runtimeBytecode ⟨2753⟩,
     decode runtimeBytecode ⟨2754⟩, decode runtimeBytecode ⟨2755⟩,
     decode runtimeBytecode ⟨2756⟩, decode runtimeBytecode ⟨2757⟩,
     decode runtimeBytecode ⟨2758⟩, decode runtimeBytecode ⟨2759⟩,
     decode runtimeBytecode ⟨2760⟩, decode runtimeBytecode ⟨2761⟩,
     decode runtimeBytecode ⟨2764⟩] =
    [some (.JUMPDEST,.none), some (.SWAP3,.none), some (.SWAP1,.none),
     some (.DUP1,.none), some (.MLOAD,.none), some (.PUSH0,.none),
     some (.BYTE,.none), some (.ISZERO,.none), some (.DUP3,.none),
     some (.DUP3,.none), some (.LT,.none), some (.AND,.none),
     some (.ISZERO,.none), some (.Push .PUSH2, some (⟨2776⟩,2)),
     some (.JUMPI,.none)] := by
  native_decide

private theorem skipBodyDecodes :
    [decode runtimeBytecode ⟨2765⟩, decode runtimeBytecode ⟨2766⟩,
     decode runtimeBytecode ⟨2767⟩, decode runtimeBytecode ⟨2768⟩,
     decode runtimeBytecode ⟨2769⟩, decode runtimeBytecode ⟨2770⟩,
     decode runtimeBytecode ⟨2771⟩, decode runtimeBytecode ⟨2772⟩,
     decode runtimeBytecode ⟨2775⟩] =
    [some (.DUP4,.none), some (.ADD,.none), some (.SWAP3,.none),
     some (.DUP1,.none), some (.SWAP4,.none), some (.SWAP2,.none),
     some (.SWAP4,.none), some (.Push .PUSH2, some (⟨2658⟩,2)),
     some (.JUMP,.none)] := by
  native_decide

private theorem skipExitDecodes :
    [decode runtimeBytecode ⟨2776⟩, decode runtimeBytecode ⟨2777⟩,
     decode runtimeBytecode ⟨2778⟩, decode runtimeBytecode ⟨2779⟩,
     decode runtimeBytecode ⟨2782⟩, decode runtimeBytecode ⟨2663⟩,
     decode runtimeBytecode ⟨2664⟩] =
    [some (.JUMPDEST,.none), some (.SWAP1,.none), some (.SWAP3,.none),
     some (.Push .PUSH2, some (⟨2663⟩,2)), some (.JUMP,.none),
     some (.JUMPDEST,.none), some (.POP,.none)] := by
  native_decide

/-- Execute the compiler's leading-zero scan exactly.  Its gas expression records each skipped
zero byte rather than collapsing the loop into an OOG disjunction. -/
theorem skipWideExponentZeros
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize start : Nat}
    {baseValue modulus result ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 32)
    (hactive : wideExponentDataPtr baseSize + exponentSize + 32 ≤ 32 * aw.toNat)
    (hstart : start ≤ exponentSize) (htail : tail.length ≤ 1000)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2658⟩
      (⟨1⟩ :: ⟨1⟩ :: UInt256.ofNat (wideExponentDataPtr baseSize + start) ::
        baseValue :: UInt256.ofNat (wideExponentEnd baseSize exponentSize) ::
        modulus :: ⟨1⟩ :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2665⟩
      (UInt256.ofNat (wideExponentDataPtr baseSize +
          wideSkipExponentZerosAt mem aw baseSize exponentSize start) ::
        baseValue :: UInt256.ofNat (wideExponentEnd baseSize exponentSize) ::
        modulus :: ⟨1⟩ :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc (k + wideSkipExponentStepsAt mem aw baseSize exponentSize start)
      (C + wideSkipExponentGasAt mem aw baseSize exponentSize start) := by
  have hdH := skipHeaderDecodes
  simp only [List.cons.injEq, and_true] at hdH
  rcases hdH with ⟨hh0,hh1,hh2⟩
  have rd2748 := evm_run rd0 with [known jumpdest hh0, known push2 hh1 ⟨2748⟩,
    known jumpiT hh2 (by native_decide) jumpDest_2748]
  have hdC := skipConditionDecodes
  simp only [List.cons.injEq, and_true] at hdC
  rcases hdC with ⟨hc0,hc1,hc2,hc3,hc4,hc5,hc6,hc7,hc8,hc9,hc10,hc11,hc12,hc13,hc14⟩
  have hptr256 : wideExponentDataPtr baseSize + start < UInt256.size := by
    apply lt_of_le_of_lt
      (show wideExponentDataPtr baseSize + start ≤ 2240 by
        unfold wideExponentDataPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
    decide
  have hend256 : wideExponentEnd baseSize exponentSize < UInt256.size := by
    apply lt_of_le_of_lt
      (show wideExponentEnd baseSize exponentSize ≤ 2240 by
        unfold wideExponentEnd wideExponentDataPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
    decide
  have haccess : wideExponentDataPtr baseSize + start + 32 ≤ 32 * aw.toNat := by omega
  have rd2752 := evm_run rd2748 with [known jumpdest hc0, known swap3 hc1,
    known swap1 hc2, known dup1 hc3]
  have rd2753 := RDx.mloadWithin rd2752 hc4 (by
    rw [UInt256.toNat_ofNat_of_lt hptr256]
    exact haccess) (by simp; omega)
  have rd2764 := evm_run rd2753 with [known push0 hc5, known byte hc6,
    known iszero hc7, known dup3 hc8, known dup3 hc9, known lt hc10,
    known and hc11, known iszero hc12, known push2 hc13 ⟨2776⟩]
  by_cases hcond : start < exponentSize ∧
      wideExponentByteAt mem aw baseSize start = ⟨0⟩
  · rcases hcond with ⟨hltNat,hbyte⟩
    have hlt : UInt256.lt (UInt256.ofNat (wideExponentDataPtr baseSize + start))
        (UInt256.ofNat (wideExponentEnd baseSize exponentSize)) = ⟨1⟩ := by
      apply ult_one
      rw [UInt256.toNat_ofNat_of_lt hptr256, UInt256.toNat_ofNat_of_lt hend256]
      unfold wideExponentEnd
      omega
    have hiszero : UInt256.isZero
        (wideExponentByteAt mem aw baseSize start) = ⟨1⟩ := by
      rw [hbyte]
      native_decide
    have htest : UInt256.isZero (UInt256.land
        (UInt256.lt (UInt256.ofNat (wideExponentDataPtr baseSize + start))
          (UInt256.ofNat (wideExponentEnd baseSize exponentSize)))
        (UInt256.isZero (wideExponentByteAt mem aw baseSize start))) = ⟨0⟩ := by
      rw [hlt, hiszero]
      native_decide
    have rd2765 := rd2764.jumpiNT hc14 htest (by evm_ov)
    have hdB := skipBodyDecodes
    simp only [List.cons.injEq, and_true] at hdB
    rcases hdB with ⟨hb0,hb1,hb2,hb3,hb4,hb5,hb6,hb7,hb8⟩
    have rdNext := evm_run rd2765 with [known dup4 hb0, known add hb1,
      known swap3 hb2, known dup1 hb3, known swap4 hb4, known swap2 hb5,
      known swap4 hb6, known push2 hb7 ⟨2658⟩, known jump hb8 jumpDest_2658]
    have hnext256 : wideExponentDataPtr baseSize + start + 1 < UInt256.size := by
      unfold wideExponentEnd at hend256
      omega
    have hadd : UInt256.ofNat (wideExponentDataPtr baseSize + start) + ⟨1⟩ =
        UInt256.ofNat (wideExponentDataPtr baseSize + (start + 1)) := by
      apply u256_inj
      rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hptr256,
        show (⟨1⟩ : UInt256).toNat = 1 by decide,
        UInt256.toNat_ofNat_of_lt (by omega), Nat.mod_eq_of_lt hnext256]
      omega
    have haddLeft : ⟨1⟩ + UInt256.ofNat (wideExponentDataPtr baseSize + start) =
        UInt256.ofNat (wideExponentDataPtr baseSize + (start + 1)) := by
      rw [u256_add_comm]
      exact hadd
    rw [haddLeft] at rdNext
    have ih := skipWideExponentZeros hb he hm hactive (start := start + 1)
      (by omega) htail rdNext
    rw [wideSkipExponentZerosAt, dif_pos hltNat, if_pos hbyte,
      wideSkipExponentStepsAt, dif_pos hltNat, if_pos hbyte,
      wideSkipExponentGasAt, dif_pos hltNat, if_pos hbyte]
    exact ih.withIndices (by omega) (by omega)
  · have htest : UInt256.isZero (UInt256.land
        (UInt256.lt (UInt256.ofNat (wideExponentDataPtr baseSize + start))
          (UInt256.ofNat (wideExponentEnd baseSize exponentSize)))
        (UInt256.isZero (wideExponentByteAt mem aw baseSize start))) = ⟨1⟩ := by
      by_cases hltNat : start < exponentSize
      · have hbyte : wideExponentByteAt mem aw baseSize start ≠ ⟨0⟩ := by
          intro hz
          exact hcond ⟨hltNat, hz⟩
        have hlt : UInt256.lt (UInt256.ofNat (wideExponentDataPtr baseSize + start))
            (UInt256.ofNat (wideExponentEnd baseSize exponentSize)) = ⟨1⟩ := by
          apply ult_one
          rw [UInt256.toNat_ofNat_of_lt hptr256, UInt256.toNat_ofNat_of_lt hend256]
          unfold wideExponentEnd
          omega
        rw [hlt, isZero_eq_zero_of_ne hbyte]
        native_decide
      · have hlt : UInt256.lt (UInt256.ofNat (wideExponentDataPtr baseSize + start))
            (UInt256.ofNat (wideExponentEnd baseSize exponentSize)) = ⟨0⟩ := by
          apply ult_zero
          rw [UInt256.toNat_ofNat_of_lt hptr256, UInt256.toNat_ofNat_of_lt hend256]
          unfold wideExponentEnd
          omega
        rw [hlt]
        have hland : UInt256.land ⟨0⟩
            (UInt256.isZero (wideExponentByteAt mem aw baseSize start)) =
            ⟨0⟩ := by
          apply u256_inj
          rw [uland_toNat]
          simp
        rw [hland]
        native_decide
    have htestRaw : UInt256.isZero (UInt256.land
        (UInt256.lt (UInt256.ofNat (wideExponentDataPtr baseSize + start))
          (UInt256.ofNat (wideExponentEnd baseSize exponentSize)))
        (UInt256.isZero (UInt256.byteAt ⟨0⟩
          (wideLoadWord mem aw
            (UInt256.ofNat (wideExponentDataPtr baseSize + start)))))) = ⟨1⟩ := by
      simpa [wideExponentByteAt] using htest
    have rd2776 := rd2764.jumpiT hc14 (by rw [htestRaw]; native_decide)
      jumpDest_2776 (by evm_ov)
    have hdE := skipExitDecodes
    simp only [List.cons.injEq, and_true] at hdE
    rcases hdE with ⟨he0,he1,he2,he3,he4,he5,he6⟩
    have rd2665 := evm_run rd2776 with [known jumpdest he0, known swap1 he1,
      known swap3 he2, known push2 he3 ⟨2663⟩, known jump he4 jumpDest_2663,
      known jumpdest he5, known pop he6]
    by_cases hltNat : start < exponentSize
    · have hbyte : wideExponentByteAt mem aw baseSize start ≠ ⟨0⟩ := by
        intro hz
        exact hcond ⟨hltNat, hz⟩
      simp [wideSkipExponentZerosAt, wideSkipExponentStepsAt, wideSkipExponentGasAt,
        hltNat, hbyte]
      exact rd2665.withIndices (by omega) (by omega)
    · simp [wideSkipExponentZerosAt, wideSkipExponentStepsAt, wideSkipExponentGasAt, hltNat]
      exact rd2665.withIndices (by omega) (by omega)
termination_by exponentSize - start
decreasing_by omega

end Modexp
