import Examples.Precompiles.Modexp.Trivial

/-!
# Exact fixed-start base-prefix scanner

The deployed runtime contains a second copy of the nonzero-range loop proved in `Range.lean`.
This copy starts at calldata offset 96 and accepts only the exclusive end offset.  Its pure result
and path-dependent gas are therefore the existing `cdRangeReference` and `cdRangeGas` functions.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem base_ofNat_toNat {n : Nat} (hn : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := UInt256.toNat_ofNat_of_lt hn

private theorem base_ofNat_sub {p end_ : Nat} (hp : p ≤ end_) (hend : end_ < UInt256.size) :
    UInt256.sub (UInt256.ofNat end_) (UInt256.ofNat p) = UInt256.ofNat (end_ - p) := by
  apply u256_inj
  rw [usub_ofNat_lit_toNat hp hend,
    base_ofNat_toNat (lt_of_le_of_lt (Nat.sub_le _ _) hend)]

private theorem base_ofNat_add32 {p : Nat} (hp : p + 32 < UInt256.size) :
    UInt256.ofNat p + (⟨32⟩ : UInt256) = UInt256.ofNat (p + 32) := by
  apply u256_inj
  rw [uadd_word_lit32_toNat _ (by rw [base_ofNat_toNat (by omega)]; omega),
    base_ofNat_toNat (by omega), base_ofNat_toNat hp]

private theorem baseRangeHeaderExitDecodes :
    [decode runtimeBytecode ⟨631⟩, decode runtimeBytecode ⟨632⟩,
      decode runtimeBytecode ⟨633⟩, decode runtimeBytecode ⟨634⟩,
      decode runtimeBytecode ⟨635⟩, decode runtimeBytecode ⟨638⟩,
      decode runtimeBytecode ⟨639⟩, decode runtimeBytecode ⟨640⟩,
      decode runtimeBytecode ⟨641⟩] =
    [some (.JUMPDEST, .none), some (.DUP2, .none), some (.DUP2, .none),
      some (.LT, .none), some (.Push .PUSH2, some (⟨642⟩, 2)), some (.JUMPI, .none),
      some (.POP, .none), some (.POP, .none), some (.JUMP, .none)] := by
  native_decide

private theorem baseRangeBodyDecodes :
    [decode runtimeBytecode ⟨642⟩, decode runtimeBytecode ⟨643⟩,
      decode runtimeBytecode ⟨644⟩, decode runtimeBytecode ⟨645⟩,
      decode runtimeBytecode ⟨646⟩, decode runtimeBytecode ⟨647⟩,
      decode runtimeBytecode ⟨648⟩, decode runtimeBytecode ⟨650⟩,
      decode runtimeBytecode ⟨651⟩, decode runtimeBytecode ⟨652⟩,
      decode runtimeBytecode ⟨655⟩] =
    [some (.JUMPDEST, .none), some (.DUP1, .none), some (.CALLDATALOAD, .none),
      some (.DUP2, .none), some (.DUP4, .none), some (.SUB, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.DUP2, .none), some (.LT, .none),
      some (.Push .PUSH2, some (⟨681⟩, 2)), some (.JUMPI, .none)] := by
  native_decide

private theorem baseRangeFullDecodes :
    [decode runtimeBytecode ⟨656⟩, decode runtimeBytecode ⟨657⟩,
      decode runtimeBytecode ⟨658⟩, decode runtimeBytecode ⟨661⟩,
      decode runtimeBytecode ⟨662⟩, decode runtimeBytecode ⟨663⟩,
      decode runtimeBytecode ⟨665⟩, decode runtimeBytecode ⟨666⟩,
      decode runtimeBytecode ⟨669⟩,
      decode runtimeBytecode ⟨670⟩, decode runtimeBytecode ⟨671⟩,
      decode runtimeBytecode ⟨672⟩, decode runtimeBytecode ⟨674⟩,
      decode runtimeBytecode ⟨675⟩, decode runtimeBytecode ⟨676⟩,
      decode runtimeBytecode ⟨677⟩, decode runtimeBytecode ⟨680⟩] =
    [some (.JUMPDEST, .none), some (.POP, .none),
      some (.Push .PUSH2, some (⟨670⟩, 2)), some (.JUMPI, .none),
      some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.ADD, .none), some (.Push .PUSH2, some (⟨631⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.POP, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)), some (.SWAP3, .none), some (.POP, .none),
      some (.DUP1, .none), some (.Push .PUSH2, some (⟨662⟩, 2)),
      some (.JUMP, .none)] := by
  native_decide

private theorem baseRangePartialDecodes :
    [decode runtimeBytecode ⟨681⟩, decode runtimeBytecode ⟨682⟩,
      decode runtimeBytecode ⟨684⟩, decode runtimeBytecode ⟨685⟩,
      decode runtimeBytecode ⟨687⟩, decode runtimeBytecode ⟨688⟩,
      decode runtimeBytecode ⟨689⟩, decode runtimeBytecode ⟨690⟩,
      decode runtimeBytecode ⟨693⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.SUB, .none), some (.Push .PUSH1, some (⟨3⟩, 1)), some (.SHL, .none),
      some (.SHR, .none), some (.PUSH0, .none),
      some (.Push .PUSH2, some (⟨656⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem baseRangeExit {cA gh bl σ σ₀ A I} {g : Sat256}
    {p end_ ret : Nat} {nz : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1017)
    (hp : p < UInt256.size) (hend : end_ < UInt256.size) (hstop : end_ ≤ p)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨631⟩
      ([UInt256.ofNat p, UInt256.ofNat end_, UInt256.ofNat ret, nz] ++ tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (nz :: tail) mem aw rdata acc (k + 9) (C + 35) := by
  simp only [List.cons_append, List.nil_append] at rd0
  have hd := baseRangeHeaderExitDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8⟩
  have hlt : UInt256.lt (UInt256.ofNat p) (UInt256.ofNat end_) = ⟨0⟩ := by
    apply ult_zero
    rw [base_ofNat_toNat hp, base_ofNat_toNat hend]
    exact hstop
  have rd := evm_run rd0 with [
    known jumpdest hd0, known dup2 hd1, known dup2 hd2, known lt hd3,
    known push2 hd4 ⟨642⟩, known jumpiNT hd5 hlt,
    known pop hd6, known pop hd7, known jump hd8 hret ]
  exact (rd.withPC rfl).withIndices (by omega) (by omega)

private theorem baseRangeReachTest {cA gh bl σ σ₀ A I} {g : Sat256}
    {p end_ ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1016) (hend : end_ + 32 < UInt256.size) (hp : p < end_)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨631⟩
      ([UInt256.ofNat p, UInt256.ofNat end_, UInt256.ofNat ret, ⟨0⟩] ++ tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨658⟩
      (cdRangeChunk I p end_ :: UInt256.ofNat p :: UInt256.ofNat end_ ::
        UInt256.ofNat ret :: ⟨0⟩ :: tail)
      mem aw rdata acc k' (C + if end_ - p < 32 then 93 else 64) := by
  simp only [List.cons_append, List.nil_append] at rd0
  have hh := baseRangeHeaderExitDecodes
  simp only [List.cons.injEq, and_true] at hh
  rcases hh with ⟨hh0, hh1, hh2, hh3, hh4, hh5, _, _, _⟩
  have hb := baseRangeBodyDecodes
  simp only [List.cons.injEq, and_true] at hb
  rcases hb with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10⟩
  have hf := baseRangeFullDecodes
  simp only [List.cons.injEq, and_true] at hf
  rcases hf with ⟨hf0, hf1, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hpBound : p < UInt256.size := by omega
  have hendBound : end_ < UInt256.size := by omega
  have hlt : UInt256.lt (UInt256.ofNat p) (UInt256.ofNat end_) = ⟨1⟩ := by
    apply ult_one
    rw [base_ofNat_toNat hpBound, base_ofNat_toNat hendBound]
    exact hp
  have rdHead := evm_run rd0 with [
    known jumpdest hh0, known dup2 hh1, known dup2 hh2, known lt hh3,
    known push2 hh4 ⟨642⟩, known jumpiT hh5 (by rw [hlt]; decide) jumpDest_642 ]
  have rdBody := evm_run rdHead with [
    known jumpdest hb0, known dup1 hb1, known calldataload hb2,
    known dup2 hb3, known dup4 hb4, known sub hb5,
    known push1 hb6 ⟨32⟩, known dup2 hb7, known lt hb8,
    known push2 hb9 ⟨681⟩ ]
  have hsub := base_ofNat_sub hp.le hendBound
  rw [hsub] at rdBody
  have hremBound : end_ - p < UInt256.size := lt_of_le_of_lt (Nat.sub_le _ _) hendBound
  by_cases hpartial : end_ - p < 32
  · have hltRem : UInt256.lt (UInt256.ofNat (end_ - p)) ⟨32⟩ = ⟨1⟩ := by
      apply ult_one
      rw [base_ofNat_toNat hremBound, show (⟨32⟩ : UInt256).toNat = 32 by decide]
      simpa using hpartial
    have rdPartial := rdBody.jumpiT hb10 (by rw [hltRem]; decide) jumpDest_681 (by evm_ov)
    have hpdec := baseRangePartialDecodes
    simp only [List.cons.injEq, and_true] at hpdec
    rcases hpdec with ⟨hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8⟩
    have rdP := evm_run rdPartial with [
      known jumpdest hp0, known push1 hp1 ⟨32⟩, known sub hp2,
      known push1 hp3 ⟨3⟩, known shl hp4, known shr hp5, known push0 hp6,
      known push2 hp7 ⟨656⟩, known jump hp8 jumpDest_656,
      known jumpdest hf0, known pop hf1 ]
    refine ⟨k + 28, ?_⟩
    simpa [cdRangeChunk, hpartial] using
      (rdP.withPC (by native_decide)).withIndices rfl (by omega)
  · have hltRem : UInt256.lt (UInt256.ofNat (end_ - p)) ⟨32⟩ = ⟨0⟩ := by
      apply ult_zero
      rw [base_ofNat_toNat hremBound, show (⟨32⟩ : UInt256).toNat = 32 by decide]
      omega
    have rdFull := rdBody.jumpiNT hb10 hltRem (by evm_ov)
    have rdF := evm_run rdFull with [known jumpdest hf0, known pop hf1]
    refine ⟨k + 19, ?_⟩
    simpa [cdRangeChunk, hpartial] using
      (rdF.withPC (by native_decide)).withIndices rfl (by omega)

/-- Execute the fixed-start scanner loop from PC 631. -/
theorem baseRangeLoopExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {p end_ ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1016) (hend : end_ + 32 < UInt256.size)
    (hpBound : p ≤ end_ + 32)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨631⟩
      ([UInt256.ofNat p, UInt256.ofNat end_, UInt256.ofNat ret, ⟨0⟩] ++ tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat ret) (UInt256.ofNat (cdRangeResult I p end_) :: tail)
      mem aw rdata acc k' (C + cdRangeGas I p end_) := by
  generalize hn : end_ - p = n
  induction n using Nat.strong_induction_on generalizing p k C
  rename_i n ih
  by_cases hp : p < end_
  · obtain ⟨kTest, rdTest⟩ := baseRangeReachTest htail hend hp rd0
    have hf := baseRangeFullDecodes
    simp only [List.cons.injEq, and_true] at hf
    rcases hf with ⟨_, _, hf2, hf3, hf4, hf5, hf6, hf7, hf8,
      hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16⟩
    by_cases hzero : cdRangeChunk I p end_ = ⟨0⟩
    · have rdAtInc := evm_run rdTest with [
        known push2 hf2 ⟨670⟩, known jumpiNT hf3 hzero ]
      have rdNext := evm_run rdAtInc with [
        known jumpdest hf4, known push1 hf5 ⟨32⟩, known add hf6,
        known push2 hf7 ⟨631⟩, known jump hf8 jumpDest_631 ]
      have hpNext : p + 32 ≤ end_ + 32 := by omega
      have hadd := base_ofNat_add32 (p := p) (by omega)
      have htop : (⟨32⟩ : UInt256) + UInt256.ofNat p = UInt256.ofNat (p + 32) :=
        (u256_add_comm _ _).trans hadd
      have rdNext' := rdNext.withStack
        (congrArg (fun x => x :: UInt256.ofNat end_ :: UInt256.ofNat ret :: ⟨0⟩ :: tail) htop)
      have hdecrease : end_ - (p + 32) < n := by omega
      obtain ⟨kFinal, rdFinal⟩ := ih _ hdecrease
        (p := p + 32) (k := _) (C := _) hpNext rdNext' rfl
      refine ⟨kFinal, ?_⟩
      rw [cdRangeResult, dif_pos hp, if_pos hzero,
        cdRangeGas, dif_pos hp, if_pos hzero]
      exact rdFinal.withIndices rfl (by split <;> omega)
    · have rdAtFound := evm_run rdTest with [
        known push2 hf2 ⟨670⟩, known jumpiT hf3 hzero jumpDest_670 ]
      have rdFound := evm_run rdAtFound with [
        known jumpdest hf9, known pop hf10, known push1 hf11 ⟨1⟩,
        known swap3 hf12, known pop hf13, known dup1 hf14,
        known push2 hf15 ⟨662⟩, known jump hf16 jumpDest_662,
        known jumpdest hf4, known push1 hf5 ⟨32⟩, known add hf6,
        known push2 hf7 ⟨631⟩, known jump hf8 jumpDest_631 ]
      have hendBound : end_ < UInt256.size := by omega
      have hadd := base_ofNat_add32 (p := end_) hend
      have htop : (⟨32⟩ : UInt256) + UInt256.ofNat end_ =
          UInt256.ofNat (end_ + 32) := (u256_add_comm _ _).trans hadd
      have rdFound' := rdFound.withStack
        (congrArg (fun x => x :: UInt256.ofNat end_ :: UInt256.ofNat ret :: ⟨1⟩ :: tail) htop)
      have rdFinal := baseRangeExit (by omega) (p := end_ + 32) (end_ := end_)
        (nz := (⟨1⟩ : UInt256)) hend hendBound (by omega) hret rdFound'
      refine ⟨kTest + 24, ?_⟩
      rw [cdRangeResult, dif_pos hp, if_neg hzero,
        cdRangeGas, dif_pos hp, if_neg hzero]
      exact rdFinal.withIndices rfl (by split <;> omega)
  · have hpWord : p < UInt256.size := by omega
    have hendWord : end_ < UInt256.size := by omega
    have rdFinal := baseRangeExit (by omega) hpWord hendWord (by omega) hret rd0
    refine ⟨k + 9, ?_⟩
    rw [cdRangeResult, dif_neg hp, cdRangeGas, dif_neg hp]
    exact rdFinal.withIndices rfl (by omega)

private theorem reachBaseRangeHeader {cA gh bl σ σ₀ A I} {g : Sat256}
    {end_ ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} (htail : tail.length ≤ 1019)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨625⟩
      (UInt256.ofNat end_ :: UInt256.ofNat ret :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨631⟩
      (UInt256.ofNat 96 :: UInt256.ofNat end_ :: UInt256.ofNat ret :: ⟨0⟩ :: tail)
      mem aw rdata acc (k + 5) (C + 12) := by
  have hd :
      [decode runtimeBytecode ⟨625⟩, decode runtimeBytecode ⟨626⟩,
        decode runtimeBytecode ⟨627⟩, decode runtimeBytecode ⟨628⟩,
        decode runtimeBytecode ⟨629⟩] =
      [some (.JUMPDEST, .none), some (.SWAP1, .none), some (.PUSH0, .none),
        some (.SWAP2, .none), some (.Push .PUSH1, some (⟨96⟩, 1))] := by native_decide
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4⟩
  have rd := evm_run rd0 with [
    known jumpdest hd0, known swap1 hd1, known push0 hd2,
    known swap2 hd3, known push1 hd4 ⟨96⟩ ]
  exact rd.withPC (by native_decide)

/-- Public PC-625 helper theorem in trusted-parser vocabulary. -/
theorem baseRangeExactTrusted {cA gh bl σ σ₀ A I} {g : Sat256}
    {end_ ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1016) (hend64 : end_ + 32 < 2 ^ 64)
    (hstart : 96 ≤ end_ + 32)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨625⟩
      (UInt256.ofNat end_ :: UInt256.ofNat ret :: tail) mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat ret) (UInt256.ofNat (cdRangeReference I 96 end_) :: tail)
      mem aw rdata acc k' (C + 12 + cdRangeGas I 96 end_) := by
  have rdHead := reachBaseRangeHeader (by omega) rd0
  obtain ⟨k', rdFinal⟩ := baseRangeLoopExact htail
    (lt_trans hend64 (by decide)) hstart hret rdHead
  rw [cdRangeResult_eq_reference I hend64 hstart] at rdFinal
  exact ⟨k', rdFinal.withIndices rfl (by omega)⟩

end Modexp
