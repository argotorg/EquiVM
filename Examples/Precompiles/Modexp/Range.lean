import Examples.Precompiles.Modexp.Wide

/-!
# Exact `cdRangeNonZero` helper

This is the first reusable arbitrary-width loop in the deployed runtime.  The pure definitions
below mirror the compiled 32-byte scan, including truncation of its final partial word and its
exact path-dependent instruction gas.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option Elab.async false

def cdRangeChunk (I : ExecutionEnv) (p end_ : Nat) : UInt256 :=
  let word := calldataWord I (UInt256.ofNat p)
  if end_ - p < 32 then
    UInt256.shiftRight word
      (UInt256.shiftLeft
        (UInt256.sub ⟨32⟩ (UInt256.ofNat (end_ - p))) ⟨3⟩)
  else word

def cdRangeResult (I : ExecutionEnv) (p end_ : Nat) : Nat :=
  if h : p < end_ then
    if cdRangeChunk I p end_ = ⟨0⟩ then cdRangeResult I (p + 32) end_ else 1
  else 0
termination_by end_ - p
decreasing_by omega

def cdRangeGas (I : ExecutionEnv) (p end_ : Nat) : Nat :=
  if h : p < end_ then
    let isPartial := end_ - p < 32
    if cdRangeChunk I p end_ = ⟨0⟩ then
      (if isPartial then 124 else 95) + cdRangeGas I (p + 32) end_
    else if isPartial then 184 else 155
  else 35
termination_by end_ - p
decreasing_by omega

/-- Each scanned word is exactly the next (at most) 32-byte slice of the trusted padded parser. -/
theorem cdRangeChunk_toNat_eq_model (I : ExecutionEnv) {p end_ : Nat}
    (hp64 : p < 2 ^ 64) :
    (cdRangeChunk I p end_).toNat =
      Model.bytesToNatPadded I.calldata p (Nat.min 32 (end_ - p)) := by
  have hpWord : p < UInt256.size := lt_trans hp64 (by decide)
  have hpToNat : (UInt256.ofNat p).toNat = p := UInt256.toNat_ofNat_of_lt hpWord
  by_cases hpartial : end_ - p < 32
  · have hrem : end_ - p < UInt256.size := lt_trans hpartial (by decide)
    have hsize : (UInt256.ofNat (end_ - p)).toNat ≤ 32 := by
      rw [UInt256.toNat_ofNat_of_lt hrem]
      omega
    have h := operandWord_toNat_eq_model I.calldata p
      (UInt256.ofNat (end_ - p)) hp64 hsize
    have hsub : (⟨32⟩ : UInt256) - UInt256.ofNat (end_ - p) =
        UInt256.sub ⟨32⟩ (UInt256.ofNat (end_ - p)) := rfl
    rw [hsub, UInt256.toNat_ofNat_of_lt hrem] at h
    simpa [cdRangeChunk, hpartial, calldataWord, hpToNat,
      Nat.min_eq_right hpartial.le] using h
  · have h := calldataWord_toNat_eq_model I.calldata p hp64
    simpa [cdRangeChunk, hpartial, calldataWord, hpToNat,
      Nat.min_eq_left (by omega : 32 ≤ end_ - p)] using h

/-- Trusted-parser presentation of the scan result. -/
def cdRangeReference (I : ExecutionEnv) (p end_ : Nat) : Nat :=
  if Model.bytesToNatPadded I.calldata p (end_ - p) = 0 then 0 else 1

/-- The implementation scan flag is zero exactly when the corresponding trusted padded integer
is zero. -/
theorem cdRangeResult_eq_reference (I : ExecutionEnv) {p end_ : Nat}
    (hend64 : end_ + 32 < 2 ^ 64) (hpBound : p ≤ end_ + 32) :
    cdRangeResult I p end_ = cdRangeReference I p end_ := by
  generalize hn : end_ - p = n
  induction n using Nat.strong_induction_on generalizing p
  rename_i n ih
  by_cases hp : p < end_
  · have hp64 : p < 2 ^ 64 := by omega
    have hchunk := cdRangeChunk_toNat_eq_model I (p := p) (end_ := end_) hp64
    by_cases hpartial : end_ - p < 32
    · have hchunkRem : (cdRangeChunk I p end_).toNat =
          Model.bytesToNatPadded I.calldata p (end_ - p) := by
        simpa only [Nat.min_eq_right hpartial.le] using hchunk
      have hpNext : end_ ≤ p + 32 := by omega
      have hnext : cdRangeResult I (p + 32) end_ = 0 := by
        rw [cdRangeResult]
        simp [hpNext]
      by_cases hzero : cdRangeChunk I p end_ = ⟨0⟩
      · have hdecoder : Model.bytesToNatPadded I.calldata p (end_ - p) = 0 := by
          have hzNat : (cdRangeChunk I p end_).toNat = 0 := by rw [hzero]; rfl
          rwa [hchunkRem] at hzNat
        rw [cdRangeResult, dif_pos hp, if_pos hzero, hnext]
        simp [cdRangeReference, hdecoder]
      · have hdecoder : Model.bytesToNatPadded I.calldata p (end_ - p) ≠ 0 := by
          intro hz
          have hzNat : (cdRangeChunk I p end_).toNat = 0 := by
            rw [hchunkRem, hz]
          exact hzero (uint256_toNat_eq_zero hzNat)
        rw [cdRangeResult, dif_pos hp, if_neg hzero]
        simp [cdRangeReference, hdecoder]
    · have hfull : 32 ≤ end_ - p := by omega
      have hwidth : end_ - p = 32 + (end_ - (p + 32)) := by omega
      have hchunk32 : (cdRangeChunk I p end_).toNat =
          Model.bytesToNatPadded I.calldata p 32 := by
        simpa [Nat.min_eq_left hfull] using hchunk
      have hpNext : p + 32 ≤ end_ + 32 := by omega
      have hdecrease : end_ - (p + 32) < n := by omega
      have ihNext := ih _ hdecrease (p := p + 32) hpNext rfl
      have hsplit := model_bytesToNatPadded_split I.calldata p 32 (end_ - (p + 32))
      rw [← hwidth] at hsplit
      by_cases hzero : cdRangeChunk I p end_ = ⟨0⟩
      · have hprefix : Model.bytesToNatPadded I.calldata p 32 = 0 := by
          have hzNat : (cdRangeChunk I p end_).toNat = 0 := by rw [hzero]; rfl
          rwa [hchunk32] at hzNat
        have hwhole : Model.bytesToNatPadded I.calldata p (end_ - p) = 0 ↔
            Model.bytesToNatPadded I.calldata (p + 32) (end_ - (p + 32)) = 0 := by
          rw [hsplit, hprefix]
          simp
        rw [cdRangeResult, dif_pos hp, if_pos hzero, ihNext]
        unfold cdRangeReference
        exact if_congr hwhole.symm rfl rfl
      · have hprefix : Model.bytesToNatPadded I.calldata p 32 ≠ 0 := by
          intro hz
          have hzNat : (cdRangeChunk I p end_).toNat = 0 := by rw [hchunk32, hz]
          exact hzero (uint256_toNat_eq_zero hzNat)
        have hwhole : Model.bytesToNatPadded I.calldata p (end_ - p) ≠ 0 := by
          rw [hsplit]
          positivity
        rw [cdRangeResult, dif_pos hp, if_neg hzero]
        simp [cdRangeReference, hwhole]
  · have hwidth : end_ - p = 0 := by omega
    have hread : Model.readPadded I.calldata p 0 = ByteArray.empty :=
      byteArray_eq_empty_of_size_eq_zero _ (model_readPadded_size _ _ _)
    rw [cdRangeResult, dif_neg hp]
    simp [cdRangeReference, hwidth, Model.bytesToNatPadded,
      Model.bytesToBigEndianNat, hread, Reasoning.Theory.byteArray_toList_eq]

private theorem ofNat_toNat {n : Nat} (hn : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := UInt256.toNat_ofNat_of_lt hn

private theorem ofNat_sub {p end_ : Nat} (hp : p ≤ end_) (hend : end_ < UInt256.size) :
    UInt256.sub (UInt256.ofNat end_) (UInt256.ofNat p) = UInt256.ofNat (end_ - p) := by
  apply u256_inj
  rw [usub_ofNat_lit_toNat hp hend,
    ofNat_toNat (lt_of_le_of_lt (Nat.sub_le _ _) hend)]

private theorem ofNat_add32 {p : Nat} (hp : p + 32 < UInt256.size) :
    UInt256.ofNat p + (⟨32⟩ : UInt256) = UInt256.ofNat (p + 32) := by
  apply u256_inj
  rw [uadd_word_lit32_toNat _ (by rw [ofNat_toNat (by omega)]; omega),
    ofNat_toNat (by omega), ofNat_toNat hp]

private theorem cdRangeHeaderExitDecodes :
    [decode runtimeBytecode ⟨699⟩, decode runtimeBytecode ⟨700⟩,
      decode runtimeBytecode ⟨701⟩, decode runtimeBytecode ⟨702⟩,
      decode runtimeBytecode ⟨703⟩, decode runtimeBytecode ⟨706⟩,
      decode runtimeBytecode ⟨707⟩, decode runtimeBytecode ⟨708⟩,
      decode runtimeBytecode ⟨709⟩] =
    [some (.JUMPDEST, .none), some (.DUP2, .none), some (.DUP2, .none),
      some (.LT, .none), some (.Push .PUSH2, some (⟨710⟩, 2)), some (.JUMPI, .none),
      some (.POP, .none), some (.POP, .none), some (.JUMP, .none)] := by
  native_decide

private theorem cdRangeBodyDecodes :
    [decode runtimeBytecode ⟨710⟩, decode runtimeBytecode ⟨711⟩,
      decode runtimeBytecode ⟨712⟩, decode runtimeBytecode ⟨713⟩,
      decode runtimeBytecode ⟨714⟩, decode runtimeBytecode ⟨715⟩,
      decode runtimeBytecode ⟨716⟩, decode runtimeBytecode ⟨718⟩,
      decode runtimeBytecode ⟨719⟩, decode runtimeBytecode ⟨720⟩,
      decode runtimeBytecode ⟨723⟩] =
    [some (.JUMPDEST, .none), some (.DUP1, .none), some (.CALLDATALOAD, .none),
      some (.DUP2, .none), some (.DUP4, .none), some (.SUB, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.DUP2, .none), some (.LT, .none),
      some (.Push .PUSH2, some (⟨749⟩, 2)), some (.JUMPI, .none)] := by
  native_decide

private theorem cdRangeFullDecodes :
    [decode runtimeBytecode ⟨724⟩, decode runtimeBytecode ⟨725⟩,
      decode runtimeBytecode ⟨726⟩, decode runtimeBytecode ⟨729⟩,
      decode runtimeBytecode ⟨730⟩, decode runtimeBytecode ⟨731⟩,
      decode runtimeBytecode ⟨733⟩, decode runtimeBytecode ⟨734⟩,
      decode runtimeBytecode ⟨737⟩,
      decode runtimeBytecode ⟨738⟩, decode runtimeBytecode ⟨739⟩,
      decode runtimeBytecode ⟨740⟩, decode runtimeBytecode ⟨742⟩,
      decode runtimeBytecode ⟨743⟩, decode runtimeBytecode ⟨744⟩,
      decode runtimeBytecode ⟨745⟩, decode runtimeBytecode ⟨748⟩] =
    [some (.JUMPDEST, .none), some (.POP, .none),
      some (.Push .PUSH2, some (⟨738⟩, 2)), some (.JUMPI, .none),
      some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.ADD, .none), some (.Push .PUSH2, some (⟨699⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.POP, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)), some (.SWAP3, .none), some (.POP, .none),
      some (.DUP1, .none), some (.Push .PUSH2, some (⟨730⟩, 2)),
      some (.JUMP, .none)] := by
  native_decide

private theorem cdRangePartialDecodes :
    [decode runtimeBytecode ⟨749⟩, decode runtimeBytecode ⟨750⟩,
      decode runtimeBytecode ⟨752⟩, decode runtimeBytecode ⟨753⟩,
      decode runtimeBytecode ⟨755⟩, decode runtimeBytecode ⟨756⟩,
      decode runtimeBytecode ⟨757⟩, decode runtimeBytecode ⟨758⟩,
      decode runtimeBytecode ⟨761⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.SUB, .none), some (.Push .PUSH1, some (⟨3⟩, 1)), some (.SHL, .none),
      some (.SHR, .none), some (.PUSH0, .none),
      some (.Push .PUSH2, some (⟨724⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem cdRangeExit {cA gh bl σ σ₀ A I} {g : Sat256}
    {p end_ ret : Nat} {nz : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1017)
    (hp : p < UInt256.size) (hend : end_ < UInt256.size)
    (hstop : end_ ≤ p)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨699⟩
      ([UInt256.ofNat p, UInt256.ofNat end_, UInt256.ofNat ret, nz] ++ tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (nz :: tail) mem aw rdata acc (k + 9) (C + 35) := by
  simp only [List.cons_append, List.nil_append] at rd0
  have hd := cdRangeHeaderExitDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8⟩
  have hlt : UInt256.lt (UInt256.ofNat p) (UInt256.ofNat end_) = ⟨0⟩ := by
    apply ult_zero
    rw [ofNat_toNat hp, ofNat_toNat hend]
    exact hstop
  have rd := evm_run rd0 with [
    known jumpdest hd0,
    known dup2 hd1,
    known dup2 hd2,
    known lt hd3,
    known push2 hd4 ⟨710⟩,
    known jumpiNT hd5 hlt,
    known pop hd6,
    known pop hd7,
    known jump hd8 hret ]
  exact (rd.withPC rfl).withIndices (by omega) (by omega)

private theorem cdRangeReachTest {cA gh bl σ σ₀ A I} {g : Sat256}
    {p end_ ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1016)
    (hend : end_ + 32 < UInt256.size) (hp : p < end_)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨699⟩
      ([UInt256.ofNat p, UInt256.ofNat end_, UInt256.ofNat ret, ⟨0⟩] ++ tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨726⟩
      (cdRangeChunk I p end_ :: UInt256.ofNat p :: UInt256.ofNat end_ ::
        UInt256.ofNat ret :: ⟨0⟩ :: tail)
      mem aw rdata acc k'
        (C + if end_ - p < 32 then 93 else 64) := by
  simp only [List.cons_append, List.nil_append] at rd0
  have hh := cdRangeHeaderExitDecodes
  simp only [List.cons.injEq, and_true] at hh
  rcases hh with ⟨hh0, hh1, hh2, hh3, hh4, hh5, _, _, _⟩
  have hb := cdRangeBodyDecodes
  simp only [List.cons.injEq, and_true] at hb
  rcases hb with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10⟩
  have hf := cdRangeFullDecodes
  simp only [List.cons.injEq, and_true] at hf
  rcases hf with ⟨hf0, hf1, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hpBound : p < UInt256.size := by omega
  have hendBound : end_ < UInt256.size := by omega
  have hlt : UInt256.lt (UInt256.ofNat p) (UInt256.ofNat end_) = ⟨1⟩ := by
    apply ult_one
    rw [ofNat_toNat hpBound, ofNat_toNat hendBound]
    exact hp
  have rdHead := evm_run rd0 with [
    known jumpdest hh0,
    known dup2 hh1,
    known dup2 hh2,
    known lt hh3,
    known push2 hh4 ⟨710⟩,
    known jumpiT hh5 (by rw [hlt]; decide) jumpDest_710 ]
  have rdBody := evm_run rdHead with [
    known jumpdest hb0,
    known dup1 hb1,
    known calldataload hb2,
    known dup2 hb3,
    known dup4 hb4,
    known sub hb5,
    known push1 hb6 ⟨32⟩,
    known dup2 hb7,
    known lt hb8,
    known push2 hb9 ⟨749⟩ ]
  have hsub := ofNat_sub hp.le hendBound
  rw [hsub] at rdBody
  have hremBound : end_ - p < UInt256.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) hendBound
  by_cases hpartial : end_ - p < 32
  · have hltRem : UInt256.lt (UInt256.ofNat (end_ - p)) ⟨32⟩ = ⟨1⟩ := by
      apply ult_one
      rw [ofNat_toNat hremBound, show (⟨32⟩ : UInt256).toNat = 32 by decide]
      simpa using hpartial
    have rdPartial := rdBody.jumpiT hb10 (by rw [hltRem]; decide) jumpDest_749 (by evm_ov)
    have hpdec := cdRangePartialDecodes
    simp only [List.cons.injEq, and_true] at hpdec
    rcases hpdec with ⟨hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8⟩
    have rdP := evm_run rdPartial with [
      known jumpdest hp0,
      known push1 hp1 ⟨32⟩,
      known sub hp2,
      known push1 hp3 ⟨3⟩,
      known shl hp4,
      known shr hp5,
      known push0 hp6,
      known push2 hp7 ⟨724⟩,
      known jump hp8 jumpDest_724,
      known jumpdest hf0,
      known pop hf1 ]
    refine ⟨k + 28, ?_⟩
    simpa [cdRangeChunk, hpartial] using
      (rdP.withPC (by native_decide)).withIndices rfl (by omega)
  · have hltRem : UInt256.lt (UInt256.ofNat (end_ - p)) ⟨32⟩ = ⟨0⟩ := by
      apply ult_zero
      rw [ofNat_toNat hremBound, show (⟨32⟩ : UInt256).toNat = 32 by decide]
      omega
    have rdFull := rdBody.jumpiNT hb10 hltRem (by evm_ov)
    have rdF := evm_run rdFull with [
      known jumpdest hf0,
      known pop hf1 ]
    refine ⟨k + 19, ?_⟩
    simpa [cdRangeChunk, hpartial] using
      (rdF.withPC (by native_decide)).withIndices rfl (by omega)

private theorem reachCdRangeHeader {cA gh bl σ σ₀ A I} {g : Sat256}
    {start end_ ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (htail : tail.length ≤ 1019)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨694⟩
      (UInt256.ofNat start :: UInt256.ofNat end_ :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨699⟩
      (UInt256.ofNat start :: UInt256.ofNat end_ :: UInt256.ofNat ret :: ⟨0⟩ :: tail)
      mem aw rdata acc (k + 5) (C + 12) := by
  have hd := cdRangeNonZeroDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd694, hd695, hd696, hd697, hd698, _⟩
  have rd := evm_run rd0 with [
    known jumpdest hd694,
    known swap1 hd695,
    known push0 hd696,
    known swap3 hd697,
    known swap2 hd698 ]
  exact rd.withPC (by native_decide)

/-- Execute the whole `cdRangeNonZero` loop from its header.  Besides the Boolean result, this
records the exact input-dependent gas: zero words continue, while the first nonzero word exits
immediately. -/
theorem cdRangeLoopExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {p end_ ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1016)
    (hend : end_ + 32 < UInt256.size) (hpBound : p ≤ end_ + 32)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨699⟩
      ([UInt256.ofNat p, UInt256.ofNat end_, UInt256.ofNat ret, ⟨0⟩] ++ tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat ret) (UInt256.ofNat (cdRangeResult I p end_) :: tail)
      mem aw rdata acc k' (C + cdRangeGas I p end_) := by
  generalize hn : end_ - p = n
  induction n using Nat.strong_induction_on generalizing p k C
  rename_i n ih
  by_cases hp : p < end_
  · obtain ⟨kTest, rdTest⟩ := cdRangeReachTest htail hend hp rd0
    have hf := cdRangeFullDecodes
    simp only [List.cons.injEq, and_true] at hf
    rcases hf with
      ⟨_, _, hf2, hf3, hf4, hf5, hf6, hf7, hf8,
        hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16⟩
    by_cases hzero : cdRangeChunk I p end_ = ⟨0⟩
    · have rdAtInc := evm_run rdTest with [
        known push2 hf2 ⟨738⟩,
        known jumpiNT hf3 hzero ]
      have rdNext := evm_run rdAtInc with [
        known jumpdest hf4,
        known push1 hf5 ⟨32⟩,
        known add hf6,
        known push2 hf7 ⟨699⟩,
        known jump hf8 jumpDest_699 ]
      have hpNext : p + 32 ≤ end_ + 32 := by omega
      have hadd : UInt256.add (UInt256.ofNat p) ⟨32⟩ = UInt256.ofNat (p + 32) :=
        ofNat_add32 (by omega)
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
        known push2 hf2 ⟨738⟩,
        known jumpiT hf3 hzero jumpDest_738 ]
      have rdFound := evm_run rdAtFound with [
        known jumpdest hf9,
        known pop hf10,
        known push1 hf11 ⟨1⟩,
        known swap3 hf12,
        known pop hf13,
        known dup1 hf14,
        known push2 hf15 ⟨730⟩,
        known jump hf16 jumpDest_730,
        known jumpdest hf4,
        known push1 hf5 ⟨32⟩,
        known add hf6,
        known push2 hf7 ⟨699⟩,
        known jump hf8 jumpDest_699 ]
      have hendBound : end_ < UInt256.size := by omega
      have hendNext : end_ + 32 < UInt256.size := hend
      have hadd : UInt256.add (UInt256.ofNat end_) ⟨32⟩ =
          UInt256.ofNat (end_ + 32) := ofNat_add32 hend
      have htop : (⟨32⟩ : UInt256) + UInt256.ofNat end_ = UInt256.ofNat (end_ + 32) :=
        (u256_add_comm _ _).trans hadd
      have rdFound' := rdFound.withStack
        (congrArg (fun x => x :: UInt256.ofNat end_ :: UInt256.ofNat ret :: ⟨1⟩ :: tail) htop)
      have rdFinal := cdRangeExit (by omega) (p := end_ + 32) (end_ := end_)
        (nz := (⟨1⟩ : UInt256)) hendNext hendBound (by omega) hret rdFound'
      refine ⟨kTest + 24, ?_⟩
      rw [cdRangeResult, dif_pos hp, if_neg hzero,
        cdRangeGas, dif_pos hp, if_neg hzero]
      exact rdFinal.withIndices rfl (by split <;> omega)
  · have hpWord : p < UInt256.size := by omega
    have hendWord : end_ < UInt256.size := by omega
    have rdFinal := cdRangeExit (by omega) hpWord hendWord (by omega) hret rd0
    refine ⟨k + 9, ?_⟩
    rw [cdRangeResult, dif_neg hp, cdRangeGas, dif_neg hp]
    exact rdFinal.withIndices rfl (by omega)

/-- Entry-point form of `cdRangeLoopExact`, including the helper's five-instruction stack setup. -/
theorem cdRangeExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {start end_ ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1016)
    (hend : end_ + 32 < UInt256.size) (hstart : start ≤ end_ + 32)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨694⟩
      (UInt256.ofNat start :: UInt256.ofNat end_ :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat ret) (UInt256.ofNat (cdRangeResult I start end_) :: tail)
      mem aw rdata acc k' (C + 12 + cdRangeGas I start end_) := by
  have rdHead := reachCdRangeHeader (by omega) rd0
  obtain ⟨k', rdFinal⟩ := cdRangeLoopExact htail hend hstart hret rdHead
  exact ⟨k', rdFinal.withIndices rfl (by omega)⟩

/-- Public scan theorem stated directly with the unchanged trusted padded integer parser. -/
theorem cdRangeExactTrusted {cA gh bl σ σ₀ A I} {g : Sat256}
    {start end_ ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (htail : tail.length ≤ 1016)
    (hend64 : end_ + 32 < 2 ^ 64) (hstart : start ≤ end_ + 32)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨694⟩
      (UInt256.ofNat start :: UInt256.ofNat end_ :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat ret) (UInt256.ofNat (cdRangeReference I start end_) :: tail)
      mem aw rdata acc k' (C + 12 + cdRangeGas I start end_) := by
  obtain ⟨k', rdFinal⟩ := cdRangeExact htail
    (lt_trans hend64 (by decide)) hstart hret rd0
  rw [cdRangeResult_eq_reference I hend64 hstart] at rdFinal
  exact ⟨k', rdFinal⟩

end Modexp
