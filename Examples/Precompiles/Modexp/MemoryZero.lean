import Examples.Precompiles.Modexp.WideWordCaller

/-!
# Exact memory byte-array zero test

This file verifies `LimbMath.isZeroBytes`, the shared byte-array scan used by both the
Montgomery and Barrett ModExp implementations.  The definitions mirror the deployed loop at
PC 2363; in particular, a final short word is shifted so bytes beyond the Solidity array length
do not affect the answer.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 300000
set_option maxHeartbeats 0
set_option Elab.async false

def memoryZeroChunk (mem : ByteArray) (aw : UInt256) (p end_ : Nat) : UInt256 :=
  let word := wideLoadWord mem aw (UInt256.ofNat p)
  if end_ - p < 32 then
    UInt256.shiftRight word
      (UInt256.shiftLeft
        (UInt256.sub ⟨32⟩ (UInt256.ofNat (end_ - p))) ⟨3⟩)
  else word

def memoryZeroResult (mem : ByteArray) (aw : UInt256) (p end_ : Nat) : Nat :=
  if h : p < end_ then
    if memoryZeroChunk mem aw p end_ = ⟨0⟩ then
      memoryZeroResult mem aw (p + 32) end_
    else 0
  else 1
termination_by end_ - p
decreasing_by omega

def memoryZeroGas (mem : ByteArray) (aw : UInt256) (p end_ : Nat) : Nat :=
  if h : p < end_ then
    let isPartial := end_ - p < 32
    if memoryZeroChunk mem aw p end_ = ⟨0⟩ then
      (if isPartial then 139 else 101) + memoryZeroGas mem aw (p + 32) end_
    else if isPartial then 200 else 162
  else 37
termination_by end_ - p
decreasing_by omega

def memoryZeroReference (mem : ByteArray) (p end_ : Nat) : Nat :=
  if Model.bytesToNatPadded mem p (end_ - p) = 0 then 1 else 0

private theorem wideLoadWord_toNat_eq_model {mem : ByteArray} {aw : UInt256} {p : Nat}
    (hp64 : p < 2 ^ 64) (hactive : p + 32 ≤ 32 * aw.toNat)
    (haw : 32 * aw.toNat < UInt256.size) :
    (wideLoadWord mem aw (UInt256.ofNat p)).toNat =
      Model.bytesToNatPadded mem p 32 := by
  have hpWord : p < UInt256.size := lt_trans hp64 (by decide)
  have hfrontier : ¬ UInt256.ofNat p ≥ aw * ⟨32⟩ := by
    intro h
    change (aw * (⟨32⟩ : UInt256)).toNat ≤ (UInt256.ofNat p).toNat at h
    rw [umul_toNat _ _ (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
      omega), show (⟨32⟩ : UInt256).toNat = 32 by decide,
      UInt256.toNat_ofNat_of_lt hpWord] at h
    omega
  by_cases hp : p < mem.size
  · unfold wideLoadWord
    rw [UInt256.toNat_ofNat_of_lt hpWord]
    rw [if_neg (by
      exact not_or_intro (by omega) hfrontier)]
    rw [UInt256.toNat_ofNat_of_lt]
    · rw [readWithPadding_eq_model_readPadded mem p 32 hp64 (by decide)]
      unfold Model.bytesToNatPadded
      exact (bytesToBigEndianNat_eq_fromByteArrayBigEndian _).symm
    · rw [readWithPadding_eq_model_readPadded mem p 32 hp64 (by decide)]
      rw [← bytesToBigEndianNat_eq_fromByteArrayBigEndian]
      have h := model_bytesToBigEndianNat_lt_pow (Model.readPadded mem p 32)
      rw [model_readPadded_size] at h
      simpa [UInt256.size] using h
  · have hpast : mem.size ≤ p := by omega
    have hpad : Model.readPadded mem p 32 = ffi.ByteArray.zeroes 32 := by
      rw [← readWithPadding_eq_model_readPadded mem p 32 hp64 (by decide)]
      exact readWithPadding_past_end mem p 32 hpast (by decide)
    unfold wideLoadWord
    rw [if_pos (by
      left
      simpa [UInt256.toNat_ofNat_of_lt hpWord] using hpast)]
    unfold Model.bytesToNatPadded
    rw [hpad, ← zero_toByteArray_eq_zeroes32,
      bytesToBigEndianNat_eq_fromByteArrayBigEndian,
      fromByteArrayBigEndian_toByteArray]

theorem memoryZeroChunk_toNat_eq_model {mem : ByteArray} {aw : UInt256}
    {p end_ : Nat} (hp64 : p < 2 ^ 64) (hactive : p + 32 ≤ 32 * aw.toNat)
    (haw : 32 * aw.toNat < UInt256.size) :
    (memoryZeroChunk mem aw p end_).toNat =
      Model.bytesToNatPadded mem p (Nat.min 32 (end_ - p)) := by
  have hwide := wideLoadWord_toNat_eq_model (mem := mem) hp64 hactive haw
  have hcd := calldataWord_toNat_eq_model mem p hp64
  have hwideEq : wideLoadWord mem aw (UInt256.ofNat p) =
      uInt256OfByteArray (mem.readBytes p 32) := by
    apply u256_inj
    rw [hwide, hcd]
  by_cases hpartial : end_ - p < 32
  · have hrem : end_ - p < UInt256.size := lt_trans hpartial (by decide)
    have hopen := operandWord_toNat_eq_model mem p (UInt256.ofNat (end_ - p))
      hp64 (by rw [UInt256.toNat_ofNat_of_lt hrem]; omega)
    rw [UInt256.toNat_ofNat_of_lt hrem] at hopen
    simpa [memoryZeroChunk, hpartial, hwideEq,
      Nat.min_eq_right hpartial.le] using hopen
  · have hmin : Nat.min 32 (end_ - p) = 32 := Nat.min_eq_left (by omega)
    rw [memoryZeroChunk, if_neg hpartial, hmin]
    exact hwide

/-- The scan result is one exactly when the entire padded memory range denotes zero. -/
theorem memoryZeroResult_eq_reference {mem : ByteArray} {aw : UInt256}
    {p end_ : Nat} (hend64 : end_ + 32 < 2 ^ 64)
    (hactive : end_ + 32 ≤ 32 * aw.toNat) (haw : 32 * aw.toNat < UInt256.size)
    (hpBound : p ≤ end_ + 32) :
    memoryZeroResult mem aw p end_ = memoryZeroReference mem p end_ := by
  generalize hn : end_ - p = n
  induction n using Nat.strong_induction_on generalizing p
  rename_i n ih
  by_cases hp : p < end_
  · have hpActive : p + 32 ≤ 32 * aw.toNat := by
      exact (by omega : p + 32 ≤ end_ + 32).trans hactive
    have hchunk := memoryZeroChunk_toNat_eq_model (mem := mem) (aw := aw)
      (end_ := end_) (by omega) hpActive haw
    by_cases hpartial : end_ - p < 32
    · have hchunkRem : (memoryZeroChunk mem aw p end_).toNat =
          Model.bytesToNatPadded mem p (end_ - p) := by
        simpa only [Nat.min_eq_right hpartial.le] using hchunk
      have hpNext : end_ ≤ p + 32 := by omega
      have hnext : memoryZeroResult mem aw (p + 32) end_ = 1 := by
        rw [memoryZeroResult]
        simp [hpNext]
      by_cases hzero : memoryZeroChunk mem aw p end_ = ⟨0⟩
      · have hdecoder : Model.bytesToNatPadded mem p (end_ - p) = 0 := by
          have hzNat : (memoryZeroChunk mem aw p end_).toNat = 0 := by rw [hzero]; rfl
          rwa [hchunkRem] at hzNat
        rw [memoryZeroResult, dif_pos hp, if_pos hzero, hnext]
        simp [memoryZeroReference, hdecoder]
      · have hdecoder : Model.bytesToNatPadded mem p (end_ - p) ≠ 0 := by
          intro hz
          have hzNat : (memoryZeroChunk mem aw p end_).toNat = 0 := by
            rw [hchunkRem, hz]
          exact hzero (uint256_toNat_eq_zero hzNat)
        rw [memoryZeroResult, dif_pos hp, if_neg hzero]
        simp [memoryZeroReference, hdecoder]
    · have hfull : 32 ≤ end_ - p := by omega
      have hwidth : end_ - p = 32 + (end_ - (p + 32)) := by omega
      have hchunk32 : (memoryZeroChunk mem aw p end_).toNat =
          Model.bytesToNatPadded mem p 32 := by
        simpa [Nat.min_eq_left hfull] using hchunk
      have hpNext : p + 32 ≤ end_ + 32 := by omega
      have hdecrease : end_ - (p + 32) < n := by omega
      have ihNext := ih _ hdecrease (p := p + 32) hpNext rfl
      have hsplit := model_bytesToNatPadded_split mem p 32 (end_ - (p + 32))
      rw [← hwidth] at hsplit
      by_cases hzero : memoryZeroChunk mem aw p end_ = ⟨0⟩
      · have hprefix : Model.bytesToNatPadded mem p 32 = 0 := by
          have hzNat : (memoryZeroChunk mem aw p end_).toNat = 0 := by rw [hzero]; rfl
          rwa [hchunk32] at hzNat
        have hwhole : Model.bytesToNatPadded mem p (end_ - p) = 0 ↔
            Model.bytesToNatPadded mem (p + 32) (end_ - (p + 32)) = 0 := by
          rw [hsplit, hprefix]
          simp
        rw [memoryZeroResult, dif_pos hp, if_pos hzero, ihNext]
        unfold memoryZeroReference
        exact if_congr hwhole.symm rfl rfl
      · have hprefix : Model.bytesToNatPadded mem p 32 ≠ 0 := by
          intro hz
          have hzNat : (memoryZeroChunk mem aw p end_).toNat = 0 := by rw [hchunk32, hz]
          exact hzero (uint256_toNat_eq_zero hzNat)
        have hwhole : Model.bytesToNatPadded mem p (end_ - p) ≠ 0 := by
          rw [hsplit]
          positivity
        rw [memoryZeroResult, dif_pos hp, if_neg hzero]
        simp [memoryZeroReference, hwhole]
  · have hwidth : end_ - p = 0 := by omega
    rw [memoryZeroResult, dif_neg hp]
    simp [memoryZeroReference, hwidth]

private theorem memoryZeroJumpDests :
    (D_J runtimeBytecode 0).contains ⟨2363⟩ = true ∧
    (D_J runtimeBytecode 0).contains ⟨2380⟩ = true ∧
    (D_J runtimeBytecode 0).contains ⟨2392⟩ = true ∧
    (D_J runtimeBytecode 0).contains ⟨2408⟩ = true ∧
    (D_J runtimeBytecode 0).contains ⟨2414⟩ = true ∧
    (D_J runtimeBytecode 0).contains ⟨2422⟩ = true ∧
    (D_J runtimeBytecode 0).contains ⟨2432⟩ = true := by
  native_decide

@[valid_jumps] theorem jumpDest_2363 :
    (D_J runtimeBytecode 0).contains ⟨2363⟩ = true := memoryZeroJumpDests.1
@[valid_jumps] theorem jumpDest_2380 :
    (D_J runtimeBytecode 0).contains ⟨2380⟩ = true := memoryZeroJumpDests.2.1
@[valid_jumps] theorem jumpDest_2392 :
    (D_J runtimeBytecode 0).contains ⟨2392⟩ = true := memoryZeroJumpDests.2.2.1
@[valid_jumps] theorem jumpDest_2408 :
    (D_J runtimeBytecode 0).contains ⟨2408⟩ = true := memoryZeroJumpDests.2.2.2.1
@[valid_jumps] theorem jumpDest_2414 :
    (D_J runtimeBytecode 0).contains ⟨2414⟩ = true := memoryZeroJumpDests.2.2.2.2.1
@[valid_jumps] theorem jumpDest_2422 :
    (D_J runtimeBytecode 0).contains ⟨2422⟩ = true := memoryZeroJumpDests.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_2432 :
    (D_J runtimeBytecode 0).contains ⟨2432⟩ = true := memoryZeroJumpDests.2.2.2.2.2.2

private theorem memoryZeroSetupDecodes :
    [decode runtimeBytecode ⟨2363⟩, decode runtimeBytecode ⟨2364⟩,
      decode runtimeBytecode ⟨2365⟩, decode runtimeBytecode ⟨2366⟩,
      decode runtimeBytecode ⟨2367⟩, decode runtimeBytecode ⟨2369⟩,
      decode runtimeBytecode ⟨2370⟩, decode runtimeBytecode ⟨2371⟩,
      decode runtimeBytecode ⟨2372⟩, decode runtimeBytecode ⟨2373⟩,
      decode runtimeBytecode ⟨2375⟩, decode runtimeBytecode ⟨2376⟩,
      decode runtimeBytecode ⟨2377⟩, decode runtimeBytecode ⟨2379⟩] =
    [some (.JUMPDEST, .none), some (.SWAP1, .none), some (.DUP2, .none),
      some (.MLOAD, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.DUP4, .none), some (.ADD, .none), some (.SWAP3, .none),
      some (.ADD, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.DUP2, .none), some (.ADD, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)), some (.SWAP4, .none)] := by
  native_decide

private theorem memoryZeroHeaderExitDecodes :
    [decode runtimeBytecode ⟨2380⟩, decode runtimeBytecode ⟨2381⟩,
      decode runtimeBytecode ⟨2382⟩, decode runtimeBytecode ⟨2383⟩,
      decode runtimeBytecode ⟨2384⟩, decode runtimeBytecode ⟨2387⟩,
      decode runtimeBytecode ⟨2388⟩, decode runtimeBytecode ⟨2389⟩,
      decode runtimeBytecode ⟨2390⟩, decode runtimeBytecode ⟨2391⟩] =
    [some (.JUMPDEST, .none), some (.DUP2, .none), some (.DUP2, .none),
      some (.LT, .none), some (.Push .PUSH2, some (⟨2392⟩, 2)),
      some (.JUMPI, .none), some (.POP, .none), some (.POP, .none),
      some (.POP, .none), some (.JUMP, .none)] := by
  native_decide

private theorem memoryZeroBodyDecodes :
    [decode runtimeBytecode ⟨2392⟩, decode runtimeBytecode ⟨2393⟩,
      decode runtimeBytecode ⟨2394⟩, decode runtimeBytecode ⟨2395⟩,
      decode runtimeBytecode ⟨2396⟩, decode runtimeBytecode ⟨2397⟩,
      decode runtimeBytecode ⟨2398⟩, decode runtimeBytecode ⟨2400⟩,
      decode runtimeBytecode ⟨2401⟩, decode runtimeBytecode ⟨2402⟩,
      decode runtimeBytecode ⟨2403⟩, decode runtimeBytecode ⟨2404⟩,
      decode runtimeBytecode ⟨2407⟩] =
    [some (.JUMPDEST, .none), some (.DUP1, .none), some (.MLOAD, .none),
      some (.DUP2, .none), some (.DUP5, .none), some (.SUB, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.DUP1, .none),
      some (.DUP3, .none), some (.ADD, .none), some (.LT, .none),
      some (.Push .PUSH2, some (⟨2432⟩, 2)), some (.JUMPI, .none)] := by
  native_decide

private theorem memoryZeroPartialDecodes :
    [decode runtimeBytecode ⟨2432⟩, decode runtimeBytecode ⟨2433⟩,
      decode runtimeBytecode ⟨2435⟩, decode runtimeBytecode ⟨2436⟩,
      decode runtimeBytecode ⟨2438⟩, decode runtimeBytecode ⟨2439⟩,
      decode runtimeBytecode ⟨2440⟩, decode runtimeBytecode ⟨2442⟩,
      decode runtimeBytecode ⟨2443⟩, decode runtimeBytecode ⟨2444⟩,
      decode runtimeBytecode ⟨2445⟩, decode runtimeBytecode ⟨2448⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.SUB, .none), some (.Push .PUSH1, some (⟨31⟩, 1)),
      some (.NOT, .none), some (.ADD, .none),
      some (.Push .PUSH1, some (⟨3⟩, 1)), some (.SHL, .none),
      some (.SHR, .none), some (.PUSH0, .none),
      some (.Push .PUSH2, some (⟨2408⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem memoryZeroControlDecodes :
    [decode runtimeBytecode ⟨2408⟩, decode runtimeBytecode ⟨2409⟩,
      decode runtimeBytecode ⟨2410⟩, decode runtimeBytecode ⟨2413⟩,
      decode runtimeBytecode ⟨2414⟩, decode runtimeBytecode ⟨2415⟩,
      decode runtimeBytecode ⟨2417⟩, decode runtimeBytecode ⟨2418⟩,
      decode runtimeBytecode ⟨2421⟩, decode runtimeBytecode ⟨2422⟩,
      decode runtimeBytecode ⟨2423⟩, decode runtimeBytecode ⟨2424⟩,
      decode runtimeBytecode ⟨2425⟩, decode runtimeBytecode ⟨2426⟩,
      decode runtimeBytecode ⟨2427⟩, decode runtimeBytecode ⟨2428⟩,
      decode runtimeBytecode ⟨2431⟩] =
    [some (.JUMPDEST, .none), some (.POP, .none),
      some (.Push .PUSH2, some (⟨2422⟩, 2)), some (.JUMPI, .none),
      some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.ADD, .none), some (.Push .PUSH2, some (⟨2380⟩, 2)),
      some (.JUMP, .none), some (.JUMPDEST, .none), some (.POP, .none),
      some (.PUSH0, .none), some (.SWAP4, .none), some (.POP, .none),
      some (.DUP1, .none), some (.Push .PUSH2, some (⟨2414⟩, 2)),
      some (.JUMP, .none)] := by
  native_decide

theorem wrappedRemainingOffset {offset p end_ : Nat}
    (hoffset : offset ≤ end_) (hp : p < end_) (hend : end_ < UInt256.size) :
    UInt256.ofNat offset +
        UInt256.sub (UInt256.ofNat (end_ - offset)) (UInt256.ofNat p) =
      UInt256.ofNat (end_ - p) := by
  apply u256_inj
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega),
    UInt256.toNat_ofNat_of_lt (by omega)]
  by_cases hpa : p ≤ end_ - offset
  · rw [usub_toNat (by
      rw [UInt256.toNat_ofNat_of_lt (by omega),
        UInt256.toNat_ofNat_of_lt (by omega)]
      exact hpa)]
    rw [UInt256.toNat_ofNat_of_lt (by omega),
      UInt256.toNat_ofNat_of_lt (by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [usub_toNat_underflow (by
      rw [UInt256.toNat_ofNat_of_lt (by omega),
        UInt256.toNat_ofNat_of_lt (by omega)]
      omega)]
    rw [UInt256.toNat_ofNat_of_lt (by omega),
      UInt256.toNat_ofNat_of_lt (by omega)]
    have heq : offset + (UInt256.size + (end_ - offset) - p) =
        UInt256.size + (end_ - p) := by omega
    have hremLt : end_ - p < UInt256.size :=
      lt_of_le_of_lt (Nat.sub_le _ _) hend
    rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
    simpa [Nat.mod_eq_of_lt hremLt]

private theorem wrappedRemaining {p end_ : Nat}
    (hend32 : 32 ≤ end_) (hp : p < end_) (hend : end_ < UInt256.size) :
    (⟨32⟩ : UInt256) +
        UInt256.sub (UInt256.ofNat (end_ - 32)) (UInt256.ofNat p) =
      UInt256.ofNat (end_ - p) :=
  wrappedRemainingOffset hend32 hp hend

theorem partialShiftCount {x rem : UInt256}
    (hrem : x + ⟨32⟩ = rem) :
    UInt256.lnot ⟨31⟩ + UInt256.sub ⟨32⟩ x =
      UInt256.sub ⟨32⟩ rem := by
  rw [← hrem]
  have hnot : UInt256.lnot ⟨31⟩ = UInt256.sub ⟨0⟩ ⟨32⟩ := by native_decide
  rw [hnot]
  cases x with
  | mk x =>
      apply u256_inj
      exact congrArg Fin.val (by
        change ((0 : Fin UInt256.size) - 32 + (32 - x)) = 32 - (x + 32)
        abel)

private theorem memoryZeroExit
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {p end_ anchor ret : Nat} {z : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hpWord : p < UInt256.size) (hendWord : end_ < UInt256.size)
    (hstop : end_ ≤ p) (htail : tail.length ≤ 1017)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2380⟩
      (UInt256.ofNat p :: UInt256.ofNat end_ :: UInt256.ofNat anchor ::
        UInt256.ofNat ret :: z :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (z :: tail) mem aw rdata acc (k + 10) (C + 37) := by
  have hd := memoryZeroHeaderExitDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  have hlt : UInt256.lt (UInt256.ofNat p) (UInt256.ofNat end_) = ⟨0⟩ := by
    apply ult_zero
    rw [UInt256.toNat_ofNat_of_lt hpWord, UInt256.toNat_ofNat_of_lt hendWord]
    exact hstop
  have rd := evm_run rd0 with [known jumpdest h0, known dup2 h1, known dup2 h2,
    known lt h3, known push2 h4 ⟨2392⟩, known jumpiNT h5 hlt,
    known pop h6, known pop h7, known pop h8, known jump h9 hret]
  exact (rd.withPC rfl).withIndices (by omega) (by omega)

private theorem memoryZeroReachChunk
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {p end_ ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hend32 : 32 ≤ end_) (hendWord : end_ + 32 < UInt256.size)
    (hp : p < end_) (haccess : p + 32 ≤ 32 * aw.toNat)
    (htail : tail.length ≤ 1014)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2380⟩
      (UInt256.ofNat p :: UInt256.ofNat end_ :: UInt256.ofNat (end_ - 32) ::
        UInt256.ofNat ret :: ⟨1⟩ :: tail) mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2410⟩
      (memoryZeroChunk mem aw p end_ :: UInt256.ofNat p :: UInt256.ofNat end_ ::
        UInt256.ofNat (end_ - 32) :: UInt256.ofNat ret :: ⟨1⟩ :: tail)
      mem aw rdata acc k' (C + if end_ - p < 32 then 108 else 70) := by
  have hh := memoryZeroHeaderExitDecodes
  simp only [List.cons.injEq, and_true] at hh
  rcases hh with ⟨hh0,hh1,hh2,hh3,hh4,hh5,_,_,_,_⟩
  have hb := memoryZeroBodyDecodes
  simp only [List.cons.injEq, and_true] at hb
  rcases hb with ⟨hb0,hb1,hb2,hb3,hb4,hb5,hb6,hb7,hb8,hb9,hb10,hb11,hb12⟩
  have hpWord : p < UInt256.size := by omega
  have hendLt : end_ < UInt256.size := by omega
  have hlt : UInt256.lt (UInt256.ofNat p) (UInt256.ofNat end_) = ⟨1⟩ := by
    apply ult_one
    rw [UInt256.toNat_ofNat_of_lt hpWord, UInt256.toNat_ofNat_of_lt hendLt]
    exact hp
  have rdHead := evm_run rd0 with [known jumpdest hh0, known dup2 hh1,
    known dup2 hh2, known lt hh3, known push2 hh4 ⟨2392⟩,
    known jumpiT hh5 (by rw [hlt]; decide) jumpDest_2392]
  have rd2394 := evm_run rdHead with [known jumpdest hb0, known dup1 hb1]
  have rd2395 := RDx.mloadWithin rd2394 hb2 (by
    rw [UInt256.toNat_ofNat_of_lt hpWord]
    exact haccess) (by simp; omega)
  have rd2407 := evm_run rd2395 with [known dup2 hb3, known dup5 hb4,
    known sub hb5, known push1 hb6 ⟨32⟩, known dup1 hb7, known dup3 hb8,
    known add hb9, known lt hb10, known push2 hb11 ⟨2432⟩]
  have hrem := wrappedRemaining hend32 hp hendLt
  have hrem' : UInt256.sub (UInt256.ofNat (end_ - 32)) (UInt256.ofNat p) +
      (⟨32⟩ : UInt256) = UInt256.ofNat (end_ - p) := by
    rw [u256_add_comm]
    exact hrem
  rw [hrem'] at rd2407
  have hremWord : end_ - p < UInt256.size := by omega
  by_cases hpartial : end_ - p < 32
  · have hltRem : UInt256.lt (UInt256.ofNat (end_ - p)) ⟨32⟩ = ⟨1⟩ := by
      apply ult_one
      rw [UInt256.toNat_ofNat_of_lt hremWord,
        show (⟨32⟩ : UInt256).toNat = 32 by decide]
      exact hpartial
    have rdPartial := rd2407.jumpiT hb12 (by rw [hltRem]; decide)
      jumpDest_2432 (by evm_ov)
    have hd := memoryZeroPartialDecodes
    simp only [List.cons.injEq, and_true] at hd
    rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩
    have rd := evm_run rdPartial with [known jumpdest h0,
      known push1 h1 ⟨32⟩, known sub h2, known push1 h3 ⟨31⟩,
      known not h4, known add h5, known push1 h6 ⟨3⟩, known shl h7,
      known shr h8, known push0 h9, known push2 h10 ⟨2408⟩,
      known jump h11 jumpDest_2408]
    have hc := memoryZeroControlDecodes
    simp only [List.cons.injEq, and_true] at hc
    rcases hc with ⟨hc0,hc1,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩
    have rd' := evm_run rd with [known jumpdest hc0, known pop hc1]
    have hpc : (⟨2408⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ = ⟨2410⟩ := by native_decide
    rw [hpc] at rd'
    have hchunk :
        UInt256.shiftRight (wideLoadWord mem aw (UInt256.ofNat p))
            (UInt256.shiftLeft
              (UInt256.lnot ⟨31⟩ +
                UInt256.sub ⟨32⟩
                  (UInt256.sub (UInt256.ofNat (end_ - 32)) (UInt256.ofNat p)))
              ⟨3⟩) =
          memoryZeroChunk mem aw p end_ := by
      rw [memoryZeroChunk, if_pos hpartial,
        partialShiftCount hrem']
    rw [hchunk] at rd'
    have rdFinal : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2410⟩
        (memoryZeroChunk mem aw p end_ :: UInt256.ofNat p :: UInt256.ofNat end_ ::
          UInt256.ofNat (end_ - 32) :: UInt256.ofNat ret :: ⟨1⟩ :: tail)
        mem aw rdata acc (k + 33) (C + 108) := by
      exact rd'.withIndices (by omega) (by omega)
    exact ⟨k + 33, rdFinal.withIndices rfl (by simp [hpartial])⟩
  · have hltRem : UInt256.lt (UInt256.ofNat (end_ - p)) ⟨32⟩ = ⟨0⟩ := by
      apply ult_zero
      rw [UInt256.toNat_ofNat_of_lt hremWord,
        show (⟨32⟩ : UInt256).toNat = 32 by decide]
      omega
    have rdFull := rd2407.jumpiNT hb12 hltRem (by evm_ov)
    have hc := memoryZeroControlDecodes
    simp only [List.cons.injEq, and_true] at hc
    rcases hc with ⟨hc0,hc1,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩
    have rd := evm_run rdFull with [known jumpdest hc0, known pop hc1]
    have rdFinal : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2410⟩
        (memoryZeroChunk mem aw p end_ :: UInt256.ofNat p :: UInt256.ofNat end_ ::
          UInt256.ofNat (end_ - 32) :: UInt256.ofNat ret :: ⟨1⟩ :: tail)
        mem aw rdata acc (k + 21) (C + 70) := by
      simpa [memoryZeroChunk, hpartial] using
        (rd.withPC (by native_decide)).withIndices (by omega) (by omega)
    exact ⟨k + 21, rdFinal.withIndices rfl (by simp [hpartial])⟩

/-- Exact execution of the memory zero-test loop.  Its gas is path-sensitive: it records the
number of zero chunks traversed, whether the last chunk is partial, and an early nonzero exit. -/
theorem memoryZeroLoopExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {p end_ ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hend32 : 32 ≤ end_) (hendWord : end_ + 32 < UInt256.size)
    (hpBound : p ≤ end_ + 32) (hactive : end_ + 32 ≤ 32 * aw.toNat)
    (htail : tail.length ≤ 1014)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2380⟩
      (UInt256.ofNat p :: UInt256.ofNat end_ :: UInt256.ofNat (end_ - 32) ::
        UInt256.ofNat ret :: ⟨1⟩ :: tail) mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat ret) (UInt256.ofNat (memoryZeroResult mem aw p end_) :: tail)
      mem aw rdata acc k' (C + memoryZeroGas mem aw p end_) := by
  generalize hn : end_ - p = n
  induction n using Nat.strong_induction_on generalizing p k C
  rename_i n ih
  by_cases hp : p < end_
  · obtain ⟨kChunk, rdChunk⟩ := memoryZeroReachChunk hend32 hendWord hp
      (by omega) htail rd0
    have hc := memoryZeroControlDecodes
    simp only [List.cons.injEq, and_true] at hc
    rcases hc with
      ⟨_,_,hc2,hc3,hc4,hc5,hc6,hc7,hc8,hc9,hc10,hc11,hc12,hc13,hc14,hc15,hc16⟩
    by_cases hzero : memoryZeroChunk mem aw p end_ = ⟨0⟩
    · have rdNext := evm_run rdChunk with [known push2 hc2 ⟨2422⟩,
        known jumpiNT hc3 hzero, known jumpdest hc4, known push1 hc5 ⟨32⟩,
        known add hc6, known push2 hc7 ⟨2380⟩,
        known jump hc8 jumpDest_2380]
      have hpNextWord : p + 32 < UInt256.size := by omega
      have hpNext : UInt256.ofNat p + (⟨32⟩ : UInt256) =
          UInt256.ofNat (p + 32) := by
        simpa only [show (⟨32⟩ : UInt256) = UInt256.ofNat 32 by rfl] using
          ofNat_add_bounded (a := p) (b := 32) hpNextWord
      have hpNext' : (⟨32⟩ : UInt256) + UInt256.ofNat p =
          UInt256.ofNat (p + 32) := by
        rw [u256_add_comm]
        exact hpNext
      rw [hpNext'] at rdNext
      have hdecrease : end_ - (p + 32) < n := by omega
      obtain ⟨kFinal, rdFinal⟩ := ih _ hdecrease
        (p := p + 32) (k := _) (C := _) (by omega) rdNext rfl
      refine ⟨kFinal, ?_⟩
      rw [memoryZeroResult, dif_pos hp, if_pos hzero,
        memoryZeroGas, dif_pos hp, if_pos hzero]
      exact rdFinal.withIndices rfl (by split <;> omega)
    · have rdFound := evm_run rdChunk with [known push2 hc2 ⟨2422⟩,
        known jumpiT hc3 hzero jumpDest_2422, known jumpdest hc9,
        known pop hc10, known push0 hc11, known swap4 hc12, known pop hc13,
        known dup1 hc14, known push2 hc15 ⟨2414⟩,
        known jump hc16 jumpDest_2414, known jumpdest hc4,
        known push1 hc5 ⟨32⟩, known add hc6, known push2 hc7 ⟨2380⟩,
        known jump hc8 jumpDest_2380]
      have hendAdd : UInt256.ofNat end_ + (⟨32⟩ : UInt256) =
          UInt256.ofNat (end_ + 32) := by
        simpa only [show (⟨32⟩ : UInt256) = UInt256.ofNat 32 by rfl] using
          ofNat_add_bounded (a := end_) (b := 32) hendWord
      have hendAdd' : (⟨32⟩ : UInt256) + UInt256.ofNat end_ =
          UInt256.ofNat (end_ + 32) := by
        rw [u256_add_comm]
        exact hendAdd
      rw [hendAdd'] at rdFound
      have rdFinal := memoryZeroExit (p := end_ + 32) (end_ := end_)
        (anchor := end_ - 32) (z := (⟨0⟩ : UInt256)) hendWord (by omega)
        (by omega) (by omega) hret rdFound
      refine ⟨kChunk + 25, ?_⟩
      rw [memoryZeroResult, dif_pos hp, if_neg hzero,
        memoryZeroGas, dif_pos hp, if_neg hzero]
      exact rdFinal.withIndices rfl (by split <;> omega)
  · have hpWord : p < UInt256.size := by omega
    have hendLt : end_ < UInt256.size := by omega
    have rdFinal := memoryZeroExit (p := p) (end_ := end_)
      (anchor := end_ - 32) (z := (⟨1⟩ : UInt256)) hpWord hendLt
      (by omega) (by omega) hret rd0
    refine ⟨k + 10, ?_⟩
    rw [memoryZeroResult, dif_neg hp, memoryZeroGas, dif_neg hp]
    exact rdFinal.withIndices rfl (by omega)

/-- The byte-array helper's entry stack setup.  `anchor = end - 32` is retained by the compiler
to implement the final-partial-word test with wrapping word arithmetic. -/
theorem reachMemoryZeroLoop
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {ptr len ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hptr : ptr + 32 + len < UInt256.size)
    (haccess : ptr + 32 ≤ 32 * aw.toNat)
    (hlength : wideLoadWord mem aw (UInt256.ofNat ptr) = UInt256.ofNat len)
    (htail : tail.length ≤ 1019)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2363⟩
      (UInt256.ofNat ptr :: UInt256.ofNat ret :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2380⟩
      (UInt256.ofNat (ptr + 32) :: UInt256.ofNat (ptr + 32 + len) ::
        UInt256.ofNat (ptr + len) :: UInt256.ofNat ret :: ⟨1⟩ :: tail)
      mem aw rdata acc (k + 14) (C + 40) := by
  have hd := memoryZeroSetupDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13⟩
  have rd2366 := evm_run rd0 with [known jumpdest h0, known swap1 h1, known dup2 h2]
  have rd2367 := RDx.mloadWithin rd2366 h3 (by
    rw [UInt256.toNat_ofNat_of_lt (by omega)]
    exact haccess) (by simp; omega)
  rw [hlength] at rd2367
  have rd := evm_run rd2367 with [known push1 h4 ⟨32⟩, known dup4 h5,
    known add h6, known swap3 h7, known add h8, known push1 h9 ⟨32⟩,
    known dup2 h10, known add h11, known push1 h12 ⟨1⟩, known swap4 h13]
  have hp32 := ofNat_add_bounded (a := ptr) (b := 32) (by omega)
  have hplen := ofNat_add_bounded (a := ptr) (b := len) (by omega)
  have hend := ofNat_add_bounded (a := ptr + len) (b := 32) (by omega)
  simp only [show (⟨32⟩ : UInt256) = UInt256.ofNat 32 by rfl] at rd
  rw [hp32, hplen, hend] at rd
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (rd.withPC (by native_decide)).withIndices (by omega) (by omega)

/-- Full exact theorem for `LimbMath.isZeroBytes` at PC 2363. -/
theorem memoryZeroExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {ptr len ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hbound : ptr + 32 + len + 32 < UInt256.size)
    (hactive : ptr + 32 + len + 32 ≤ 32 * aw.toNat)
    (hlength : wideLoadWord mem aw (UInt256.ofNat ptr) = UInt256.ofNat len)
    (htail : tail.length ≤ 1014)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2363⟩
      (UInt256.ofNat ptr :: UInt256.ofNat ret :: tail) mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat ret)
      (UInt256.ofNat
          (memoryZeroResult mem aw (ptr + 32) (ptr + 32 + len)) :: tail)
      mem aw rdata acc k'
        (C + 40 + memoryZeroGas mem aw (ptr + 32) (ptr + 32 + len)) := by
  have rdLoop := reachMemoryZeroLoop (ptr := ptr) (len := len) (ret := ret)
    (by omega) (by omega) hlength (by omega) rd0
  obtain ⟨k', rdFinal⟩ := memoryZeroLoopExact
    (p := ptr + 32) (end_ := ptr + 32 + len) (ret := ret)
    (by omega) (by omega) (by omega) hactive htail hret (by
      simpa only [show ptr + 32 + len - 32 = ptr + len by omega] using rdLoop)
  exact ⟨k', rdFinal.withIndices rfl (by omega)⟩

end Modexp
