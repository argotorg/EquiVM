import Examples.Precompiles.Modexp.MemoryZero

/-!
# Exact memory byte-array one test

This file verifies `LimbMath.isOneBytes` at PC 2449 of the deployed ModExp bytecode.  The
source algorithm is from `evmification/src/modexp/LimbMath.sol`: it rejects an empty array,
checks that every byte except the last is zero, and checks that the last byte is one.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 300000
set_option maxHeartbeats 0
set_option Elab.async false

def memoryOneLast (mem : ByteArray) (aw : UInt256) (last : Nat) : UInt256 :=
  UInt256.byteAt ⟨0⟩ (wideLoadWord mem aw (UInt256.ofNat last))

def memoryOneLastResult (mem : ByteArray) (aw : UInt256) (last : Nat) : Nat :=
  if memoryOneLast mem aw last = ⟨1⟩ then 1 else 0

theorem memoryOneLastWordResult (mem : ByteArray) (aw : UInt256) (last : Nat) :
    UInt256.eq (memoryOneLast mem aw last) ⟨1⟩ =
      UInt256.ofNat (memoryOneLastResult mem aw last) := by
  unfold memoryOneLastResult
  by_cases h : memoryOneLast mem aw last = ⟨1⟩
  · rw [if_pos h, h, uInt256_eq_self]
    rfl
  · rw [if_neg h]
    have heq : UInt256.eq (memoryOneLast mem aw last) ⟨1⟩ = ⟨0⟩ := by
      apply uInt256_eq_zero_of_ne
      intro hone
      exact h (uInt256_eq_one_eq hone)
    rw [heq]
    rfl

def memoryOneLoopResult (mem : ByteArray) (aw : UInt256)
    (p end_ : Nat) : Nat :=
  if h : p < end_ then
    if memoryZeroChunk mem aw p end_ = ⟨0⟩ then
      memoryOneLoopResult mem aw (p + 32) end_
    else 0
  else memoryOneLastResult mem aw end_
termination_by end_ - p
decreasing_by omega

def memoryOneLoopGas (mem : ByteArray) (aw : UInt256)
    (p end_ : Nat) : Nat :=
  if h : p < end_ then
    let isPartial := end_ - p < 32
    if memoryZeroChunk mem aw p end_ = ⟨0⟩ then
      (if isPartial then 164 else 126) + memoryOneLoopGas mem aw (p + 32) end_
    else if isPartial then 238 else 200
  else 68
termination_by end_ - p
decreasing_by omega

def memoryOneResult (mem : ByteArray) (aw : UInt256) (ptr len : Nat) : Nat :=
  if len = 0 then 0
  else memoryOneLoopResult mem aw (ptr + 32) (ptr + 32 + (len - 1))

def memoryOneGas (mem : ByteArray) (aw : UInt256) (ptr len : Nat) : Nat :=
  if len = 0 then 47
  else 71 + memoryOneLoopGas mem aw (ptr + 32) (ptr + 32 + (len - 1))

def memoryOneReference (mem : ByteArray) (ptr len : Nat) : Nat :=
  if Model.bytesToNatPadded mem (ptr + 32) len = 1 then 1 else 0

private theorem memoryOneLast_toNat_eq_model {mem : ByteArray} {aw : UInt256}
    {last : Nat} (hlast64 : last < 2 ^ 64)
    (hactive : last + 32 ≤ 32 * aw.toNat)
    (haw : 32 * aw.toNat < UInt256.size) :
    (memoryOneLast mem aw last).toNat =
      Model.bytesToNatPadded mem last 1 := by
  rw [memoryOneLast, byteAt_zero_toNat]
  have hchunk := memoryZeroChunk_toNat_eq_model
    (mem := mem) (aw := aw) (p := last) (end_ := last + 1)
    hlast64 hactive haw
  simpa [memoryZeroChunk] using hchunk

private theorem memoryOneLast_eq_one_iff_model {mem : ByteArray} {aw : UInt256}
    {last : Nat} (hlast64 : last < 2 ^ 64)
    (hactive : last + 32 ≤ 32 * aw.toNat)
    (haw : 32 * aw.toNat < UInt256.size) :
    memoryOneLast mem aw last = ⟨1⟩ ↔
      Model.bytesToNatPadded mem last 1 = 1 := by
  have hlast := memoryOneLast_toNat_eq_model (mem := mem) (aw := aw)
    hlast64 hactive haw
  constructor
  · intro h
    have := congrArg UInt256.toNat h
    simpa [hlast] using this
  · intro h
    apply u256_inj
    simpa [hlast] using h

private theorem memoryOneLoopResult_eq_reference {mem : ByteArray} {aw : UInt256}
    {p end_ : Nat} (hend64 : end_ + 32 < 2 ^ 64)
    (hactive : end_ + 32 ≤ 32 * aw.toNat)
    (haw : 32 * aw.toNat < UInt256.size) (hpLe : p ≤ end_) :
    memoryOneLoopResult mem aw p end_ =
      (if Model.bytesToNatPadded mem p (end_ - p + 1) = 1 then 1 else 0) := by
  generalize hn : end_ - p = n
  induction n using Nat.strong_induction_on generalizing p
  rename_i n ih
  subst n
  by_cases hp : p < end_
  · have hpActive : p + 32 ≤ 32 * aw.toNat := by omega
    have hchunk := memoryZeroChunk_toNat_eq_model (mem := mem) (aw := aw)
      (p := p) (end_ := end_) (by omega) hpActive haw
    by_cases hzero : memoryZeroChunk mem aw p end_ = ⟨0⟩
    · have hprefix : Model.bytesToNatPadded mem p (Nat.min 32 (end_ - p)) = 0 := by
        rw [← hchunk, hzero]
        rfl
      by_cases hpartial : end_ - p < 32
      · have hpNext : ¬ p + 32 < end_ := by omega
        have hzeroRange : Model.bytesToNatPadded mem p (end_ - p) = 0 := by
          simpa [Nat.min_eq_right hpartial.le] using hprefix
        have hsplit := model_bytesToNatPadded_split mem p (end_ - p) 1
        rw [show p + (end_ - p) = end_ by omega, hzeroRange,
          zero_mul, zero_add] at hsplit
        have hone := memoryOneLast_eq_one_iff_model (mem := mem) (aw := aw)
          (last := end_) (by omega) (by omega) haw
        rw [memoryOneLoopResult, dif_pos hp, if_pos hzero,
          memoryOneLoopResult, dif_neg hpNext, hsplit]
        simp only [memoryOneLastResult, hone]
      · have hpNext : p + 32 ≤ end_ := by omega
        have hnext := ih (end_ - (p + 32)) (by omega) (p := p + 32)
          hpNext rfl
        have hsplit := model_bytesToNatPadded_split mem p 32
          (end_ - (p + 32) + 1)
        have hwidth : 32 + (end_ - (p + 32) + 1) = end_ - p + 1 := by omega
        have hprefix32 : Model.bytesToNatPadded mem p 32 = 0 := by
          simpa [Nat.min_eq_left (by omega : 32 ≤ end_ - p)] using hprefix
        rw [hwidth, hprefix32, zero_mul, zero_add] at hsplit
        rw [memoryOneLoopResult, dif_pos hp, if_pos hzero, hnext, hsplit]
    · rw [memoryOneLoopResult, dif_pos hp, if_neg hzero]
      have hchunkPos : 0 < Model.bytesToNatPadded mem p (Nat.min 32 (end_ - p)) := by
        rw [← hchunk]
        exact Nat.pos_of_ne_zero (by
          intro hz
          apply hzero
          apply u256_inj
          simpa using hz)
      have hprefixLen : Nat.min 32 (end_ - p) ≤ end_ - p + 1 := by
        exact (Nat.min_le_right _ _).trans (Nat.le_add_right _ 1)
      have hsplit := model_bytesToNatPadded_split mem p (Nat.min 32 (end_ - p))
        (end_ - p + 1 - Nat.min 32 (end_ - p))
      have hwidth : Nat.min 32 (end_ - p) +
          (end_ - p + 1 - Nat.min 32 (end_ - p)) = end_ - p + 1 :=
        Nat.add_sub_of_le hprefixLen
      rw [hwidth] at hsplit
      have hrestPos : 0 < end_ - p + 1 - Nat.min 32 (end_ - p) := by
        have hmin : Nat.min 32 (end_ - p) ≤ end_ - p := Nat.min_le_right _ _
        omega
      have hpow : 1 < 256 ^ (end_ - p + 1 - Nat.min 32 (end_ - p)) :=
        Nat.one_lt_pow (Nat.ne_of_gt hrestPos) (by decide)
      have hmul : 256 ^ (end_ - p + 1 - Nat.min 32 (end_ - p)) ≤
          Model.bytesToNatPadded mem p (Nat.min 32 (end_ - p)) *
            256 ^ (end_ - p + 1 - Nat.min 32 (end_ - p)) := by
        simpa [Nat.mul_comm] using
          (Nat.mul_le_mul_right
            (256 ^ (end_ - p + 1 - Nat.min 32 (end_ - p))) hchunkPos)
      have hterm : 1 < Model.bytesToNatPadded mem p (Nat.min 32 (end_ - p)) *
          256 ^ (end_ - p + 1 - Nat.min 32 (end_ - p)) :=
        lt_of_lt_of_le hpow hmul
      have htotal : 1 < Model.bytesToNatPadded mem p (end_ - p + 1) := by
        rw [hsplit]
        omega
      simp [htotal.ne']
  · have hpEq : p = end_ := by omega
    subst p
    rw [memoryOneLoopResult, dif_neg (by omega)]
    have hone := memoryOneLast_eq_one_iff_model (mem := mem) (aw := aw)
      (last := end_) (by omega) (by omega) haw
    simp [memoryOneLastResult, hone]

theorem memoryOneResult_eq_reference {mem : ByteArray} {aw : UInt256}
    {ptr len : Nat} (hbound : ptr + 32 + len + 32 < 2 ^ 64)
    (hactive : ptr + 32 + len + 32 ≤ 32 * aw.toNat)
    (haw : 32 * aw.toNat < UInt256.size) :
    memoryOneResult mem aw ptr len = memoryOneReference mem ptr len := by
  by_cases hzero : len = 0
  · subst len
    have hread : Model.readPadded mem (ptr + 32) 0 = ByteArray.empty :=
      byteArray_eq_empty_of_size_eq_zero _ (model_readPadded_size mem (ptr + 32) 0)
    simp [memoryOneResult, memoryOneReference, Model.bytesToNatPadded,
      Model.bytesToBigEndianNat, hread, Reasoning.Theory.byteArray_toList_eq]
  · have hloop := memoryOneLoopResult_eq_reference (mem := mem) (aw := aw)
      (p := ptr + 32) (end_ := ptr + 32 + (len - 1))
      (by omega) (by omega) haw (by omega)
    rw [memoryOneResult, if_neg hzero, memoryOneReference]
    have hlen : len - 1 + 1 = len := by omega
    simpa [hlen] using hloop

private theorem memoryOneSetupDecodes :
    [decode runtimeBytecode ⟨2449⟩, decode runtimeBytecode ⟨2450⟩,
      decode runtimeBytecode ⟨2451⟩, decode runtimeBytecode ⟨2452⟩,
      decode runtimeBytecode ⟨2453⟩, decode runtimeBytecode ⟨2454⟩,
      decode runtimeBytecode ⟨2455⟩, decode runtimeBytecode ⟨2458⟩] =
    [some (.JUMPDEST, .none), some (.SWAP1, .none), some (.DUP2, .none),
      some (.MLOAD, .none), some (.DUP1, .none), some (.ISZERO, .none),
      some (.Push .PUSH2, some (⟨2568⟩, 2)), some (.JUMPI, .none)] := by
  native_decide

private theorem memoryOneNonzeroSetupDecodes :
    [decode runtimeBytecode ⟨2459⟩, decode runtimeBytecode ⟨2461⟩,
      decode runtimeBytecode ⟨2462⟩, decode runtimeBytecode ⟨2463⟩,
      decode runtimeBytecode ⟨2464⟩, decode runtimeBytecode ⟨2465⟩,
      decode runtimeBytecode ⟨2466⟩, decode runtimeBytecode ⟨2468⟩,
      decode runtimeBytecode ⟨2469⟩, decode runtimeBytecode ⟨2470⟩,
      decode runtimeBytecode ⟨2471⟩, decode runtimeBytecode ⟨2473⟩,
      decode runtimeBytecode ⟨2474⟩, decode runtimeBytecode ⟨2475⟩] =
    [some (.Push .PUSH1, some (⟨32⟩, 1)), some (.DUP4, .none),
      some (.ADD, .none), some (.SWAP3, .none), some (.ADD, .none),
      some (.SWAP2, .none), some (.Push .PUSH1, some (⟨31⟩, 1)),
      some (.DUP4, .none), some (.ADD, .none), some (.SWAP1, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)), some (.SWAP4, .none),
      some (.DUP5, .none), some (.SWAP2, .none)] := by
  native_decide

private theorem memoryOneZeroExitDecodes :
    [decode runtimeBytecode ⟨2568⟩, decode runtimeBytecode ⟨2569⟩,
      decode runtimeBytecode ⟨2570⟩, decode runtimeBytecode ⟨2571⟩,
      decode runtimeBytecode ⟨2572⟩, decode runtimeBytecode ⟨2573⟩] =
    [some (.JUMPDEST, .none), some (.POP, .none), some (.PUSH0, .none),
      some (.SWAP2, .none), some (.POP, .none), some (.JUMP, .none)] := by
  native_decide

private theorem memoryOneLoopHeaderDecodes :
    [decode runtimeBytecode ⟨2476⟩, decode runtimeBytecode ⟨2477⟩,
      decode runtimeBytecode ⟨2478⟩, decode runtimeBytecode ⟨2479⟩,
      decode runtimeBytecode ⟨2480⟩, decode runtimeBytecode ⟨2483⟩] =
    [some (.JUMPDEST, .none), some (.DUP4, .none), some (.DUP2, .none),
      some (.LT, .none), some (.Push .PUSH2, some (⟨2502⟩, 2)),
      some (.JUMPI, .none)] := by
  native_decide

private theorem memoryOneFinalDecodes :
    [decode runtimeBytecode ⟨2484⟩, decode runtimeBytecode ⟨2485⟩,
      decode runtimeBytecode ⟨2486⟩, decode runtimeBytecode ⟨2489⟩,
      decode runtimeBytecode ⟨2490⟩, decode runtimeBytecode ⟨2491⟩,
      decode runtimeBytecode ⟨2492⟩, decode runtimeBytecode ⟨2493⟩,
      decode runtimeBytecode ⟨2494⟩, decode runtimeBytecode ⟨2495⟩,
      decode runtimeBytecode ⟨2496⟩, decode runtimeBytecode ⟨2498⟩,
      decode runtimeBytecode ⟨2499⟩, decode runtimeBytecode ⟨2500⟩,
      decode runtimeBytecode ⟨2501⟩] =
    [some (.POP, .none), some (.POP, .none),
      some (.Push .PUSH2, some (⟨2492⟩, 2)), some (.JUMPI, .none),
      some (.POP, .none), some (.JUMP, .none), some (.JUMPDEST, .none),
      some (.MLOAD, .none), some (.PUSH0, .none), some (.BYTE, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)), some (.EQ, .none),
      some (.SWAP2, .none), some (.POP, .none), some (.JUMP, .none)] := by
  native_decide

private theorem memoryOneBodyDecodes :
    [decode runtimeBytecode ⟨2502⟩, decode runtimeBytecode ⟨2503⟩,
      decode runtimeBytecode ⟨2504⟩, decode runtimeBytecode ⟨2505⟩,
      decode runtimeBytecode ⟨2506⟩, decode runtimeBytecode ⟨2507⟩,
      decode runtimeBytecode ⟨2508⟩, decode runtimeBytecode ⟨2509⟩,
      decode runtimeBytecode ⟨2510⟩, decode runtimeBytecode ⟨2511⟩,
      decode runtimeBytecode ⟨2512⟩, decode runtimeBytecode ⟨2513⟩,
      decode runtimeBytecode ⟨2514⟩, decode runtimeBytecode ⟨2516⟩,
      decode runtimeBytecode ⟨2517⟩, decode runtimeBytecode ⟨2518⟩,
      decode runtimeBytecode ⟨2519⟩, decode runtimeBytecode ⟨2520⟩,
      decode runtimeBytecode ⟨2523⟩] =
    [some (.JUMPDEST, .none), some (.DUP1, .none), some (.SWAP2, .none),
      some (.SWAP3, .none), some (.POP, .none), some (.MLOAD, .none),
      some (.PUSH0, .none), some (.NOT, .none), some (.DUP3, .none),
      some (.DUP5, .none), some (.SUB, .none), some (.ADD, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.DUP1, .none),
      some (.DUP3, .none), some (.ADD, .none), some (.LT, .none),
      some (.Push .PUSH2, some (⟨2551⟩, 2)), some (.JUMPI, .none)] := by
  native_decide

private theorem memoryOnePartialDecodes :
    [decode runtimeBytecode ⟨2551⟩, decode runtimeBytecode ⟨2552⟩,
      decode runtimeBytecode ⟨2554⟩, decode runtimeBytecode ⟨2555⟩,
      decode runtimeBytecode ⟨2557⟩, decode runtimeBytecode ⟨2558⟩,
      decode runtimeBytecode ⟨2559⟩, decode runtimeBytecode ⟨2561⟩,
      decode runtimeBytecode ⟨2562⟩, decode runtimeBytecode ⟨2563⟩,
      decode runtimeBytecode ⟨2564⟩, decode runtimeBytecode ⟨2567⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.SUB, .none), some (.Push .PUSH1, some (⟨31⟩, 1)),
      some (.NOT, .none), some (.ADD, .none),
      some (.Push .PUSH1, some (⟨3⟩, 1)), some (.SHL, .none),
      some (.SHR, .none), some (.PUSH0, .none),
      some (.Push .PUSH2, some (⟨2524⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem memoryOneControlDecodes :
    [decode runtimeBytecode ⟨2524⟩, decode runtimeBytecode ⟨2525⟩,
      decode runtimeBytecode ⟨2526⟩, decode runtimeBytecode ⟨2529⟩,
      decode runtimeBytecode ⟨2530⟩, decode runtimeBytecode ⟨2531⟩,
      decode runtimeBytecode ⟨2533⟩, decode runtimeBytecode ⟨2534⟩,
      decode runtimeBytecode ⟨2535⟩, decode runtimeBytecode ⟨2536⟩,
      decode runtimeBytecode ⟨2537⟩, decode runtimeBytecode ⟨2540⟩,
      decode runtimeBytecode ⟨2541⟩, decode runtimeBytecode ⟨2542⟩,
      decode runtimeBytecode ⟨2543⟩, decode runtimeBytecode ⟨2544⟩,
      decode runtimeBytecode ⟨2545⟩, decode runtimeBytecode ⟨2546⟩,
      decode runtimeBytecode ⟨2547⟩, decode runtimeBytecode ⟨2550⟩] =
    [some (.JUMPDEST, .none), some (.POP, .none),
      some (.Push .PUSH2, some (⟨2541⟩, 2)), some (.JUMPI, .none),
      some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.ADD, .none), some (.SWAP1, .none), some (.DUP5, .none),
      some (.SWAP2, .none), some (.Push .PUSH2, some (⟨2476⟩, 2)),
      some (.JUMP, .none), some (.JUMPDEST, .none), some (.POP, .none),
      some (.PUSH0, .none), some (.SWAP4, .none), some (.POP, .none),
      some (.DUP2, .none), some (.Push .PUSH2, some (⟨2530⟩, 2)),
      some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_2476 :
    (D_J runtimeBytecode 0).contains ⟨2476⟩ = true := by native_decide

private theorem jumpDest_2492 :
    (D_J runtimeBytecode 0).contains ⟨2492⟩ = true := by native_decide

private theorem jumpDest_2502 :
    (D_J runtimeBytecode 0).contains ⟨2502⟩ = true := by native_decide

private theorem jumpDest_2524 :
    (D_J runtimeBytecode 0).contains ⟨2524⟩ = true := by native_decide

private theorem jumpDest_2530 :
    (D_J runtimeBytecode 0).contains ⟨2530⟩ = true := by native_decide

private theorem jumpDest_2541 :
    (D_J runtimeBytecode 0).contains ⟨2541⟩ = true := by native_decide

private theorem jumpDest_2551 :
    (D_J runtimeBytecode 0).contains ⟨2551⟩ = true := by native_decide

private theorem jumpDest_2568 :
    (D_J runtimeBytecode 0).contains ⟨2568⟩ = true := by native_decide

private theorem memoryOneLoopExitOne
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {p anchor end_ ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hpWord : p < UInt256.size) (hendWord : end_ < UInt256.size)
    (hstop : end_ ≤ p) (haccess : end_ + 32 ≤ 32 * aw.toNat)
    (htail : tail.length ≤ 1014)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2476⟩
      (UInt256.ofNat p :: UInt256.ofNat anchor :: ⟨1⟩ ::
        UInt256.ofNat end_ :: UInt256.ofNat ret :: ⟨1⟩ :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (UInt256.ofNat (memoryOneLastResult mem aw end_) :: tail)
      mem aw rdata acc (k + 19) (C + 68) := by
  have hh := memoryOneLoopHeaderDecodes
  simp only [List.cons.injEq, and_true] at hh
  rcases hh with ⟨h0,h1,h2,h3,h4,h5⟩
  have hlt : UInt256.lt (UInt256.ofNat p) (UInt256.ofNat end_) = ⟨0⟩ := by
    apply ult_zero
    rw [UInt256.toNat_ofNat_of_lt hpWord, UInt256.toNat_ofNat_of_lt hendWord]
    exact hstop
  have rdExit := evm_run rd0 with [known jumpdest h0, known dup4 h1,
    known dup2 h2, known lt h3, known push2 h4 ⟨2502⟩,
    known jumpiNT h5 hlt]
  have hf := memoryOneFinalDecodes
  simp only [List.cons.injEq, and_true] at hf
  rcases hf with ⟨f0,f1,f2,f3,_,_,f6,f7,f8,f9,f10,f11,f12,f13,f14⟩
  have rdLast := evm_run rdExit with [known pop f0, known pop f1,
    known push2 f2 ⟨2492⟩,
    known jumpiT f3 (by decide) jumpDest_2492, known jumpdest f6]
  have rdLoad := RDx.mloadWithin rdLast f7 (by
    rw [UInt256.toNat_ofNat_of_lt hendWord]
    exact haccess) (by simp; omega)
  have rd := evm_run rdLoad with [known push0 f8, known byte f9,
    known push1 f10 ⟨1⟩, known eq f11, known swap2 f12,
    known pop f13, known jump f14 hret]
  have hresult := memoryOneLastWordResult mem aw end_
  rw [memoryOneLast] at hresult
  rw [uInt256_eq_comm ⟨1⟩
    (UInt256.byteAt ⟨0⟩ (wideLoadWord mem aw (UInt256.ofNat end_)))] at rd
  rw [hresult] at rd
  exact rd.withIndices (by omega) (by omega)

private theorem memoryOneLoopExitZero
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {p anchor end_ ret : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hpWord : p < UInt256.size) (hendWord : end_ < UInt256.size)
    (hstop : end_ ≤ p) (htail : tail.length ≤ 1014)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2476⟩
      (UInt256.ofNat p :: UInt256.ofNat anchor :: ⟨0⟩ ::
        UInt256.ofNat end_ :: UInt256.ofNat ret :: ⟨0⟩ :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (⟨0⟩ :: tail) mem aw rdata acc (k + 12) (C + 50) := by
  have hh := memoryOneLoopHeaderDecodes
  simp only [List.cons.injEq, and_true] at hh
  rcases hh with ⟨h0,h1,h2,h3,h4,h5⟩
  have hlt : UInt256.lt (UInt256.ofNat p) (UInt256.ofNat end_) = ⟨0⟩ := by
    apply ult_zero
    rw [UInt256.toNat_ofNat_of_lt hpWord, UInt256.toNat_ofNat_of_lt hendWord]
    exact hstop
  have rdExit := evm_run rd0 with [known jumpdest h0, known dup4 h1,
    known dup2 h2, known lt h3, known push2 h4 ⟨2502⟩,
    known jumpiNT h5 hlt]
  have hf := memoryOneFinalDecodes
  simp only [List.cons.injEq, and_true] at hf
  rcases hf with ⟨f0,f1,f2,f3,f4,f5,_,_,_,_,_,_,_,_,_⟩
  have rd := evm_run rdExit with [known pop f0, known pop f1,
    known push2 f2 ⟨2492⟩, known jumpiNT f3 (by decide),
    known pop f4, known jump f5 hret]
  exact rd.withIndices (by omega) (by omega)

private theorem memoryOneWrappedRemaining {p end_ : Nat}
    (hend31 : 31 ≤ end_) (hp : p < end_) (hend : end_ < UInt256.size) :
    (UInt256.lnot ⟨0⟩ +
        UInt256.sub (UInt256.ofNat (end_ - 31)) (UInt256.ofNat p)) + ⟨32⟩ =
      UInt256.ofNat (end_ - p) := by
  let x := UInt256.sub (UInt256.ofNat (end_ - 31)) (UInt256.ofNat p)
  calc
    (UInt256.lnot ⟨0⟩ + x) + ⟨32⟩ =
        (UInt256.lnot ⟨0⟩ + ⟨32⟩) + x := by
          rw [u256_add_assoc, u256_add_comm x ⟨32⟩, ← u256_add_assoc]
    _ = UInt256.ofNat 31 + x := by
          rw [show UInt256.lnot ⟨0⟩ + ⟨32⟩ = UInt256.ofNat 31 by
            native_decide]
    _ = UInt256.ofNat (end_ - p) :=
          wrappedRemainingOffset hend31 hp hend

private theorem memoryOneReachChunk
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {p end_ ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hend31 : 31 ≤ end_) (hendWord : end_ + 32 < UInt256.size)
    (hp : p < end_) (haccess : p + 32 ≤ 32 * aw.toNat)
    (htail : tail.length ≤ 1013)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2476⟩
      (UInt256.ofNat p :: UInt256.ofNat (end_ - 31) :: ⟨1⟩ ::
        UInt256.ofNat end_ :: UInt256.ofNat ret :: ⟨1⟩ :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2526⟩
      (memoryZeroChunk mem aw p end_ :: UInt256.ofNat p ::
        UInt256.ofNat (end_ - 31) :: UInt256.ofNat end_ ::
        UInt256.ofNat ret :: ⟨1⟩ :: tail)
      mem aw rdata acc k' (C + if end_ - p < 32 then 124 else 86) := by
  have hh := memoryOneLoopHeaderDecodes
  simp only [List.cons.injEq, and_true] at hh
  rcases hh with ⟨hh0,hh1,hh2,hh3,hh4,hh5⟩
  have hb := memoryOneBodyDecodes
  simp only [List.cons.injEq, and_true] at hb
  rcases hb with
    ⟨hb0,hb1,hb2,hb3,hb4,hb5,hb6,hb7,hb8,hb9,hb10,hb11,hb12,
      hb13,hb14,hb15,hb16,hb17,hb18⟩
  have hpWord : p < UInt256.size := by omega
  have hendLt : end_ < UInt256.size := by omega
  have hlt : UInt256.lt (UInt256.ofNat p) (UInt256.ofNat end_) = ⟨1⟩ := by
    apply ult_one
    rw [UInt256.toNat_ofNat_of_lt hpWord, UInt256.toNat_ofNat_of_lt hendLt]
    exact hp
  have rdBody := evm_run rd0 with [known jumpdest hh0, known dup4 hh1,
    known dup2 hh2, known lt hh3, known push2 hh4 ⟨2502⟩,
    known jumpiT hh5 (by rw [hlt]; decide) jumpDest_2502,
    known jumpdest hb0, known dup1 hb1, known swap2 hb2,
    known swap3 hb3, known pop hb4]
  have rdLoad := RDx.mloadWithin rdBody hb5 (by
    rw [UInt256.toNat_ofNat_of_lt hpWord]
    exact haccess) (by simp; omega)
  have rdSelect := evm_run rdLoad with [known push0 hb6, known not hb7,
    known dup3 hb8, known dup5 hb9, known sub hb10, known add hb11,
    known push1 hb12 ⟨32⟩, known dup1 hb13, known dup3 hb14,
    known add hb15, known lt hb16, known push2 hb17 ⟨2551⟩]
  have hrem := memoryOneWrappedRemaining hend31 hp hendLt
  have hrem' :
      (UInt256.sub (UInt256.ofNat (end_ - 31)) (UInt256.ofNat p) +
          UInt256.lnot ⟨0⟩) + ⟨32⟩ = UInt256.ofNat (end_ - p) := by
    rw [u256_add_comm
      (UInt256.sub (UInt256.ofNat (end_ - 31)) (UInt256.ofNat p))
      (UInt256.lnot ⟨0⟩)]
    exact hrem
  rw [hrem'] at rdSelect
  have hremWord : end_ - p < UInt256.size := by omega
  by_cases hpartial : end_ - p < 32
  · have hltRem : UInt256.lt (UInt256.ofNat (end_ - p)) ⟨32⟩ = ⟨1⟩ := by
      apply ult_one
      rw [UInt256.toNat_ofNat_of_lt hremWord,
        show (⟨32⟩ : UInt256).toNat = 32 by decide]
      exact hpartial
    have rdPartial := rdSelect.jumpiT hb18 (by rw [hltRem]; decide)
      jumpDest_2551 (by evm_ov)
    have hd := memoryOnePartialDecodes
    simp only [List.cons.injEq, and_true] at hd
    rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩
    have rd := evm_run rdPartial with [known jumpdest h0,
      known push1 h1 ⟨32⟩, known sub h2, known push1 h3 ⟨31⟩,
      known not h4, known add h5, known push1 h6 ⟨3⟩, known shl h7,
      known shr h8, known push0 h9, known push2 h10 ⟨2524⟩,
      known jump h11 jumpDest_2524]
    have hc := memoryOneControlDecodes
    simp only [List.cons.injEq, and_true] at hc
    rcases hc with ⟨hc0,hc1,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩
    have rd' := evm_run rd with [known jumpdest hc0, known pop hc1]
    have hpc : (⟨2524⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ = ⟨2526⟩ := by
      native_decide
    rw [hpc] at rd'
    have hchunk :
        UInt256.shiftRight (wideLoadWord mem aw (UInt256.ofNat p))
            (UInt256.shiftLeft
              (UInt256.lnot ⟨31⟩ + UInt256.sub ⟨32⟩
                (UInt256.sub (UInt256.ofNat (end_ - 31)) (UInt256.ofNat p) +
                  UInt256.lnot ⟨0⟩))
              ⟨3⟩) = memoryZeroChunk mem aw p end_ := by
      rw [memoryZeroChunk, if_pos hpartial, partialShiftCount hrem']
    rw [hchunk] at rd'
    exact ⟨k + 39, rd'.withIndices (by omega) (by simp [hpartial])⟩
  · have hltRem : UInt256.lt (UInt256.ofNat (end_ - p)) ⟨32⟩ = ⟨0⟩ := by
      apply ult_zero
      rw [UInt256.toNat_ofNat_of_lt hremWord,
        show (⟨32⟩ : UInt256).toNat = 32 by decide]
      omega
    have rdFull := rdSelect.jumpiNT hb18 hltRem (by evm_ov)
    have hc := memoryOneControlDecodes
    simp only [List.cons.injEq, and_true] at hc
    rcases hc with ⟨hc0,hc1,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩
    have rd := evm_run rdFull with [known jumpdest hc0, known pop hc1]
    refine ⟨k + 27, ?_⟩
    simpa [memoryZeroChunk, hpartial] using
      (rd.withPC (by native_decide)).withIndices (by omega) (by simp [hpartial])

theorem memoryOneLoopExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {p end_ ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hend31 : 31 ≤ end_) (hendWord : end_ + 32 < UInt256.size)
    (hpBound : p ≤ end_ + 32) (hactive : end_ + 32 ≤ 32 * aw.toNat)
    (htail : tail.length ≤ 1013)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2476⟩
      (UInt256.ofNat p :: UInt256.ofNat (end_ - 31) :: ⟨1⟩ ::
        UInt256.ofNat end_ :: UInt256.ofNat ret :: ⟨1⟩ :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat ret) (UInt256.ofNat (memoryOneLoopResult mem aw p end_) :: tail)
      mem aw rdata acc k' (C + memoryOneLoopGas mem aw p end_) := by
  generalize hn : end_ - p = n
  induction n using Nat.strong_induction_on generalizing p k C
  rename_i n ih
  by_cases hp : p < end_
  · obtain ⟨kChunk, rdChunk⟩ := memoryOneReachChunk hend31 hendWord hp
      (by omega) htail rd0
    have hc := memoryOneControlDecodes
    simp only [List.cons.injEq, and_true] at hc
    rcases hc with
      ⟨_,_,hc2,hc3,hc4,hc5,hc6,hc7,hc8,hc9,hc10,hc11,
        hc12,hc13,hc14,hc15,hc16,hc17,hc18,hc19⟩
    by_cases hzero : memoryZeroChunk mem aw p end_ = ⟨0⟩
    · have rdNext := evm_run rdChunk with [known push2 hc2 ⟨2541⟩,
        known jumpiNT hc3 hzero, known jumpdest hc4,
        known push1 hc5 ⟨32⟩, known add hc6, known swap1 hc7,
        known dup5 hc8, known swap2 hc9, known push2 hc10 ⟨2476⟩,
        known jump hc11 jumpDest_2476]
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
      rw [memoryOneLoopResult, dif_pos hp, if_pos hzero,
        memoryOneLoopGas, dif_pos hp, if_pos hzero]
      exact rdFinal.withIndices rfl (by split <;> omega)
    · have rdFound := evm_run rdChunk with [known push2 hc2 ⟨2541⟩,
        known jumpiT hc3 hzero jumpDest_2541, known jumpdest hc12,
        known pop hc13, known push0 hc14, known swap4 hc15, known pop hc16,
        known dup2 hc17, known push2 hc18 ⟨2530⟩,
        known jump hc19 jumpDest_2530, known jumpdest hc4,
        known push1 hc5 ⟨32⟩, known add hc6, known swap1 hc7,
        known dup5 hc8, known swap2 hc9, known push2 hc10 ⟨2476⟩,
        known jump hc11 jumpDest_2476]
      have hendAdd : UInt256.ofNat end_ + (⟨32⟩ : UInt256) =
          UInt256.ofNat (end_ + 32) := by
        simpa only [show (⟨32⟩ : UInt256) = UInt256.ofNat 32 by rfl] using
          ofNat_add_bounded (a := end_) (b := 32) hendWord
      have hendAdd' : (⟨32⟩ : UInt256) + UInt256.ofNat end_ =
          UInt256.ofNat (end_ + 32) := by
        rw [u256_add_comm]
        exact hendAdd
      rw [hendAdd'] at rdFound
      have rdFinal := memoryOneLoopExitZero (p := end_ + 32) (end_ := end_)
        (anchor := end_ - 31) hendWord (by omega) (by omega) (by omega) hret rdFound
      refine ⟨kChunk + 30, ?_⟩
      rw [memoryOneLoopResult, dif_pos hp, if_neg hzero,
        memoryOneLoopGas, dif_pos hp, if_neg hzero]
      exact rdFinal.withIndices rfl (by split <;> omega)
  · have hpWord : p < UInt256.size := by omega
    have hendLt : end_ < UInt256.size := by omega
    have rdFinal := memoryOneLoopExitOne (p := p) (end_ := end_)
      (anchor := end_ - 31) hpWord hendLt (by omega) hactive (by omega) hret rd0
    refine ⟨k + 19, ?_⟩
    rw [memoryOneLoopResult, dif_neg hp, memoryOneLoopGas, dif_neg hp]
    exact rdFinal.withIndices rfl (by omega)

private theorem memoryOneZeroExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {ptr ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hptr : ptr < UInt256.size) (haccess : ptr + 32 ≤ 32 * aw.toNat)
    (hlength : wideLoadWord mem aw (UInt256.ofNat ptr) = ⟨0⟩)
    (htail : tail.length ≤ 1018)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2449⟩
      (UInt256.ofNat ptr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (⟨0⟩ :: tail) mem aw rdata acc (k + 14) (C + 47) := by
  have hs := memoryOneSetupDecodes
  simp only [List.cons.injEq, and_true] at hs
  rcases hs with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  have rdLoadAt := evm_run rd0 with [known jumpdest h0, known swap1 h1,
    known dup2 h2]
  have rdLoad := RDx.mloadWithin rdLoadAt h3 (by
    rw [UInt256.toNat_ofNat_of_lt hptr]
    exact haccess) (by simp; omega)
  rw [hlength] at rdLoad
  have rdExit := evm_run rdLoad with [known dup1 h4, known iszero h5,
    known push2 h6 ⟨2568⟩,
    known jumpiT h7 (by decide) jumpDest_2568]
  have hz := memoryOneZeroExitDecodes
  simp only [List.cons.injEq, and_true] at hz
  rcases hz with ⟨z0,z1,z2,z3,z4,z5⟩
  have rd := evm_run rdExit with [known jumpdest z0, known pop z1,
    known push0 z2, known swap2 z3, known pop z4, known jump z5 hret]
  exact rd.withIndices (by omega) (by omega)

private theorem reachMemoryOneLoop
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {ptr len ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hbound : ptr + 32 + len + 32 < UInt256.size)
    (haccess : ptr + 32 ≤ 32 * aw.toNat) (hlen : 0 < len)
    (hlength : wideLoadWord mem aw (UInt256.ofNat ptr) = UInt256.ofNat len)
    (htail : tail.length ≤ 1018)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2449⟩
      (UInt256.ofNat ptr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2476⟩
      (UInt256.ofNat (ptr + 32) :: UInt256.ofNat (ptr + len) :: ⟨1⟩ ::
        UInt256.ofNat (ptr + len + 31) :: UInt256.ofNat ret :: ⟨1⟩ :: tail)
      mem aw rdata acc (k + 22) (C + 71) := by
  have hs := memoryOneSetupDecodes
  simp only [List.cons.injEq, and_true] at hs
  rcases hs with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  have hptrWord : ptr < UInt256.size := by omega
  have hlenWord : len < UInt256.size := by omega
  have rdLoadAt := evm_run rd0 with [known jumpdest h0, known swap1 h1,
    known dup2 h2]
  have rdLoad := RDx.mloadWithin rdLoadAt h3 (by
    rw [UInt256.toNat_ofNat_of_lt hptrWord]
    exact haccess) (by simp; omega)
  rw [hlength] at rdLoad
  have hlenNe : UInt256.ofNat len ≠ ⟨0⟩ := by
    intro hz
    have := congrArg UInt256.toNat hz
    rw [UInt256.toNat_ofNat_of_lt hlenWord] at this
    simp at this
    omega
  have hnotZero := isZero_eq_zero_of_ne hlenNe
  have rdSetup := evm_run rdLoad with [known dup1 h4, known iszero h5,
    known push2 h6 ⟨2568⟩, known jumpiNT h7 hnotZero]
  have hn := memoryOneNonzeroSetupDecodes
  simp only [List.cons.injEq, and_true] at hn
  rcases hn with ⟨n0,n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,n12,n13⟩
  have rd := evm_run rdSetup with [known push1 n0 ⟨32⟩,
    known dup4 n1, known add n2, known swap3 n3, known add n4,
    known swap2 n5, known push1 n6 ⟨31⟩, known dup4 n7,
    known add n8, known swap1 n9, known push1 n10 ⟨1⟩,
    known swap4 n11, known dup5 n12, known swap2 n13]
  have hp32 := ofNat_add_bounded (a := ptr) (b := 32) (by omega)
  have hplen := ofNat_add_bounded (a := ptr) (b := len) (by omega)
  have hend31 := ofNat_add_bounded (a := ptr + len) (b := 31) (by omega)
  simp only [show (⟨32⟩ : UInt256) = UInt256.ofNat 32 by rfl,
    show (⟨31⟩ : UInt256) = UInt256.ofNat 31 by rfl] at rd
  rw [hp32, hplen, hend31] at rd
  exact (rd.withPC (by native_decide)).withIndices (by omega) (by omega)

/-- Full exact theorem for `LimbMath.isOneBytes` at PC 2449. -/
theorem memoryOneExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {ptr len ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hbound : ptr + 32 + len + 32 < UInt256.size)
    (hactive : ptr + 32 + len + 32 ≤ 32 * aw.toNat)
    (hlength : wideLoadWord mem aw (UInt256.ofNat ptr) = UInt256.ofNat len)
    (htail : tail.length ≤ 1013)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2449⟩
      (UInt256.ofNat ptr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat ret) (UInt256.ofNat (memoryOneResult mem aw ptr len) :: tail)
      mem aw rdata acc k' (C + memoryOneGas mem aw ptr len) := by
  by_cases hzero : len = 0
  · subst len
    have hlength0 : wideLoadWord mem aw (UInt256.ofNat ptr) = ⟨0⟩ := by
      simpa using hlength
    have rd := memoryOneZeroExact (ptr := ptr) (tail := tail) (by omega)
      (by omega) hlength0 (by omega) hret rd0
    refine ⟨k + 14, ?_⟩
    simpa [memoryOneResult, memoryOneGas] using rd
  · have hpos : 0 < len := Nat.pos_of_ne_zero hzero
    have rdLoop := reachMemoryOneLoop (ptr := ptr) (len := len) (ret := ret)
      hbound (by omega) hpos hlength (by omega) rd0
    have hendEq : ptr + len + 31 = ptr + 32 + (len - 1) := by omega
    rw [hendEq] at rdLoop
    obtain ⟨k', rdFinal⟩ := memoryOneLoopExact
      (p := ptr + 32) (end_ := ptr + 32 + (len - 1)) (ret := ret)
      (tail := tail) (mem := mem) (aw := aw)
      (by omega) (by omega) (by omega) (by omega) htail hret (by
        simpa only [show ptr + 32 + (len - 1) - 31 = ptr + len by omega] using rdLoop)
    refine ⟨k', ?_⟩
    rw [memoryOneResult, if_neg hzero, memoryOneGas, if_neg hzero]
    exact rdFinal.withIndices rfl (by omega)

/-- Public helper theorem stated only through the unchanged trusted ModExp parser. -/
theorem memoryOneExactTrusted
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {ptr len ret : Nat} {tail : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hbound : ptr + 32 + len + 32 < 2 ^ 64)
    (hactive : ptr + 32 + len + 32 ≤ 32 * aw.toNat)
    (haw : 32 * aw.toNat < UInt256.size)
    (hlength : wideLoadWord mem aw (UInt256.ofNat ptr) = UInt256.ofNat len)
    (htail : tail.length ≤ 1013)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2449⟩
      (UInt256.ofNat ptr :: UInt256.ofNat ret :: tail)
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      (UInt256.ofNat ret)
      (UInt256.ofNat
        (if Model.bytesToNatPadded mem (ptr + 32) len = 1 then 1 else 0) :: tail)
      mem aw rdata acc k' (C + memoryOneGas mem aw ptr len) := by
  obtain ⟨k', rd⟩ := memoryOneExact (hbound := lt_trans hbound (by decide))
    hactive hlength htail hret rd0
  rw [memoryOneResult_eq_reference hbound hactive haw] at rd
  exact ⟨k', rd⟩

end Modexp
