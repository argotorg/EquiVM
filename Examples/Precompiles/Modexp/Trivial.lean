import Examples.Precompiles.Modexp.GtOne

/-!
# Exact arbitrary-width trivial paths

This layer connects the wide dispatcher to the trusted exponent/base zero-or-one predicates.  Gas
definitions are intentionally bytecode-specific; functional predicates use only `Modexp.Model`.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false

def wideExponentOffset (baseSize : Nat) : Nat := 96 + baseSize
def wideModulusOffset (baseSize exponentSize : Nat) : Nat := 96 + baseSize + exponentSize

/-- Logical memory high-water mark after the exponent-zero block reserves its return region. -/
def exponentZeroWords (modulusSize : Nat) : Nat :=
  MachineState.M 3 128 modulusSize

def exponentZeroActiveWords (modulusSize : Nat) : UInt256 :=
  UInt256.ofNat (exponentZeroWords modulusSize)

/-- Dynamic memory expansion charged by the exponent-zero `CALLDATACOPY`. -/
def exponentZeroCopyMemoryGas (modulusSize : Nat) : Nat :=
  Cₘ (exponentZeroActiveWords modulusSize) - Cₘ (UInt256.ofNat 3)

/-- Complete local charge of that `CALLDATACOPY`, including its per-word copy component. -/
def exponentZeroCopyGas (modulusSize : Nat) : Nat :=
  exponentZeroCopyMemoryGas modulusSize + 3 + 3 * ((modulusSize + 31) / 32)

/-- Charge from PC 268 through the return from the trusted `isGt1` helper at PC 283. -/
def exponentZeroPredicateGas (I : ExecutionEnv) (modulusOffset modulusSize : Nat) : Nat :=
  29 + exponentZeroCopyGas modulusSize + isGt1Gas I modulusOffset modulusSize

/-- Final PC-283 return block charge, selected by the trusted modulus predicate. -/
def exponentZeroReturnGas (I : ExecutionEnv) (modulusOffset modulusSize : Nat) : Nat :=
  if 1 < Model.bytesToNatPadded I.calldata modulusOffset modulusSize then 33 else 17

/-- Exact charge from the wide implementation entry at PC 62 through exponent-zero return. -/
def wideExponentZeroGas (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  79 + cdRangeGas I (wideExponentOffset baseSize)
      (wideModulusOffset baseSize exponentSize) +
    exponentZeroPredicateGas I (wideModulusOffset baseSize exponentSize) modulusSize +
    exponentZeroReturnGas I (wideModulusOffset baseSize exponentSize) modulusSize

/-- Concrete memory after the exponent-zero/modulus-greater-than-one branch writes its final byte. -/
def exponentOneMemory (modulusSize : Nat) : ByteArray :=
  (⟨#[1]⟩ : ByteArray).write 0 solcFreePtrMem (127 + modulusSize) 1

theorem exponentZeroWords_lt_uint256 {modulusSize : Nat}
    (hsize : modulusSize ≤ 1024) : exponentZeroWords modulusSize < UInt256.size := by
  have hq : (128 + modulusSize + 31) / 32 ≤ 36 := by omega
  cases modulusSize with
  | zero => native_decide
  | succ n =>
      simp [exponentZeroWords, MachineState.M]
      exact ⟨by native_decide,
        lt_of_le_of_lt hq (by native_decide : 36 < UInt256.size)⟩

theorem exponentZeroWords_covers_return (modulusSize : Nat) :
    MachineState.M (exponentZeroWords modulusSize) 128 modulusSize =
      exponentZeroWords modulusSize := by
  cases modulusSize with
  | zero => rfl
  | succ n =>
      simp only [exponentZeroWords, MachineState.M]
      omega

theorem exponentZeroWords_covers_last {modulusSize : Nat} (hpos : 0 < modulusSize) :
    MachineState.M (exponentZeroWords modulusSize) (127 + modulusSize) 1 =
      exponentZeroWords modulusSize := by
  unfold exponentZeroWords MachineState.M
  simp only
  have hsame : (127 + modulusSize + 1 + 31) / 32 =
      (128 + modulusSize + 31) / 32 := by congr 2 <;> omega
  rw [hsame]
  cases modulusSize with
  | zero => omega
  | succ n => simp [MachineState.M]

theorem exponentOneMemory_eq {modulusSize : Nat} (hsize : modulusSize ≤ 1024) :
    exponentOneMemory modulusSize =
      solcFreePtrMem ++ ffi.ByteArray.zeroes (31 + modulusSize) ++ ⟨#[1]⟩ := by
  unfold exponentOneMemory
  rw [write_eq_gap (⟨#[1]⟩ : ByteArray) solcFreePtrMem (127 + modulusSize) 1
    (by decide) (by decide) (by rw [solcFreePtrMem_size]; omega)
    (by rw [solcFreePtrMem_size]; exact lt_usize _ (by omega))]
  rw [show 127 + modulusSize - solcFreePtrMem.size = 31 + modulusSize by
    rw [solcFreePtrMem_size]; omega]
  congr 1

theorem exponentOneMemory_read {modulusSize : Nat}
    (hsize : modulusSize ≤ 1024) (hpos : 0 < modulusSize) :
    (exponentOneMemory modulusSize).readWithPadding 128 modulusSize =
      Model.natToBytes 1 modulusSize := by
  rw [exponentOneMemory_eq hsize]
  let preMem : ByteArray := solcFreePtrMem ++ ffi.ByteArray.zeroes (31 + modulusSize)
  have hpreMem : preMem.size = 127 + modulusSize := by
    simp [preMem, solcFreePtrMem_size, ByteArray_zeroes_size]
    omega
  rw [readWithPadding_eq_extract' _ 128 modulusSize hpos (by omega) (by
    change 128 + modulusSize ≤ (preMem ++ (⟨#[1]⟩ : ByteArray)).size
    rw [ByteArray.size_append, hpreMem]
    change 128 + modulusSize ≤ 127 + modulusSize + 1
    omega)]
  change (preMem ++ (⟨#[1]⟩ : ByteArray)).extract 128 (128 + modulusSize) = _
  rw [extract_append_span preMem (⟨#[1]⟩ : ByteArray) 128 (128 + modulusSize)
    (by rw [hpreMem]; omega) (by rw [hpreMem]; omega)]
  rw [extract_append_right_window solcFreePtrMem
    (ffi.ByteArray.zeroes (31 + modulusSize)) 128 preMem.size
    (by rw [solcFreePtrMem_size]; omega)]
  rw [solcFreePtrMem_size, hpreMem]
  rw [show 128 - 96 = 32 by omega,
    show 127 + modulusSize - 96 = 31 + modulusSize by omega]
  rw [zeroes_extract (31 + modulusSize) 32 (31 + modulusSize) (by omega) (le_refl _)]
  rw [show 31 + modulusSize - 32 = modulusSize - 1 by omega]
  rw [show 128 + modulusSize - (127 + modulusSize) = 1 by omega]
  have honeExtract : (⟨#[1]⟩ : ByteArray).extract 0 1 = ⟨#[1]⟩ := by
    apply ByteArray.ext
    simp only [ByteArray.data_extract]
    rfl
  rw [honeExtract, model_natToBytes_one hpos]
  congr 1
  rw [← model_natToBytes_zero_eq_zeroes, model_natToBytes_zero]

private theorem wideExponentSetupDecodes :
    [decode runtimeBytecode ⟨62⟩, decode runtimeBytecode ⟨63⟩,
      decode runtimeBytecode ⟨65⟩, decode runtimeBytecode ⟨66⟩,
      decode runtimeBytecode ⟨67⟩, decode runtimeBytecode ⟨69⟩,
      decode runtimeBytecode ⟨70⟩, decode runtimeBytecode ⟨71⟩,
      decode runtimeBytecode ⟨72⟩, decode runtimeBytecode ⟨73⟩,
      decode runtimeBytecode ⟨74⟩, decode runtimeBytecode ⟨77⟩,
      decode runtimeBytecode ⟨78⟩, decode runtimeBytecode ⟨79⟩,
      decode runtimeBytecode ⟨82⟩, decode runtimeBytecode ⟨83⟩,
      decode runtimeBytecode ⟨84⟩, decode runtimeBytecode ⟨85⟩,
      decode runtimeBytecode ⟨88⟩] =
    [some (.DUP2, .none), some (.Push .PUSH1, some (⟨96⟩, 1)),
      some (.ADD, .none), some (.SWAP1, .none),
      some (.Push .PUSH1, some (⟨96⟩, 1)), some (.DUP2, .none),
      some (.DUP5, .none), some (.ADD, .none), some (.ADD, .none),
      some (.DUP5, .none), some (.Push .PUSH2, some (⟨83⟩, 2)),
      some (.DUP3, .none), some (.DUP6, .none),
      some (.Push .PUSH2, some (⟨694⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.ISZERO, .none),
      some (.Push .PUSH2, some (⟨268⟩, 2)), some (.JUMPI, .none)] := by
  native_decide

private theorem exponentZeroPredicateDecodes :
    [decode runtimeBytecode ⟨268⟩, decode runtimeBytecode ⟨269⟩,
      decode runtimeBytecode ⟨272⟩, decode runtimeBytecode ⟨273⟩,
      decode runtimeBytecode ⟨274⟩, decode runtimeBytecode ⟨275⟩,
      decode runtimeBytecode ⟨276⟩, decode runtimeBytecode ⟨278⟩,
      decode runtimeBytecode ⟨279⟩, decode runtimeBytecode ⟨282⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH2, some (⟨283⟩, 2)),
      some (.DUP2, .none), some (.DUP4, .none), some (.DUP2, .none),
      some (.CALLDATASIZE, .none), some (.Push .PUSH1, some (⟨128⟩, 1)),
      some (.CALLDATACOPY, .none), some (.Push .PUSH2, some (⟨762⟩, 2)),
      some (.JUMP, .none)] := by
  native_decide

private theorem exponentZeroReturnDecodes :
    [decode runtimeBytecode ⟨283⟩, decode runtimeBytecode ⟨284⟩,
      decode runtimeBytecode ⟨287⟩, decode runtimeBytecode ⟨288⟩,
      decode runtimeBytecode ⟨290⟩, decode runtimeBytecode ⟨291⟩,
      decode runtimeBytecode ⟨292⟩, decode runtimeBytecode ⟨294⟩,
      decode runtimeBytecode ⟨296⟩, decode runtimeBytecode ⟨297⟩,
      decode runtimeBytecode ⟨298⟩, decode runtimeBytecode ⟨299⟩,
      decode runtimeBytecode ⟨301⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH2, some (⟨291⟩, 2)),
      some (.JUMPI, .none), some (.Push .PUSH1, some (⟨128⟩, 1)),
      some (.RETURN, .none), some (.JUMPDEST, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)),
      some (.Push .PUSH1, some (⟨127⟩, 1)), some (.DUP3, .none),
      some (.ADD, .none), some (.MSTORE8, .none),
      some (.Push .PUSH1, some (⟨128⟩, 1)), some (.RETURN, .none)] := by
  native_decide

private theorem ofNat_add {a b : Nat} (hab : a + b < UInt256.size) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  apply u256_inj
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega),
    UInt256.toNat_ofNat_of_lt (by omega), UInt256.toNat_ofNat_of_lt hab,
    Nat.mod_eq_of_lt hab]

/-- Common wide prelude through the completed exponent scan, before its zero/nonzero branch. -/
theorem reachWideExponentScanned {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hbound : 96 + baseSize + exponentSize + 32 < 2 ^ 64)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨62⟩
      [UInt256.ofNat exponentSize, UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨83⟩
      (UInt256.ofNat (if Model.bytesToNatPadded I.calldata
          (wideExponentOffset baseSize) exponentSize = 0 then 0 else 1) ::
        UInt256.ofNat modulusSize :: UInt256.ofNat (wideModulusOffset baseSize exponentSize) ::
        UInt256.ofNat exponentSize :: UInt256.ofNat (wideExponentOffset baseSize) ::
        UInt256.ofNat baseSize :: UInt256.ofNat modulusSize :: [])
      mem aw rdata acc k'
      (C + 62 + cdRangeGas I (wideExponentOffset baseSize)
        (wideModulusOffset baseSize exponentSize)) := by
  have hd := wideExponentSetupDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9,
    hd10, hd11, hd12, hd13, hd14, _, _, _, _⟩
  have rdRangeRaw := evm_run rd0 with [
    known dup2 hd0, known push1 hd1 ⟨96⟩, known add hd2, known swap1 hd3,
    known push1 hd4 ⟨96⟩, known dup2 hd5, known dup5 hd6,
    known add hd7, known add hd8, known dup5 hd9,
    known push2 hd10 ⟨83⟩, known dup3 hd11, known dup6 hd12,
    known push2 hd13 ⟨694⟩, known jump hd14 jumpDest_694 ]
  have hb96 : 96 + baseSize < UInt256.size :=
    lt_trans (by omega : 96 + baseSize < 2 ^ 64) (by decide)
  have hbe96 : 96 + baseSize + exponentSize < UInt256.size :=
    lt_trans (by omega : 96 + baseSize + exponentSize < 2 ^ 64) (by decide)
  have h96 : (⟨96⟩ : UInt256) = UInt256.ofNat 96 := by native_decide
  have hExpOff : (⟨96⟩ : UInt256) + UInt256.ofNat baseSize =
      UInt256.ofNat (wideExponentOffset baseSize) := by
    rw [h96, ofNat_add hb96]
    rfl
  have hModOff : UInt256.ofNat baseSize + UInt256.ofNat exponentSize + (⟨96⟩ : UInt256) =
      UInt256.ofNat (wideModulusOffset baseSize exponentSize) := by
    calc
      _ = UInt256.ofNat (baseSize + exponentSize) + UInt256.ofNat 96 := by
        rw [ofNat_add (by omega), h96]
      _ = UInt256.ofNat (baseSize + exponentSize + 96) := ofNat_add (by omega)
      _ = UInt256.ofNat (wideModulusOffset baseSize exponentSize) :=
        congrArg UInt256.ofNat (by unfold wideModulusOffset; omega)
  have rdRange := rdRangeRaw.withStack (by rw [hExpOff, hModOff])
  obtain ⟨kScan, rdScanned⟩ := cdRangeExactTrusted (I := I)
    (tail := [UInt256.ofNat modulusSize,
      UInt256.ofNat (wideModulusOffset baseSize exponentSize),
      UInt256.ofNat exponentSize, UInt256.ofNat (wideExponentOffset baseSize),
      UInt256.ofNat baseSize, UInt256.ofNat modulusSize])
    (htail := by simp) (hend64 := by unfold wideModulusOffset; omega)
    (hstart := by unfold wideExponentOffset wideModulusOffset; omega)
    jumpDest_83 rdRange
  unfold cdRangeReference at rdScanned
  rw [show wideModulusOffset baseSize exponentSize - wideExponentOffset baseSize =
    exponentSize by unfold wideExponentOffset wideModulusOffset; omega] at rdScanned
  exact ⟨kScan, rdScanned.withIndices rfl (by omega)⟩

/-- Nonzero-exponent side of the common wide prelude. -/
theorem reachWideExponentNonzero {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hbound : 96 + baseSize + exponentSize + 32 < 2 ^ 64)
    (hexp : Model.bytesToNatPadded I.calldata
      (wideExponentOffset baseSize) exponentSize ≠ 0)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨62⟩
      [UInt256.ofNat exponentSize, UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨89⟩
      [UInt256.ofNat modulusSize, UInt256.ofNat (wideModulusOffset baseSize exponentSize),
        UInt256.ofNat exponentSize, UInt256.ofNat (wideExponentOffset baseSize),
        UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      mem aw rdata acc k'
      (C + 79 + cdRangeGas I (wideExponentOffset baseSize)
        (wideModulusOffset baseSize exponentSize)) := by
  obtain ⟨k1, rd1⟩ := reachWideExponentScanned hbound rd0
  have hd := wideExponentSetupDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd15, hd16, hd17, hd18⟩
  have rdFlag : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨83⟩
      ((⟨1⟩ : UInt256) :: UInt256.ofNat modulusSize ::
        UInt256.ofNat (wideModulusOffset baseSize exponentSize) ::
        UInt256.ofNat exponentSize :: UInt256.ofNat (wideExponentOffset baseSize) ::
        UInt256.ofNat baseSize :: UInt256.ofNat modulusSize :: [])
      mem aw rdata acc k1
      (C + 62 + cdRangeGas I (wideExponentOffset baseSize)
        (wideModulusOffset baseSize exponentSize)) := by
    simpa [hexp] using rd1
  have rd := evm_run rdFlag with [
    known jumpdest hd15, known iszero hd16,
    known push2 hd17 ⟨268⟩, known jumpiNT hd18 (by native_decide) ]
  exact ⟨k1 + 4, rd.withIndices (by omega) (by omega)⟩

/-- The shared wide prelude scans the exponent and selects the exponent-zero return block. -/
theorem reachWideExponentZero {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hbound : 96 + baseSize + exponentSize + 32 < 2 ^ 64)
    (hexp : Model.bytesToNatPadded I.calldata
      (wideExponentOffset baseSize) exponentSize = 0)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨62⟩
      [UInt256.ofNat exponentSize, UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      mem aw rdata acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨268⟩
      [UInt256.ofNat modulusSize, UInt256.ofNat (wideModulusOffset baseSize exponentSize),
        UInt256.ofNat exponentSize, UInt256.ofNat (wideExponentOffset baseSize),
        UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      mem aw rdata acc k'
      (C + 79 + cdRangeGas I (wideExponentOffset baseSize)
        (wideModulusOffset baseSize exponentSize)) := by
  have hd := wideExponentSetupDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9,
    hd10, hd11, hd12, hd13, hd14, hd15, hd16, hd17, hd18⟩
  have rdRangeRaw := evm_run rd0 with [
    known dup2 hd0,
    known push1 hd1 ⟨96⟩,
    known add hd2,
    known swap1 hd3,
    known push1 hd4 ⟨96⟩,
    known dup2 hd5,
    known dup5 hd6,
    known add hd7,
    known add hd8,
    known dup5 hd9,
    known push2 hd10 ⟨83⟩,
    known dup3 hd11,
    known dup6 hd12,
    known push2 hd13 ⟨694⟩,
    known jump hd14 jumpDest_694 ]
  have hb96 : 96 + baseSize < UInt256.size := by
    exact lt_trans (by omega : 96 + baseSize < 2 ^ 64) (by decide)
  have hbe96 : 96 + baseSize + exponentSize < UInt256.size := by
    exact lt_trans (by omega : 96 + baseSize + exponentSize < 2 ^ 64) (by decide)
  have h96 : (⟨96⟩ : UInt256) = UInt256.ofNat 96 := by native_decide
  have hExpOff : (⟨96⟩ : UInt256) + UInt256.ofNat baseSize =
      UInt256.ofNat (wideExponentOffset baseSize) := by
    rw [h96, ofNat_add hb96]
    rfl
  have hModOff : UInt256.ofNat baseSize + UInt256.ofNat exponentSize + (⟨96⟩ : UInt256) =
      UInt256.ofNat (wideModulusOffset baseSize exponentSize) := by
    calc
      _ = UInt256.ofNat (baseSize + exponentSize) + UInt256.ofNat 96 := by
        rw [ofNat_add (by omega)]
        rw [h96]
      _ = UInt256.ofNat (baseSize + exponentSize + 96) :=
        ofNat_add (by omega)
      _ = UInt256.ofNat (wideModulusOffset baseSize exponentSize) :=
        congrArg UInt256.ofNat (by unfold wideModulusOffset; omega)
  have hstack :
      [(⟨96⟩ : UInt256) + UInt256.ofNat baseSize,
        UInt256.ofNat baseSize + UInt256.ofNat exponentSize + (⟨96⟩ : UInt256),
        ⟨83⟩, UInt256.ofNat modulusSize,
        UInt256.ofNat baseSize + UInt256.ofNat exponentSize + (⟨96⟩ : UInt256),
        UInt256.ofNat exponentSize, (⟨96⟩ : UInt256) + UInt256.ofNat baseSize,
        UInt256.ofNat baseSize, UInt256.ofNat modulusSize] =
      [UInt256.ofNat (wideExponentOffset baseSize),
        UInt256.ofNat (wideModulusOffset baseSize exponentSize), ⟨83⟩,
        UInt256.ofNat modulusSize, UInt256.ofNat (wideModulusOffset baseSize exponentSize),
        UInt256.ofNat exponentSize, UInt256.ofNat (wideExponentOffset baseSize),
        UInt256.ofNat baseSize, UInt256.ofNat modulusSize] := by
    rw [hExpOff, hModOff]
  have rdRange := rdRangeRaw.withStack hstack
  obtain ⟨kScan, rdScanned⟩ := cdRangeExactTrusted (I := I)
    (tail := [UInt256.ofNat modulusSize,
      UInt256.ofNat (wideModulusOffset baseSize exponentSize),
      UInt256.ofNat exponentSize, UInt256.ofNat (wideExponentOffset baseSize),
      UInt256.ofNat baseSize, UInt256.ofNat modulusSize])
    (htail := by simp only [List.length_cons, List.length_nil]; omega)
    (hend64 := by unfold wideModulusOffset; omega)
    (hstart := by unfold wideExponentOffset wideModulusOffset; omega)
    jumpDest_83 rdRange
  have href : cdRangeReference I (wideExponentOffset baseSize)
      (wideModulusOffset baseSize exponentSize) = 0 := by
    unfold cdRangeReference
    rw [show wideModulusOffset baseSize exponentSize - wideExponentOffset baseSize =
      exponentSize by unfold wideExponentOffset wideModulusOffset; omega]
    rw [hexp]
    rfl
  have rdZero := rdScanned.withStack (by rw [href])
  have rdFinal := evm_run rdZero with [
    known jumpdest hd15,
    known iszero hd16,
    known push2 hd17 ⟨268⟩,
    known jumpiT hd18 (by native_decide) jumpDest_268 ]
  exact ⟨kScan + 4, rdFinal.withIndices (by omega) (by omega)⟩

/-- Reserve the zero return region and evaluate whether the trusted modulus field exceeds one.
The concrete byte-array copy is a no-op because it deliberately copies from `calldatasize()`, but
the logical active-memory words and the exact expansion/copy gas are retained. -/
theorem reachExponentZeroPredicate {cA gh bl σ σ₀ A I} {g : Sat256}
    {modulusOffset modulusSize : Nat} {tail : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hsize : modulusSize ≤ 1024)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hbound : modulusOffset + modulusSize + 32 < 2 ^ 64)
    (htail : tail.length ≤ 1011)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨268⟩
      (UInt256.ofNat modulusSize :: UInt256.ofNat modulusOffset :: tail)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    ∃ k', RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨283⟩
      (UInt256.ofNat
          (if 1 < Model.bytesToNatPadded I.calldata modulusOffset modulusSize then 1 else 0) ::
        UInt256.ofNat modulusSize :: UInt256.ofNat modulusOffset :: tail)
      solcFreePtrMem (exponentZeroActiveWords modulusSize) ByteArray.empty acc k'
      (C + exponentZeroPredicateGas I modulusOffset modulusSize) := by
  have hd := exponentZeroPredicateDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9⟩
  have hsize256 : modulusSize < UInt256.size :=
    lt_trans (lt_of_le_of_lt hsize (by decide : 1024 < 2 ^ 64)) (by decide)
  have hcd256 : I.calldata.size < UInt256.size :=
    lt_trans hcalldata (by decide)
  have rdCopy0 := evm_run rd0 with [
    known jumpdest hd0,
    known push2 hd1 ⟨283⟩,
    known dup2 hd2,
    known dup4 hd3,
    known dup2 hd4,
    known calldatasize hd5,
    known push1 hd6 ⟨128⟩ ]
  have rdCopy := RDx.calldatacopy
    (exponentZeroCopyMemoryGas modulusSize) solcFreePtrMem
    (exponentZeroActiveWords modulusSize) rdCopy0 hd7
    (by
      intro s haw hstk
      simp [exponentZeroCopyMemoryGas, exponentZeroActiveWords,
        exponentZeroWords, memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      rw [show (UInt256.ofNat 3).toNat = 3 by native_decide,
        show (⟨128⟩ : UInt256).toNat = 128 by native_decide,
        UInt256.toNat_ofNat_of_lt hsize256])
    (by
      rw [UInt256.toNat_ofNat_of_lt hcd256, UInt256.toNat_ofNat_of_lt hsize256]
      exact write_from_source_end_past_dest I.calldata solcFreePtrMem
        I.calldata.size 128 modulusSize (le_refl _)
          (by rw [solcFreePtrMem_size]; omega))
    (by
      simp [exponentZeroActiveWords, exponentZeroWords]
      rw [show (UInt256.ofNat 3).toNat = 3 by native_decide,
        show (⟨128⟩ : UInt256).toNat = 128 by native_decide,
        UInt256.toNat_ofNat_of_lt hsize256])
    (by simp only [List.length_cons]; omega)
  have rdHelperRaw := evm_run rdCopy with [
    known push2 hd8 ⟨762⟩,
    known jump hd9 jumpDest_762 ]
  have rdHelper : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨762⟩
      (UInt256.ofNat modulusOffset :: UInt256.ofNat modulusSize :: ⟨283⟩ ::
        UInt256.ofNat modulusSize :: UInt256.ofNat modulusOffset :: tail)
      solcFreePtrMem (exponentZeroActiveWords modulusSize) ByteArray.empty acc
      (k + 10) (C + 29 + exponentZeroCopyGas modulusSize) := by
    exact (rdHelperRaw.withStack (by rfl)).withIndices (by omega) (by
      rw [UInt256.toNat_ofNat_of_lt hsize256]
      simp [exponentZeroCopyGas, GasConstants.Gverylow, GasConstants.Gcopy]
      omega)
  obtain ⟨k', rdResult⟩ := isGt1ExactTrusted
    (tail := UInt256.ofNat modulusSize :: UInt256.ofNat modulusOffset :: tail)
    (by simp only [List.length_cons]; omega) hbound jumpDest_283 rdHelper
  exact ⟨k', rdResult.withIndices rfl (by simp [exponentZeroPredicateGas]; omega)⟩

/-- Exact terminal behavior of the exponent-zero return block.  It returns zero for modulus zero
or one and the width-padded integer one otherwise, exactly matching `b^0 mod m`. -/
theorem exponentZeroReturnExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {modulusOffset modulusSize : Nat} {tail : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hsize : modulusSize ≤ 1024) (htail : tail.length ≤ 1016)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨283⟩
      (UInt256.ofNat
          (if 1 < Model.bytesToNatPadded I.calldata modulusOffset modulusSize then 1 else 0) ::
        UInt256.ofNat modulusSize :: UInt256.ofNat modulusOffset :: tail)
      solcFreePtrMem (exponentZeroActiveWords modulusSize) ByteArray.empty acc k C) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes
        (if 1 < Model.bytesToNatPadded I.calldata modulusOffset modulusSize then 1 else 0)
        modulusSize)
      (C + exponentZeroReturnGas I modulusOffset modulusSize) := by
  have hd := exponentZeroReturnDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12⟩
  have hsize256 : modulusSize < UInt256.size :=
    lt_trans (lt_of_le_of_lt hsize (by decide : 1024 < 2 ^ 64)) (by decide)
  have hwords256 := exponentZeroWords_lt_uint256 hsize
  by_cases hgt : 1 < Model.bytesToNatPadded I.calldata modulusOffset modulusSize
  · have hpos : 0 < modulusSize := by
      by_contra hnpos
      have hz : modulusSize = 0 := Nat.eq_zero_of_not_pos hnpos
      subst modulusSize
      simp at hgt
    have rdCommon0 := rd0.withStack (by rw [if_pos hgt])
    have rdAt291 := evm_run rdCommon0 with [
      known jumpdest hd0,
      known push2 hd1 ⟨291⟩,
      known jumpiT hd2 (by native_decide) jumpDest_291 ]
    have rdStore0 := evm_run rdAt291 with [
      known jumpdest hd5,
      known push1 hd6 ⟨1⟩,
      known push1 hd7 ⟨127⟩,
      known dup3 hd8,
      known add hd9 ]
    have haddr256 : 127 + modulusSize < UInt256.size :=
      lt_trans (by omega : 127 + modulusSize < 2 ^ 64) (by decide)
    have haddr : UInt256.ofNat modulusSize + (⟨127⟩ : UInt256) =
        UInt256.ofNat (127 + modulusSize) := by
      rw [show (⟨127⟩ : UInt256) = UInt256.ofNat 127 by native_decide,
        ofNat_add (by omega)]
      exact congrArg UInt256.ofNat (Nat.add_comm modulusSize 127)
    rw [haddr] at rdStore0
    have rdStore := RDx.mstore8 0 (exponentOneMemory modulusSize)
      (exponentZeroActiveWords modulusSize) rdStore0 hd10
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          exponentZeroActiveWords]
        rw [UInt256.toNat_ofNat_of_lt hwords256,
          UInt256.toNat_ofNat_of_lt haddr256,
          exponentZeroWords_covers_last hpos]
        omega)
      (by
        rw [UInt256.toNat_ofNat_of_lt haddr256]
        rw [show UInt8.ofNat (⟨1⟩ : UInt256).toNat = 1 by native_decide]
        rfl)
      (by
        simp [exponentZeroActiveWords]
        rw [UInt256.toNat_ofNat_of_lt hwords256,
          UInt256.toNat_ofNat_of_lt haddr256,
          exponentZeroWords_covers_last hpos])
      (by simp only [List.length_cons]; omega)
    have rdReturnRaw := evm_run rdStore with [known push1 hd11 ⟨128⟩]
    have rdReturn : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨301⟩
        (⟨128⟩ :: UInt256.ofNat modulusSize :: UInt256.ofNat modulusOffset :: tail)
        (exponentOneMemory modulusSize) (exponentZeroActiveWords modulusSize)
        ByteArray.empty acc (k + 10) (C + 33) := by
      exact rdReturnRaw.withIndices (by omega) (by omega)
    have hret := RDx.ret 0 (Model.natToBytes 1 modulusSize) rdReturn hd12
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          exponentZeroActiveWords]
        rw [show (⟨128⟩ : UInt256).toNat = 128 by native_decide,
          UInt256.toNat_ofNat_of_lt hwords256,
          UInt256.toNat_ofNat_of_lt hsize256,
          exponentZeroWords_covers_return]
        omega)
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 by native_decide,
          UInt256.toNat_ofNat_of_lt hsize256]
        exact exponentOneMemory_read hsize hpos)
      (by simp only [List.length_cons]; omega)
    simpa [exponentZeroReturnGas, hgt] using hret
  · have rdCommon0 := rd0.withStack (by rw [if_neg hgt])
    have rdReturnRaw := evm_run rdCommon0 with [
      known jumpdest hd0,
      known push2 hd1 ⟨291⟩,
      known jumpiNT hd2 (by native_decide),
      known push1 hd3 ⟨128⟩ ]
    have rdReturn : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨290⟩
        (⟨128⟩ :: UInt256.ofNat modulusSize :: UInt256.ofNat modulusOffset :: tail)
        solcFreePtrMem (exponentZeroActiveWords modulusSize) ByteArray.empty acc
        (k + 4) (C + 17) := by
      exact rdReturnRaw.withIndices (by omega) (by omega)
    have hret := RDx.ret 0 (Model.natToBytes 0 modulusSize) rdReturn hd4
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          exponentZeroActiveWords]
        rw [show (⟨128⟩ : UInt256).toNat = 128 by native_decide,
          UInt256.toNat_ofNat_of_lt hwords256,
          UInt256.toNat_ofNat_of_lt hsize256,
          exponentZeroWords_covers_return]
        omega)
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 by native_decide,
          UInt256.toNat_ofNat_of_lt hsize256]
        rw [readWithPadding_past_end solcFreePtrMem 128 modulusSize
          (by rw [solcFreePtrMem_size]; omega) (by omega)]
        exact (model_natToBytes_zero_eq_zeroes modulusSize).symm)
      (by simp only [List.length_cons]; omega)
    simpa [exponentZeroReturnGas, hgt] using hret

/-- Completed arbitrary-width exponent-zero path, from the common wide entry through `RETURN`. -/
theorem wideExponentZeroExact {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat} {k C : Nat}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hsize : modulusSize ≤ 1024)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hbound : 96 + baseSize + exponentSize + modulusSize + 32 < 2 ^ 64)
    (hexp : Model.bytesToNatPadded I.calldata
      (wideExponentOffset baseSize) exponentSize = 0)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨62⟩
      [UInt256.ofNat exponentSize, UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes
        (if 1 < Model.bytesToNatPadded I.calldata
          (wideModulusOffset baseSize exponentSize) modulusSize then 1 else 0)
        modulusSize)
      (C + wideExponentZeroGas I baseSize exponentSize modulusSize) := by
  obtain ⟨k1, rd1⟩ := reachWideExponentZero
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (by omega) hexp rd0
  obtain ⟨k2, rd2⟩ := reachExponentZeroPredicate
    (modulusOffset := wideModulusOffset baseSize exponentSize)
    (modulusSize := modulusSize)
    (tail := [UInt256.ofNat exponentSize, UInt256.ofNat (wideExponentOffset baseSize),
      UInt256.ofNat baseSize, UInt256.ofNat modulusSize])
    hsize hcalldata (by unfold wideModulusOffset; omega) (by simp) rd1
  have hret := exponentZeroReturnExact
    (tail := [UInt256.ofNat exponentSize, UInt256.ofNat (wideExponentOffset baseSize),
      UInt256.ofNat baseSize, UInt256.ofNat modulusSize])
    hsize (by simp) rd2
  exact hret.withCost (by simp [wideExponentZeroGas]; omega)

end Modexp
