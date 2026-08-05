import Examples.Precompiles.Modexp.WideWordReturn

/-! # Exact arbitrary-input, one-word-modulus helper

This file composes the decoded setup, base reduction, exponentiation, and result-copy traces for
`LimbMath.modexpWordInto`.  Its cost functions describe this particular bytecode implementation;
the semantic theorem below relates its computed word to the trusted EEST-tested ModExp model.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxHeartbeats 0
set_option maxRecDepth 500000
set_option Elab.async false

def wideWordBaseStart (baseSize : Nat) : Nat := baseSize % 32

def wideWordBaseAccAt (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  if baseSize % 32 = 0 then ⟨0⟩
  else widePartialBaseAt mem aw baseSize exponentSize modulusSize

def wideWordBaseAcc (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  wideWordBaseAccAt (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize)
    baseSize exponentSize modulusSize

def wideWordBaseAccWithModulusAt (mem : ByteArray) (aw : UInt256)
    (baseSize : Nat) (modulus : UInt256) : UInt256 :=
  if baseSize % 32 = 0 then ⟨0⟩
  else widePartialBaseWithModulusAt mem aw baseSize modulus

def wideWordBaseValueAt (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  wideBaseFold mem aw
    (wideR256 (wideWordModulusAt mem aw baseSize exponentSize modulusSize))
    (wideWordModulusAt mem aw baseSize exponentSize modulusSize) (baseSize / 32)
    (operandBasePtr + 32 + wideWordBaseStart baseSize)
    (wideWordBaseAccAt mem aw baseSize exponentSize modulusSize)

def wideWordBaseValueWithModulusAt (mem : ByteArray) (aw : UInt256)
    (baseSize : Nat) (modulus : UInt256) : UInt256 :=
  wideBaseFold mem aw (wideR256 modulus) modulus (baseSize / 32)
    (operandBasePtr + 32 + wideWordBaseStart baseSize)
    (wideWordBaseAccWithModulusAt mem aw baseSize modulus)

def wideWordBaseValue (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  wideWordBaseValueAt (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize)
    baseSize exponentSize modulusSize

def wideWordExponentStartAt (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize : Nat) : Nat :=
  wideSkipExponentZerosAt mem aw baseSize exponentSize 0

def wideWordExponentStart (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  wideWordExponentStartAt (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize) baseSize exponentSize

def wideWordValueAt (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  let start := wideWordExponentStartAt mem aw baseSize exponentSize
  wideExponentFoldAt mem aw baseSize
    (wideWordBaseValueAt mem aw baseSize exponentSize modulusSize)
    (wideWordModulusAt mem aw baseSize exponentSize modulusSize)
    (exponentSize - start) start ⟨1⟩

def wideWordValueAtModulusPtr (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize modulusPtr modulusSize : Nat) : UInt256 :=
  let modulus := wideWordModulusAtPtr mem aw modulusPtr modulusSize
  let start := wideWordExponentStartAt mem aw baseSize exponentSize
  wideExponentFoldAt mem aw baseSize
    (wideWordBaseValueWithModulusAt mem aw baseSize modulus)
    modulus (exponentSize - start) start ⟨1⟩

def wideWordValue (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  wideWordValueAt (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize)
    baseSize exponentSize modulusSize

def wideWordHelperStepsAt (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  let start := wideWordExponentStartAt mem aw baseSize exponentSize
  34 + (if baseSize % 32 = 0 then 0 else 26) + 13 +
    (26 * (baseSize / 32) + 6) + 18 +
    wideSkipExponentStepsAt mem aw baseSize exponentSize 0 +
    wideExponentStepsAt mem aw baseSize (exponentSize - start) start + 12

def wideWordHelperSteps (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  wideWordHelperStepsAt (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize)
    baseSize exponentSize modulusSize

def wideWordHelperGasAt (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  let start := wideWordExponentStartAt mem aw baseSize exponentSize
  106 + (if baseSize % 32 = 0 then 0 else 82) + 42 +
    (96 * (baseSize / 32) + 23) + 51 +
    wideSkipExponentGasAt mem aw baseSize exponentSize 0 +
    wideExponentGasAt mem aw baseSize (exponentSize - start) start +
    36 + 3 * ((modulusSize + 31) / 32)

def wideWordHelperGas (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  wideWordHelperGasAt (operandCopiedMemory I baseSize exponentSize modulusSize)
    (operandModulusActiveWords baseSize exponentSize modulusSize)
    baseSize exponentSize modulusSize

private theorem wideBaseDataPtr_nat :
    wideBaseDataPtr = UInt256.ofNat (operandBasePtr + 32) := by
  unfold wideBaseDataPtr
  exact ofNat_add_bounded (by unfold operandBasePtr; decide)

private theorem wideBaseAfterPartialPtr_nat (baseSize : Nat) (hb : baseSize ≤ 1024) :
    wideBaseAfterPartialPtr baseSize =
      UInt256.ofNat (operandBasePtr + 32 + baseSize % 32) := by
  unfold wideBaseAfterPartialPtr wideBaseRemainder
  rw [u256_add_assoc, u256_add_comm (UInt256.ofNat (baseSize % 32)) ⟨32⟩,
    ← u256_add_assoc]
  have h₁ : operandBasePtr + 32 < UInt256.size := by unfold operandBasePtr; decide
  change UInt256.ofNat operandBasePtr + UInt256.ofNat 32 +
    UInt256.ofNat (baseSize % 32) = _
  rw [ofNat_add_bounded h₁]
  have h₂ : operandBasePtr + 32 + baseSize % 32 < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandBasePtr + 32 + baseSize % 32 ≤ 191 by
        have := Nat.mod_lt baseSize (by decide : 0 < 32)
        unfold operandBasePtr
        omega)
    decide
  exact ofNat_add_bounded h₂

private theorem wideBaseEnd_nat (baseSize : Nat) (hb : baseSize ≤ 1024) :
    wideBaseEnd baseSize = UInt256.ofNat (operandBasePtr + 32 + baseSize) := by
  unfold wideBaseEnd
  have h₁ : operandBasePtr + baseSize < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandBasePtr + baseSize ≤ 1152 by unfold operandBasePtr; omega)
    decide
  rw [ofNat_add_bounded h₁]
  rw [u256_add_comm]
  have h₂ : operandBasePtr + baseSize + 32 < UInt256.size := by
    apply lt_of_le_of_lt
      (show operandBasePtr + baseSize + 32 ≤ 1184 by unfold operandBasePtr; omega)
    decide
  rw [show operandBasePtr + 32 + baseSize = operandBasePtr + baseSize + 32 by omega]
  exact ofNat_add_bounded h₂

/-- Exact execution of `modexpWordInto`, from its internal entry to its caller's return PC. -/
theorem runWideWordHelperExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat} {result ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hbaseLength : wideLoadWord mem aw (UInt256.ofNat operandBasePtr) =
      UInt256.ofNat baseSize)
    (hexponentLength : wideLoadWord mem aw
      (UInt256.ofNat (operandExponentPtr baseSize)) = UInt256.ofNat exponentSize)
    (hmodulusLength : wideLoadWord mem aw
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize)) =
        UInt256.ofNat modulusSize)
    (hoperandsActive : operandFreePtr baseSize exponentSize modulusSize ≤ 32 * aw.toNat)
    (hresult : result.toNat + 32 < UInt256.size)
    (hawResult : result.toNat + 32 + modulusSize ≤
      32 * aw.toNat)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (htail : tail.length ≤ 1000)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2574⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: result :: ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ret tail
      (wideWordReturnMemory mem
        (wideWordValueAt mem aw baseSize exponentSize modulusSize) result modulusSize)
      aw rdata acc
      (k + wideWordHelperStepsAt mem aw baseSize exponentSize modulusSize)
      (C + wideWordHelperGasAt mem aw baseSize exponentSize modulusSize) := by
  let rem := baseSize % 32
  let n := baseSize / 32
  let modulus := wideWordModulusAt mem aw baseSize exponentSize modulusSize
  let baseValue := wideWordBaseValueAt mem aw baseSize exponentSize modulusSize
  have hdecomp : rem + 32 * n = baseSize := by
    simpa [rem, n] using Nat.mod_add_div baseSize 32
  have hbaseEnd : operandBasePtr + 32 + baseSize ≤
      operandFreePtr baseSize exponentSize modulusSize := by
    have halloc := bytesHeaderAndSize_le_allocation baseSize
    unfold operandFreePtr operandModulusPtr operandExponentPtr
    omega
  have hexponentEnd : wideExponentDataPtr baseSize + exponentSize + 32 ≤
      operandFreePtr baseSize exponentSize modulusSize := by
    have halloc := bytesHeaderAndSize_le_allocation exponentSize
    have htoModulus : wideExponentDataPtr baseSize + exponentSize ≤
        operandModulusPtr baseSize exponentSize := by
      unfold wideExponentDataPtr operandModulusPtr
      omega
    have hheader : operandModulusPtr baseSize exponentSize + 32 ≤
        operandFreePtr baseSize exponentSize modulusSize := by
      unfold operandFreePtr bytesAllocationSize
      omega
    omega
  have hmodData : operandModulusPtr baseSize exponentSize + 64 ≤
      operandFreePtr baseSize exponentSize modulusSize := by
    have hword : 1 ≤ (modulusSize + 31) / 32 := by omega
    unfold operandFreePtr bytesAllocationSize
    omega
  have hbaseActive : operandBasePtr + 32 + baseSize ≤ 32 * aw.toNat :=
    hbaseEnd.trans hoperandsActive
  have hexponentActive : wideExponentDataPtr baseSize + exponentSize + 32 ≤
      32 * aw.toNat := hexponentEnd.trans hoperandsActive
  have hmodDataActive : operandModulusPtr baseSize exponentSize + 64 ≤ 32 * aw.toNat :=
    hmodData.trans hoperandsActive
  have hmodHeaderActive : operandModulusPtr baseSize exponentSize + 32 ≤ 32 * aw.toNat :=
    (by omega)
  have hbaseHeaderActive : operandBasePtr + 32 ≤ 32 * aw.toNat := by omega
  have hexponentHeaderActive : operandExponentPtr baseSize + 32 ≤ 32 * aw.toNat := by
    unfold wideExponentDataPtr at hexponentActive
    omega
  have rd2615 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2615⟩
      ((if rem = 0 then ⟨0⟩ else ⟨32⟩) :: UInt256.ofNat operandBasePtr ::
        UInt256.ofNat baseSize :: UInt256.ofNat (operandBasePtr + 32 + rem) ::
        UInt256.ofNat (operandExponentPtr baseSize) :: modulus ::
        wideWordBaseAccAt mem aw baseSize exponentSize modulusSize :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc
      (k + 34 + (if rem = 0 then 0 else 26))
      (C + 106 + (if rem = 0 then 0 else 82)) := by
    by_cases hr : rem = 0
    · have rd := reachWideWordNoPartial hb he hmodPos hm hbaseHeaderActive
        hmodHeaderActive hmodDataActive hbaseLength hmodulusLength
        (by simpa [rem] using hr) htail rd0
      rw [wideBaseDataPtr_nat] at rd
      simpa [rem, hr, modulus, wideWordBaseAccAt] using
        rd.withIndices (by omega) (by omega)
    · have rd2806 := reachWideWordPartial hb he hmodPos hm hbaseHeaderActive
        hmodHeaderActive hmodDataActive hbaseLength hmodulusLength
        (by simpa [rem] using hr) htail rd0
      have hbaseDataActive : operandBasePtr + 64 ≤ 32 * aw.toNat := by
        have hword : 1 ≤ (baseSize + 31) / 32 := by
          unfold rem at hr
          omega
        have hdata : operandBasePtr + 64 ≤
            operandFreePtr baseSize exponentSize modulusSize := by
          unfold operandFreePtr operandModulusPtr operandExponentPtr bytesAllocationSize
          omega
        exact hdata.trans hoperandsActive
      have rd := reduceWideWordPartial hb he hmodPos hm hbaseDataActive htail rd2806
      rw [wideBaseAfterPartialPtr_nat baseSize hb] at rd
      simpa [rem, hr, modulus, wideWordBaseAccAt] using
        rd.withIndices (by omega) (by omega)
  have rd2630 := reachWideBaseLoop (exponentSize := exponentSize) htail rd2615
  rw [wideBaseEnd_nat baseSize hb] at rd2630
  have rd2638 := foldWideBaseChunks hb he hm
    (ptr := operandBasePtr + 32 + rem)
    (end_ := operandBasePtr + 32 + baseSize) (n := n)
    (hend := by omega) (hendBound := by omega) hbaseActive htail rd2630
  have rd2638' : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2638⟩
      (wideR256 modulus :: UInt256.ofNat (operandBasePtr + 32 + baseSize) ::
        UInt256.ofNat (operandBasePtr + 32 + baseSize) ::
        UInt256.ofNat (operandExponentPtr baseSize) :: modulus :: baseValue :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc
      (k + 34 + (if rem = 0 then 0 else 26) + 13 + (26 * n + 6))
      (C + 106 + (if rem = 0 then 0 else 82) + 42 + (96 * n + 23)) := by
    simpa [rem, n, modulus, baseValue, wideWordBaseValueAt, wideWordBaseStart,
      Nat.add_assoc] using rd2638
  have rd2658 := reachWideExponentLoopSetup hb he hm hexponentHeaderActive
    hexponentLength htail rd2638'
  have rd2665 := skipWideExponentZeros hb he hm hexponentActive
    (start := 0) (by omega) htail (by
    simpa using rd2658)
  let start := wideWordExponentStartAt mem aw baseSize exponentSize
  have hstartBounds := wideSkipExponentZerosAt_bounds mem aw baseSize exponentSize 0
    (by omega)
  have hendEq : wideExponentDataPtr baseSize + exponentSize =
      wideExponentDataPtr baseSize + start + (exponentSize - start) := by
    unfold start wideWordExponentStartAt
    omega
  rw [show wideExponentEnd baseSize exponentSize =
      wideExponentDataPtr baseSize + exponentSize by rfl, hendEq] at rd2665
  have rd2673 := foldWideExponentBytes hb he hm
    (start := start) (n := exponentSize - start) (by omega) htail hexponentActive (by
      simpa [start, wideWordExponentStartAt] using rd2665)
  have hawScratch : 3 ≤ aw.toNat := by
    have : 96 ≤ operandFreePtr baseSize exponentSize modulusSize := by
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega
    omega
  have rdret := returnWideWordExact hm hawScratch hresult hawResult hret
    (Nat.le_trans htail (by omega)) (by
      simpa [start, modulus, baseValue, wideWordValueAt, wideWordExponentStartAt]
        using rd2673)
  dsimp only [start, rem, n] at rdret ⊢
  simpa [wideWordHelperStepsAt, wideWordHelperGasAt, wideWordExponentStartAt,
    Nat.add_assoc] using rdret.withIndices (by omega) (by omega)

/-- Exact execution of `modexpWordInto` when only the modulus array pointer is arbitrary.

This is the shape needed by normalized Barrett re-entry: the base and exponent arrays are still the
original copied calldata arrays, but the modulus argument points at a freshly allocated normalized
bytes array. -/
theorem runWideWordHelperModulusPtrExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusPtr modulusSize : Nat} {result ret : UInt256}
    {tail : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hmodPtrWord : modulusPtr < UInt256.size)
    (hmodDataWord : modulusPtr + 32 < UInt256.size)
    (hbaseLength : wideLoadWord mem aw (UInt256.ofNat operandBasePtr) =
      UInt256.ofNat baseSize)
    (hexponentLength : wideLoadWord mem aw
      (UInt256.ofNat (operandExponentPtr baseSize)) = UInt256.ofNat exponentSize)
    (hmodulusLength : wideLoadWord mem aw (UInt256.ofNat modulusPtr) =
      UInt256.ofNat modulusSize)
    (hbaseActive : operandBasePtr + 32 + baseSize ≤ 32 * aw.toNat)
    (hbaseDataActive : operandBasePtr + 64 ≤ 32 * aw.toNat)
    (hexponentActive : wideExponentDataPtr baseSize + exponentSize + 32 ≤
      32 * aw.toNat)
    (hmodHeaderActive : modulusPtr + 32 ≤ 32 * aw.toNat)
    (hmodDataActive : modulusPtr + 64 ≤ 32 * aw.toNat)
    (hresult : result.toNat + 32 < UInt256.size)
    (hawResult : result.toNat + 32 + modulusSize ≤ 32 * aw.toNat)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (htail : tail.length ≤ 1000)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2574⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat modulusPtr :: result :: ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ret tail
      (wideWordReturnMemory mem
        (wideWordValueAtModulusPtr mem aw baseSize exponentSize modulusPtr modulusSize)
        result modulusSize)
      aw rdata acc
      (k + wideWordHelperStepsAt mem aw baseSize exponentSize modulusSize)
      (C + wideWordHelperGasAt mem aw baseSize exponentSize modulusSize) := by
  let rem := baseSize % 32
  let n := baseSize / 32
  let modulus := wideWordModulusAtPtr mem aw modulusPtr modulusSize
  let baseValue := wideWordBaseValueWithModulusAt mem aw baseSize modulus
  have hbaseHeaderActive : operandBasePtr + 32 ≤ 32 * aw.toNat := by omega
  have hexponentHeaderActive : operandExponentPtr baseSize + 32 ≤ 32 * aw.toNat := by
    unfold wideExponentDataPtr at hexponentActive
    omega
  have rd2615 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2615⟩
      ((if rem = 0 then ⟨0⟩ else ⟨32⟩) :: UInt256.ofNat operandBasePtr ::
        UInt256.ofNat baseSize :: UInt256.ofNat (operandBasePtr + 32 + rem) ::
        UInt256.ofNat (operandExponentPtr baseSize) :: modulus ::
        wideWordBaseAccWithModulusAt mem aw baseSize modulus :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc
      (k + 34 + (if rem = 0 then 0 else 26))
      (C + 106 + (if rem = 0 then 0 else 82)) := by
    by_cases hr : rem = 0
    · have rd := reachWideWordNoPartialAt
        (basePtr := operandBasePtr) (exponentPtr := operandExponentPtr baseSize)
        (modulusPtr := modulusPtr) (baseSize := baseSize) (modulusSize := modulusSize)
        hb hm (by unfold operandBasePtr; decide)
        (by unfold operandBasePtr; decide) hmodPtrWord hmodDataWord
        hbaseHeaderActive hmodHeaderActive hmodDataActive hbaseLength hmodulusLength
        (by simpa [rem] using hr) htail rd0
      have hbaseData : wideBaseDataPtrAt operandBasePtr =
          UInt256.ofNat (operandBasePtr + 32 + rem) := by
        unfold wideBaseDataPtrAt
        rw [hr]
        simp only [add_zero]
        exact ofNat_add_bounded (by unfold operandBasePtr; decide)
      simpa [rem, hr, modulus, wideWordBaseAccWithModulusAt, hbaseData] using
        rd.withIndices (by omega) (by omega)
    · have rd2806 := reachWideWordPartialAt
        (basePtr := operandBasePtr) (exponentPtr := operandExponentPtr baseSize)
        (modulusPtr := modulusPtr) (baseSize := baseSize) (modulusSize := modulusSize)
        hb hm (by unfold operandBasePtr; decide)
        (by unfold operandBasePtr; decide) hmodPtrWord hmodDataWord
        hbaseHeaderActive hmodHeaderActive hmodDataActive hbaseLength hmodulusLength
        (by simpa [rem] using hr) htail rd0
      have rd := reduceWideWordPartialWithModulus
        (baseSize := baseSize) (exponentSize := exponentSize)
        (modulusSize := modulusSize) (modulus := modulus)
        hb hm hbaseDataActive htail (by
          simpa [wideBaseDataPtrAt, wideBaseDataPtr, modulus] using rd2806)
      rw [wideBaseAfterPartialPtr_nat baseSize hb] at rd
      simpa [rem, hr, modulus, wideWordBaseAccWithModulusAt] using
        rd.withIndices (by omega) (by omega)
  have rd2630 := reachWideBaseLoop (exponentSize := exponentSize) htail rd2615
  rw [wideBaseEnd_nat baseSize hb] at rd2630
  have rd2638 := foldWideBaseChunks hb he hm
    (ptr := operandBasePtr + 32 + rem)
    (end_ := operandBasePtr + 32 + baseSize) (n := n)
    (hend := by
      have hdecomp : rem + 32 * n = baseSize := by
        dsimp only [rem, n]
        simpa using Nat.mod_add_div baseSize 32
      omega)
    (hendBound := by omega) hbaseActive htail rd2630
  have rd2638' : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2638⟩
      (wideR256 modulus :: UInt256.ofNat (operandBasePtr + 32 + baseSize) ::
        UInt256.ofNat (operandBasePtr + 32 + baseSize) ::
        UInt256.ofNat (operandExponentPtr baseSize) :: modulus :: baseValue :: result ::
        UInt256.sub ⟨32⟩ (UInt256.ofNat modulusSize) :: UInt256.ofNat modulusSize ::
        ret :: tail)
      mem aw rdata acc
      (k + 34 + (if rem = 0 then 0 else 26) + 13 + (26 * n + 6))
      (C + 106 + (if rem = 0 then 0 else 82) + 42 + (96 * n + 23)) := by
    simpa [rem, n, modulus, baseValue, wideWordBaseValueWithModulusAt, wideWordBaseStart,
      Nat.add_assoc] using rd2638
  have rd2658 := reachWideExponentLoopSetup hb he hm hexponentHeaderActive
    hexponentLength htail rd2638'
  have rd2665 := skipWideExponentZeros hb he hm hexponentActive
    (start := 0) (by omega) htail (by
    simpa using rd2658)
  let start := wideWordExponentStartAt mem aw baseSize exponentSize
  have hstartBounds := wideSkipExponentZerosAt_bounds mem aw baseSize exponentSize 0
    (by omega)
  have hendEq : wideExponentDataPtr baseSize + exponentSize =
      wideExponentDataPtr baseSize + start + (exponentSize - start) := by
    unfold start wideWordExponentStartAt
    omega
  rw [show wideExponentEnd baseSize exponentSize =
      wideExponentDataPtr baseSize + exponentSize by rfl, hendEq] at rd2665
  have rd2673 := foldWideExponentBytes hb he hm
    (start := start) (n := exponentSize - start) (by omega) htail hexponentActive (by
      simpa [start, wideWordExponentStartAt] using rd2665)
  have hawScratch : 3 ≤ aw.toNat := by
    have : operandBasePtr + 32 ≤ 32 * aw.toNat := hbaseHeaderActive
    unfold operandBasePtr at this
    omega
  have rdret := returnWideWordExact hm hawScratch hresult hawResult hret
    (Nat.le_trans htail (by omega)) (by
      simpa [start, modulus, baseValue, wideWordValueAtModulusPtr, wideWordExponentStartAt]
        using rd2673)
  dsimp only [start, rem, n] at rdret ⊢
  simpa [wideWordHelperStepsAt, wideWordHelperGasAt, wideWordExponentStartAt,
    Nat.add_assoc] using rdret.withIndices (by omega) (by omega)

/-- The word produced by the helper is the trusted model's modular exponentiation result. -/
theorem wideWordValue_toNat_eq_model (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize) :
    (wideWordValue I baseSize exponentSize modulusSize).toNat =
      Model.modPow
        (Model.bytesToNatPadded I.calldata 96 baseSize)
        (Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize)
        (Model.bytesToNatPadded I.calldata
          (96 + baseSize + exponentSize) modulusSize) := by
  let rem := wideWordBaseStart baseSize
  let n := baseSize / 32
  let modulusNat := Model.bytesToNatPadded I.calldata
    (96 + baseSize + exponentSize) modulusSize
  let baseNat := Model.bytesToNatPadded I.calldata 96 baseSize
  let exponentNat := Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize
  let modulus := wideWordModulus I baseSize exponentSize modulusSize
  let baseValue := wideWordBaseValue I baseSize exponentSize modulusSize
  have hdecomp : rem + 32 * n = baseSize := by
    simpa [rem, wideWordBaseStart, n] using Nat.mod_add_div baseSize 32
  have hacc : (wideWordBaseAcc I baseSize exponentSize modulusSize).toNat =
      Model.bytesToNatPadded I.calldata 96 rem % modulusNat := by
    by_cases hr : baseSize % 32 = 0
    · simp [wideWordBaseAcc, wideWordBaseAccAt, rem, wideWordBaseStart, hr,
        model_bytesToNatPadded_zero_width]
    · have hp := widePartialBase_toNat_eq_model I baseSize exponentSize modulusSize
        hb he hmodPos hm hr hmod
      simpa [wideWordBaseAcc, wideWordBaseAccAt, widePartialBase, rem,
        wideWordBaseStart, modulusNat, hr] using hp
  have hbase : baseValue.toNat = baseNat % modulusNat := by
    have hf := wideBaseFold_toNat_eq_model I baseSize exponentSize modulusSize
      n rem (wideWordBaseAcc I baseSize exponentSize modulusSize)
      hb he hmodPos hm (by omega) hmod hacc
    simpa [baseValue, wideWordBaseValue, rem, n, baseNat, modulusNat, hdecomp]
      using hf
  have hmodWord : modulus.toNat = modulusNat := by
    exact wideWordModulus_toNat_eq_model I baseSize exponentSize modulusSize
      hb he hmodPos hm
  let start := wideWordExponentStart I baseSize exponentSize modulusSize
  have hstart := wideSkipExponentZeros_bounds I baseSize exponentSize modulusSize 0
    (by omega)
  have hskip := wideSkipExponentZeros_value I baseSize exponentSize modulusSize 0
    hb he hm (by omega)
  have hfullExponent :
      Model.bytesToNatPadded I.calldata (96 + baseSize + start)
          (exponentSize - start) = exponentNat := by
    simpa [start, wideWordExponentStart, exponentNat] using hskip.symm
  have hfullExponent' :
      Model.bytesToNatPadded I.calldata
          (96 + baseSize +
            wideSkipExponentZeros I baseSize exponentSize modulusSize 0)
          (exponentSize -
            wideSkipExponentZeros I baseSize exponentSize modulusSize 0) = exponentNat := by
    simpa [start, wideWordExponentStart] using hfullExponent
  have hstartLe : start ≤ exponentSize := by
    simpa [start, wideWordExponentStart] using hstart.2
  have hfold := wideExponentFold_toNat_eq_pow I baseSize exponentSize modulusSize
    start (exponentSize - start) 0 baseValue modulus ⟨1⟩ hb he hm
    (by omega)
    (by rw [hmodWord]; exact hmod) (by
      rw [show (⟨1⟩ : UInt256).toNat = 1 by decide]
      rw [pow_zero, Nat.mod_eq_of_lt (by rw [hmodWord]; exact hmod)])
  simp only [Nat.zero_mul, Nat.zero_add] at hfold
  rw [hfullExponent, hmodWord] at hfold
  have hvalue : (wideWordValue I baseSize exponentSize modulusSize).toNat =
      baseValue.toNat ^ exponentNat % modulusNat := by
    simpa [wideWordValue, wideWordValueAt, wideExponentFold, wideWordBaseValue,
      wideWordModulus, start, wideWordExponentStart, wideSkipExponentZeros,
      baseValue, modulus,
      hfullExponent', hmodWord] using hfold
  rw [hvalue, hbase]
  have hcong : (baseNat % modulusNat) ^ exponentNat ≡
      baseNat ^ exponentNat [MOD modulusNat] :=
    (Nat.mod_modEq baseNat modulusNat).pow exponentNat
  change (baseNat % modulusNat) ^ exponentNat % modulusNat =
    Model.modPow baseNat exponentNat modulusNat
  rw [model_modPow_eq_pow_mod baseNat exponentNat modulusNat hmod]
  exact hcong

/-- Generic base-word fold bridge.  This is the pointer-independent version of
`wideBaseFold_toNat_eq_model`: the caller only has to provide the interpretation of every
32-byte base chunk in the current memory view. -/
theorem wideBaseFoldAt_toNat_eq_model_of (I : ExecutionEnv)
    (mem : ByteArray) (aw : UInt256) (baseSize n start : Nat)
    (modulus baseAcc : UInt256)
    (hwindow : start + 32 * n ≤ baseSize)
    (hmod : 1 < modulus.toNat)
    (hchunk : ∀ s, s + 32 ≤ baseSize →
      (wideLoadWord mem aw (UInt256.ofNat (operandBasePtr + 32 + s))).toNat =
        Model.bytesToNatPadded I.calldata (96 + s) 32)
    (hacc : baseAcc.toNat =
      Model.bytesToNatPadded I.calldata 96 start % modulus.toNat) :
    (wideBaseFold mem aw (wideR256 modulus) modulus n
      (operandBasePtr + 32 + start) baseAcc).toNat =
      Model.bytesToNatPadded I.calldata 96 (start + 32 * n) % modulus.toNat := by
  induction n generalizing start baseAcc with
  | zero =>
      simpa [wideBaseFold] using hacc
  | succ n ih =>
      let r256 := wideR256 modulus
      let chunk := wideLoadWord mem aw (UInt256.ofNat (operandBasePtr + 32 + start))
      let nextAcc := UInt256.addMod (UInt256.mulMod baseAcc r256 modulus) chunk modulus
      have hm0 : modulus.toNat ≠ 0 := by omega
      have hr256 : r256.toNat = UInt256.size % modulus.toNat := by
        unfold r256
        exact wideR256_toNat modulus hmod
      have hchunk' : chunk.toNat =
          Model.bytesToNatPadded I.calldata (96 + start) 32 := by
        exact hchunk start (by omega)
      have hnextAcc : nextAcc.toNat =
          Model.bytesToNatPadded I.calldata 96 (start + 32) % modulus.toNat := by
        unfold nextAcc
        rw [addMod_toNat hm0, mulMod_toNat hm0, hacc, hr256, hchunk']
        rw [show UInt256.size = 256 ^ 32 by native_decide]
        rw [model_bytesToNatPadded_split I.calldata 96 start 32]
        simp [Nat.mul_mod, Nat.add_mod, Nat.mod_mod]
      have hrec := ih (start := start + 32) (baseAcc := nextAcc)
        (by omega) hnextAcc
      unfold wideBaseFold
      change
        (wideBaseFold mem aw r256 modulus n ((operandBasePtr + 32 + start) + 32)
          nextAcc).toNat = _
      simpa [r256, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_succ]
        using hrec

/-- Generic bridge for the optional leading partial base chunk, once the caller has interpreted
the shifted first word in the current memory view. -/
theorem widePartialBaseWithModulusAt_toNat_eq_model_of (I : ExecutionEnv)
    (mem : ByteArray) (aw : UInt256) (baseSize : Nat) (modulus : UInt256)
    (_hrem : baseSize % 32 ≠ 0) (hmod : 1 < modulus.toNat)
    (hfirst :
      (UInt256.shiftRight (wideBaseFirstWordAt mem aw)
        (UInt256.shiftLeft (UInt256.sub ⟨32⟩ (wideBaseRemainder baseSize)) ⟨3⟩)).toNat =
        Model.bytesToNatPadded I.calldata 96 (baseSize % 32)) :
    (widePartialBaseWithModulusAt mem aw baseSize modulus).toNat =
      Model.bytesToNatPadded I.calldata 96 (baseSize % 32) % modulus.toNat := by
  unfold widePartialBaseWithModulusAt
  rw [umod_toNat (by omega), hfirst]

/-- Generic bridge for the helper's initial base accumulator. -/
theorem wideWordBaseAccWithModulusAt_toNat_eq_model_of (I : ExecutionEnv)
    (mem : ByteArray) (aw : UInt256) (baseSize : Nat) (modulus : UInt256)
    (hmod : 1 < modulus.toNat)
    (hfirst :
      baseSize % 32 ≠ 0 →
        (UInt256.shiftRight (wideBaseFirstWordAt mem aw)
          (UInt256.shiftLeft (UInt256.sub ⟨32⟩ (wideBaseRemainder baseSize)) ⟨3⟩)).toNat =
          Model.bytesToNatPadded I.calldata 96 (baseSize % 32)) :
    (wideWordBaseAccWithModulusAt mem aw baseSize modulus).toNat =
      Model.bytesToNatPadded I.calldata 96 (wideWordBaseStart baseSize) %
        modulus.toNat := by
  by_cases hr : baseSize % 32 = 0
  · simp [wideWordBaseAccWithModulusAt, wideWordBaseStart, hr,
      model_bytesToNatPadded_zero_width]
  · have hp := widePartialBaseWithModulusAt_toNat_eq_model_of I mem aw baseSize modulus
      hr hmod (hfirst hr)
    simpa [wideWordBaseAccWithModulusAt, wideWordBaseStart, hr] using hp

/-- Pointer-generic trusted-model bridge for `modexpWordInto`, with the trusted modulus value
supplied independently from the byte width used to load it.

The normalized Barrett path uses this form: the helper loads a shortened one-word modulus from a
temporary bytes array, but that word denotes the original trusted modulus integer. -/
theorem wideWordValueAtModulusPtr_toNat_eq_model_of_modulusNat (I : ExecutionEnv)
    (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize modulusPtr modulusSize modulusNat : Nat)
    (he : exponentSize ≤ 1024)
    (hmod : 1 < modulusNat)
    (hmodWord :
      (wideWordModulusAtPtr mem aw modulusPtr modulusSize).toNat = modulusNat)
    (hbaseAcc :
      (wideWordBaseAccWithModulusAt mem aw baseSize
        (wideWordModulusAtPtr mem aw modulusPtr modulusSize)).toNat =
        Model.bytesToNatPadded I.calldata 96 (wideWordBaseStart baseSize) % modulusNat)
    (hbaseChunk : ∀ s, s + 32 ≤ baseSize →
      (wideLoadWord mem aw (UInt256.ofNat (operandBasePtr + 32 + s))).toNat =
        Model.bytesToNatPadded I.calldata (96 + s) 32)
    (hexponentByte : ∀ s, s < exponentSize →
      (wideExponentByteAt mem aw baseSize s).toNat =
        Model.bytesToNatPadded I.calldata (96 + baseSize + s) 1) :
    (wideWordValueAtModulusPtr mem aw baseSize exponentSize modulusPtr modulusSize).toNat =
      Model.modPow
        (Model.bytesToNatPadded I.calldata 96 baseSize)
        (Model.bytesToNatPadded I.calldata (wideExponentOffset baseSize) exponentSize)
        modulusNat := by
  let rem := wideWordBaseStart baseSize
  let n := baseSize / 32
  let baseNat := Model.bytesToNatPadded I.calldata 96 baseSize
  let exponentNat := Model.bytesToNatPadded I.calldata (wideExponentOffset baseSize) exponentSize
  let modulus := wideWordModulusAtPtr mem aw modulusPtr modulusSize
  let baseValue := wideWordBaseValueWithModulusAt mem aw baseSize modulus
  have hdecomp : rem + 32 * n = baseSize := by
    simpa [rem, wideWordBaseStart, n] using Nat.mod_add_div baseSize 32
  have hbase : baseValue.toNat = baseNat % modulusNat := by
    have hf := wideBaseFoldAt_toNat_eq_model_of I mem aw baseSize n rem
      modulus (wideWordBaseAccWithModulusAt mem aw baseSize modulus)
      (by omega)
      (by rw [hmodWord]; exact hmod)
      hbaseChunk
      (by
        rw [hmodWord]
        simpa [modulus, rem] using hbaseAcc)
    rw [hmodWord] at hf
    simpa [baseValue, wideWordBaseValueWithModulusAt, rem, n, baseNat,
      hdecomp] using hf
  let start := wideWordExponentStartAt mem aw baseSize exponentSize
  have hstartBounds := wideSkipExponentZerosAt_bounds mem aw baseSize exponentSize 0
    (by omega)
  have hskip := wideSkipExponentZerosAt_value I mem aw baseSize exponentSize 0
    (by omega) hexponentByte
  have hfullExponent :
      Model.bytesToNatPadded I.calldata (96 + baseSize + start)
          (exponentSize - start) = exponentNat := by
    simpa [start, exponentNat, wideExponentOffset] using hskip.symm
  have hfold := wideExponentFoldAt_toNat_eq_pow I mem aw baseSize exponentSize
    start (exponentSize - start) 0 baseValue modulus ⟨1⟩
    (by
      have hs : start ≤ exponentSize := by
        simpa [start] using hstartBounds.2
      omega)
    (by rw [hmodWord]; exact hmod)
    hexponentByte
    (by
      rw [show (⟨1⟩ : UInt256).toNat = 1 by decide]
      rw [pow_zero, Nat.mod_eq_of_lt (by rw [hmodWord]; exact hmod)])
  simp only [Nat.zero_mul, Nat.zero_add] at hfold
  rw [hfullExponent, hmodWord] at hfold
  have hvalue :
      (wideWordValueAtModulusPtr mem aw baseSize exponentSize modulusPtr modulusSize).toNat =
        baseValue.toNat ^ exponentNat % modulusNat := by
    simpa [wideWordValueAtModulusPtr, wideWordExponentStartAt, start, baseValue, modulus,
      exponentNat] using hfold
  rw [hvalue, hbase]
  have hcong : (baseNat % modulusNat) ^ exponentNat ≡
      baseNat ^ exponentNat [MOD modulusNat] :=
    (Nat.mod_modEq baseNat modulusNat).pow exponentNat
  change (baseNat % modulusNat) ^ exponentNat % modulusNat =
    Model.modPow baseNat exponentNat modulusNat
  rw [model_modPow_eq_pow_mod baseNat exponentNat modulusNat hmod]
  exact hcong

/-- Pointer-generic trusted-model bridge for `modexpWordInto`.

The normalized Barrett path re-enters the one-word helper with the same base/exponent arrays but
with the modulus at a freshly allocated pointer.  This theorem factors out the pure side: as long
as the current memory view exposes the trusted base chunks, trusted exponent bytes, and a modulus
word whose value equals the trusted modulus integer, the helper's word value is the trusted
`Model.modPow`. -/
theorem wideWordValueAtModulusPtr_toNat_eq_model_of (I : ExecutionEnv)
    (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize modulusPtr modulusSize : Nat)
    (he : exponentSize ≤ 1024)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (wideModulusOffset baseSize exponentSize) modulusSize)
    (hmodWord :
      (wideWordModulusAtPtr mem aw modulusPtr modulusSize).toNat =
        Model.bytesToNatPadded I.calldata
          (wideModulusOffset baseSize exponentSize) modulusSize)
    (hbaseAcc :
      (wideWordBaseAccWithModulusAt mem aw baseSize
        (wideWordModulusAtPtr mem aw modulusPtr modulusSize)).toNat =
        Model.bytesToNatPadded I.calldata 96 (wideWordBaseStart baseSize) %
          Model.bytesToNatPadded I.calldata
            (wideModulusOffset baseSize exponentSize) modulusSize)
    (hbaseChunk : ∀ s, s + 32 ≤ baseSize →
      (wideLoadWord mem aw (UInt256.ofNat (operandBasePtr + 32 + s))).toNat =
        Model.bytesToNatPadded I.calldata (96 + s) 32)
    (hexponentByte : ∀ s, s < exponentSize →
      (wideExponentByteAt mem aw baseSize s).toNat =
        Model.bytesToNatPadded I.calldata (96 + baseSize + s) 1) :
    (wideWordValueAtModulusPtr mem aw baseSize exponentSize modulusPtr modulusSize).toNat =
      Model.modPow
        (Model.bytesToNatPadded I.calldata 96 baseSize)
        (Model.bytesToNatPadded I.calldata (wideExponentOffset baseSize) exponentSize)
        (Model.bytesToNatPadded I.calldata
          (wideModulusOffset baseSize exponentSize) modulusSize) := by
  exact wideWordValueAtModulusPtr_toNat_eq_model_of_modulusNat I mem aw
    baseSize exponentSize modulusPtr modulusSize
    (Model.bytesToNatPadded I.calldata
      (wideModulusOffset baseSize exponentSize) modulusSize)
    he hmod hmodWord hbaseAcc hbaseChunk hexponentByte

/-- The bytes copied into the caller's result payload are exactly the trusted fixed-width
encoding.  `hdest` is the concrete-memory counterpart of the caller's prior `new bytes`
allocation. -/
theorem wideWordReturnData_eq_model (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) (result : UInt256)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize)
    (hdest : result.toNat + 32 ≤
      (wideWordScratchMemory
        (operandCopiedMemory I baseSize exponentSize modulusSize)
        (wideWordValue I baseSize exponentSize modulusSize)).size) :
    (wideWordReturnMemory (operandCopiedMemory I baseSize exponentSize modulusSize)
        (wideWordValue I baseSize exponentSize modulusSize) result modulusSize).readWithPadding
      (result.toNat + 32) modulusSize =
      Model.natToBytes
        (Model.modPow
          (Model.bytesToNatPadded I.calldata 96 baseSize)
          (Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize)
          (Model.bytesToNatPadded I.calldata
            (96 + baseSize + exponentSize) modulusSize))
        modulusSize := by
  let mem := operandCopiedMemory I baseSize exponentSize modulusSize
  let value := wideWordValue I baseSize exponentSize modulusSize
  let scratch := wideWordScratchMemory mem value
  let modulusNat := Model.bytesToNatPadded I.calldata
    (96 + baseSize + exponentSize) modulusSize
  let modelValue := Model.modPow
    (Model.bytesToNatPadded I.calldata 96 baseSize)
    (Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize)
    modulusNat
  have hvalue : value.toNat = modelValue := by
    exact wideWordValue_toNat_eq_model I baseSize exponentSize modulusSize
      hb he hmodPos hm hmod
  have hscratchSize : 32 ≤ scratch.size := by
    unfold scratch wideWordScratchMemory
    exact toByteArray_write_size_ge_off_add32 value mem 0 (by
      simp)
  have hsum : 32 - modulusSize + modulusSize = 32 := by omega
  have hsrc : 32 - modulusSize + modulusSize ≤ scratch.size := by omega
  have hcopy := write_read_back_from_gen scratch scratch
    (32 - modulusSize) (result.toNat + 32) modulusSize
    (by omega) hsrc hdest (by omega)
  have hscratchRead : scratch.readWithPadding (32 - modulusSize) modulusSize =
      value.toByteArray.extract (32 - modulusSize) 32 := by
    unfold scratch wideWordScratchMemory
    simpa [hsum] using toByteArray_write_read_window_of_gap value mem 0
      (32 - modulusSize) modulusSize (by omega) hmodPos (by omega) (by
        simp)
  have hextract : scratch.extract (32 - modulusSize) 32 =
      value.toByteArray.extract (32 - modulusSize) 32 := by
    rw [← hscratchRead]
    simpa [hsum] using
      (readWithPadding_eq_extract' scratch (32 - modulusSize) modulusSize
        hmodPos (by omega) hsrc).symm
  have hfit : value.toNat < 256 ^ modulusSize := by
    rw [hvalue]
    have hmodelLt : modelValue < modulusNat := by
      unfold modelValue
      rw [model_modPow_eq_pow_mod _ _ modulusNat hmod]
      exact Nat.mod_lt _ (by omega)
    exact lt_trans hmodelLt
      (model_bytesToNatPadded_lt_pow I.calldata
        (96 + baseSize + exponentSize) modulusSize)
  rw [show wideWordReturnMemory mem value result modulusSize =
      scratch.write (32 - modulusSize) scratch (result.toNat + 32) modulusSize by rfl]
  rw [hcopy, hsum, hextract]
  rw [← model_natToBytes_eq_toByteArray_suffix value modulusSize hm hfit, hvalue]

/-- Pointer-generic one-word modulus decoding: the helper's shifted word is the trusted
big-endian interpretation of the bytes at `modulusPtr + 32`. -/
theorem wideWordModulusAtPtr_toNat_eq_model_bytes
    (mem : ByteArray) (aw : UInt256) (modulusPtr modulusSize : Nat)
    (hm : modulusSize ≤ 32)
    (haddr256 : modulusPtr + 32 < UInt256.size)
    (haddr64 : modulusPtr + 32 < 2 ^ 64)
    (haw : ¬ UInt256.ofNat (modulusPtr + 32) ≥ aw * ⟨32⟩) :
    (wideWordModulusAtPtr mem aw modulusPtr modulusSize).toNat =
      Model.bytesToNatPadded mem (modulusPtr + 32) modulusSize := by
  let addr := modulusPtr + 32
  have haddrEq : UInt256.ofNat modulusPtr + ⟨32⟩ = UInt256.ofNat addr := by
    unfold addr
    simpa using (ofNat_add_bounded
      (a := modulusPtr) (b := 32) haddr256)
  have hload :
      wideLoadWord mem aw (UInt256.ofNat addr) =
        uInt256OfByteArray (mem.readBytes addr 32) := by
    rw [wideLoadWord_eq_decode_bounded haw]
    congr 1
    rw [UInt256.toNat_ofNat_of_lt haddr256,
      readWithPadding_eq_model_readPadded mem addr 32 haddr64 (by decide),
      readBytes_eq_model_readPadded mem addr 32 haddr64 (by decide)]
  have hopen := operandWord_toNat_eq_model mem addr (UInt256.ofNat modulusSize)
    haddr64 (by
      rw [UInt256.toNat_ofNat_of_lt (by omega : modulusSize < UInt256.size)]
      exact hm)
  unfold wideWordModulusAtPtr
  rw [haddrEq, hload]
  simpa [addr, UInt256.toNat_ofNat_of_lt (by omega : modulusSize < UInt256.size)]
    using hopen

end Modexp
