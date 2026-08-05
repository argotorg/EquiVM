import Examples.Precompiles.Modexp.BarrettWordCaller
import Examples.Precompiles.Modexp.MontgomerySpec

/-!
# Exact even one-word Barrett direct path for ModExp

This branch-local bytecode spec covers the even-modulus one-word Barrett path whose leading-zero
scan exits directly.  It is intentionally not a full Barrett proof: if the modulus payload starts
with leading zero bytes and has length greater than one, the deployed code takes a normalization
path which is not covered here yet.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 500000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem jumpDest_wrapper173_barrett :
    (D_J runtimeBytecode 0).contains (UInt256.ofNat 173) = true := by
  native_decide

def wideBarrettDirectWordGas (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  79 + cdRangeGas I (wideExponentOffset baseSize) (wideModulusOffset baseSize exponentSize) +
    wideBaseGtOneGas I baseSize +
    operandSetupGas I baseSize exponentSize modulusSize +
    preparedBarrettDirectWordGasFromAw I
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize +
    16

def wideBarrettDirectWordCondition (I : ExecutionEnv) : Prop :=
  let l := lengths I.calldata
  0 < l.modulus ∧ l.modulus ≤ 32 ∧
  Model.bytesToNatPadded I.calldata (wideExponentOffset l.base) l.exponent ≠ 0 ∧
  1 < Model.bytesToNatPadded I.calldata 96 l.base ∧
  1 < Model.bytesToNatPadded I.calldata (wideModulusOffset l.base l.exponent) l.modulus ∧
  modulusLastByteParity
    (operandCopiedMemory I l.base l.exponent l.modulus)
    (operandModulusActiveWords l.base l.exponent l.modulus)
    l.base l.exponent l.modulus = ⟨0⟩ ∧
  (l.modulus = 1 ∨
    UInt256.byteAt ⟨0⟩
      (wideLoadWord
        (wideWordResultMemory I l.base l.exponent l.modulus)
        (wideWordResultWords l.base l.exponent l.modulus)
        (UInt256.ofNat (operandModulusPtr l.base l.exponent + 32))) ≠ ⟨0⟩)

def wideBarrettDirectWordAccepts (ctx : BytecodeContext) : Prop :=
  ctx.executionEnv.weiValue = ⟨0⟩ ∧
  ctx.executionEnv.calldata.size < 2 ^ 64 ∧
  validOsaka ctx.executionEnv.calldata ∧
  ¬ wordSized ctx.executionEnv.calldata ∧
  wideBarrettDirectWordCondition ctx.executionEnv

def wideBarrettDirectWordTotalGas (I : ExecutionEnv) : Nat :=
  let l := lengths I.calldata
  wideEntryGas I.calldata + wideBarrettDirectWordGas I l.base l.exponent l.modulus

def wideBarrettDirectWordEnsures (ctx : BytecodeContext) (result : BytecodeResult) : Prop :=
  ExactGasPost ctx (Model.output ctx.executionEnv.calldata)
    (wideBarrettDirectWordTotalGas ctx.executionEnv) result

theorem wideBarrettDirectWordFromEntryExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat}
    {output : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hexp : Model.bytesToNatPadded I.calldata
      (wideExponentOffset baseSize) exponentSize ≠ 0)
    (hbase : 1 < Model.bytesToNatPadded I.calldata 96 baseSize)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (wideModulusOffset baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (heven : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = ⟨0⟩)
    (hfirst :
      modulusSize = 1 ∨
      UInt256.byteAt ⟨0⟩
        (wideLoadWord
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (UInt256.ofNat (operandModulusPtr baseSize exponentSize + 32))) ≠ ⟨0⟩)
    (hheader :
      (if operandFreePtr baseSize exponentSize modulusSize ≥
            (wideMontgomeryWordMemory I baseSize exponentSize modulusSize).size ∨
          UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) ≥
            wideWordResultWords baseSize exponentSize modulusSize * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
          ((wideMontgomeryWordMemory I baseSize exponentSize modulusSize).readWithPadding
            (operandFreePtr baseSize exponentSize modulusSize) 32))) =
        UInt256.ofNat modulusSize)
    (houtput :
      (wideMontgomeryWordMemory I baseSize exponentSize modulusSize).readWithPadding
        (operandFreePtr baseSize exponentSize modulusSize + 32) modulusSize = output)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨62⟩
      [UInt256.ofNat exponentSize, UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc output
      (C + wideBarrettDirectWordGas I baseSize exponentSize modulusSize) := by
  have hm1024 : modulusSize ≤ 1024 := by omega
  obtain ⟨kExp, rd89⟩ := reachWideExponentNonzero
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (by omega : 96 + baseSize + exponentSize + 32 < 2 ^ 64) hexp rd0
  obtain ⟨kBase, rd105⟩ := reachWideBaseGtOne
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (by omega : 96 + baseSize + exponentSize + 32 < 2 ^ 64) hbase rd89
  have rd1183 := prepareOperandsExact
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (tail := []) hb he hm1024 hcalldata (by simp)
    (by
      simpa [wideModulusOffset, wideExponentOffset] using rd105)
  have rd1183' : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1183⟩
      [UInt256.ofNat operandBasePtr, UInt256.ofNat (operandExponentPtr baseSize),
        UInt256.ofNat (operandModulusPtr baseSize exponentSize), UInt256.ofNat 173]
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      ByteArray.empty acc
      (kBase + 292 + baseCalldataCopySteps I baseSize +
        calldataSegmentSteps I (96 + baseSize) exponentSize +
        calldataSegmentSteps I (96 + baseSize + exponentSize) modulusSize)
      (C + 79 + cdRangeGas I (96 + baseSize) (96 + baseSize + exponentSize) +
        wideBaseGtOneGas I baseSize +
        operandSetupGas I baseSize exponentSize modulusSize) := by
    exact RDx.withStack rd1183 (by
      rw [show (⟨173⟩ : UInt256) = UInt256.ofNat 173 by native_decide])
  obtain ⟨kBarrett, rd173⟩ := runPreparedBarrettDirectWordExactAny
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (ret := 173) (tail := []) hb he hmodPos hm
    (by simpa [wideModulusOffset] using hmod)
    hcalldata heven hfirst jumpDest_wrapper173_barrett (by simp)
    rd1183'
  have hfpBound :
      operandFreePtr baseSize exponentSize modulusSize + 32 < 2 ^ 64 := by
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hawNat := wideWordResultWords_toNat hb he hm1024
  have hloadActive :
      operandFreePtr baseSize exponentSize modulusSize + 32 ≤
        32 * (wideWordResultWords baseSize exponentSize modulusSize).toNat := by
    rw [hawNat, operandFreePtr_eq]
    unfold bytesAllocationWords
    omega
  have hreturnActive :
      operandFreePtr baseSize exponentSize modulusSize + 32 + modulusSize ≤
        32 * (wideWordResultWords baseSize exponentSize modulusSize).toNat := by
    rw [hawNat, operandFreePtr_eq]
    unfold bytesAllocationWords
    have hround := bytesSize_le_roundedPayload modulusSize
    omega
  have hret := wrapperReturnExact
    (ptr := operandFreePtr baseSize exponentSize modulusSize)
    (len := modulusSize) (tail := [])
    (mem := wideMontgomeryWordMemory I baseSize exponentSize modulusSize)
    (aw := wideWordResultWords baseSize exponentSize modulusSize)
    (output := output) hm1024 hfpBound hloadActive hreturnActive hheader houtput (by simp) rd173
  exact hret.withCost (by
    unfold wideBarrettDirectWordGas wideExponentOffset wideModulusOffset
    omega)

theorem wideBarrettDirectWordFromEntryModelExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hexp : Model.bytesToNatPadded I.calldata
      (wideExponentOffset baseSize) exponentSize ≠ 0)
    (hbase : 1 < Model.bytesToNatPadded I.calldata 96 baseSize)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (wideModulusOffset baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (heven : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = ⟨0⟩)
    (hfirst :
      modulusSize = 1 ∨
      UInt256.byteAt ⟨0⟩
        (wideLoadWord
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (UInt256.ofNat (operandModulusPtr baseSize exponentSize + 32))) ≠ ⟨0⟩)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨62⟩
      [UInt256.ofNat exponentSize, UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes
        (Model.modPow
          (Model.bytesToNatPadded I.calldata 96 baseSize)
          (Model.bytesToNatPadded I.calldata (wideExponentOffset baseSize) exponentSize)
          (Model.bytesToNatPadded I.calldata
            (wideModulusOffset baseSize exponentSize) modulusSize))
        modulusSize)
      (C + wideBarrettDirectWordGas I baseSize exponentSize modulusSize) := by
  exact wideBarrettDirectWordFromEntryExact
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    hb he hmodPos hm hexp hbase hmod hcalldata heven hfirst
    (wideMontgomeryWordHeader_eq I baseSize exponentSize modulusSize hb he hmodPos hm)
    (wideMontgomeryWordOutput_eq_model I baseSize exponentSize modulusSize
      hb he hmodPos hm hmod)
    rd0

theorem wideBarrettDirectWordModelExactGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hvalid : validOsaka I.calldata) (hwide : ¬ wordSized I.calldata)
    (hcond : wideBarrettDirectWordCondition I) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (Model.output I.calldata) (wideBarrettDirectWordTotalGas I) := by
  let l := lengths I.calldata
  unfold wideBarrettDirectWordCondition at hcond
  dsimp [l] at hcond
  rcases hcond with
    ⟨hmodPos, hmWord, hexp, hbase, hmod, heven, hfirst⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, hm⟩
  obtain ⟨kEntry, rd62⟩ := reachWideEntry
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hvalue hvalid hwide
  have hret := wideBarrettDirectWordFromEntryModelExact
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    (baseSize := l.base) (exponentSize := l.exponent) (modulusSize := l.modulus)
    (acc := (cA, σ)) hb he hmodPos hmWord hexp hbase hmod hcalldata heven hfirst rd62
  have hout := model_output_of_lengths I.calldata
    (by rfl : Model.bytesToNatPadded I.calldata 0 32 = l.base)
    (by rfl : Model.bytesToNatPadded I.calldata 32 32 = l.exponent)
    (by rfl : Model.bytesToNatPadded I.calldata 64 32 = l.modulus)
  rw [hout]
  convert hret using 1

theorem wideBarrettDirectWordBytecodeSpec :
    BytecodeSpec runtimeBytecode wideBarrettDirectWordAccepts wideBarrettDirectWordEnsures := by
  simpa [wideBarrettDirectWordEnsures] using
    (ExactGasSpec.ofRDxRet (code := runtimeBytecode)
      (accepts := wideBarrettDirectWordAccepts)
      (output := fun ctx => Model.output ctx.executionEnv.calldata)
      (gasCost := fun ctx => wideBarrettDirectWordTotalGas ctx.executionEnv)
      (fun ctx hcode haccepts => by
        rcases haccepts with ⟨hvalue, hcalldata, hvalid, hwide, hcond⟩
        exact wideBarrettDirectWordModelExactGas
          (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
          (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
          (I := ctx.executionEnv) (g := ctx.gas)
          hcode hvalue hcalldata hvalid hwide hcond))

/-! ## Normalized even one-word Barrett path

The leading-zero Barrett path first allocates a normalized modulus byte array, re-enters the
Barrett caller, runs the one-word backend on that normalized array, and then restores the shortened
result payload into the originally allocated result array.  The control-flow proof is in
`BarrettWordCaller`; this section packages it as the same public `BytecodeSpec` interface as the
direct path.  The pure memory facts about the normalized temporary arrays are intentionally kept in
one structure so they can be discharged independently.
-/

def wideBarrettNormalizedFp
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  operandFreePtr baseSize exponentSize modulusSize + bytesAllocationSize modulusSize

def wideBarrettNormalizedLenFor (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  barrettNormalizedLen
    (wideWordResultMemory I baseSize exponentSize modulusSize)
    (wideWordResultWords baseSize exponentSize modulusSize)
    (operandModulusPtr baseSize exponentSize) modulusSize

def wideBarrettNormalizedResultFp (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  wideBarrettNormalizedFp baseSize exponentSize modulusSize +
    bytesAllocationSize (wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize)

def wideBarrettNormalizedFinalMemory (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : ByteArray :=
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let resultFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let n := barrettNormalizedLen mem aw p modulusSize
  barrettRestoreMemory
    (wideWordReturnMemory
      (barrettNormalizedResultMem mem aw fp p modulusSize resultFp)
      (wideWordValueAtModulusPtr
        (barrettNormalizedResultMem mem aw fp p modulusSize resultFp)
        (barrettNormalizedResultAw mem aw fp p modulusSize resultFp)
        baseSize exponentSize fp n)
      (UInt256.ofNat resultFp) n)
    resultFp (operandFreePtr baseSize exponentSize modulusSize)
    (barrettNormalizedOffset mem aw p modulusSize) n

def wideBarrettNormalizedFinalWords (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let resultFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  barrettRestoreWords
    (barrettNormalizedResultAw mem aw fp p modulusSize resultFp)
    resultFp (operandFreePtr baseSize exponentSize modulusSize)
    (barrettNormalizedOffset mem aw p modulusSize)
    (barrettNormalizedLen mem aw p modulusSize)

def wideBarrettNormalizedWordGas (I : ExecutionEnv)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  79 + cdRangeGas I (wideExponentOffset baseSize) (wideModulusOffset baseSize exponentSize) +
    wideBaseGtOneGas I baseSize +
    operandSetupGas I baseSize exponentSize modulusSize +
    preparedBarrettNormalizedWordGasFromAw I
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize) +
    16

private theorem barrettNormalizedMemory_base_size
    {mem : ByteArray} {fp len : Nat}
    (hmem96 : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) :
    (storeBytesLength (setFreePtr mem (fp + bytesAllocationSize len)) fp len).size =
      fp + 32 := by
  exact storeBytesLength_size
    (by rw [setFreePtr_size hmem96]; exact hmemLe)
    (by rw [setFreePtr_size hmem96]; exact hgap)

private theorem barrettNormalizedMemory_size
    {mem : ByteArray} {fp p offset len : Nat}
    (hmem96 : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) (hlen : 0 < len)
    (hsrc : p + offset + len ≤ fp + 32) :
    (barrettNormalizedMemory mem fp p offset len).size = fp + 32 + len := by
  let mem1 := storeBytesLength (setFreePtr mem (fp + bytesAllocationSize len)) fp len
  have hmem1Size : mem1.size = fp + 32 := by
    simpa [mem1] using
      (barrettNormalizedMemory_base_size (len := len) hmem96 hmemLe hgap)
  have hwrite := write_end_size_from mem1 mem1 (p + offset) len
    (Nat.ne_of_gt hlen) (by rw [hmem1Size]; exact hsrc)
  unfold barrettNormalizedMemory
  simpa [mem1, hmem1Size] using hwrite

private theorem barrettNormalizedMemory_read_length
    {mem : ByteArray} {fp p offset len : Nat}
    (hmem96 : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) (hlen : 0 < len)
    (hsrc : p + offset + len ≤ fp + 32) :
    (barrettNormalizedMemory mem fp p offset len).readWithPadding fp 32 =
      UInt256.toByteArray (UInt256.ofNat len) := by
  let mem1 := storeBytesLength (setFreePtr mem (fp + bytesAllocationSize len)) fp len
  have hmem1Size : mem1.size = fp + 32 := by
    simpa [mem1] using
      (barrettNormalizedMemory_base_size (len := len) hmem96 hmemLe hgap)
  have hpres := write_read_below_end_from mem1 mem1 (p + offset) len fp
    (Nat.ne_of_gt hlen) (by rw [hmem1Size]; exact hsrc)
    (by rw [hmem1Size])
  have hself :
      mem1.readWithPadding fp 32 = UInt256.toByteArray (UInt256.ofNat len) := by
    simpa [mem1] using
      (storeBytesLength_read_self
        (mem := setFreePtr mem (fp + bytesAllocationSize len)) (fp := fp) (n := len)
        (by rw [setFreePtr_size hmem96]; exact hgap))
  unfold barrettNormalizedMemory
  simpa [mem1, hmem1Size] using hpres.trans hself

private theorem barrettNormalizedMemory_read64
    {mem : ByteArray} {fp p offset len : Nat}
    (hmem96 : 96 ≤ mem.size) (hfp96 : 96 ≤ fp) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) (hlen : 0 < len)
    (hsrc : p + offset + len ≤ fp + 32) :
    (barrettNormalizedMemory mem fp p offset len).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat (fp + bytesAllocationSize len)) := by
  let mem1 := storeBytesLength (setFreePtr mem (fp + bytesAllocationSize len)) fp len
  have hmem1Size : mem1.size = fp + 32 := by
    simpa [mem1] using
      (barrettNormalizedMemory_base_size (len := len) hmem96 hmemLe hgap)
  have hpres := write_read_below_end_from mem1 mem1 (p + offset) len 64
    (Nat.ne_of_gt hlen) (by rw [hmem1Size]; exact hsrc)
    (by rw [hmem1Size]; omega)
  have hread64 :
      mem1.readWithPadding 64 32 =
        UInt256.toByteArray (UInt256.ofNat (fp + bytesAllocationSize len)) := by
    rw [show mem1.readWithPadding 64 32 =
        (setFreePtr mem (fp + bytesAllocationSize len)).readWithPadding 64 32 from by
          simpa [mem1] using
            (storeBytesLength_read64
              (mem := setFreePtr mem (fp + bytesAllocationSize len)) (fp := fp)
              (n := len)
              (by rw [setFreePtr_size hmem96]; exact hmem96)
              hfp96
              (by rw [setFreePtr_size hmem96]; exact hgap))]
    exact setFreePtr_read64 hmem96
  unfold barrettNormalizedMemory
  simpa [mem1, hmem1Size] using hpres.trans hread64

private theorem barrettNormalizedMemory_read_below_padded
    {mem : ByteArray} {fp p offset len read : Nat}
    (hmem96 : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) (hlen : 0 < len)
    (hsrc : p + offset + len ≤ fp + 32)
    (hread : 96 ≤ read) (hbelow : read + 32 ≤ fp) :
    (barrettNormalizedMemory mem fp p offset len).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  let mem1 := storeBytesLength (setFreePtr mem (fp + bytesAllocationSize len)) fp len
  have hmem1Size : mem1.size = fp + 32 := by
    simpa [mem1] using
      (barrettNormalizedMemory_base_size (len := len) hmem96 hmemLe hgap)
  have hpresCopy := write_read_below_end_from mem1 mem1 (p + offset) len read
    (Nat.ne_of_gt hlen) (by rw [hmem1Size]; exact hsrc)
    (by rw [hmem1Size]; omega)
  have hpresHeader :
      mem1.readWithPadding read 32 =
        (setFreePtr mem (fp + bytesAllocationSize len)).readWithPadding read 32 := by
    simpa [mem1] using
      (storeBytesLength_read_below_padded
        (mem := setFreePtr mem (fp + bytesAllocationSize len)) (fp := fp)
        (n := len) (read := read)
        (by rw [setFreePtr_size hmem96]; omega)
        hbelow
        (by rw [setFreePtr_size hmem96]; exact hgap))
  have hpresFree :
      (setFreePtr mem (fp + bytesAllocationSize len)).readWithPadding read 32 =
        mem.readWithPadding read 32 :=
    setFreePtr_read_above_padded hmem96 hread
  unfold barrettNormalizedMemory
  simpa [mem1, hmem1Size] using hpresCopy.trans (hpresHeader.trans hpresFree)

/-- Variable-width reads below the normalized allocation are preserved. -/
private theorem barrettNormalizedMemory_read_below_len
    {mem : ByteArray} {fp p offset written read len : Nat}
    (hmem96 : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) (hwritten : 0 < written)
    (hsrc : p + offset + written ≤ fp + 32)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hreadAbove : 96 ≤ read) (hreadIn : read + len ≤ mem.size)
    (hbelow : read + len ≤ fp) :
    (barrettNormalizedMemory mem fp p offset written).readWithPadding read len =
      mem.readWithPadding read len := by
  let mem1 := storeBytesLength (setFreePtr mem (fp + bytesAllocationSize written)) fp written
  have hmem1Size : mem1.size = fp + 32 := by
    simpa [mem1] using
      (barrettNormalizedMemory_base_size (len := written) hmem96 hmemLe hgap)
  have hpresCopy := write_read_below_gen_from_extend mem1 mem1 (p + offset) (fp + 32)
    written read len
    (Nat.ne_of_gt hwritten)
    (by rw [hmem1Size]; exact hsrc)
    (by rw [hmem1Size])
    (by omega)
    (by rw [hmem1Size]; omega)
    hpos hlen64
  have hpresHeader :
      mem1.readWithPadding read len =
        (setFreePtr mem (fp + bytesAllocationSize written)).readWithPadding read len := by
    simpa [mem1] using
      (storeBytesLength_read_below_len
        (mem := setFreePtr mem (fp + bytesAllocationSize written)) (fp := fp)
        (n := written) (read := read) (len := len)
        (by rw [setFreePtr_size hmem96]; exact hreadIn)
        hbelow hpos hlen64
        (by rw [setFreePtr_size hmem96]; exact hgap))
  have hpresFree :
      (setFreePtr mem (fp + bytesAllocationSize written)).readWithPadding read len =
        mem.readWithPadding read len :=
    setFreePtr_read_above_len hmem96 hreadAbove hreadIn hpos hlen64
  unfold barrettNormalizedMemory
  exact hpresCopy.trans (hpresHeader.trans hpresFree)

/-- Variable-width reads inside the zero gap below the normalized allocation return zeroes. -/
private theorem barrettNormalizedMemory_read_gap_len
    {mem : ByteArray} {fp p offset written read len : Nat}
    (hmem96 : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) (hwritten : 0 < written)
    (hsrc : p + offset + written ≤ fp + 32)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hstart : mem.size ≤ read) (hbelow : read + len ≤ fp) :
    (barrettNormalizedMemory mem fp p offset written).readWithPadding read len =
      ffi.ByteArray.zeroes len := by
  let mem1 := storeBytesLength (setFreePtr mem (fp + bytesAllocationSize written)) fp written
  have hmem1Size : mem1.size = fp + 32 := by
    simpa [mem1] using
      (barrettNormalizedMemory_base_size (len := written) hmem96 hmemLe hgap)
  have hpresCopy := write_read_below_gen_from_extend mem1 mem1 (p + offset) (fp + 32)
    written read len
    (Nat.ne_of_gt hwritten)
    (by rw [hmem1Size]; exact hsrc)
    (by rw [hmem1Size])
    (by omega)
    (by rw [hmem1Size]; omega)
    hpos hlen64
  have hmem1Zero :
      mem1.readWithPadding read len = ffi.ByteArray.zeroes len := by
    dsimp [mem1]
    unfold storeBytesLength
    exact toByteArray_write_read_gap_of_gap (UInt256.ofNat written)
      (setFreePtr mem (fp + bytesAllocationSize written)) fp read len
      (by rw [setFreePtr_size hmem96]; exact hstart)
      hbelow hpos hlen64
      (by rw [setFreePtr_size hmem96]; exact hgap)
  unfold barrettNormalizedMemory
  exact hpresCopy.trans hmem1Zero

/-- The normalized temporary modulus payload is exactly the significant suffix copied from the
original modulus bytes. -/
theorem barrettNormalizedMemory_read_payload
    {mem : ByteArray} {fp p offset len : Nat}
    (hmem96 : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) (hlen : 0 < len) (hlen64 : len < 2 ^ 64)
    (hsrc : p + offset + len ≤ fp + 32) :
    (barrettNormalizedMemory mem fp p offset len).readWithPadding (fp + 32) len =
      (storeBytesLength (setFreePtr mem (fp + bytesAllocationSize len)) fp len).extract
        (p + offset) (p + offset + len) := by
  let mem1 := storeBytesLength (setFreePtr mem (fp + bytesAllocationSize len)) fp len
  have hmem1Size : mem1.size = fp + 32 := by
    simpa [mem1] using
      (barrettNormalizedMemory_base_size (len := len) hmem96 hmemLe hgap)
  have hcopy := write_read_back_from_gen mem1 mem1 (p + offset) (fp + 32) len
    (Nat.ne_of_gt hlen)
    (by rw [hmem1Size]; exact hsrc)
    (by rw [hmem1Size])
    hlen64
  unfold barrettNormalizedMemory
  simpa [mem1] using hcopy

/-- Allocating the normalized result array above the normalized modulus keeps the normalized
modulus payload unchanged. -/
theorem barrettNormalizedResultMem_read_payload
    {mem : ByteArray} {fp p m resultFp : Nat} {aw : UInt256}
    (hresultMemSize : 96 ≤ (barrettNormalizedMem mem aw fp p m).size)
    (hresultGap : resultFp - (barrettNormalizedMem mem aw fp p m).size < USize.size)
    (hfpRead : 96 ≤ fp + 32)
    (hlen : 0 < barrettNormalizedLen mem aw p m)
    (hlen64 : barrettNormalizedLen mem aw p m < 2 ^ 64)
    (hreadIn :
      fp + 32 + barrettNormalizedLen mem aw p m ≤
        (barrettNormalizedMem mem aw fp p m).size)
    (hbelowResultFp : fp + 32 + barrettNormalizedLen mem aw p m ≤ resultFp) :
    (barrettNormalizedResultMem mem aw fp p m resultFp).readWithPadding
        (fp + 32) (barrettNormalizedLen mem aw p m) =
      (barrettNormalizedMem mem aw fp p m).readWithPadding
        (fp + 32) (barrettNormalizedLen mem aw p m) := by
  unfold barrettNormalizedResultMem
  have hfree :
      (setFreePtr (barrettNormalizedMem mem aw fp p m)
          (resultFp + bytesAllocationSize (barrettNormalizedLen mem aw p m))).readWithPadding
          (fp + 32) (barrettNormalizedLen mem aw p m) =
        (barrettNormalizedMem mem aw fp p m).readWithPadding
          (fp + 32) (barrettNormalizedLen mem aw p m) := by
    exact setFreePtr_read_above_len
      (mem := barrettNormalizedMem mem aw fp p m)
      (fp := resultFp + bytesAllocationSize (barrettNormalizedLen mem aw p m))
      (read := fp + 32) (len := barrettNormalizedLen mem aw p m)
      hresultMemSize hfpRead hreadIn hlen hlen64
  have hstore :
      (storeBytesLength
          (setFreePtr (barrettNormalizedMem mem aw fp p m)
            (resultFp + bytesAllocationSize (barrettNormalizedLen mem aw p m)))
          resultFp (barrettNormalizedLen mem aw p m)).readWithPadding
          (fp + 32) (barrettNormalizedLen mem aw p m) =
        (setFreePtr (barrettNormalizedMem mem aw fp p m)
          (resultFp + bytesAllocationSize (barrettNormalizedLen mem aw p m))).readWithPadding
          (fp + 32) (barrettNormalizedLen mem aw p m) := by
    exact storeBytesLength_read_below_len
      (mem := setFreePtr (barrettNormalizedMem mem aw fp p m)
        (resultFp + bytesAllocationSize (barrettNormalizedLen mem aw p m)))
      (fp := resultFp) (n := barrettNormalizedLen mem aw p m)
      (read := fp + 32) (len := barrettNormalizedLen mem aw p m)
      (by rw [setFreePtr_size hresultMemSize]; exact hreadIn)
      hbelowResultFp hlen hlen64
      (by rw [setFreePtr_size hresultMemSize]; exact hresultGap)
  exact hstore.trans hfree

/-- The normalized result payload is the significant suffix read from the original memory.  This
combines the normalized-modulus allocation preservation, the result-allocation preservation, and
the conversion from the intermediate copied extract back to a padded read of the original source. -/
theorem barrettNormalizedResultMem_read_source_payload
    {mem : ByteArray} {fp p m resultFp : Nat} {aw : UInt256}
    (hmem96 : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hlen : 0 < barrettNormalizedLen mem aw p m)
    (hlen64 : barrettNormalizedLen mem aw p m < 2 ^ 64)
    (hsrc : p + barrettNormalizedOffset mem aw p m +
      barrettNormalizedLen mem aw p m ≤ fp + 32)
    (hsourceInMem :
      p + barrettNormalizedOffset mem aw p m +
        barrettNormalizedLen mem aw p m ≤ mem.size)
    (hsourceAbove : 96 ≤ p + barrettNormalizedOffset mem aw p m)
    (hsourceBelowFp :
      p + barrettNormalizedOffset mem aw p m +
        barrettNormalizedLen mem aw p m ≤ fp)
    (hresultFp :
      resultFp = fp + bytesAllocationSize (barrettNormalizedLen mem aw p m)) :
    (barrettNormalizedResultMem mem aw fp p m resultFp).readWithPadding
        (fp + 32) (barrettNormalizedLen mem aw p m) =
      mem.readWithPadding
        (p + barrettNormalizedOffset mem aw p m)
        (barrettNormalizedLen mem aw p m) := by
  let len := barrettNormalizedLen mem aw p m
  let offset := barrettNormalizedOffset mem aw p m
  let mem1 := storeBytesLength (setFreePtr mem (fp + bytesAllocationSize len)) fp len
  have hnormMemSize :
      (barrettNormalizedMem mem aw fp p m).size = fp + 32 + len := by
    simpa [barrettNormalizedMem, offset, len] using
      barrettNormalizedMemory_size
        (mem := mem) (fp := fp) (p := p) (offset := offset) (len := len)
        hmem96 hmemLe hgap (by simpa [len] using hlen)
        (by simpa [offset, len] using hsrc)
  have hresultMemSize : 96 ≤ (barrettNormalizedMem mem aw fp p m).size := by
    rw [hnormMemSize]
    omega
  have hreadIn :
      fp + 32 + barrettNormalizedLen mem aw p m ≤
        (barrettNormalizedMem mem aw fp p m).size := by
    rw [hnormMemSize]
  have hresultGap :
      resultFp - (barrettNormalizedMem mem aw fp p m).size < USize.size := by
    rw [hresultFp, hnormMemSize]
    dsimp [len]
    unfold bytesAllocationSize
    exact lt_usize _ (by omega)
  have hbelowResultFp :
      fp + 32 + barrettNormalizedLen mem aw p m ≤ resultFp := by
    rw [hresultFp]
    unfold bytesAllocationSize
    omega
  have hresultPayloadRead :
      (barrettNormalizedResultMem mem aw fp p m resultFp).readWithPadding
          (fp + 32) (barrettNormalizedLen mem aw p m) =
        (barrettNormalizedMem mem aw fp p m).readWithPadding
          (fp + 32) (barrettNormalizedLen mem aw p m) := by
    exact barrettNormalizedResultMem_read_payload
      hresultMemSize hresultGap (by omega) hlen hlen64 hreadIn hbelowResultFp
  have hnormalizedPayloadRead :
      (barrettNormalizedMem mem aw fp p m).readWithPadding
          (fp + 32) (barrettNormalizedLen mem aw p m) =
        mem.readWithPadding
          (p + barrettNormalizedOffset mem aw p m)
          (barrettNormalizedLen mem aw p m) := by
    have hpayload := barrettNormalizedMemory_read_payload
      (mem := mem) (fp := fp) (p := p) (offset := offset) (len := len)
      hmem96 hmemLe hgap (by simpa [len] using hlen)
      (by simpa [len] using hlen64)
      (by simpa [offset, len] using hsrc)
    have hmem1Read :
        mem1.readWithPadding (p + offset) len =
          mem.readWithPadding (p + offset) len := by
      have hfree :
          (setFreePtr mem (fp + bytesAllocationSize len)).readWithPadding
              (p + offset) len =
            mem.readWithPadding (p + offset) len := by
        exact setFreePtr_read_above_len hmem96
          (by simpa [offset] using hsourceAbove)
          (by simpa [offset, len] using hsourceInMem)
          (by simpa [len] using hlen)
          (by simpa [len] using hlen64)
      have hstore :
          mem1.readWithPadding (p + offset) len =
            (setFreePtr mem (fp + bytesAllocationSize len)).readWithPadding
              (p + offset) len := by
        dsimp [mem1]
        exact storeBytesLength_read_below_len
          (mem := setFreePtr mem (fp + bytesAllocationSize len)) (fp := fp)
          (n := len)
          (read := p + offset)
          (len := len)
          (by rw [setFreePtr_size hmem96]; simpa [offset, len] using hsourceInMem)
          (by simpa [offset, len] using hsourceBelowFp)
          (by simpa [len] using hlen)
          (by simpa [len] using hlen64)
          (by rw [setFreePtr_size hmem96]; exact hgap)
      exact hstore.trans hfree
    have hmem1Extract :
        mem1.extract (p + offset) (p + offset + len) =
          mem1.readWithPadding (p + offset) len := by
      apply Eq.symm
      apply readWithPadding_eq_extract'
      · simpa [len] using hlen
      · simpa [len] using hlen64
      · dsimp [mem1]
        rw [storeBytesLength_size]
        · simpa [offset, len] using hsrc
        · rw [setFreePtr_size hmem96]
          exact hmemLe
        · rw [setFreePtr_size hmem96]
          exact hgap
    simpa [barrettNormalizedMem, offset, len, mem1] using
      hpayload.trans (hmem1Extract.trans hmem1Read)
  exact hresultPayloadRead.trans hnormalizedPayloadRead

/-- Allocating the normalized result array above a lower window preserves variable-width reads from
the normalized memory. -/
theorem barrettNormalizedResultMem_read_below_len
    {mem : ByteArray} {fp p m resultFp read len : Nat} {aw : UInt256}
    (hresultMemSize : 96 ≤ (barrettNormalizedMem mem aw fp p m).size)
    (hresultGap : resultFp - (barrettNormalizedMem mem aw fp p m).size < USize.size)
    (hreadAbove : 96 ≤ read)
    (hpos : 0 < len)
    (hlen64 : len < 2 ^ 64)
    (hreadIn : read + len ≤ (barrettNormalizedMem mem aw fp p m).size)
    (hbelowResultFp : read + len ≤ resultFp) :
    (barrettNormalizedResultMem mem aw fp p m resultFp).readWithPadding read len =
      (barrettNormalizedMem mem aw fp p m).readWithPadding read len := by
  unfold barrettNormalizedResultMem
  have hfree :
      (setFreePtr (barrettNormalizedMem mem aw fp p m)
          (resultFp + bytesAllocationSize (barrettNormalizedLen mem aw p m))).readWithPadding
          read len =
        (barrettNormalizedMem mem aw fp p m).readWithPadding read len := by
    exact setFreePtr_read_above_len
      (mem := barrettNormalizedMem mem aw fp p m)
      (fp := resultFp + bytesAllocationSize (barrettNormalizedLen mem aw p m))
      (read := read) (len := len)
      hresultMemSize hreadAbove hreadIn hpos hlen64
  have hstore :
      (storeBytesLength
          (setFreePtr (barrettNormalizedMem mem aw fp p m)
            (resultFp + bytesAllocationSize (barrettNormalizedLen mem aw p m)))
          resultFp (barrettNormalizedLen mem aw p m)).readWithPadding read len =
        (setFreePtr (barrettNormalizedMem mem aw fp p m)
          (resultFp + bytesAllocationSize (barrettNormalizedLen mem aw p m))).readWithPadding
          read len := by
    exact storeBytesLength_read_below_len
      (mem := setFreePtr (barrettNormalizedMem mem aw fp p m)
        (resultFp + bytesAllocationSize (barrettNormalizedLen mem aw p m)))
      (fp := resultFp) (n := barrettNormalizedLen mem aw p m)
      (read := read) (len := len)
      (by rw [setFreePtr_size hresultMemSize]; exact hreadIn)
      hbelowResultFp hpos hlen64
      (by rw [setFreePtr_size hresultMemSize]; exact hresultGap)
  exact hstore.trans hfree

/-- The two normalized allocations preserve any in-bounds original operand window below the
normalized allocation pointer. -/
theorem barrettNormalizedResultMem_read_original_len
    {mem : ByteArray} {aw : UInt256} {fp p m resultFp read len : Nat}
    (hmem96 : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hwritten : 0 < barrettNormalizedLen mem aw p m)
    (hsrc : p + barrettNormalizedOffset mem aw p m +
      barrettNormalizedLen mem aw p m ≤ fp + 32)
    (hresultMemSize : 96 ≤ (barrettNormalizedMem mem aw fp p m).size)
    (hresultGap : resultFp - (barrettNormalizedMem mem aw fp p m).size < USize.size)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hreadAbove : 96 ≤ read)
    (hreadIn : read + len ≤ mem.size)
    (hbelowFp : read + len ≤ fp)
    (hbelowResultFp : read + len ≤ resultFp) :
    (barrettNormalizedResultMem mem aw fp p m resultFp).readWithPadding read len =
      mem.readWithPadding read len := by
  have hnorm :
      (barrettNormalizedMem mem aw fp p m).readWithPadding read len =
        mem.readWithPadding read len := by
    exact barrettNormalizedMemory_read_below_len
      hmem96 hmemLe hgap hwritten hsrc hpos hlen64 hreadAbove hreadIn hbelowFp
  have hreadInNorm : read + len ≤ (barrettNormalizedMem mem aw fp p m).size := by
    have hnormSize := barrettNormalizedMemory_size hmem96 hmemLe hgap hwritten hsrc
    change read + len ≤
      (barrettNormalizedMemory mem fp p (barrettNormalizedOffset mem aw p m)
        (barrettNormalizedLen mem aw p m)).size
    rw [hnormSize]
    omega
  have hresult :
      (barrettNormalizedResultMem mem aw fp p m resultFp).readWithPadding read len =
        (barrettNormalizedMem mem aw fp p m).readWithPadding read len := by
    exact barrettNormalizedResultMem_read_below_len
      hresultMemSize hresultGap hreadAbove hpos hlen64 hreadInNorm hbelowResultFp
  exact hresult.trans hnorm

/-- The byte tested by the Barrett leading-zero scan is the trusted one-byte padded read. -/
theorem barrettScanByteAt_toNat_eq_model
    {mem : ByteArray} {aw : UInt256} {cur : Nat}
    (hcur256 : cur < UInt256.size) (hcur64 : cur < 2 ^ 64)
    (haw : ¬ UInt256.ofNat cur ≥ aw * ⟨32⟩) :
    (barrettScanByteAt mem aw cur).toNat =
      Model.bytesToNatPadded mem cur 1 := by
  have hload :
      wideLoadWord mem aw (UInt256.ofNat cur) =
        uInt256OfByteArray (mem.readBytes cur 32) := by
    rw [wideLoadWord_eq_decode_bounded haw]
    congr 1
    rw [UInt256.toNat_ofNat_of_lt hcur256,
      readWithPadding_eq_model_readPadded mem cur 32 hcur64 (by decide),
      readBytes_eq_model_readPadded mem cur 32 hcur64 (by decide)]
  unfold barrettScanByteAt
  rw [hload]
  exact calldataByte0_toNat_eq_model mem cur hcur64

/-- A bounded `wideLoadWord` denotes the trusted 32-byte padded big-endian read at the same
address. -/
private theorem wideLoadWord_toNat_eq_model_bytes
    {mem : ByteArray} {aw : UInt256} {addr : Nat}
    (haddr256 : addr < UInt256.size) (haddr64 : addr < 2 ^ 64)
    (haw : ¬ UInt256.ofNat addr ≥ aw * ⟨32⟩) :
    (wideLoadWord mem aw (UInt256.ofNat addr)).toNat =
      Model.bytesToNatPadded mem addr 32 := by
  have hload :
      wideLoadWord mem aw (UInt256.ofNat addr) =
        uInt256OfByteArray (mem.readWithPadding addr 32) := by
    rw [wideLoadWord_eq_decode_bounded haw]
    rw [UInt256.toNat_ofNat_of_lt haddr256]
  rw [hload, uInt256OfByteArray_eq]
  have hlt :
      fromByteArrayBigEndian (mem.readWithPadding addr 32) < UInt256.size := by
    rw [← bytesToBigEndianNat_eq_fromByteArrayBigEndian]
    have hmodel := model_bytesToNatPadded_lt_pow mem addr 32
    rw [show UInt256.size = 256 ^ 32 by native_decide]
    simpa [Model.bytesToNatPadded,
      readWithPadding_eq_model_readPadded mem addr 32 haddr64 (by decide)] using hmodel
  rw [UInt256.toNat_ofNat_of_lt hlt]
  rw [← bytesToBigEndianNat_eq_fromByteArrayBigEndian]
  simp [Model.bytesToNatPadded,
    readWithPadding_eq_model_readPadded mem addr 32 haddr64 (by decide)]

private theorem wideWordScratchMemory_read_above
    {mem : ByteArray} {value : UInt256} {read : Nat}
    (habove : 32 ≤ read) (hin : read + 32 ≤ mem.size) :
    (wideWordScratchMemory mem value).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  unfold wideWordScratchMemory
  exact write32_read_above (UInt256.toByteArray value) mem 0 read
    (by rw [toByteArray_size]) (by simp) habove hin

private theorem wideWordScratchMemory_read_above_len
    {mem : ByteArray} {value : UInt256} {read len : Nat}
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (habove : 32 ≤ read) (hin : read + len ≤ mem.size) :
    (wideWordScratchMemory mem value).readWithPadding read len =
      mem.readWithPadding read len := by
  unfold wideWordScratchMemory
  exact write_read_above_gen_from (UInt256.toByteArray value) mem 0 0 32 read len
    (by decide) (by rw [toByteArray_size]) (by omega) habove hin hpos hlen64

private theorem wideWordReturnMemory_read_below
    {mem : ByteArray} {value result : UInt256} {len read : Nat}
    (hlen : 0 < len) (hlen32 : len ≤ 32)
    (hdest : result.toNat + 32 ≤ (wideWordScratchMemory mem value).size)
    (hbelow : read + 32 ≤ result.toNat + 32)
    (hreadIn : read + 32 ≤ (wideWordScratchMemory mem value).size) :
    (wideWordReturnMemory mem value result len).readWithPadding read 32 =
      (wideWordScratchMemory mem value).readWithPadding read 32 := by
  let scratch := wideWordScratchMemory mem value
  unfold wideWordReturnMemory
  exact write_read_below_gen_from_extend scratch scratch (32 - len) (result.toNat + 32)
    len read 32
    (Nat.ne_of_gt hlen)
    (by dsimp [scratch]; omega)
    (by dsimp [scratch]; exact hdest)
    hbelow
    (by dsimp [scratch]; exact hreadIn)
    (by decide) (by decide)

private theorem wideWordReturnMemory_read_below_len
    {mem : ByteArray} {value result : UInt256} {written read len : Nat}
    (hwritten : 0 < written) (hpos : 0 < len)
    (hwritten32 : written ≤ 32)
    (hlen64 : len < 2 ^ 64)
    (hdest : result.toNat + 32 ≤ (wideWordScratchMemory mem value).size)
    (hbelow : read + len ≤ result.toNat + 32)
    (hreadIn : read + len ≤ (wideWordScratchMemory mem value).size) :
    (wideWordReturnMemory mem value result written).readWithPadding read len =
      (wideWordScratchMemory mem value).readWithPadding read len := by
  let scratch := wideWordScratchMemory mem value
  unfold wideWordReturnMemory
  exact write_read_below_gen_from_extend scratch scratch (32 - written) (result.toNat + 32)
    written read len
    (Nat.ne_of_gt hwritten)
    (by dsimp [scratch]; omega)
    (by dsimp [scratch]; exact hdest)
    hbelow
    (by dsimp [scratch]; exact hreadIn)
    hpos hlen64

private theorem wideWordReturnMemory_size_at_end
    {mem : ByteArray} {value result : UInt256} {len : Nat}
    (hlen : 0 < len) (hlen32 : len ≤ 32)
    (hdest : result.toNat + 32 = (wideWordScratchMemory mem value).size) :
    (wideWordReturnMemory mem value result len).size = result.toNat + 32 + len := by
  let scratch := wideWordScratchMemory mem value
  unfold wideWordReturnMemory
  rw [hdest]
  exact write_end_size_from scratch scratch (32 - len) len
    (Nat.ne_of_gt hlen)
    (by dsimp [scratch]; omega)

private theorem wideWordReturnMemory_payload_eq_natToBytes
    {mem : ByteArray} {value result : UInt256} {width : Nat}
    (hpos : 0 < width) (hwidth : width ≤ 32)
    (hdest : result.toNat + 32 ≤ (wideWordScratchMemory mem value).size)
    (hfit : value.toNat < 256 ^ width) :
    (wideWordReturnMemory mem value result width).readWithPadding
        (result.toNat + 32) width =
      Model.natToBytes value.toNat width := by
  let scratch := wideWordScratchMemory mem value
  have hsum : 32 - width + width = 32 := by omega
  have hsrc : 32 - width + width ≤ scratch.size := by
    dsimp [scratch, wideWordScratchMemory]
    have hsize : 32 ≤ ((UInt256.toByteArray value).write 0 mem 0 32).size :=
      toByteArray_write_size_ge_off_add32 value mem 0 (by simp)
    omega
  have hcopy := write_read_back_from_gen scratch scratch
    (32 - width) (result.toNat + 32) width
    (Nat.ne_of_gt hpos) hsrc hdest (by omega)
  have hscratchRead :
      scratch.readWithPadding (32 - width) width =
        value.toByteArray.extract (32 - width) 32 := by
    dsimp [scratch]
    unfold wideWordScratchMemory
    simpa [hsum] using toByteArray_write_read_window_of_gap value mem 0
      (32 - width) width (by omega) hpos (by omega) (by simp)
  have hextract :
      scratch.extract (32 - width) 32 =
        value.toByteArray.extract (32 - width) 32 := by
    rw [← hscratchRead]
    simpa [hsum] using
      (readWithPadding_eq_extract' scratch (32 - width) width
        hpos (by omega) hsrc).symm
  unfold wideWordReturnMemory
  rw [hcopy, hsum, hextract]
  rw [← model_natToBytes_eq_toByteArray_suffix value width hwidth hfit]

private theorem barrettRestoreMemory_read_below
    {mem : ByteArray} {temp result offset len read : Nat}
    (hlen : 0 < len)
    (hsrc : temp + 32 + len ≤ mem.size)
    (hdest : result + offset ≤ mem.size)
    (hbelow : read + 32 ≤ result + offset)
    (hreadIn : read + 32 ≤ mem.size) :
    (barrettRestoreMemory mem temp result offset len).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  unfold barrettRestoreMemory
  exact write_read_below_gen_from_extend mem mem (temp + 32) (result + offset) len read 32
    (Nat.ne_of_gt hlen) hsrc hdest hbelow hreadIn (by decide) (by decide)

private theorem barrettRestoreMemory_read_below_len
    {mem : ByteArray} {temp result offset written read len : Nat}
    (hwritten : 0 < written) (hpos : 0 < len)
    (hlen64 : len < 2 ^ 64)
    (hsrc : temp + 32 + written ≤ mem.size)
    (hdest : result + offset ≤ mem.size)
    (hbelow : read + len ≤ result + offset)
    (hreadIn : read + len ≤ mem.size) :
    (barrettRestoreMemory mem temp result offset written).readWithPadding read len =
      mem.readWithPadding read len := by
  unfold barrettRestoreMemory
  exact write_read_below_gen_from_extend mem mem (temp + 32) (result + offset) written
    read len (Nat.ne_of_gt hwritten) hsrc hdest hbelow hreadIn hpos hlen64

private theorem barrettRestoreMemory_read_restored
    {mem : ByteArray} {temp result offset len : Nat}
    (hlen : 0 < len)
    (hsrc : temp + 32 + len ≤ mem.size)
    (hdest : result + offset ≤ mem.size)
    (hlen64 : len < 2 ^ 64) :
    (barrettRestoreMemory mem temp result offset len).readWithPadding
        (result + offset) len =
      mem.readWithPadding (temp + 32) len := by
  unfold barrettRestoreMemory
  rw [write_read_back_from_gen mem mem (temp + 32) (result + offset) len
    (Nat.ne_of_gt hlen) hsrc hdest hlen64]
  exact (readWithPadding_eq_extract' mem (temp + 32) len hlen hlen64 hsrc).symm

private theorem readWithPadding_eq_leftPaddedNatToBytes
    {mem : ByteArray} {start k len width value : Nat}
    (hklen : k + len = width)
    (hlenPos : 0 < len)
    (hwidth64 : width < 2 ^ 64)
    (hin : start + width ≤ mem.size)
    (hprefix : mem.readWithPadding start k = ffi.ByteArray.zeroes k)
    (hsuffix : mem.readWithPadding (start + k) len = Model.natToBytes value len)
    (hfit : value < 256 ^ len) :
    mem.readWithPadding start width = Model.natToBytes value width := by
  by_cases hk : k = 0
  · subst k
    have hwidth : width = len := by omega
    simpa [hwidth] using hsuffix
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk
    have hlen64 : len < 2 ^ 64 := by omega
    have hk64 : k < 2 ^ 64 := by omega
    have hsum64 : k + len < 2 ^ 64 := by omega
    have hsplit := byteArray_readWithPadding_split mem start k len
      hkPos hlenPos hk64 hlen64 hsum64 (by omega)
    rw [show width = k + len by omega, hsplit, hprefix, hsuffix]
    exact model_natToBytes_leftPad value k len hfit

private theorem barrettRestoreMemory_size_inBounds
    {mem : ByteArray} {temp result offset len : Nat}
    (hlen : 0 < len)
    (hsrc : temp + 32 + len ≤ mem.size)
    (hdest : result + offset + len ≤ mem.size) :
    (barrettRestoreMemory mem temp result offset len).size = mem.size := by
  unfold barrettRestoreMemory
  exact write_size_of_inBounds_from mem mem (temp + 32) (result + offset) len
    (Nat.ne_of_gt hlen) hsrc hdest

private theorem wideWordResultMemory_readResultLength
    (I : ExecutionEnv) (baseSize exponentSize modulusSize : Nat)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    (wideWordResultMemory I baseSize exponentSize modulusSize).readWithPadding
      (operandFreePtr baseSize exponentSize modulusSize) 32 =
      UInt256.toByteArray (UInt256.ofNat modulusSize) := by
  let fp := operandFreePtr baseSize exponentSize modulusSize
  let oldMem := operandCopiedMemory I baseSize exponentSize modulusSize
  have holdMem96 : 96 ≤ oldMem.size := by
    have hge := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
    have hptr : 96 ≤ operandModulusPtr baseSize exponentSize + 32 := by
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    exact hptr.trans hge
  have hgap :
      fp - (setFreePtr oldMem (fp + bytesAllocationSize modulusSize)).size < USize.size := by
    rw [setFreePtr_size holdMem96]
    exact lt_usize _ (by
      have hle : fp - oldMem.size ≤ fp := Nat.sub_le fp oldMem.size
      have hfp : fp < 2 ^ 32 := by
        unfold fp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega
      omega)
  simpa [fp, oldMem, wideWordResultMemory] using storeBytesLength_read_self hgap

private theorem wideWordReturnThenRestore_read_below_header
    {mem : ByteArray} {value : UInt256} {resultFp result offset len : Nat}
    {out : ByteArray}
    (hlen : 0 < len) (hlen32 : len ≤ 32)
    (hresultFpNat : (UInt256.ofNat resultFp).toNat = resultFp)
    (hmemSize : mem.size = resultFp + 32)
    (hread : mem.readWithPadding result 32 = out)
    (hresultGe32 : 32 ≤ result)
    (hbelowResultFp : result + 32 ≤ resultFp)
    (hoffsetGe32 : 32 ≤ offset)
    (hdestEnd : result + offset + len ≤ resultFp + 32 + len) :
    (barrettRestoreMemory
        (wideWordReturnMemory mem value (UInt256.ofNat resultFp) len)
        resultFp result offset len).readWithPadding result 32 = out := by
  let scratch := wideWordScratchMemory mem value
  let returned := wideWordReturnMemory mem value (UInt256.ofNat resultFp) len
  have hscratchSize : scratch.size = mem.size := by
    dsimp [scratch]
    unfold wideWordScratchMemory
    exact write_size_of_inBounds_from (UInt256.toByteArray value) mem 0 0 32
      (by decide)
      (by rw [toByteArray_size])
      (by rw [hmemSize]; omega)
  have hreadScratch : scratch.readWithPadding result 32 = out := by
    have hpres := wideWordScratchMemory_read_above
      (mem := mem) (value := value) (read := result)
      hresultGe32
      (by rw [hmemSize]; exact Nat.le_trans hbelowResultFp (by omega))
    simpa [scratch, hread] using hpres
  have hdestEq :
      (UInt256.ofNat resultFp).toNat + 32 =
        (wideWordScratchMemory mem value).size := by
    rw [hresultFpNat, hscratchSize, hmemSize]
  have hreturnedSize : returned.size = resultFp + 32 + len := by
    dsimp [returned]
    have h := wideWordReturnMemory_size_at_end
      (mem := mem) (value := value) (result := UInt256.ofNat resultFp) (len := len)
      hlen hlen32 hdestEq
    simpa [hresultFpNat] using h
  have hreadReturned : returned.readWithPadding result 32 = out := by
    dsimp [returned]
    have hpres := wideWordReturnMemory_read_below
      (mem := mem) (value := value) (result := UInt256.ofNat resultFp)
      (len := len) (read := result)
      hlen hlen32
      (by rw [hresultFpNat, hscratchSize, hmemSize])
      (by rw [hresultFpNat]; omega)
      (by rw [hscratchSize, hmemSize]; exact Nat.le_trans hbelowResultFp (by omega))
    simpa [scratch, hreadScratch] using hpres
  have hpresRestore := barrettRestoreMemory_read_below
    (mem := returned) (temp := resultFp) (result := result) (offset := offset)
    (len := len) (read := result)
    hlen
    (by rw [hreturnedSize])
    (by rw [hreturnedSize]; omega)
    (by omega)
    (by rw [hreturnedSize]; exact Nat.le_trans hbelowResultFp (by omega))
  simpa [returned, hreadReturned] using hpresRestore

private theorem wideWordReturnThenRestore_read_below_len
    {mem : ByteArray} {value : UInt256} {resultFp result offset written read len : Nat}
    {out : ByteArray}
    (hwritten : 0 < written) (hwritten32 : written ≤ 32)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hresultFpNat : (UInt256.ofNat resultFp).toNat = resultFp)
    (hmemSize : mem.size = resultFp + 32)
    (hread : mem.readWithPadding read len = out)
    (haboveScratch : 32 ≤ read)
    (hbelowResultFp : read + len ≤ resultFp)
    (hbelowRestore : read + len ≤ result + offset)
    (hdest : result + offset ≤ resultFp + 32 + written) :
    (barrettRestoreMemory
        (wideWordReturnMemory mem value (UInt256.ofNat resultFp) written)
        resultFp result offset written).readWithPadding read len = out := by
  let scratch := wideWordScratchMemory mem value
  let returned := wideWordReturnMemory mem value (UInt256.ofNat resultFp) written
  have hscratchSize : scratch.size = mem.size := by
    dsimp [scratch]
    unfold wideWordScratchMemory
    exact write_size_of_inBounds_from (UInt256.toByteArray value) mem 0 0 32
      (by decide)
      (by rw [toByteArray_size])
      (by rw [hmemSize]; omega)
  have hreadScratch : scratch.readWithPadding read len = out := by
    have hpres := wideWordScratchMemory_read_above_len
      (mem := mem) (value := value) (read := read) (len := len)
      hpos hlen64 haboveScratch (by rw [hmemSize]; omega)
    simpa [scratch, hread] using hpres
  have hdestEq :
      (UInt256.ofNat resultFp).toNat + 32 =
        (wideWordScratchMemory mem value).size := by
    rw [hresultFpNat, hscratchSize, hmemSize]
  have hreturnedSize : returned.size = resultFp + 32 + written := by
    dsimp [returned]
    have h := wideWordReturnMemory_size_at_end
      (mem := mem) (value := value) (result := UInt256.ofNat resultFp) (len := written)
      hwritten hwritten32 hdestEq
    simpa [hresultFpNat] using h
  have hreadReturned : returned.readWithPadding read len = out := by
    dsimp [returned]
    have hpres := wideWordReturnMemory_read_below_len
      (mem := mem) (value := value) (result := UInt256.ofNat resultFp)
      (written := written) (read := read) (len := len)
      hwritten hpos hwritten32 hlen64
      (by rw [hresultFpNat, hscratchSize, hmemSize])
      (by rw [hresultFpNat]; omega)
      (by rw [hscratchSize, hmemSize]; omega)
    simpa [scratch, hreadScratch] using hpres
  have hpresRestore := barrettRestoreMemory_read_below_len
    (mem := returned) (temp := resultFp) (result := result) (offset := offset)
    (written := written) (read := read) (len := len)
    hwritten hpos hlen64
    (by rw [hreturnedSize])
    (by rw [hreturnedSize]; exact hdest)
    hbelowRestore
    (by rw [hreturnedSize]; exact Nat.le_trans hbelowRestore hdest)
  simpa [returned, hreadReturned] using hpresRestore

private theorem wideWordReturnThenRestore_read_restored_payload
    {mem : ByteArray} {value : UInt256} {resultFp result offset len : Nat}
    (hlen : 0 < len) (hlen32 : len ≤ 32)
    (hlen64 : len < 2 ^ 64)
    (hresultFpNat : (UInt256.ofNat resultFp).toNat = resultFp)
    (hmemSize : mem.size = resultFp + 32)
    (hdest : result + offset ≤ resultFp + 32 + len)
    (hfit : value.toNat < 256 ^ len) :
    (barrettRestoreMemory
        (wideWordReturnMemory mem value (UInt256.ofNat resultFp) len)
        resultFp result offset len).readWithPadding (result + offset) len =
      Model.natToBytes value.toNat len := by
  let returned := wideWordReturnMemory mem value (UInt256.ofNat resultFp) len
  have hscratchSize :
      (wideWordScratchMemory mem value).size = mem.size := by
    unfold wideWordScratchMemory
    exact write_size_of_inBounds_from (UInt256.toByteArray value) mem 0 0 32
      (by decide)
      (by rw [toByteArray_size])
      (by rw [hmemSize]; omega)
  have hdestEq :
      (UInt256.ofNat resultFp).toNat + 32 =
        (wideWordScratchMemory mem value).size := by
    rw [hresultFpNat, hscratchSize, hmemSize]
  have hreturnedSize : returned.size = resultFp + 32 + len := by
    dsimp [returned]
    have h := wideWordReturnMemory_size_at_end
      (mem := mem) (value := value) (result := UInt256.ofNat resultFp) (len := len)
      hlen hlen32 hdestEq
    simpa [hresultFpNat] using h
  have hrestored := barrettRestoreMemory_read_restored
    (mem := returned) (temp := resultFp) (result := result) (offset := offset)
    (len := len)
    hlen
    (by rw [hreturnedSize])
    (by rw [hreturnedSize]; exact hdest)
    hlen64
  have hpayload := wideWordReturnMemory_payload_eq_natToBytes
    (mem := mem) (value := value) (result := UInt256.ofNat resultFp) (width := len)
    hlen hlen32
    (by rw [hresultFpNat, hscratchSize, hmemSize])
    hfit
  have hpayload' :
      returned.readWithPadding (resultFp + 32) len =
        Model.natToBytes value.toNat len := by
    simpa [returned, hresultFpNat] using hpayload
  exact hrestored.trans hpayload'

private theorem wideWordReturnThenRestore_size
    {mem : ByteArray} {value : UInt256} {resultFp result offset len : Nat}
    (hlen : 0 < len) (hlen32 : len ≤ 32)
    (hresultFpNat : (UInt256.ofNat resultFp).toNat = resultFp)
    (hmemSize : mem.size = resultFp + 32)
    (hdestEnd : result + offset + len ≤ resultFp + 32 + len) :
    (barrettRestoreMemory
        (wideWordReturnMemory mem value (UInt256.ofNat resultFp) len)
        resultFp result offset len).size = resultFp + 32 + len := by
  let returned := wideWordReturnMemory mem value (UInt256.ofNat resultFp) len
  have hscratchSize :
      (wideWordScratchMemory mem value).size = mem.size := by
    unfold wideWordScratchMemory
    exact write_size_of_inBounds_from (UInt256.toByteArray value) mem 0 0 32
      (by decide)
      (by rw [toByteArray_size])
      (by rw [hmemSize]; omega)
  have hdestEq :
      (UInt256.ofNat resultFp).toNat + 32 =
        (wideWordScratchMemory mem value).size := by
    rw [hresultFpNat, hscratchSize, hmemSize]
  have hreturnedSize : returned.size = resultFp + 32 + len := by
    dsimp [returned]
    have h := wideWordReturnMemory_size_at_end
      (mem := mem) (value := value) (result := UInt256.ofNat resultFp) (len := len)
      hlen hlen32 hdestEq
    simpa [hresultFpNat] using h
  have hsize := barrettRestoreMemory_size_inBounds
    (mem := returned) (temp := resultFp) (result := result) (offset := offset)
    (len := len)
    hlen
    (by rw [hreturnedSize])
    (by rw [hreturnedSize]; exact hdestEnd)
  simpa [returned, hreturnedSize] using hsize

private theorem barrettNormalizedFinalHeader_eq_generic
    {baseSize exponentSize result fp p m resultFp : Nat}
    {mem0 : ByteArray} {aw0 finalWords : UInt256}
    (hreadMem0 : mem0.readWithPadding result 32 =
      UInt256.toByteArray (UInt256.ofNat m))
    (hmemSize : 96 ≤ mem0.size) (hmemLe : mem0.size ≤ fp)
    (hgap : fp - mem0.size < USize.size)
    (hlenPos : 0 < barrettNormalizedLen mem0 aw0 p m)
    (hlenLe32 : barrettNormalizedLen mem0 aw0 p m ≤ 32)
    (hsource :
      p + barrettNormalizedOffset mem0 aw0 p m + barrettNormalizedLen mem0 aw0 p m ≤
        fp + 32)
    (hresultMemSize : 96 ≤ (barrettNormalizedMem mem0 aw0 fp p m).size)
    (hresultGap :
      resultFp - (barrettNormalizedMem mem0 aw0 fp p m).size < USize.size)
    (hresultAllocated :
      (barrettNormalizedResultMem mem0 aw0 fp p m resultFp).size = resultFp + 32)
    (hresultWord : result < UInt256.size)
    (hresultFpNat : (UInt256.ofNat resultFp).toNat = resultFp)
    (hresultGe96 : 96 ≤ result)
    (hbelowFp : result + 32 ≤ fp)
    (hbelowResultFp : result + 32 ≤ resultFp)
    (hoffsetGe32 : 32 ≤ barrettNormalizedOffset mem0 aw0 p m)
    (hdestEnd :
      result + barrettNormalizedOffset mem0 aw0 p m + barrettNormalizedLen mem0 aw0 p m ≤
        resultFp + 32 + barrettNormalizedLen mem0 aw0 p m)
    (hfinalMul32 :
      (finalWords * ⟨32⟩).toNat = 32 * finalWords.toNat)
    (hreturnLoadActive : result + 32 ≤ 32 * finalWords.toNat) :
    let resultMem := barrettNormalizedResultMem mem0 aw0 fp p m resultFp
    let value :=
      wideWordValueAtModulusPtr resultMem
        (barrettNormalizedResultAw mem0 aw0 fp p m resultFp)
        baseSize exponentSize fp (barrettNormalizedLen mem0 aw0 p m)
    let finalMem :=
      barrettRestoreMemory
        (wideWordReturnMemory resultMem value (UInt256.ofNat resultFp)
          (barrettNormalizedLen mem0 aw0 p m))
        resultFp result (barrettNormalizedOffset mem0 aw0 p m)
        (barrettNormalizedLen mem0 aw0 p m)
    (if result ≥ finalMem.size ∨ UInt256.ofNat result ≥ finalWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
        (finalMem.readWithPadding result 32))) =
      UInt256.ofNat m := by
  let len := barrettNormalizedLen mem0 aw0 p m
  let offset := barrettNormalizedOffset mem0 aw0 p m
  let resultMem := barrettNormalizedResultMem mem0 aw0 fp p m resultFp
  let value :=
    wideWordValueAtModulusPtr resultMem
      (barrettNormalizedResultAw mem0 aw0 fp p m resultFp)
      baseSize exponentSize fp len
  let finalMem :=
    barrettRestoreMemory
      (wideWordReturnMemory resultMem value (UInt256.ofNat resultFp) len)
      resultFp result offset len
  have hheaderReadNorm :
      (barrettNormalizedMem mem0 aw0 fp p m).readWithPadding result 32 =
        UInt256.toByteArray (UInt256.ofNat m) := by
    have hpres := barrettNormalizedMemory_read_below_padded
      (mem := mem0) (fp := fp) (p := p) (offset := offset) (len := len)
      (read := result)
      hmemSize hmemLe hgap
      (by simpa [len] using hlenPos)
      (by simpa [len, offset] using hsource)
      hresultGe96
      (by simpa [offset] using hbelowFp)
    simpa [barrettNormalizedMem, len, offset, hreadMem0] using hpres
  have hheaderReadResult :
      resultMem.readWithPadding result 32 =
        UInt256.toByteArray (UInt256.ofNat m) := by
    dsimp [resultMem]
    unfold barrettNormalizedResultMem
    rw [storeBytesLength_read_below_padded]
    · rw [setFreePtr_read_above_padded]
      · exact hheaderReadNorm
      · exact hresultMemSize
      · exact hresultGe96
    · rw [setFreePtr_size hresultMemSize]
      omega
    · exact hbelowResultFp
    · rw [setFreePtr_size hresultMemSize]
      exact hresultGap
  have hreadFinal :
      finalMem.readWithPadding result 32 = UInt256.toByteArray (UInt256.ofNat m) := by
    dsimp [finalMem, resultMem, value, len, offset]
    exact wideWordReturnThenRestore_read_below_header
      (mem := barrettNormalizedResultMem mem0 aw0 fp p m resultFp)
      (value := wideWordValueAtModulusPtr
        (barrettNormalizedResultMem mem0 aw0 fp p m resultFp)
        (barrettNormalizedResultAw mem0 aw0 fp p m resultFp)
        baseSize exponentSize fp (barrettNormalizedLen mem0 aw0 p m))
      (resultFp := resultFp) (result := result)
      (offset := barrettNormalizedOffset mem0 aw0 p m)
      (len := barrettNormalizedLen mem0 aw0 p m)
      hlenPos hlenLe32 hresultFpNat hresultAllocated hheaderReadResult
      (by omega) hbelowResultFp hoffsetGe32 hdestEnd
  have hfinalSize : finalMem.size = resultFp + 32 + len := by
    dsimp [finalMem, resultMem, value, len, offset]
    exact wideWordReturnThenRestore_size
      (mem := barrettNormalizedResultMem mem0 aw0 fp p m resultFp)
      (value := wideWordValueAtModulusPtr
        (barrettNormalizedResultMem mem0 aw0 fp p m resultFp)
        (barrettNormalizedResultAw mem0 aw0 fp p m resultFp)
        baseSize exponentSize fp (barrettNormalizedLen mem0 aw0 p m))
      (resultFp := resultFp) (result := result)
      (offset := barrettNormalizedOffset mem0 aw0 p m)
      (len := barrettNormalizedLen mem0 aw0 p m)
      hlenPos hlenLe32 hresultFpNat hresultAllocated hdestEnd
  have hresultNat : (UInt256.ofNat result).toNat = result :=
    UInt256.toNat_ofNat_of_lt hresultWord
  have hmload := mloadWordValue_of_readWithPadding
    (mem := finalMem) (aw := finalWords) (off := UInt256.ofNat result)
    (v := UInt256.ofNat m)
    (by
      rw [hresultNat, hfinalSize]
      omega)
    (by
      intro h
      change (finalWords * ⟨32⟩).toNat ≤ (UInt256.ofNat result).toNat at h
      rw [hfinalMul32, hresultNat] at h
      omega)
    (by
      rw [hresultNat]
      exact hreadFinal)
  simpa [finalMem, resultMem, value, len, offset, hresultNat] using hmload

structure WideBarrettNormalizedWordFacts (I : ExecutionEnv) : Prop where
  hnorm :
    let l := lengths I.calldata
    operandModulusPtr l.base l.exponent + 32 <
      barrettScanStop
        (wideWordResultMemory I l.base l.exponent l.modulus)
        (wideWordResultWords l.base l.exponent l.modulus)
        (operandModulusPtr l.base l.exponent) l.modulus
  hzero :
    let l := lengths I.calldata
    memoryZeroResult
      (barrettNormalizedResultMem
        (wideWordResultMemory I l.base l.exponent l.modulus)
        (wideWordResultWords l.base l.exponent l.modulus)
        (wideBarrettNormalizedFp l.base l.exponent l.modulus)
        (operandModulusPtr l.base l.exponent) l.modulus
        (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
      (barrettNormalizedResultAw
        (wideWordResultMemory I l.base l.exponent l.modulus)
        (wideWordResultWords l.base l.exponent l.modulus)
        (wideBarrettNormalizedFp l.base l.exponent l.modulus)
        (operandModulusPtr l.base l.exponent) l.modulus
        (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
      (wideBarrettNormalizedFp l.base l.exponent l.modulus + 32)
      (wideBarrettNormalizedFp l.base l.exponent l.modulus + 32 +
        wideBarrettNormalizedLenFor I l.base l.exponent l.modulus) = 0
  hone :
    let l := lengths I.calldata
    memoryOneResult
      (barrettNormalizedResultMem
        (wideWordResultMemory I l.base l.exponent l.modulus)
        (wideWordResultWords l.base l.exponent l.modulus)
        (wideBarrettNormalizedFp l.base l.exponent l.modulus)
        (operandModulusPtr l.base l.exponent) l.modulus
        (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
      (barrettNormalizedResultAw
        (wideWordResultMemory I l.base l.exponent l.modulus)
        (wideWordResultWords l.base l.exponent l.modulus)
        (wideBarrettNormalizedFp l.base l.exponent l.modulus)
        (operandModulusPtr l.base l.exponent) l.modulus
        (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
      (wideBarrettNormalizedFp l.base l.exponent l.modulus)
      (wideBarrettNormalizedLenFor I l.base l.exponent l.modulus) = 0
  hfirst :
    let l := lengths I.calldata
    wideBarrettNormalizedLenFor I l.base l.exponent l.modulus = 1 ∨
      UInt256.byteAt ⟨0⟩
        (wideLoadWord
          (barrettNormalizedResultMem
            (wideWordResultMemory I l.base l.exponent l.modulus)
            (wideWordResultWords l.base l.exponent l.modulus)
            (wideBarrettNormalizedFp l.base l.exponent l.modulus)
            (operandModulusPtr l.base l.exponent) l.modulus
            (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
          (barrettNormalizedResultAw
            (wideWordResultMemory I l.base l.exponent l.modulus)
            (wideWordResultWords l.base l.exponent l.modulus)
            (wideBarrettNormalizedFp l.base l.exponent l.modulus)
            (operandModulusPtr l.base l.exponent) l.modulus
            (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
          (UInt256.ofNat (wideBarrettNormalizedFp l.base l.exponent l.modulus + 32))) ≠ ⟨0⟩

def wideBarrettNormalizedWordCondition (I : ExecutionEnv) : Prop :=
  let l := lengths I.calldata
  0 < l.modulus ∧ l.modulus ≤ 32 ∧
  Model.bytesToNatPadded I.calldata (wideExponentOffset l.base) l.exponent ≠ 0 ∧
  1 < Model.bytesToNatPadded I.calldata 96 l.base ∧
  1 < Model.bytesToNatPadded I.calldata (wideModulusOffset l.base l.exponent) l.modulus ∧
  modulusLastByteParity
    (operandCopiedMemory I l.base l.exponent l.modulus)
    (operandModulusActiveWords l.base l.exponent l.modulus)
    l.base l.exponent l.modulus = ⟨0⟩ ∧
  WideBarrettNormalizedWordFacts I

def wideBarrettNormalizedWordAccepts (ctx : BytecodeContext) : Prop :=
  ctx.executionEnv.weiValue = ⟨0⟩ ∧
  ctx.executionEnv.calldata.size < 2 ^ 64 ∧
  validOsaka ctx.executionEnv.calldata ∧
  ¬ wordSized ctx.executionEnv.calldata ∧
  wideBarrettNormalizedWordCondition ctx.executionEnv

def wideBarrettNormalizedWordTotalGas (I : ExecutionEnv) : Nat :=
  let l := lengths I.calldata
  wideEntryGas I.calldata + wideBarrettNormalizedWordGas I l.base l.exponent l.modulus

def wideBarrettNormalizedWordEnsures (ctx : BytecodeContext)
    (result : BytecodeResult) : Prop :=
  ExactGasPost ctx (Model.output ctx.executionEnv.calldata)
    (wideBarrettNormalizedWordTotalGas ctx.executionEnv) result

theorem wideBarrettNormalizedWordFromEntryModelExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {baseSize exponentSize modulusSize : Nat}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024)
    (hmodPos : 0 < modulusSize) (hm : modulusSize ≤ 32)
    (hexp : Model.bytesToNatPadded I.calldata
      (wideExponentOffset baseSize) exponentSize ≠ 0)
    (hbase : 1 < Model.bytesToNatPadded I.calldata 96 baseSize)
    (hmod : 1 < Model.bytesToNatPadded I.calldata
      (wideModulusOffset baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (heven : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = ⟨0⟩)
    (hfacts : WideBarrettNormalizedWordFacts I)
    (hlenEq : lengths I.calldata =
      { base := baseSize, exponent := exponentSize, modulus := modulusSize })
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨62⟩
      [UInt256.ofNat exponentSize, UInt256.ofNat baseSize, UInt256.ofNat modulusSize]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes
        (Model.modPow
          (Model.bytesToNatPadded I.calldata 96 baseSize)
          (Model.bytesToNatPadded I.calldata (wideExponentOffset baseSize) exponentSize)
          (Model.bytesToNatPadded I.calldata
            (wideModulusOffset baseSize exponentSize) modulusSize))
        modulusSize)
      (C + wideBarrettNormalizedWordGas I baseSize exponentSize modulusSize) := by
  have hm1024 : modulusSize ≤ 1024 := by omega
  obtain ⟨kExp, rd89⟩ := reachWideExponentNonzero
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (by omega : 96 + baseSize + exponentSize + 32 < 2 ^ 64) hexp rd0
  obtain ⟨kBase, rd105⟩ := reachWideBaseGtOne
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (by omega : 96 + baseSize + exponentSize + 32 < 2 ^ 64) hbase rd89
  have rd1183 := prepareOperandsExact
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (tail := []) hb he hm1024 hcalldata (by simp)
    (by
      simpa [wideModulusOffset, wideExponentOffset] using rd105)
  have rd1183' : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1183⟩
      [UInt256.ofNat operandBasePtr, UInt256.ofNat (operandExponentPtr baseSize),
        UInt256.ofNat (operandModulusPtr baseSize exponentSize), UInt256.ofNat 173]
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      ByteArray.empty acc
      (kBase + 292 + baseCalldataCopySteps I baseSize +
        calldataSegmentSteps I (96 + baseSize) exponentSize +
        calldataSegmentSteps I (96 + baseSize + exponentSize) modulusSize)
      (C + 79 + cdRangeGas I (96 + baseSize) (96 + baseSize + exponentSize) +
        wideBaseGtOneGas I baseSize +
        operandSetupGas I baseSize exponentSize modulusSize) := by
    exact RDx.withStack rd1183 (by
      rw [show (⟨173⟩ : UInt256) = UInt256.ofNat 173 by native_decide])
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let resultFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let mem0 := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw0 := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
  have hnormLocal :
      p + 32 < barrettScanStop mem0 aw0 p modulusSize := by
    simpa [hlenEq, mem0, aw0, p, fp, resultFp] using hfacts.hnorm
  have hstartLeEnd : barrettScanStart p ≤ barrettScanEnd p modulusSize := by
    unfold barrettScanStart barrettScanEnd
    omega
  have hstopBounds := barrettScanStopAt_bounds mem0 aw0
    (barrettScanEnd p modulusSize) (barrettScanStart p) hstartLeEnd
  have hstopLower : barrettScanStart p ≤ barrettScanStop mem0 aw0 p modulusSize := by
    simpa [barrettScanStop] using hstopBounds.1
  have hstopUpper : barrettScanStop mem0 aw0 p modulusSize ≤ barrettScanEnd p modulusSize := by
    simpa [barrettScanStop] using hstopBounds.2
  have hdeltaLt :
      barrettScanStop mem0 aw0 p modulusSize - p - 32 < modulusSize := by
    unfold barrettScanEnd at hstopUpper
    omega
  have hnormLenPosLocal :
      0 < wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize := by
    simpa [wideBarrettNormalizedLenFor, barrettNormalizedLen, barrettNormalizedOffset,
      mem0, aw0, p] using Nat.sub_pos_of_lt hdeltaLt
  have hnormLenLe32Local :
      wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize ≤ 32 := by
    have hleMod :
        wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize ≤ modulusSize := by
      simpa [wideBarrettNormalizedLenFor, barrettNormalizedLen, barrettNormalizedOffset,
        mem0, aw0, p] using
          (Nat.sub_le modulusSize
            (barrettScanStop mem0 aw0 p modulusSize - p - 32))
    exact le_trans hleMod hm
  have hnormLenWordLocal :
      wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize < UInt256.size := by
    exact lt_of_le_of_lt hnormLenLe32Local (by decide)
  have hmemSizeLocal : 96 ≤ mem0.size := by
    rw [show mem0.size =
        operandFreePtr baseSize exponentSize modulusSize + 32 by
      exact wideWordResultMemory_size I hb he hm1024]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
      bytesAllocationSize
    omega
  have hmemLeLocal : mem0.size ≤ fp := by
    rw [show mem0.size =
        operandFreePtr baseSize exponentSize modulusSize + 32 by
      exact wideWordResultMemory_size I hb he hm1024]
    dsimp [fp, wideBarrettNormalizedFp]
    unfold bytesAllocationSize
    omega
  have hgapLocal : fp - mem0.size < USize.size := by
    rw [show mem0.size =
        operandFreePtr baseSize exponentSize modulusSize + 32 by
      exact wideWordResultMemory_size I hb he hm1024]
    dsimp [fp, wideBarrettNormalizedFp]
    exact lt_usize _ (by
      unfold bytesAllocationSize
      omega)
  have haw3Local : 3 ≤ aw0.toNat := by
    dsimp [aw0]
    rw [wideWordResultWords_toNat hb he hm1024]
    unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
    omega
  have haw64Local : ¬ (⟨64⟩ : UInt256) ≥ aw0 * ⟨32⟩ := by
    intro h
    change (aw0 * ⟨32⟩).toNat ≤ (⟨64⟩ : UInt256).toNat at h
    rw [show (⟨64⟩ : UInt256).toNat = 64 by decide] at h
    rw [show (aw0 * ⟨32⟩).toNat =
        operandFreePtr baseSize exponentSize modulusSize + bytesAllocationSize modulusSize by
      dsimp [aw0]
      exact resultActiveBytes_toNat hb he hm1024] at h
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
      bytesAllocationSize at h
    omega
  have hreadLocal : mem0.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat fp) := by
    let oldMem := operandCopiedMemory I baseSize exponentSize modulusSize
    let oldFp := operandFreePtr baseSize exponentSize modulusSize
    have holdMem96 : 96 ≤ oldMem.size := by
      have hge := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
      have hptr : 96 ≤ operandModulusPtr baseSize exponentSize + 32 := by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      exact hptr.trans hge
    have hsetSize :
        (setFreePtr oldMem (oldFp + bytesAllocationSize modulusSize)).size = oldMem.size :=
      setFreePtr_size holdMem96
    have hgapOld :
        oldFp -
          (setFreePtr oldMem (oldFp + bytesAllocationSize modulusSize)).size < USize.size := by
      rw [hsetSize]
      exact lt_usize _ (by
        unfold oldFp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
    have holdFp96 : 96 ≤ oldFp := by
      unfold oldFp operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega
    dsimp [mem0, wideWordResultMemory, oldMem, oldFp, fp, wideBarrettNormalizedFp]
    rw [storeBytesLength_read64]
    · exact setFreePtr_read64 holdMem96
    · rw [hsetSize]
      exact holdMem96
    · exact holdFp96
    · exact hgapOld
  have hallocNormLe64 :
      bytesAllocationSize (wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize) ≤
        64 := by
    unfold bytesAllocationSize
    omega
  have hfpLe : fp ≤ 2368 := by
    dsimp [fp, wideBarrettNormalizedFp]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
      bytesAllocationSize
    omega
  have hresultFpEq :
      resultFp = fp +
        bytesAllocationSize (wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize) := by
    dsimp [resultFp, fp, wideBarrettNormalizedResultFp]
  have hresultFpLe : resultFp ≤ 2432 := by
    rw [hresultFpEq]
    omega
  have hboundLocal :
      fp + bytesAllocationSize
        (wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize) < 2 ^ 64 := by
    exact lt_of_le_of_lt (by omega : fp +
      bytesAllocationSize (wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize) ≤
        2432) (by decide)
  have hfp32WordLocal : fp + 32 < UInt256.size := by
    exact lt_of_le_of_lt (by omega : fp + 32 ≤ 2400) (by decide)
  have hresultBoundLocal :
      resultFp + bytesAllocationSize
        (wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize) < 2 ^ 64 := by
    exact lt_of_le_of_lt (by omega : resultFp +
      bytesAllocationSize (wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize) ≤
        2496) (by decide)
  have hchecksBoundLocal :
      fp + 32 + wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize + 32 <
        UInt256.size := by
    exact lt_of_le_of_lt (by omega : fp + 32 +
      wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize + 32 ≤ 2464) (by decide)
  have hfpEndWordLocal :
      fp + wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize + 31 <
        UInt256.size := by
    exact lt_of_le_of_lt (by omega : fp +
      wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize + 31 ≤ 2431) (by decide)
  have hresultFpWordLocal : resultFp + 32 < UInt256.size := by
    exact lt_of_le_of_lt (by omega : resultFp + 32 ≤ 2464) (by decide)
  have hresultOffsetWordLocal :
      operandFreePtr baseSize exponentSize modulusSize +
        barrettNormalizedOffset mem0 aw0 p modulusSize < UInt256.size := by
    have hoffsetLe : barrettNormalizedOffset mem0 aw0 p modulusSize ≤ modulusSize + 31 := by
      dsimp [barrettNormalizedOffset]
      unfold barrettScanEnd at hstopUpper
      omega
    have hfreeLe : operandFreePtr baseSize exponentSize modulusSize ≤ 2304 := by
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    exact lt_of_le_of_lt (by
      calc
        operandFreePtr baseSize exponentSize modulusSize +
            barrettNormalizedOffset mem0 aw0 p modulusSize
            ≤ operandFreePtr baseSize exponentSize modulusSize + (modulusSize + 31) := by
              exact Nat.add_le_add_left hoffsetLe _
        _ ≤ 2367 := by omega) (by decide)
  let q := operandModulusWords baseSize exponentSize modulusSize + bytesAllocationWords modulusSize
  have haw0Eq : aw0 = UInt256.ofNat q := by
    dsimp [aw0, q]
    exact wideWordResultWords_eq hb he hm1024
  have hfpEq : fp = 32 * q := by
    dsimp [fp, wideBarrettNormalizedFp, q]
    rw [operandFreePtr_eq, bytesAllocationSize_eq_words]
    omega
  have hqBound : q + bytesAllocationWords n < UInt256.size := by
    dsimp [q, n]
    unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
    omega
  have hnewEq :
      newBytesWords aw0 fp n = UInt256.ofNat (q + bytesAllocationWords n) := by
    rw [haw0Eq, hfpEq]
    exact newBytesWords_aligned hqBound
  have hnewNat : (newBytesWords aw0 fp n).toNat = q + bytesAllocationWords n := by
    rw [hnewEq]
    exact UInt256.toNat_ofNat_of_lt hqBound
  have hnewActiveBytes :
      32 * (newBytesWords aw0 fp n).toNat = fp + bytesAllocationSize n := by
    rw [hnewNat, hfpEq, bytesAllocationSize_eq_words]
    omega
  have hnEq : n = barrettNormalizedLen mem0 aw0 p modulusSize := by
    rfl
  have hoffsetLeLocal : barrettNormalizedOffset mem0 aw0 p modulusSize ≤ modulusSize + 31 := by
    dsimp [barrettNormalizedOffset]
    unfold barrettScanEnd at hstopUpper
    omega
  have hoffsetLenEq :
      barrettNormalizedOffset mem0 aw0 p modulusSize + n = modulusSize + 32 := by
    rw [hnEq]
    unfold barrettNormalizedLen barrettNormalizedOffset
    omega
  have hoffsetGe32Local : 32 ≤ barrettNormalizedOffset mem0 aw0 p modulusSize := by
    dsimp [barrettNormalizedOffset]
    omega
  have hcopySourceActive :
      p + barrettNormalizedOffset mem0 aw0 p modulusSize + n ≤
        32 * (newBytesWords aw0 fp n).toNat := by
    rw [hnewActiveBytes]
    rw [show p + barrettNormalizedOffset mem0 aw0 p modulusSize + n =
        p + (modulusSize + 32) by omega]
    dsimp [fp, wideBarrettNormalizedFp, p]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hcopyDestActive :
      fp + 32 + n ≤ 32 * (newBytesWords aw0 fp n).toNat := by
    rw [hnewActiveBytes]
    unfold bytesAllocationSize
    omega
  have hcopyMaxActive :
      max (fp + 32) (p + barrettNormalizedOffset mem0 aw0 p modulusSize) + n ≤
        32 * (newBytesWords aw0 fp n).toNat := by
    rw [← Nat.add_max_add_right]
    exact max_le hcopyDestActive hcopySourceActive
  have hnormalizedAwEq :
      barrettNormalizedAw aw0 mem0 fp p modulusSize = newBytesWords aw0 fp n := by
    unfold barrettNormalizedAw barrettNormalizeCopyWords
    have hM :
        MachineState.M
            (newBytesWords aw0 fp (barrettNormalizedLen mem0 aw0 p modulusSize)).toNat
            (max (fp + 32) (p + barrettNormalizedOffset mem0 aw0 p modulusSize))
            (barrettNormalizedLen mem0 aw0 p modulusSize) =
          (newBytesWords aw0 fp (barrettNormalizedLen mem0 aw0 p modulusSize)).toNat := by
      simpa [← hnEq] using machineM_eq_of_access hcopyMaxActive
    rw [hM, u256_ofNat_toNat]
    rw [hnEq]
  have hnormalizedAwNat :
      (barrettNormalizedAw aw0 mem0 fp p modulusSize).toNat = q + bytesAllocationWords n := by
    rw [hnormalizedAwEq, hnewNat]
  have hnormalizedActiveBytes :
      32 * (barrettNormalizedAw aw0 mem0 fp p modulusSize).toNat =
        fp + bytesAllocationSize n := by
    rw [hnormalizedAwNat, hfpEq, bytesAllocationSize_eq_words]
    omega
  have hmodAccessLocal :
      (UInt256.ofNat fp).toNat + 32 ≤
        32 * (barrettNormalizedAw aw0 mem0 fp p modulusSize).toNat := by
    have hfpWord : fp < UInt256.size := by omega
    rw [UInt256.toNat_ofNat_of_lt hfpWord]
    rw [hnormalizedActiveBytes]
    unfold bytesAllocationSize
    omega
  have hresultAw3Local : 3 ≤ (barrettNormalizedAw aw0 mem0 fp p modulusSize).toNat := by
    rw [hnormalizedAwNat]
    dsimp [q]
    unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
    omega
  have hnormalizedMul32 :
      (barrettNormalizedAw aw0 mem0 fp p modulusSize * ⟨32⟩).toNat =
        32 * (barrettNormalizedAw aw0 mem0 fp p modulusSize).toNat := by
    rw [umul_toNat]
    · rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
      omega
    · rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
      rw [hnormalizedAwNat]
      dsimp [q]
      have hlt64 :
          32 *
              (operandModulusWords baseSize exponentSize modulusSize +
                bytesAllocationWords modulusSize + bytesAllocationWords n) < 2 ^ 64 := by
        calc
          32 *
              (operandModulusWords baseSize exponentSize modulusSize +
                bytesAllocationWords modulusSize + bytesAllocationWords n)
              = 32 * (q + bytesAllocationWords n) := by
                  dsimp [q]
          _ = 32 * (newBytesWords aw0 fp n).toNat := by rw [hnewNat]
          _ = fp + bytesAllocationSize n := hnewActiveBytes
          _ < 2 ^ 64 := hboundLocal
      have h64_256 : 2 ^ 64 < UInt256.size := by
        norm_num [UInt256.size]
      omega
  have hresultAw64Local :
      ¬ (⟨64⟩ : UInt256) ≥
        barrettNormalizedAw aw0 mem0 fp p modulusSize * ⟨32⟩ := by
    intro h
    change (barrettNormalizedAw aw0 mem0 fp p modulusSize * ⟨32⟩).toNat ≤
      (⟨64⟩ : UInt256).toNat at h
    rw [show (⟨64⟩ : UInt256).toNat = 64 by decide] at h
    rw [hnormalizedMul32, hnormalizedActiveBytes] at h
    dsimp [fp, wideBarrettNormalizedFp] at h
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
      bytesAllocationSize at h
    omega
  have hnormalizeSourceConcrete :
      p + barrettNormalizedOffset mem0 aw0 p modulusSize + n ≤ fp + 32 := by
    rw [show p + barrettNormalizedOffset mem0 aw0 p modulusSize + n =
        p + (modulusSize + 32) by omega]
    dsimp [fp, wideBarrettNormalizedFp, p]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hnormMemSizeEq :
      (barrettNormalizedMem mem0 aw0 fp p modulusSize).size = fp + 32 + n := by
    unfold barrettNormalizedMem
    have h := barrettNormalizedMemory_size
      (mem := mem0) (fp := fp) (p := p)
      (offset := barrettNormalizedOffset mem0 aw0 p modulusSize)
      (len := barrettNormalizedLen mem0 aw0 p modulusSize)
      hmemSizeLocal hmemLeLocal hgapLocal
      (by simpa [← hnEq] using hnormLenPosLocal)
      (by simpa [← hnEq] using hnormalizeSourceConcrete)
    simpa [← hnEq] using h
  have hlengthLocal :
      wideLoadWord
        (barrettNormalizedMem mem0 aw0 fp p modulusSize)
        (barrettNormalizedAw aw0 mem0 fp p modulusSize)
        (UInt256.ofNat fp) = UInt256.ofNat n := by
    apply wideLoadWord_eq_of_read
    · rw [UInt256.toNat_ofNat_of_lt (by omega : fp < UInt256.size), hnormMemSizeEq]
      omega
    · intro h
      change
        (barrettNormalizedAw aw0 mem0 fp p modulusSize * ⟨32⟩).toNat ≤
          (UInt256.ofNat fp).toNat at h
      rw [hnormalizedMul32] at h
      rw [UInt256.toNat_ofNat_of_lt (by omega : fp < UInt256.size)] at h
      omega
    · have hread := barrettNormalizedMemory_read_length
        (mem := mem0) (fp := fp) (p := p)
        (offset := barrettNormalizedOffset mem0 aw0 p modulusSize)
        (len := barrettNormalizedLen mem0 aw0 p modulusSize)
        hmemSizeLocal hmemLeLocal hgapLocal
        (by simpa [← hnEq] using hnormLenPosLocal)
        (by simpa [← hnEq] using hnormalizeSourceConcrete)
      simpa [barrettNormalizedMem, ← hnEq,
        UInt256.toNat_ofNat_of_lt (by omega : fp < UInt256.size)] using hread
  have hresultMemSizeLocal :
      96 ≤ (barrettNormalizedMem mem0 aw0 fp p modulusSize).size := by
    rw [hnormMemSizeEq]
    omega
  have hresultMemLeLocal :
      (barrettNormalizedMem mem0 aw0 fp p modulusSize).size ≤ resultFp := by
    rw [hnormMemSizeEq, hresultFpEq]
    unfold bytesAllocationSize
    omega
  have hresultGapLocal :
      resultFp - (barrettNormalizedMem mem0 aw0 fp p modulusSize).size < USize.size := by
    rw [hnormMemSizeEq, hresultFpEq]
    exact lt_usize _ (by
      unfold bytesAllocationSize
      omega)
  have hresultReadLocal :
      (barrettNormalizedMem mem0 aw0 fp p modulusSize).readWithPadding 64 32 =
        UInt256.toByteArray (UInt256.ofNat resultFp) := by
    have hread := barrettNormalizedMemory_read64
      (mem := mem0) (fp := fp) (p := p)
      (offset := barrettNormalizedOffset mem0 aw0 p modulusSize)
      (len := barrettNormalizedLen mem0 aw0 p modulusSize)
      hmemSizeLocal
      (by dsimp [fp, wideBarrettNormalizedFp]
          unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
            bytesAllocationSize
          omega)
      hmemLeLocal hgapLocal
      (by simpa [← hnEq] using hnormLenPosLocal)
      (by simpa [← hnEq] using hnormalizeSourceConcrete)
    simpa [barrettNormalizedMem, ← hnEq, hresultFpEq] using hread
  let qn := q + bytesAllocationWords n
  have hnormalizedAwOfNat :
      barrettNormalizedAw aw0 mem0 fp p modulusSize = UInt256.ofNat qn := by
    dsimp [qn]
    rw [hnormalizedAwEq, hnewEq]
  have hresultFpWords : resultFp = 32 * qn := by
    dsimp [qn]
    rw [hresultFpEq, ← hnewActiveBytes, hnewNat]
  have hqnBound : qn + bytesAllocationWords n < UInt256.size := by
    dsimp [qn, q]
    unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
    omega
  have hresultAwEq :
      barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp =
        UInt256.ofNat (qn + bytesAllocationWords n) := by
    unfold barrettNormalizedResultAw
    rw [hnormalizedAwOfNat, hresultFpWords]
    exact newBytesWords_aligned hqnBound
  have hresultAwNat :
      (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat =
        qn + bytesAllocationWords n := by
    rw [hresultAwEq]
    exact UInt256.toNat_ofNat_of_lt hqnBound
  have hresultActiveBytes :
      32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat =
        resultFp + bytesAllocationSize n := by
    rw [hresultAwNat, hresultFpWords, bytesAllocationSize_eq_words]
    omega
  have hchecksActiveLocal :
      fp + 32 + n + 32 ≤
        32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat := by
    rw [hresultActiveBytes, hresultFpEq]
    unfold bytesAllocationSize
    omega
  have hchecksAwLocal :
      32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat <
        UInt256.size := by
    have hlt64 : 32 *
        (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat < 2 ^ 64 := by
      rw [hresultActiveBytes]
      exact hresultBoundLocal
    exact lt_trans hlt64 (by norm_num [UInt256.size])
  have hresultAwMul32 :
      (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp * ⟨32⟩).toNat =
        32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat := by
    rw [umul_toNat]
    · rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
      omega
    · rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
      simpa [Nat.mul_comm] using hchecksAwLocal
  have hresultAllocatedMemSizeEq :
      (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp).size =
        resultFp + 32 := by
    unfold barrettNormalizedResultMem
    exact storeBytesLength_size
      (by rw [setFreePtr_size hresultMemSizeLocal]; exact hresultMemLeLocal)
      (by rw [setFreePtr_size hresultMemSizeLocal]; exact hresultGapLocal)
  have hresultReadLenLocal :
      (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp).readWithPadding
          fp 32 =
        UInt256.toByteArray (UInt256.ofNat n) := by
    have hnormRead := barrettNormalizedMemory_read_length
      (mem := mem0) (fp := fp) (p := p)
      (offset := barrettNormalizedOffset mem0 aw0 p modulusSize)
      (len := barrettNormalizedLen mem0 aw0 p modulusSize)
      hmemSizeLocal hmemLeLocal hgapLocal
      (by simpa [← hnEq] using hnormLenPosLocal)
      (by simpa [← hnEq] using hnormalizeSourceConcrete)
    have hnormRead' :
        (barrettNormalizedMem mem0 aw0 fp p modulusSize).readWithPadding fp 32 =
          UInt256.toByteArray (UInt256.ofNat n) := by
      simpa [barrettNormalizedMem, ← hnEq] using hnormRead
    unfold barrettNormalizedResultMem
    rw [storeBytesLength_read_below_padded]
    · rw [setFreePtr_read_above_padded]
      · exact hnormRead'
      · exact hresultMemSizeLocal
      · dsimp [fp, wideBarrettNormalizedFp]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega
    · rw [setFreePtr_size hresultMemSizeLocal]
      omega
    · rw [hresultFpEq]
      unfold bytesAllocationSize
      omega
    · rw [setFreePtr_size hresultMemSizeLocal]
      exact hresultGapLocal
  have hlengthAfterResultLocal :
      wideLoadWord
        (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
        (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp)
        (UInt256.ofNat fp) = UInt256.ofNat n := by
    apply wideLoadWord_eq_of_read
    · rw [UInt256.toNat_ofNat_of_lt (by omega : fp < UInt256.size),
        hresultAllocatedMemSizeEq]
      omega
    · intro h
      change
        (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp * ⟨32⟩).toNat ≤
          (UInt256.ofNat fp).toNat at h
      rw [hresultAwMul32, UInt256.toNat_ofNat_of_lt (by omega : fp < UInt256.size)] at h
      rw [hresultActiveBytes, hresultFpEq] at h
      unfold bytesAllocationSize at h
      omega
    · simpa [UInt256.toNat_ofNat_of_lt (by omega : fp < UInt256.size)]
        using hresultReadLenLocal
  have hfpActiveLocal :
      fp + 64 ≤
        32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat := by
    rw [hresultActiveBytes, hresultFpEq]
    unfold bytesAllocationSize
    omega
  have hresultPayloadActiveLocal :
      resultFp + 32 + n ≤
        32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat := by
    rw [hresultActiveBytes]
    unfold bytesAllocationSize
    omega
  have hbaseActiveLocal :
      operandBasePtr + 32 + baseSize ≤
        32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat := by
    rw [hresultActiveBytes, hresultFpEq]
    dsimp [fp, wideBarrettNormalizedFp]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
      bytesAllocationSize
    omega
  have hbaseDataActiveLocal :
      operandBasePtr + 64 ≤
        32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat := by
    rw [hresultActiveBytes, hresultFpEq]
    dsimp [fp, wideBarrettNormalizedFp]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
      bytesAllocationSize
    omega
  have hexponentActiveLocal :
      wideExponentDataPtr baseSize + exponentSize + 32 ≤
        32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat := by
    have htoFree :
        wideExponentDataPtr baseSize + exponentSize + 32 ≤
          operandFreePtr baseSize exponentSize modulusSize := by
      have hexpCover : exponentSize + 32 ≤ bytesAllocationSize exponentSize := by
        unfold bytesAllocationSize
        omega
      have hmodCover : 32 ≤ bytesAllocationSize modulusSize := by
        unfold bytesAllocationSize
        omega
      unfold operandFreePtr operandModulusPtr wideExponentDataPtr
      omega
    have hfreeActive :
        operandFreePtr baseSize exponentSize modulusSize ≤
          32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat := by
      rw [hresultActiveBytes, hresultFpEq]
      dsimp [fp, wideBarrettNormalizedFp]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega
    exact htoFree.trans hfreeActive
  have hbaseReadMem0 :
      mem0.readWithPadding operandBasePtr 32 =
        UInt256.toByteArray (UInt256.ofNat baseSize) := by
    rw [show mem0.readWithPadding operandBasePtr 32 =
        (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          operandBasePtr 32 from by
          dsimp [mem0]
          exact wideWordResultMemory_readOperand I hb he hm1024
            (by unfold operandBasePtr; omega)
            (by
              unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
                bytesAllocationSize
              omega)]
    exact operandCopiedMemory_readBaseLength I baseSize exponentSize modulusSize hb he
  have hexponentReadMem0 :
      mem0.readWithPadding (operandExponentPtr baseSize) 32 =
        UInt256.toByteArray (UInt256.ofNat exponentSize) := by
    rw [show mem0.readWithPadding (operandExponentPtr baseSize) 32 =
        (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          (operandExponentPtr baseSize) 32 from by
          dsimp [mem0]
          exact wideWordResultMemory_readOperand I hb he hm1024
            (by
              unfold operandExponentPtr operandBasePtr bytesAllocationSize
              omega)
            (by
              unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
                bytesAllocationSize
              omega)]
    exact operandCopiedMemory_readExponentLength I baseSize exponentSize modulusSize hb he
  have hbaseReadNorm :
      (barrettNormalizedMem mem0 aw0 fp p modulusSize).readWithPadding operandBasePtr 32 =
        UInt256.toByteArray (UInt256.ofNat baseSize) := by
    have hpres := barrettNormalizedMemory_read_below_padded
      (mem := mem0) (fp := fp) (p := p)
      (offset := barrettNormalizedOffset mem0 aw0 p modulusSize)
      (len := barrettNormalizedLen mem0 aw0 p modulusSize)
      (read := operandBasePtr)
      hmemSizeLocal hmemLeLocal hgapLocal
      (by simpa [← hnEq] using hnormLenPosLocal)
      (by simpa [← hnEq] using hnormalizeSourceConcrete)
      (by unfold operandBasePtr; omega)
      (by
        dsimp [fp, wideBarrettNormalizedFp]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
    simpa [barrettNormalizedMem, ← hnEq, hbaseReadMem0] using hpres
  have hexponentReadNorm :
      (barrettNormalizedMem mem0 aw0 fp p modulusSize).readWithPadding
          (operandExponentPtr baseSize) 32 =
        UInt256.toByteArray (UInt256.ofNat exponentSize) := by
    have hpres := barrettNormalizedMemory_read_below_padded
      (mem := mem0) (fp := fp) (p := p)
      (offset := barrettNormalizedOffset mem0 aw0 p modulusSize)
      (len := barrettNormalizedLen mem0 aw0 p modulusSize)
      (read := operandExponentPtr baseSize)
      hmemSizeLocal hmemLeLocal hgapLocal
      (by simpa [← hnEq] using hnormLenPosLocal)
      (by simpa [← hnEq] using hnormalizeSourceConcrete)
      (by
        unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by
        dsimp [fp, wideBarrettNormalizedFp]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
    simpa [barrettNormalizedMem, ← hnEq, hexponentReadMem0] using hpres
  have hbaseReadResult :
      (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp).readWithPadding
          operandBasePtr 32 =
        UInt256.toByteArray (UInt256.ofNat baseSize) := by
    unfold barrettNormalizedResultMem
    rw [storeBytesLength_read_below_padded]
    · rw [setFreePtr_read_above_padded]
      · exact hbaseReadNorm
      · exact hresultMemSizeLocal
      · unfold operandBasePtr
        omega
    · rw [setFreePtr_size hresultMemSizeLocal]
      omega
    · rw [hresultFpEq]
      dsimp [fp, wideBarrettNormalizedFp]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega
    · rw [setFreePtr_size hresultMemSizeLocal]
      exact hresultGapLocal
  have hexponentReadResult :
      (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp).readWithPadding
          (operandExponentPtr baseSize) 32 =
        UInt256.toByteArray (UInt256.ofNat exponentSize) := by
    unfold barrettNormalizedResultMem
    rw [storeBytesLength_read_below_padded]
    · rw [setFreePtr_read_above_padded]
      · exact hexponentReadNorm
      · exact hresultMemSizeLocal
      · unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega
    · rw [setFreePtr_size hresultMemSizeLocal]
      omega
    · rw [hresultFpEq]
      dsimp [fp, wideBarrettNormalizedFp]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega
    · rw [setFreePtr_size hresultMemSizeLocal]
      exact hresultGapLocal
  have hbaseLengthLocal :
      wideLoadWord
        (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
        (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp)
        (UInt256.ofNat operandBasePtr) = UInt256.ofNat baseSize := by
    have hbasePtrWord : operandBasePtr < UInt256.size := by
      unfold operandBasePtr
      decide
    apply wideLoadWord_eq_of_read
    · rw [UInt256.toNat_ofNat_of_lt hbasePtrWord,
        hresultAllocatedMemSizeEq]
      unfold operandBasePtr
      omega
    · intro h
      change
        (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp * ⟨32⟩).toNat ≤
          (UInt256.ofNat operandBasePtr).toNat at h
      rw [hresultAwMul32, UInt256.toNat_ofNat_of_lt hbasePtrWord] at h
      have hactive :
          operandBasePtr + 32 ≤
            32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat := by
        omega
      omega
    · simpa [UInt256.toNat_ofNat_of_lt hbasePtrWord]
        using hbaseReadResult
  have hexponentLengthLocal :
      wideLoadWord
        (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
        (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp)
        (UInt256.ofNat (operandExponentPtr baseSize)) =
          UInt256.ofNat exponentSize := by
    have hptrWord : operandExponentPtr baseSize < UInt256.size := by
      exact lt_of_le_of_lt (by
        unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega) (by decide : 1184 < UInt256.size)
    apply wideLoadWord_eq_of_read
    · rw [UInt256.toNat_ofNat_of_lt hptrWord, hresultAllocatedMemSizeEq]
      have hptrBelowFree :
          operandExponentPtr baseSize + 32 ≤
            operandFreePtr baseSize exponentSize modulusSize := by
        unfold operandFreePtr operandModulusPtr
        have hexpAlloc : 32 ≤ bytesAllocationSize exponentSize := by
          unfold bytesAllocationSize
          omega
        have hmodAlloc : 32 ≤ bytesAllocationSize modulusSize := by
          unfold bytesAllocationSize
          omega
        omega
      have hfreeLeResult : operandFreePtr baseSize exponentSize modulusSize ≤ resultFp := by
        rw [hresultFpEq]
        dsimp [fp, wideBarrettNormalizedFp]
        unfold bytesAllocationSize
        omega
      omega
    · intro h
      change
        (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp * ⟨32⟩).toNat ≤
          (UInt256.ofNat (operandExponentPtr baseSize)).toNat at h
      rw [hresultAwMul32, UInt256.toNat_ofNat_of_lt hptrWord] at h
      have hactive :
          operandExponentPtr baseSize + 32 ≤
            32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat := by
        exact Nat.le_trans (by
          unfold wideExponentDataPtr
          omega) hexponentActiveLocal
      omega
    · simpa [UInt256.toNat_ofNat_of_lt hptrWord]
        using hexponentReadResult
  have hnormalizedModulusWordLocal :
      (wideWordModulusAtPtr
        (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
        (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp)
        fp n).toNat =
        Model.bytesToNatPadded I.calldata
          (wideModulusOffset baseSize exponentSize) modulusSize := by
    have hlen64 : n < 2 ^ 64 := by omega
    have haddr64 : fp + 32 < 2 ^ 64 := by
      dsimp [fp, wideBarrettNormalizedFp]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega
    have hmodPtrFrontier :
        ¬ UInt256.ofNat (fp + 32) ≥
          barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp * ⟨32⟩ := by
      intro h
      change
        (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp * ⟨32⟩).toNat ≤
          (UInt256.ofNat (fp + 32)).toNat at h
      rw [hresultAwMul32, UInt256.toNat_ofNat_of_lt hfp32WordLocal] at h
      rw [hresultActiveBytes, hresultFpEq] at h
      unfold bytesAllocationSize at h
      omega
    have hdecoded :
        (wideWordModulusAtPtr
          (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
          (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp)
          fp n).toNat =
          Model.bytesToNatPadded
            (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
            (fp + 32) n := by
      exact wideWordModulusAtPtr_toNat_eq_model_bytes
        (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
        (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp)
        fp n hnormLenLe32Local hfp32WordLocal haddr64 hmodPtrFrontier
    have hresultPayloadRead :
        (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp).readWithPadding
            (fp + 32) n =
          (barrettNormalizedMem mem0 aw0 fp p modulusSize).readWithPadding
            (fp + 32) n := by
      have hpres := barrettNormalizedResultMem_read_payload
        (mem := mem0) (aw := aw0) (fp := fp) (p := p) (m := modulusSize)
        (resultFp := resultFp)
        hresultMemSizeLocal hresultGapLocal
        (by omega : 96 ≤ fp + 32)
        (by simpa [← hnEq] using hnormLenPosLocal)
        hlen64
        (by rw [hnormMemSizeEq]; omega)
        (by rw [hresultFpEq]; unfold bytesAllocationSize; omega)
      simpa [← hnEq] using hpres
    have hsourceInMem0 :
        p + barrettNormalizedOffset mem0 aw0 p modulusSize + n ≤ mem0.size := by
      rw [show mem0.size =
          operandFreePtr baseSize exponentSize modulusSize + 32 by
        exact wideWordResultMemory_size I hb he hm1024]
      rw [show p + barrettNormalizedOffset mem0 aw0 p modulusSize + n =
          p + (modulusSize + 32) by omega]
      dsimp [p]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega
    have hnormalizeSourceBelowFp :
        p + barrettNormalizedOffset mem0 aw0 p modulusSize + n ≤ fp := by
      rw [show p + barrettNormalizedOffset mem0 aw0 p modulusSize + n =
          p + (modulusSize + 32) by omega]
      dsimp [fp, wideBarrettNormalizedFp, p]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega
    have hnormalizedPayloadRead :
        (barrettNormalizedMem mem0 aw0 fp p modulusSize).readWithPadding
            (fp + 32) n =
          mem0.readWithPadding
            (p + barrettNormalizedOffset mem0 aw0 p modulusSize) n := by
      let mem1 :=
        storeBytesLength (setFreePtr mem0 (fp + bytesAllocationSize n)) fp n
      have hpayload := barrettNormalizedMemory_read_payload
        (mem := mem0) (fp := fp) (p := p)
        (offset := barrettNormalizedOffset mem0 aw0 p modulusSize)
        (len := barrettNormalizedLen mem0 aw0 p modulusSize)
        hmemSizeLocal hmemLeLocal hgapLocal
        (by simpa [← hnEq] using hnormLenPosLocal)
        (by simpa [← hnEq] using hlen64)
        (by simpa [← hnEq] using hnormalizeSourceConcrete)
      have hmem1Read :
          mem1.readWithPadding
              (p + barrettNormalizedOffset mem0 aw0 p modulusSize) n =
            mem0.readWithPadding
              (p + barrettNormalizedOffset mem0 aw0 p modulusSize) n := by
        have hfree :
            (setFreePtr mem0 (fp + bytesAllocationSize n)).readWithPadding
                (p + barrettNormalizedOffset mem0 aw0 p modulusSize) n =
              mem0.readWithPadding
                (p + barrettNormalizedOffset mem0 aw0 p modulusSize) n := by
          exact setFreePtr_read_above_len hmemSizeLocal
            (by
              dsimp [p]
              unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
              omega)
            hsourceInMem0
            (by simpa [← hnEq] using hnormLenPosLocal)
            hlen64
        have hstore :
            mem1.readWithPadding
                (p + barrettNormalizedOffset mem0 aw0 p modulusSize) n =
              (setFreePtr mem0 (fp + bytesAllocationSize n)).readWithPadding
                (p + barrettNormalizedOffset mem0 aw0 p modulusSize) n := by
          dsimp [mem1]
          exact storeBytesLength_read_below_len
            (mem := setFreePtr mem0 (fp + bytesAllocationSize n)) (fp := fp)
            (n := n)
            (read := p + barrettNormalizedOffset mem0 aw0 p modulusSize)
            (len := n)
            (by rw [setFreePtr_size hmemSizeLocal]; exact hsourceInMem0)
            hnormalizeSourceBelowFp
            (by simpa [← hnEq] using hnormLenPosLocal)
            hlen64
            (by rw [setFreePtr_size hmemSizeLocal]; exact hgapLocal)
        exact hstore.trans hfree
      have hmem1Extract :
          mem1.extract
              (p + barrettNormalizedOffset mem0 aw0 p modulusSize)
              (p + barrettNormalizedOffset mem0 aw0 p modulusSize + n) =
            mem1.readWithPadding
              (p + barrettNormalizedOffset mem0 aw0 p modulusSize) n := by
        apply Eq.symm
        apply readWithPadding_eq_extract'
        · simpa [← hnEq] using hnormLenPosLocal
        · exact hlen64
        · dsimp [mem1]
          rw [storeBytesLength_size]
          · exact hnormalizeSourceConcrete
          · rw [setFreePtr_size hmemSizeLocal]
            exact hmemLeLocal
          · rw [setFreePtr_size hmemSizeLocal]
            exact hgapLocal
      simpa [barrettNormalizedMem, mem1, ← hnEq] using
        hpayload.trans (hmem1Extract.trans hmem1Read)
    have hnormalizedBytes :
        Model.bytesToNatPadded
            (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
            (fp + 32) n =
          Model.bytesToNatPadded mem0
            (p + barrettNormalizedOffset mem0 aw0 p modulusSize) n := by
      have hsourceAddr64 :
          p + barrettNormalizedOffset mem0 aw0 p modulusSize < 2 ^ 64 := by
        have hltFp :
            p + barrettNormalizedOffset mem0 aw0 p modulusSize < fp := by
          exact Nat.lt_of_lt_of_le
            (Nat.lt_add_of_pos_right hnormLenPosLocal)
            hnormalizeSourceBelowFp
        exact Nat.lt_of_lt_of_le hltFp
          (Nat.le_trans hfpLe (by decide : 2368 ≤ 2 ^ 64))
      exact model_bytesToNatPadded_eq_of_readWithPadding
        haddr64
        hsourceAddr64
        hlen64
        (hresultPayloadRead.trans hnormalizedPayloadRead)
    let kprefix := barrettNormalizedOffset mem0 aw0 p modulusSize - 32
    have hkprefixLen : kprefix + n = modulusSize := by
      dsimp [kprefix]
      omega
    have hprefixZero :
        Model.bytesToNatPadded mem0 (p + 32) kprefix = 0 := by
      apply model_bytesToNatPadded_eq_zero_of_bytes
      intro i hi
      have hscanZero :
          barrettScanByteAt mem0 aw0 (p + 32 + i) = ⟨0⟩ := by
        have hbefore :
            p + 32 + i < barrettScanStop mem0 aw0 p modulusSize := by
          dsimp [kprefix, barrettNormalizedOffset] at hi
          omega
        simpa [barrettScanStop, barrettScanStart] using
          barrettScanStopAt_zero_before mem0 aw0
            (barrettScanEnd p modulusSize) (barrettScanStart p)
            (p + 32 + i)
            (by simp [barrettScanStart])
            (by simpa [barrettScanStop, barrettScanStart] using hbefore)
      have hbyteModel :
          (barrettScanByteAt mem0 aw0 (p + 32 + i)).toNat =
            Model.bytesToNatPadded mem0 (p + 32 + i) 1 := by
        have haddrLtFp : p + 32 + i < fp := by
          have haddrLtSource :
              p + 32 + i <
                p + barrettNormalizedOffset mem0 aw0 p modulusSize := by
            dsimp [kprefix] at hi
            omega
          exact Nat.lt_of_lt_of_le haddrLtSource
            (Nat.le_trans (Nat.le_add_right _ _) hnormalizeSourceBelowFp)
        have haddrLtWord : p + 32 + i < UInt256.size := by
          exact Nat.lt_of_lt_of_le haddrLtFp
            (Nat.le_trans hfpLe (by decide : 2368 ≤ UInt256.size))
        apply barrettScanByteAt_toNat_eq_model
        · exact haddrLtWord
        · exact Nat.lt_of_lt_of_le haddrLtFp
            (Nat.le_trans hfpLe (by decide : 2368 ≤ 2 ^ 64))
        · intro hfrontier
          change (aw0 * ⟨32⟩).toNat ≤
              (UInt256.ofNat (p + 32 + i)).toNat at hfrontier
          rw [show (aw0 * ⟨32⟩).toNat =
              operandFreePtr baseSize exponentSize modulusSize +
                bytesAllocationSize modulusSize by
            dsimp [aw0]
            exact resultActiveBytes_toNat hb he hm1024] at hfrontier
          rw [UInt256.toNat_ofNat_of_lt haddrLtWord] at hfrontier
          have haddrBeforeFrontier :
              p + 32 + i <
                operandFreePtr baseSize exponentSize modulusSize +
                  bytesAllocationSize modulusSize := by
            have haddrLeStop :
                p + 32 + i < barrettScanStop mem0 aw0 p modulusSize := by
              dsimp [kprefix, barrettNormalizedOffset] at hi
              omega
            have hstopLeEnd :
                barrettScanStop mem0 aw0 p modulusSize ≤ p + modulusSize + 31 := by
              simpa [barrettScanEnd] using hstopUpper
            have hword : 1 ≤ (modulusSize + 31) / 32 := by omega
            dsimp [p]
            unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
              bytesAllocationSize
            omega
          omega
      have hzNat : (barrettScanByteAt mem0 aw0 (p + 32 + i)).toNat = 0 := by
        rw [hscanZero]
        rfl
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hbyteModel.symm.trans hzNat
    have hsuffixOriginal :
        Model.bytesToNatPadded mem0
            (p + barrettNormalizedOffset mem0 aw0 p modulusSize) n =
          Model.bytesToNatPadded mem0 (p + 32) modulusSize := by
      have hsplit := model_bytesToNatPadded_split mem0 (p + 32) kprefix n
      rw [show kprefix + n = modulusSize by exact hkprefixLen] at hsplit
      rw [hsplit, hprefixZero]
      simp [kprefix, Nat.add_assoc]
      congr 1
      omega
    have horiginalModulus :=
      wideWordResultModulus_toNat_eq_model I baseSize exponentSize modulusSize
        hb he hmodPos (by omega)
    calc
      (wideWordModulusAtPtr
          (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
          (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp)
          fp n).toNat
          = Model.bytesToNatPadded
              (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
              (fp + 32) n := hdecoded
      _ = Model.bytesToNatPadded mem0
            (p + barrettNormalizedOffset mem0 aw0 p modulusSize) n := hnormalizedBytes
      _ = Model.bytesToNatPadded mem0 (p + 32) modulusSize := hsuffixOriginal
      _ = Model.bytesToNatPadded I.calldata
            (wideModulusOffset baseSize exponentSize) modulusSize := by
          simpa [mem0, p, wideModulusOffset] using horiginalModulus
  have hbaseChunkLocal : ∀ s, s + 32 ≤ baseSize →
      (wideLoadWord
        (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
        (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp)
        (UInt256.ofNat (operandBasePtr + 32 + s))).toNat =
        Model.bytesToNatPadded I.calldata (96 + s) 32 := by
    intro s hs
    let resultMem := barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp
    let resultAw := barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp
    let addr := operandBasePtr + 32 + s
    have haddr256 : addr < UInt256.size := by
      dsimp [addr]
      unfold operandBasePtr
      exact lt_of_le_of_lt (by omega) (by decide : 1184 < UInt256.size)
    have haddr64 : addr < 2 ^ 64 := by
      dsimp [addr]
      unfold operandBasePtr
      omega
    have hfrontier : ¬ UInt256.ofNat addr ≥ resultAw * ⟨32⟩ := by
      intro h
      change (resultAw * ⟨32⟩).toNat ≤ (UInt256.ofNat addr).toNat at h
      rw [show (resultAw * ⟨32⟩).toNat =
          32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat by
            dsimp [resultAw]; exact hresultAwMul32,
        UInt256.toNat_ofNat_of_lt haddr256] at h
      have hactive :
          addr + 32 ≤
            32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat := by
        dsimp [addr]
        exact Nat.le_trans (by omega) hbaseActiveLocal
      omega
    have hword :
        (wideLoadWord
          (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
          (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp)
          (UInt256.ofNat addr)).toNat =
          Model.bytesToNatPadded
            (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp) addr 32 := by
      exact wideLoadWord_toNat_eq_model_bytes haddr256 haddr64 hfrontier
    have hreadResultMem :
        (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp).readWithPadding addr 32 =
          mem0.readWithPadding addr 32 := by
      exact barrettNormalizedResultMem_read_original_len
        hmemSizeLocal hmemLeLocal hgapLocal
        (by simpa [← hnEq] using hnormLenPosLocal)
        (by simpa [← hnEq] using hnormalizeSourceConcrete)
        hresultMemSizeLocal hresultGapLocal
        (by decide) (by decide)
        (by dsimp [addr]; unfold operandBasePtr; omega)
        (by
          rw [show mem0.size =
              operandFreePtr baseSize exponentSize modulusSize + 32 by
                exact wideWordResultMemory_size I hb he hm1024]
          dsimp [addr]
          unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
            bytesAllocationSize
          omega)
        (by
          dsimp [addr, fp, wideBarrettNormalizedFp]
          unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
            bytesAllocationSize
          omega)
        (by
          rw [hresultFpEq]
          dsimp [addr, fp, wideBarrettNormalizedFp]
          unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
            bytesAllocationSize
          omega)
    have hreadMem0 :
        mem0.readWithPadding addr 32 =
          (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding addr 32 := by
      dsimp [mem0]
      exact wideWordResultMemory_readOperandLen I hb he hm1024
        (by change 96 ≤ operandBasePtr + 32 + s; unfold operandBasePtr; omega)
        (by decide) (by decide)
        (by
          have hge := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
          exact Nat.le_trans (by
            change operandBasePtr + 32 + s + 32 ≤
              operandModulusPtr baseSize exponentSize + 32
            unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
            omega) hge)
        (by
          dsimp [addr]
          unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
            bytesAllocationSize
          omega)
    have hcalldataRead :
        (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding addr 32 =
          I.calldata.readWithPadding (96 + s) 32 := by
      have hwindow := operandCopiedBaseWindow I baseSize exponentSize modulusSize s 32
        hb he hs
      have hmodelRead :
          Model.readPadded I.calldata (96 + s) 32 =
            I.calldata.readWithPadding (96 + s) 32 := by
        exact (readWithPadding_eq_model_readPadded I.calldata (96 + s) 32
          (by omega) (by decide)).symm
      exact hwindow.trans hmodelRead
    have hmodel :
        Model.bytesToNatPadded
            (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp) addr 32 =
          Model.bytesToNatPadded I.calldata (96 + s) 32 := by
      exact model_bytesToNatPadded_eq_of_readWithPadding
        haddr64 (by omega) (by decide)
        (hreadResultMem.trans (hreadMem0.trans hcalldataRead))
    simpa [addr] using hword.trans hmodel
  have hbaseFirstLocal :
      baseSize % 32 ≠ 0 →
        (UInt256.shiftRight
          (wideBaseFirstWordAt
            (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
            (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp))
          (UInt256.shiftLeft (UInt256.sub ⟨32⟩ (wideBaseRemainder baseSize)) ⟨3⟩)).toNat =
          Model.bytesToNatPadded I.calldata 96 (baseSize % 32) := by
    intro hrem
    let resultMem := barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp
    let resultAw := barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp
    let rem := baseSize % 32
    let addr := operandBasePtr + 32
    have hremPos : 0 < rem := by dsimp [rem]; omega
    have hremLe : rem ≤ baseSize := by
      dsimp [rem]
      exact le_trans (Nat.mod_le _ _) (by omega)
    have haddr256 : addr < UInt256.size := by
      dsimp [addr]
      unfold operandBasePtr
      decide
    have haddr64 : addr < 2 ^ 64 := by
      dsimp [addr]
      unfold operandBasePtr
      decide
    have hfrontier : ¬ UInt256.ofNat addr ≥ resultAw * ⟨32⟩ := by
      intro h
      change (resultAw * ⟨32⟩).toNat ≤ (UInt256.ofNat addr).toNat at h
      rw [show (resultAw * ⟨32⟩).toNat =
          32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat by
            dsimp [resultAw]; exact hresultAwMul32,
        UInt256.toNat_ofNat_of_lt haddr256] at h
      have hactive :
          addr + 32 ≤
            32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat := by
        dsimp [addr]
        unfold operandBasePtr
        exact hbaseDataActiveLocal
      omega
    have hload :
        wideBaseFirstWordAt resultMem resultAw =
          uInt256OfByteArray (resultMem.readBytes addr 32) := by
      unfold wideBaseFirstWordAt wideBaseDataPtr
      rw [show UInt256.ofNat operandBasePtr + ⟨32⟩ = UInt256.ofNat addr by
        dsimp [addr]
        change UInt256.ofNat operandBasePtr + UInt256.ofNat 32 = _
        exact ofNat_add_bounded haddr256]
      rw [wideLoadWord_eq_decode_bounded hfrontier]
      congr 1
      change resultMem.readWithPadding (UInt256.ofNat addr).toNat 32 =
        resultMem.readBytes addr 32
      rw [UInt256.toNat_ofNat_of_lt haddr256,
        readWithPadding_eq_model_readPadded resultMem addr 32 haddr64 (by decide),
        readBytes_eq_model_readPadded resultMem addr 32 haddr64 (by decide)]
    have hopen := operandWord_toNat_eq_model resultMem addr (UInt256.ofNat rem)
      haddr64 (by
        rw [UInt256.toNat_ofNat_of_lt (by dsimp [rem]; omega)]
        dsimp [rem]
        omega)
    have hfield :
        Model.bytesToNatPadded resultMem addr rem =
          Model.bytesToNatPadded I.calldata 96 rem := by
      have hreadResultMem :
          resultMem.readWithPadding addr rem =
            mem0.readWithPadding addr rem := by
        exact barrettNormalizedResultMem_read_original_len
          hmemSizeLocal hmemLeLocal hgapLocal
          (by simpa [← hnEq] using hnormLenPosLocal)
          (by simpa [← hnEq] using hnormalizeSourceConcrete)
          hresultMemSizeLocal hresultGapLocal
          hremPos (by dsimp [rem]; omega)
          (by dsimp [addr]; unfold operandBasePtr; omega)
          (by
            rw [show mem0.size =
                operandFreePtr baseSize exponentSize modulusSize + 32 by
                  exact wideWordResultMemory_size I hb he hm1024]
            dsimp [addr, rem]
            unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
              bytesAllocationSize
            omega)
          (by
            dsimp [addr, rem, fp, wideBarrettNormalizedFp]
            unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
              bytesAllocationSize
            omega)
          (by
            rw [hresultFpEq]
            dsimp [addr, rem, fp, wideBarrettNormalizedFp]
            unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
              bytesAllocationSize
            omega)
      have hreadMem0 :
          mem0.readWithPadding addr rem =
            (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding addr rem := by
        dsimp [mem0]
        exact wideWordResultMemory_readOperandLen I hb he hm1024
          (by dsimp [addr]; unfold operandBasePtr; omega)
            hremPos (by dsimp [rem]; omega)
            (by
              have hge := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
              exact Nat.le_trans (by
                dsimp [addr, rem]
                unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
                omega) hge)
          (by
            dsimp [addr, rem]
            unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
              bytesAllocationSize
            omega)
      have hcalldataRead :
          (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding addr rem =
            I.calldata.readWithPadding 96 rem := by
        have hwindow := operandCopiedBaseWindow I baseSize exponentSize modulusSize 0 rem
          hb he (by dsimp [rem]; omega)
        have hmodelRead :
            Model.readPadded I.calldata 96 rem =
              I.calldata.readWithPadding 96 rem := by
          exact (readWithPadding_eq_model_readPadded I.calldata 96 rem
            (by decide) (by dsimp [rem]; omega)).symm
        simpa [addr] using hwindow.trans hmodelRead
      exact model_bytesToNatPadded_eq_of_readWithPadding
        haddr64 (by decide) (by dsimp [rem]; omega)
        (hreadResultMem.trans (hreadMem0.trans hcalldataRead))
    unfold wideBaseRemainder
    rw [show UInt256.ofNat (baseSize % 32) = UInt256.ofNat rem by rfl, hload]
    have hremNat : (UInt256.ofNat rem).toNat = rem := by
      rw [UInt256.toNat_ofNat_of_lt (by dsimp [rem]; omega)]
    rw [hremNat] at hopen
    exact hopen.trans hfield
  have hbaseAccLocal :
      (wideWordBaseAccWithModulusAt
        (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
        (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp)
        baseSize
        (wideWordModulusAtPtr
          (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
          (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp)
          fp n)).toNat =
        Model.bytesToNatPadded I.calldata 96 (wideWordBaseStart baseSize) %
          Model.bytesToNatPadded I.calldata
            (wideModulusOffset baseSize exponentSize) modulusSize := by
    have hacc := wideWordBaseAccWithModulusAt_toNat_eq_model_of I
      (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
      (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp)
      baseSize
      (wideWordModulusAtPtr
        (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
        (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp)
        fp n)
      (by rw [hnormalizedModulusWordLocal]; exact hmod)
      hbaseFirstLocal
    rw [hnormalizedModulusWordLocal] at hacc
    exact hacc
  have hexponentByteLocal : ∀ s, s < exponentSize →
      (wideExponentByteAt
        (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
        (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp)
        baseSize s).toNat =
        Model.bytesToNatPadded I.calldata (96 + baseSize + s) 1 := by
    intro s hs
    let resultMem := barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp
    let resultAw := barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp
    let addr := wideExponentDataPtr baseSize + s
    have haddr256 : addr < UInt256.size := by
      dsimp [addr]
      unfold wideExponentDataPtr operandExponentPtr operandBasePtr bytesAllocationSize
      exact lt_of_le_of_lt (by omega) (by decide : 2240 < UInt256.size)
    have haddr64 : addr < 2 ^ 64 := by
      dsimp [addr]
      unfold wideExponentDataPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    have haddrEndLeModulusPtr :
        addr + 1 ≤ operandModulusPtr baseSize exponentSize := by
      dsimp [addr]
      have halloc := bytesHeaderAndSize_le_allocation exponentSize
      change wideExponentDataPtr baseSize + s + 1 ≤
        operandModulusPtr baseSize exponentSize
      unfold wideExponentDataPtr operandModulusPtr
      omega
    have haddrEndLeFree :
        addr + 1 ≤ operandFreePtr baseSize exponentSize modulusSize := by
      exact Nat.le_trans haddrEndLeModulusPtr (by
        unfold operandFreePtr
        omega)
    have hfrontier : ¬ UInt256.ofNat addr ≥ resultAw * ⟨32⟩ := by
      intro h
      change (resultAw * ⟨32⟩).toNat ≤ (UInt256.ofNat addr).toNat at h
      rw [show (resultAw * ⟨32⟩).toNat =
          32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat by
            dsimp [resultAw]; exact hresultAwMul32,
        UInt256.toNat_ofNat_of_lt haddr256] at h
      have hactive :
          addr + 32 ≤
            32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat := by
        dsimp [addr]
        exact Nat.le_trans (by omega) hexponentActiveLocal
      omega
    have hbyteModel :
        (wideExponentByteAt
          (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
          (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp)
          baseSize s).toNat =
          Model.bytesToNatPadded
            (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp) addr 1 := by
      simpa [wideExponentByteAt, addr] using
        (barrettScanByteAt_toNat_eq_model (mem := resultMem) (aw := resultAw)
          (cur := addr) haddr256 haddr64 hfrontier)
    have hreadResultMem :
        (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp).readWithPadding addr 1 =
          mem0.readWithPadding addr 1 := by
      exact barrettNormalizedResultMem_read_original_len
        hmemSizeLocal hmemLeLocal hgapLocal
        (by simpa [← hnEq] using hnormLenPosLocal)
        (by simpa [← hnEq] using hnormalizeSourceConcrete)
        hresultMemSizeLocal hresultGapLocal
        (by decide) (by decide)
        (by
          dsimp [addr]
          unfold wideExponentDataPtr operandExponentPtr operandBasePtr bytesAllocationSize
          omega)
        (by
          rw [show mem0.size =
              operandFreePtr baseSize exponentSize modulusSize + 32 by
                exact wideWordResultMemory_size I hb he hm1024]
          omega)
        (by
          dsimp [fp, wideBarrettNormalizedFp]
          omega)
        (by
          rw [hresultFpEq]
          dsimp [fp, wideBarrettNormalizedFp]
          unfold bytesAllocationSize
          omega)
    have hreadMem0 :
        mem0.readWithPadding addr 1 =
          (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding addr 1 := by
      dsimp [mem0]
      exact wideWordResultMemory_readOperandLen I hb he hm1024
        (by
          dsimp [addr]
          unfold wideExponentDataPtr operandExponentPtr operandBasePtr bytesAllocationSize
          omega)
        (by decide) (by decide)
        (by
          have hge := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
          exact Nat.le_trans (Nat.le_trans haddrEndLeModulusPtr (by omega)) hge)
        (by
          exact haddrEndLeFree)
    have hcalldataRead :
        (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding addr 1 =
          I.calldata.readWithPadding (96 + baseSize + s) 1 := by
      have hwindow := operandCopiedExponentWindow I baseSize exponentSize modulusSize s 1
        hb he (by omega)
      have hmodelRead :
          Model.readPadded I.calldata (96 + baseSize + s) 1 =
            I.calldata.readWithPadding (96 + baseSize + s) 1 := by
        exact (readWithPadding_eq_model_readPadded I.calldata (96 + baseSize + s) 1
          (by omega) (by decide)).symm
      simpa [addr, wideExponentDataPtr] using hwindow.trans hmodelRead
    have hmodel :
        Model.bytesToNatPadded
            (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp) addr 1 =
          Model.bytesToNatPadded I.calldata (96 + baseSize + s) 1 := by
      exact model_bytesToNatPadded_eq_of_readWithPadding
        haddr64 (by omega) (by decide)
        (hreadResultMem.trans (hreadMem0.trans hcalldataRead))
    exact hbyteModel.trans hmodel
  have hvalueLocal :
      (wideWordValueAtModulusPtr
        (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
        (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp)
        baseSize exponentSize fp n).toNat =
        Model.modPow
          (Model.bytesToNatPadded I.calldata 96 baseSize)
          (Model.bytesToNatPadded I.calldata (wideExponentOffset baseSize) exponentSize)
          (Model.bytesToNatPadded I.calldata
            (wideModulusOffset baseSize exponentSize) modulusSize) := by
    exact wideWordValueAtModulusPtr_toNat_eq_model_of_modulusNat I
      (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
      (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp)
      baseSize exponentSize fp n
      (Model.bytesToNatPadded I.calldata
        (wideModulusOffset baseSize exponentSize) modulusSize)
      he hmod
      hnormalizedModulusWordLocal hbaseAccLocal hbaseChunkLocal hexponentByteLocal
  have hrestoreDestActive :
      operandFreePtr baseSize exponentSize modulusSize +
        barrettNormalizedOffset mem0 aw0 p modulusSize + n ≤
          32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat := by
    rw [hresultActiveBytes, hresultFpEq]
    rw [show operandFreePtr baseSize exponentSize modulusSize +
        barrettNormalizedOffset mem0 aw0 p modulusSize + n =
          operandFreePtr baseSize exponentSize modulusSize + (modulusSize + 32) by
            omega]
    dsimp [fp, wideBarrettNormalizedFp]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
      bytesAllocationSize
    omega
  have hrestoreMaxActive :
      max (operandFreePtr baseSize exponentSize modulusSize +
            barrettNormalizedOffset mem0 aw0 p modulusSize)
          (resultFp + 32) + n ≤
        32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat := by
    rw [← Nat.add_max_add_right]
    exact max_le hrestoreDestActive hresultPayloadActiveLocal
  have hfinalWordsEq :
      wideBarrettNormalizedFinalWords I baseSize exponentSize modulusSize =
        barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp := by
    unfold wideBarrettNormalizedFinalWords barrettRestoreWords
    dsimp [mem0, aw0, p, fp, resultFp]
    have hM :
        MachineState.M
            (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat
            (max (operandFreePtr baseSize exponentSize modulusSize +
                barrettNormalizedOffset mem0 aw0 p modulusSize) (resultFp + 32))
            (barrettNormalizedLen mem0 aw0 p modulusSize) =
          (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat := by
      simpa [← hnEq] using machineM_eq_of_access hrestoreMaxActive
    rw [hM, u256_ofNat_toNat]
  have hreturnLoadActiveLocal :
      operandFreePtr baseSize exponentSize modulusSize + 32 ≤
        32 * (wideBarrettNormalizedFinalWords I baseSize exponentSize modulusSize).toNat := by
    rw [hfinalWordsEq]
    exact Nat.le_trans (by
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega) hrestoreDestActive
  have hreturnPayloadActiveLocal :
      operandFreePtr baseSize exponentSize modulusSize + 32 + modulusSize ≤
        32 * (wideBarrettNormalizedFinalWords I baseSize exponentSize modulusSize).toNat := by
    rw [hfinalWordsEq]
    have hdest :
        operandFreePtr baseSize exponentSize modulusSize + 32 + modulusSize ≤
          operandFreePtr baseSize exponentSize modulusSize +
            barrettNormalizedOffset mem0 aw0 p modulusSize + n := by
      omega
    exact hdest.trans hrestoreDestActive
  have hheaderLocal :
      (if operandFreePtr baseSize exponentSize modulusSize ≥
            (wideBarrettNormalizedFinalMemory I baseSize exponentSize modulusSize).size ∨
          UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) ≥
            wideBarrettNormalizedFinalWords I baseSize exponentSize modulusSize * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
          ((wideBarrettNormalizedFinalMemory I baseSize exponentSize modulusSize).readWithPadding
            (operandFreePtr baseSize exponentSize modulusSize) 32))) =
        UInt256.ofNat modulusSize := by
    have hresultWord :
        operandFreePtr baseSize exponentSize modulusSize < UInt256.size := by
      apply lt_of_le_of_lt
        (show operandFreePtr baseSize exponentSize modulusSize ≤ 2304 by
          unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
            bytesAllocationSize
          omega)
        (by decide)
    have hresultFpToNat : (UInt256.ofNat resultFp).toNat = resultFp := by
      exact UInt256.toNat_ofNat_of_lt (by omega : resultFp < UInt256.size)
    have hresultHeaderBelowFp :
        operandFreePtr baseSize exponentSize modulusSize + 32 ≤ fp := by
      dsimp [fp, wideBarrettNormalizedFp]
      unfold bytesAllocationSize
      omega
    have hresultHeaderBelowResultFp :
        operandFreePtr baseSize exponentSize modulusSize + 32 ≤ resultFp := by
      rw [hresultFpEq]
      dsimp [fp, wideBarrettNormalizedFp]
      unfold bytesAllocationSize
      omega
    have hoffsetGe32 :
        32 ≤ barrettNormalizedOffset mem0 aw0 p modulusSize := by
      dsimp [barrettNormalizedOffset]
      omega
    have hdestEnd :
        operandFreePtr baseSize exponentSize modulusSize +
            barrettNormalizedOffset mem0 aw0 p modulusSize +
            barrettNormalizedLen mem0 aw0 p modulusSize ≤
          resultFp + 32 + barrettNormalizedLen mem0 aw0 p modulusSize := by
      have hOffLen :
          barrettNormalizedOffset mem0 aw0 p modulusSize +
            barrettNormalizedLen mem0 aw0 p modulusSize = modulusSize + 32 := by
        rw [← hnEq]
        exact hoffsetLenEq
      rw [hresultFpEq]
      dsimp [fp, wideBarrettNormalizedFp]
      unfold bytesAllocationSize
      omega
    have hfinalMul32 :
        (wideBarrettNormalizedFinalWords I baseSize exponentSize modulusSize * ⟨32⟩).toNat =
          32 * (wideBarrettNormalizedFinalWords I baseSize exponentSize modulusSize).toNat := by
      rw [hfinalWordsEq, hresultAwMul32]
    have hgen := barrettNormalizedFinalHeader_eq_generic
      (baseSize := baseSize) (exponentSize := exponentSize)
      (result := operandFreePtr baseSize exponentSize modulusSize)
      (fp := fp) (p := p) (m := modulusSize) (resultFp := resultFp)
      (mem0 := mem0) (aw0 := aw0)
      (finalWords := wideBarrettNormalizedFinalWords I baseSize exponentSize modulusSize)
      (by
        simpa [mem0] using
          wideWordResultMemory_readResultLength I baseSize exponentSize modulusSize hb he hm1024)
      hmemSizeLocal hmemLeLocal hgapLocal
      (by simpa [← hnEq] using hnormLenPosLocal)
      (by simpa [← hnEq] using hnormLenLe32Local)
      (by simpa [← hnEq] using hnormalizeSourceConcrete)
      (by simpa [mem0, aw0, p, fp] using hresultMemSizeLocal)
      (by simpa [mem0, aw0, p, fp, resultFp] using hresultGapLocal)
      (by simpa [mem0, aw0, p, fp, resultFp] using hresultAllocatedMemSizeEq)
      hresultWord hresultFpToNat
      (by
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      hresultHeaderBelowFp
      hresultHeaderBelowResultFp
      hoffsetGe32
      hdestEnd
      hfinalMul32
      hreturnLoadActiveLocal
    simpa [wideBarrettNormalizedFinalMemory, wideBarrettNormalizedFinalWords,
      mem0, aw0, p, fp, resultFp, wideBarrettNormalizedFp,
      wideBarrettNormalizedResultFp, wideBarrettNormalizedLenFor] using hgen
  obtain ⟨kBarrett, rd173⟩ := runPreparedBarrettNormalizedWordExactAny
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (ret := 173) (fp := fp) (resultFp := resultFp) (tail := [])
    hb he hmodPos hm (by simpa [wideModulusOffset] using hmod) hcalldata heven
    (by simpa [hlenEq, fp, resultFp] using hfacts.hnorm)
    (by
      dsimp [fp, wideBarrettNormalizedFp]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega)
    hboundLocal
    (by simpa [mem0] using hmemSizeLocal)
    (by simpa [mem0, fp] using hmemLeLocal)
    (by simpa [mem0, fp] using hgapLocal)
    (by simpa [aw0] using haw3Local)
    (by simpa [aw0] using haw64Local)
    (by simpa [mem0, fp] using hreadLocal)
    hfp32WordLocal
    hnormLenPosLocal
    hnormLenWordLocal
    hnormLenLe32Local
    (by
      simpa [mem0, aw0, p, fp] using hmodAccessLocal)
    (by
      simpa [mem0, aw0, p, fp, n] using hlengthLocal)
    (by
      dsimp [resultFp, wideBarrettNormalizedResultFp, fp, wideBarrettNormalizedFp]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega)
    hresultBoundLocal
    (by
      simpa [mem0, aw0, p, fp] using hresultMemSizeLocal)
    (by
      simpa [mem0, aw0, p, fp, resultFp] using hresultMemLeLocal)
    (by
      simpa [mem0, aw0, p, fp, resultFp] using hresultGapLocal)
    (by
      simpa [mem0, aw0, p, fp] using hresultAw3Local)
    (by
      simpa [mem0, aw0, p, fp] using hresultAw64Local)
    (by
      simpa [mem0, aw0, p, fp, resultFp] using hresultReadLocal)
    hchecksBoundLocal
    (by
      simpa [mem0, aw0, p, fp, resultFp, n] using hchecksActiveLocal)
    (by
      simpa [mem0, aw0, p, fp, resultFp] using hchecksAwLocal)
    (by
      simpa [mem0, aw0, p, fp, resultFp, n] using hlengthAfterResultLocal)
    (by
      simpa [hlenEq, fp, resultFp, wideBarrettNormalizedFp, wideBarrettNormalizedResultFp,
        wideBarrettNormalizedLenFor] using hfacts.hzero)
    (by
      simpa [hlenEq, fp, resultFp, wideBarrettNormalizedFp, wideBarrettNormalizedResultFp,
        wideBarrettNormalizedLenFor] using hfacts.hone)
    hfpEndWordLocal
    (by
      simpa [mem0, aw0, p, fp, resultFp] using hfpActiveLocal)
    (by
      simpa [hlenEq, fp, resultFp, wideBarrettNormalizedFp, wideBarrettNormalizedResultFp,
        wideBarrettNormalizedLenFor] using hfacts.hfirst)
    (by
      simpa [mem0, aw0, p, fp, resultFp] using hbaseLengthLocal)
    (by
      simpa [mem0, aw0, p, fp, resultFp] using hexponentLengthLocal)
    (by
      simpa [mem0, aw0, p, fp, resultFp] using hbaseActiveLocal)
    (by
      simpa [mem0, aw0, p, fp, resultFp] using hbaseDataActiveLocal)
    (by
      simpa [mem0, aw0, p, fp, resultFp] using hexponentActiveLocal)
    hresultFpWordLocal
    (by
      simpa [mem0, aw0, p, fp, resultFp, n] using hresultPayloadActiveLocal)
    (by simpa [mem0, aw0, p] using hresultOffsetWordLocal)
    jumpDest_wrapper173_barrett (by simp) rd1183'
  have hptr32 : operandFreePtr baseSize exponentSize modulusSize + 32 < 2 ^ 64 := by
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have houtputLocal :
      (wideBarrettNormalizedFinalMemory I baseSize exponentSize modulusSize).readWithPadding
          (operandFreePtr baseSize exponentSize modulusSize + 32) modulusSize =
        Model.natToBytes
          (Model.modPow
            (Model.bytesToNatPadded I.calldata 96 baseSize)
            (Model.bytesToNatPadded I.calldata (wideExponentOffset baseSize) exponentSize)
            (Model.bytesToNatPadded I.calldata
              (wideModulusOffset baseSize exponentSize) modulusSize))
          modulusSize := by
    let result := operandFreePtr baseSize exponentSize modulusSize
    let offset := barrettNormalizedOffset mem0 aw0 p modulusSize
    let kprefix := offset - 32
    let resultMem := barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp
    let resultAw := barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp
    let value := wideWordValueAtModulusPtr resultMem resultAw baseSize exponentSize fp n
    let finalMem :=
      barrettRestoreMemory
        (wideWordReturnMemory resultMem value (UInt256.ofNat resultFp) n)
        resultFp result offset n
    have hkprefixLen : kprefix + n = modulusSize := by
      dsimp [kprefix, offset]
      omega
    have hresultFpToNat : (UInt256.ofNat resultFp).toNat = resultFp := by
      exact UInt256.toNat_ofNat_of_lt (by omega : resultFp < UInt256.size)
    have hdestRestore :
        result + offset ≤ resultFp + 32 + n := by
      rw [hresultFpEq]
      dsimp [result, offset, fp, wideBarrettNormalizedFp]
      unfold bytesAllocationSize
      omega
    have hdestRestoreEnd :
        result + offset + n ≤ resultFp + 32 + n := by
      rw [hresultFpEq]
      dsimp [result, offset, fp, wideBarrettNormalizedFp]
      unfold bytesAllocationSize
      omega
    have hfinalSize : finalMem.size = resultFp + 32 + n := by
      dsimp [finalMem, resultMem, value, resultAw]
      exact wideWordReturnThenRestore_size
        (mem := barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
        (value := wideWordValueAtModulusPtr
          (barrettNormalizedResultMem mem0 aw0 fp p modulusSize resultFp)
          (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp)
          baseSize exponentSize fp n)
        (resultFp := resultFp) (result := result)
        (offset := offset) (len := n)
        hnormLenPosLocal hnormLenLe32Local hresultFpToNat
        (by simpa [resultMem] using hresultAllocatedMemSizeEq)
        hdestRestoreEnd
    have hnormalizedModulusDecodedForFit :
        (wideWordModulusAtPtr resultMem resultAw fp n).toNat =
          Model.bytesToNatPadded resultMem (fp + 32) n := by
      have haddr64 : fp + 32 < 2 ^ 64 := by
        dsimp [fp, wideBarrettNormalizedFp]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega
      have hmodPtrFrontier :
          ¬ UInt256.ofNat (fp + 32) ≥ resultAw * ⟨32⟩ := by
        intro h
        change (resultAw * ⟨32⟩).toNat ≤
          (UInt256.ofNat (fp + 32)).toNat at h
        rw [show (resultAw * ⟨32⟩).toNat =
            32 * (barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp).toNat by
              dsimp [resultAw]; exact hresultAwMul32,
          UInt256.toNat_ofNat_of_lt hfp32WordLocal] at h
        rw [hresultActiveBytes, hresultFpEq] at h
        unfold bytesAllocationSize at h
        omega
      exact wideWordModulusAtPtr_toNat_eq_model_bytes
        resultMem resultAw fp n hnormLenLe32Local hfp32WordLocal haddr64
        hmodPtrFrontier
    have horiginalModLtPowN :
        Model.bytesToNatPadded I.calldata
            (wideModulusOffset baseSize exponentSize) modulusSize < 256 ^ n := by
      rw [← hnormalizedModulusWordLocal]
      rw [hnormalizedModulusDecodedForFit]
      exact model_bytesToNatPadded_lt_pow resultMem (fp + 32) n
    have hfitValue : value.toNat < 256 ^ n := by
      dsimp [value, resultMem, resultAw]
      rw [hvalueLocal]
      rw [model_modPow_eq_pow_mod _ _ _
        (by simpa using hmod)]
      exact Nat.lt_of_lt_of_le
        (Nat.mod_lt _ (by omega : 0 <
          Model.bytesToNatPadded I.calldata
            (wideModulusOffset baseSize exponentSize) modulusSize))
        (Nat.le_of_lt horiginalModLtPowN)
    have hfitModel :
        Model.modPow
            (Model.bytesToNatPadded I.calldata 96 baseSize)
            (Model.bytesToNatPadded I.calldata (wideExponentOffset baseSize) exponentSize)
            (Model.bytesToNatPadded I.calldata
              (wideModulusOffset baseSize exponentSize) modulusSize) < 256 ^ n := by
      rw [← hvalueLocal]
      simpa [value, resultMem, resultAw] using hfitValue
    have hresultMemPrefixZero :
        resultMem.readWithPadding (result + 32) kprefix =
          ffi.ByteArray.zeroes kprefix := by
      by_cases hk : kprefix = 0
      · rw [hk, byteArray_readWithPadding_zero]
        exact (zeroes_zero (n := 0) (by rfl)).symm
      · have hkpos : 0 < kprefix := Nat.pos_of_ne_zero hk
        have hnormPrefixZero :
            (barrettNormalizedMem mem0 aw0 fp p modulusSize).readWithPadding
                (result + 32) kprefix =
              ffi.ByteArray.zeroes kprefix := by
          have hgapRead := barrettNormalizedMemory_read_gap_len
            (mem := mem0) (fp := fp) (p := p)
            (offset := barrettNormalizedOffset mem0 aw0 p modulusSize)
            (written := barrettNormalizedLen mem0 aw0 p modulusSize)
            (read := result + 32) (len := kprefix)
            hmemSizeLocal hmemLeLocal hgapLocal
            (by simpa [← hnEq] using hnormLenPosLocal)
            (by simpa [← hnEq] using hnormalizeSourceConcrete)
            hkpos (by omega)
            (by
              rw [show mem0.size = result + 32 by
                dsimp [result, mem0]
                exact wideWordResultMemory_size I hb he hm1024])
            (by
              dsimp [result, offset, kprefix, fp, wideBarrettNormalizedFp]
              unfold bytesAllocationSize
              omega)
          simpa [barrettNormalizedMem, ← hnEq, result, offset, kprefix] using hgapRead
        have hresultPres :
            resultMem.readWithPadding (result + 32) kprefix =
              (barrettNormalizedMem mem0 aw0 fp p modulusSize).readWithPadding
                (result + 32) kprefix := by
          dsimp [resultMem]
          exact barrettNormalizedResultMem_read_below_len
            (mem := mem0) (aw := aw0) (fp := fp) (p := p)
            (m := modulusSize) (resultFp := resultFp)
            (read := result + 32) (len := kprefix)
            hresultMemSizeLocal hresultGapLocal
            (by
              dsimp [result]
              unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
                bytesAllocationSize
              omega)
            hkpos (by omega)
            (by
              rw [hnormMemSizeEq]
              dsimp [result, offset, kprefix, fp, wideBarrettNormalizedFp]
              unfold bytesAllocationSize
              omega)
            (by
              rw [hresultFpEq]
              dsimp [result, offset, kprefix, fp, wideBarrettNormalizedFp]
              unfold bytesAllocationSize
              omega)
        exact hresultPres.trans hnormPrefixZero
    have hfinalPrefixZero :
        finalMem.readWithPadding (result + 32) kprefix =
          ffi.ByteArray.zeroes kprefix := by
      by_cases hk : kprefix = 0
      · rw [hk, byteArray_readWithPadding_zero]
        exact (zeroes_zero (n := 0) (by rfl)).symm
      · have hkpos : 0 < kprefix := Nat.pos_of_ne_zero hk
        exact wideWordReturnThenRestore_read_below_len
          (mem := resultMem) (value := value)
          (resultFp := resultFp) (result := result)
          (offset := offset) (written := n)
          (read := result + 32) (len := kprefix)
          hnormLenPosLocal hnormLenLe32Local
          hkpos (by omega) hresultFpToNat
          (by simpa [resultMem] using hresultAllocatedMemSizeEq)
          hresultMemPrefixZero
          (by dsimp [result]; omega)
          (by
            rw [hresultFpEq]
            dsimp [result, offset, kprefix, fp, wideBarrettNormalizedFp]
            unfold bytesAllocationSize
            omega)
          (by dsimp [offset, kprefix]; omega)
          hdestRestore
    have hfinalSuffix :
        finalMem.readWithPadding (result + offset) n =
          Model.natToBytes
            (Model.modPow
              (Model.bytesToNatPadded I.calldata 96 baseSize)
              (Model.bytesToNatPadded I.calldata (wideExponentOffset baseSize) exponentSize)
              (Model.bytesToNatPadded I.calldata
                (wideModulusOffset baseSize exponentSize) modulusSize))
            n := by
      have hsuffixValue := wideWordReturnThenRestore_read_restored_payload
        (mem := resultMem) (value := value)
        (resultFp := resultFp) (result := result)
        (offset := offset) (len := n)
        hnormLenPosLocal hnormLenLe32Local (by omega)
        hresultFpToNat
        (by simpa [resultMem] using hresultAllocatedMemSizeEq)
        hdestRestore hfitValue
      rw [← hvalueLocal]
      simpa [finalMem, value, resultMem, resultAw] using hsuffixValue
    have hcombined := readWithPadding_eq_leftPaddedNatToBytes
      (mem := finalMem) (start := result + 32) (k := kprefix)
      (len := n) (width := modulusSize)
      (value := Model.modPow
        (Model.bytesToNatPadded I.calldata 96 baseSize)
        (Model.bytesToNatPadded I.calldata (wideExponentOffset baseSize) exponentSize)
        (Model.bytesToNatPadded I.calldata
          (wideModulusOffset baseSize exponentSize) modulusSize))
      hkprefixLen hnormLenPosLocal (by omega)
      (by
        rw [hfinalSize]
        rw [hresultFpEq]
        dsimp [result, fp, wideBarrettNormalizedFp]
        unfold bytesAllocationSize
        omega)
      hfinalPrefixZero
      (by
        have hstart : result + (32 + kprefix) = result + offset := by
          dsimp [kprefix, offset]
          omega
        simpa [Nat.add_assoc, hstart] using hfinalSuffix)
      hfitModel
    simpa [wideBarrettNormalizedFinalMemory, finalMem, resultMem, resultAw, value,
      result, offset, kprefix, mem0, aw0, p, fp, resultFp,
      wideBarrettNormalizedFp, wideBarrettNormalizedResultFp,
      wideBarrettNormalizedLenFor] using hcombined
  have hret := wrapperReturnExact
    (ptr := operandFreePtr baseSize exponentSize modulusSize)
    (len := modulusSize) (tail := [])
    (mem := wideBarrettNormalizedFinalMemory I baseSize exponentSize modulusSize)
    (aw := wideBarrettNormalizedFinalWords I baseSize exponentSize modulusSize)
    (output := Model.natToBytes
      (Model.modPow
        (Model.bytesToNatPadded I.calldata 96 baseSize)
        (Model.bytesToNatPadded I.calldata (wideExponentOffset baseSize) exponentSize)
        (Model.bytesToNatPadded I.calldata
          (wideModulusOffset baseSize exponentSize) modulusSize))
      modulusSize)
    hm1024 hptr32
    (by simpa [hlenEq] using hreturnLoadActiveLocal)
    (by simpa [hlenEq] using hreturnPayloadActiveLocal)
    hheaderLocal
    (by simpa [hlenEq] using houtputLocal)
    (by simp)
    (by
      simpa [wideBarrettNormalizedFinalMemory, wideBarrettNormalizedFinalWords,
        fp, resultFp, wideBarrettNormalizedFp, wideBarrettNormalizedResultFp,
        wideBarrettNormalizedLenFor] using rd173)
  exact hret.withCost (by
    unfold wideBarrettNormalizedWordGas wideExponentOffset wideModulusOffset
    unfold preparedBarrettNormalizedWordGasFromAw
    dsimp [fp, resultFp, wideBarrettNormalizedFp, wideBarrettNormalizedResultFp,
      wideBarrettNormalizedLenFor]
    omega)

theorem wideBarrettNormalizedWordModelExactGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hvalid : validOsaka I.calldata) (hwide : ¬ wordSized I.calldata)
    (hcond : wideBarrettNormalizedWordCondition I) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (Model.output I.calldata) (wideBarrettNormalizedWordTotalGas I) := by
  let l := lengths I.calldata
  unfold wideBarrettNormalizedWordCondition at hcond
  dsimp [l] at hcond
  rcases hcond with
    ⟨hmodPos, hmWord, hexp, hbase, hmod, heven, hfacts⟩
  have hv := hvalid
  unfold validOsaka at hv
  change (lengths I.calldata).base ≤ 1024 ∧
      (lengths I.calldata).exponent ≤ 1024 ∧
      (lengths I.calldata).modulus ≤ 1024 at hv
  rcases hv with ⟨hb, he, hm⟩
  obtain ⟨kEntry, rd62⟩ := reachWideEntry
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hvalue hvalid hwide
  have hret := wideBarrettNormalizedWordFromEntryModelExact
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    (baseSize := l.base) (exponentSize := l.exponent) (modulusSize := l.modulus)
    (acc := (cA, σ)) hb he hmodPos hmWord hexp hbase hmod hcalldata heven hfacts
    (by rfl) rd62
  have hout := model_output_of_lengths I.calldata
    (by rfl : Model.bytesToNatPadded I.calldata 0 32 = l.base)
    (by rfl : Model.bytesToNatPadded I.calldata 32 32 = l.exponent)
    (by rfl : Model.bytesToNatPadded I.calldata 64 32 = l.modulus)
  rw [hout]
  convert hret using 1

theorem wideBarrettNormalizedWordBytecodeSpec :
    BytecodeSpec runtimeBytecode
      wideBarrettNormalizedWordAccepts wideBarrettNormalizedWordEnsures := by
  simpa [wideBarrettNormalizedWordEnsures] using
    (ExactGasSpec.ofRDxRet (code := runtimeBytecode)
      (accepts := wideBarrettNormalizedWordAccepts)
      (output := fun ctx => Model.output ctx.executionEnv.calldata)
      (gasCost := fun ctx => wideBarrettNormalizedWordTotalGas ctx.executionEnv)
      (fun ctx hcode haccepts => by
        rcases haccepts with ⟨hvalue, hcalldata, hvalid, hwide, hcond⟩
        exact wideBarrettNormalizedWordModelExactGas
          (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
          (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
          (I := ctx.executionEnv) (g := ctx.gas)
          hcode hvalue hcalldata hvalid hwide hcond))

end Modexp
