import Benchmarks.Dss.Clipper.TakeCallbackSource
import Benchmarks.Dss.Clipper.TakeDogDigs
import Benchmarks.Dss.Clipper.TakePostDogFlux
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/-!
The callback calldata is copied after the ordinary `take` scratch space, so a successful
callback can leave memory larger than the 260-byte buffer used by the no-callback paths.
The compiler subsequently reuses only the fixed ABI windows below.  These lemmas record
that fixed writes preserve both the larger allocation and the free-memory-pointer word.
-/

theorem clipperTakeWrite32_size_of_end_le (mem : ByteArray) (word : UInt256)
    (off : Nat) (hend : off + 32 ≤ mem.size) :
    ((UInt256.toByteArray word).write 0 mem off 32).size = mem.size := by
  exact toByteArray_write32_size_of_le mem word off mem.size mem.size rfl
    (by omega) (max_eq_left hend)

theorem clipperTakeM_same_of_cover (aw off : UInt256) (len : Nat)
    (hcover : off.toNat + len ≤ aw.toNat * 32) :
    UInt256.ofNat (MachineState.M aw.toNat off.toNat len) = aw := by
  have hM : MachineState.M aw.toNat off.toNat len = aw.toNat := by
    unfold MachineState.M
    by_cases hlen : len = 0
    · simp [hlen]
    · simp only [hlen, ↓reduceIte]
      rw [max_eq_left]
      have hdivlt : (off.toNat + len + 31) / 32 < aw.toNat + 1 := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 32)]
        omega
      omega
  rw [hM]
  exact u256_ofNat_toNat aw

theorem clipperTakeMemoryWF_aw_ge (mem : ByteArray) (aw : UInt256)
    (hmem : clipperTakeMemoryWF mem aw) : 9 ≤ aw.toNat := by
  rcases hmem with ⟨hsize, _, hcover, _⟩
  omega

theorem clipperTakeMemoryWF_of_size_read_aw_nine {mem : ByteArray} {aw : UInt256}
    (hsize : mem.size = 260)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (haw : aw = UInt256.ofNat 9) : clipperTakeMemoryWF mem aw := by
  subst aw
  refine ⟨by omega, hread, ?_, ?_⟩
  · rw [show (UInt256.ofNat 9).toNat = 9 by decide]
    omega
  · native_decide

theorem clipperTakeMemoryWF_mstore_aw (mem : ByteArray) (aw off : UInt256)
    (hmem : clipperTakeMemoryWF mem aw) (hoff : off.toNat + 32 ≤ 260) :
    UInt256.ofNat (MachineState.M aw.toNat off.toNat 32) = aw := by
  apply clipperTakeM_same_of_cover
  rcases hmem with ⟨hsize, _, hcover, _⟩
  omega

theorem clipperTakeMemoryWF_mload64 (mem : ByteArray) (aw : UInt256)
    (hmem : clipperTakeMemoryWF mem aw) :
    (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨
        (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  rcases hmem with ⟨hsize, hread64, hcover, hawSmall⟩
  apply mloadFreePtrValue (mem := mem) (aw := aw)
  · omega
  · intro hbad
    have hawNat : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
        umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hawSmall
    have hbadNat : (⟨64⟩ : UInt256).toNat ≥
        (aw * (⟨32⟩ : UInt256)).toNat := hbad
    rw [hawNat] at hbadNat
    change 64 ≥ aw.toNat * 32 at hbadNat
    have hawGe := clipperTakeMemoryWF_aw_ge mem aw ⟨hsize, hread64, hcover, hawSmall⟩
    omega
  · simpa using hread64

theorem clipperTakeMemoryWF_after_zero_output_call
    {mem out : ByteArray} {aw inOff : UInt256} {inLen outOff : ℕ}
    (hmem : clipperTakeMemoryWF mem aw)
    (hinput : inOff.toNat + inLen ≤ mem.size) :
    clipperTakeMemoryWF (out.write 0 mem outOff 0)
      (UInt256.ofNat
        (MachineState.M (MachineState.M aw.toNat inOff.toNat inLen) outOff 0)) := by
  have hawInner : UInt256.ofNat
      (MachineState.M aw.toNat inOff.toNat inLen) = aw :=
    clipperTakeM_same_of_cover aw inOff inLen (le_trans hinput hmem.2.2.1)
  have hawFinal : UInt256.ofNat
      (MachineState.M (MachineState.M aw.toNat inOff.toNat inLen) outOff 0) = aw := by
    simpa only [MachineState.M, if_pos rfl] using hawInner
  rw [byteArray_write_len_zero, hawFinal]
  exact hmem

theorem clipperTakeMstoreCostZero {aw off val : UInt256} {t : List UInt256}
    (hawOff : UInt256.ofNat (MachineState.M aw.toNat off.toNat 32) = aw) :
    ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack = off :: val :: t → memoryExpansionCost s .MSTORE = 0 := by
  intro s haws hstks
  exact mstoreCost_of_stack haws hstks (by rw [hawOff]; simp)

theorem clipperTakeMloadCostZero {aw off : UInt256} {t : List UInt256}
    (hawOff : UInt256.ofNat (MachineState.M aw.toNat off.toNat 32) = aw) :
    ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack = off :: t → memoryExpansionCost s .MLOAD = 0 := by
  intro s haws hstks
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
    List.getElem!_cons_zero]
  rw [hawOff]
  simp

theorem clipperTakeVatMoveSelectorMem_size_ge {mem : ByteArray}
    (hmem : 260 ≤ mem.size) :
    (clipperTakeVatMoveSelectorMem mem).size = mem.size := by
  unfold clipperTakeVatMoveSelectorMem
  exact clipperTakeWrite32_size_of_end_le mem clipperTakeVatMoveSelectorShifted 128
    (by omega)

theorem clipperTakeVatMoveSenderMem_size_ge (I : ExecutionEnv) {mem : ByteArray}
    (hmem : 260 ≤ mem.size) :
    (clipperTakeVatMoveSenderMem I mem).size = mem.size := by
  unfold clipperTakeVatMoveSenderMem
  rw [clipperTakeWrite32_size_of_end_le]
  · exact clipperTakeVatMoveSelectorMem_size_ge hmem
  · rw [clipperTakeVatMoveSelectorMem_size_ge hmem]
    omega

theorem clipperTakeVatMoveVowMem_size_ge (σ : AccountMap) (I : ExecutionEnv)
    {mem : ByteArray} (hmem : 260 ≤ mem.size) :
    (clipperTakeVatMoveVowMem σ I mem).size = mem.size := by
  unfold clipperTakeVatMoveVowMem
  rw [clipperTakeWrite32_size_of_end_le]
  · exact clipperTakeVatMoveSenderMem_size_ge I hmem
  · rw [clipperTakeVatMoveSenderMem_size_ge I hmem]
    omega

theorem clipperTakeVatMoveCalldataMem_size_ge (σ : AccountMap) (I : ExecutionEnv)
    (owe : UInt256) {mem : ByteArray} (hmem : 260 ≤ mem.size) :
    (clipperTakeVatMoveCalldataMem σ I owe mem).size = mem.size := by
  unfold clipperTakeVatMoveCalldataMem
  rw [clipperTakeWrite32_size_of_end_le]
  · exact clipperTakeVatMoveVowMem_size_ge σ I hmem
  · rw [clipperTakeVatMoveVowMem_size_ge σ I hmem]
    omega

theorem clipperTakeVatMoveCalldataMem_read64_ge (σ : AccountMap) (I : ExecutionEnv)
    (owe : UInt256) {mem : ByteArray} (hmem : 260 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperTakeVatMoveCalldataMem σ I owe mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperTakeVatMoveCalldataMem
  rw [toByteArray_write_read_below_of_gap owe _ 196 64
      (by rw [clipperTakeVatMoveVowMem_size_ge σ I hmem]; omega) (by omega)
      (by apply lt_usize; rw [clipperTakeVatMoveVowMem_size_ge σ I hmem]; omega)]
  unfold clipperTakeVatMoveVowMem
  rw [toByteArray_write_read_below_of_gap (clipperTakeVowTarget σ I) _ 164 64
      (by rw [clipperTakeVatMoveSenderMem_size_ge I hmem]; omega) (by omega)
      (by apply lt_usize; rw [clipperTakeVatMoveSenderMem_size_ge I hmem]; omega)]
  unfold clipperTakeVatMoveSenderMem
  rw [toByteArray_write_read_below_of_gap (solcSourceWord I) _ 132 64
      (by rw [clipperTakeVatMoveSelectorMem_size_ge hmem]; omega) (by omega)
      (by apply lt_usize; rw [clipperTakeVatMoveSelectorMem_size_ge hmem]; omega)]
  unfold clipperTakeVatMoveSelectorMem
  rw [toByteArray_write_read_below_of_gap clipperTakeVatMoveSelectorShifted _ 128 64
      (by omega) (by omega) (by apply lt_usize; omega)]
  exact hread64

theorem clipperTakeVatMoveSelectorMem_read128_4_ge {mem : ByteArray}
    (hmem : 260 ≤ mem.size) :
    (clipperTakeVatMoveSelectorMem mem).readWithPadding 128 4 = vatMoveSelector := by
  unfold clipperTakeVatMoveSelectorMem
  rw [toByteArray_write_read_window_of_gap clipperTakeVatMoveSelectorShifted mem 128 0 4
    (by norm_num) (by norm_num) (by norm_num) (by apply lt_usize; omega)]
  rw [toByteArray_eq_toBytesBE]
  native_decide

theorem clipperTakeVatMoveCalldataMem_read128_4_ge (σ : AccountMap)
    (I : ExecutionEnv) (owe : UInt256) {mem : ByteArray} (hmem : 260 ≤ mem.size) :
    (clipperTakeVatMoveCalldataMem σ I owe mem).readWithPadding 128 4 =
      vatMoveSelector := by
  unfold clipperTakeVatMoveCalldataMem
  rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
    (by rw [clipperTakeVatMoveVowMem_size_ge σ I hmem]; omega) (by omega)
    (by rw [clipperTakeVatMoveVowMem_size_ge σ I hmem]; omega) (by norm_num)
    (by norm_num)]
  unfold clipperTakeVatMoveVowMem
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [clipperTakeVatMoveSenderMem_size_ge I hmem]; omega) (by omega)
    (by rw [clipperTakeVatMoveSenderMem_size_ge I hmem]; omega) (by norm_num)
    (by norm_num)]
  unfold clipperTakeVatMoveSenderMem
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [clipperTakeVatMoveSelectorMem_size_ge hmem]; omega) (by omega)
    (by rw [clipperTakeVatMoveSelectorMem_size_ge hmem]; omega) (by norm_num)
    (by norm_num)]
  exact clipperTakeVatMoveSelectorMem_read128_4_ge hmem

theorem clipperTakeVatMoveCalldataMem_read132_32_ge (σ : AccountMap)
    (I : ExecutionEnv) (owe : UInt256) {mem : ByteArray} (hmem : 260 ≤ mem.size) :
    (clipperTakeVatMoveCalldataMem σ I owe mem).readWithPadding 132 32 =
      UInt256.toByteArray (solcSourceWord I) := by
  unfold clipperTakeVatMoveCalldataMem
  rw [write32_read_below _ _ 196 132 (by rw [toByteArray_size])
    (by rw [clipperTakeVatMoveVowMem_size_ge σ I hmem]; omega) (by omega)]
  unfold clipperTakeVatMoveVowMem
  rw [write32_read_below _ _ 164 132 (by rw [toByteArray_size])
    (by rw [clipperTakeVatMoveSenderMem_size_ge I hmem]; omega) (by omega)]
  unfold clipperTakeVatMoveSenderMem
  rw [write32_read_back _ _ 132 (by rw [toByteArray_size])
    (by rw [clipperTakeVatMoveSelectorMem_size_ge hmem]; omega)]
  exact toByteArray_extract_all (solcSourceWord I)

theorem clipperTakeVatMoveCalldataMem_read164_32_ge (σ : AccountMap)
    (I : ExecutionEnv) (owe : UInt256) {mem : ByteArray} (hmem : 260 ≤ mem.size) :
    (clipperTakeVatMoveCalldataMem σ I owe mem).readWithPadding 164 32 =
      UInt256.toByteArray (clipperTakeVowTarget σ I) := by
  unfold clipperTakeVatMoveCalldataMem
  rw [write32_read_below _ _ 196 164 (by rw [toByteArray_size])
    (by rw [clipperTakeVatMoveVowMem_size_ge σ I hmem]; omega) (by omega)]
  unfold clipperTakeVatMoveVowMem
  rw [write32_read_back _ _ 164 (by rw [toByteArray_size])
    (by rw [clipperTakeVatMoveSenderMem_size_ge I hmem]; omega)]
  exact toByteArray_extract_all (clipperTakeVowTarget σ I)

theorem clipperTakeVatMoveCalldataMem_read196_32_ge (σ : AccountMap)
    (I : ExecutionEnv) (owe : UInt256) {mem : ByteArray} (hmem : 260 ≤ mem.size) :
    (clipperTakeVatMoveCalldataMem σ I owe mem).readWithPadding 196 32 =
      UInt256.toByteArray owe := by
  unfold clipperTakeVatMoveCalldataMem
  rw [write32_read_back _ _ 196 (by rw [toByteArray_size])
    (by rw [clipperTakeVatMoveVowMem_size_ge σ I hmem]; omega)]
  exact toByteArray_extract_all owe

theorem clipperTakeVatMoveCalldataMem_read128_100_ge (σ : AccountMap)
    (I : ExecutionEnv) (owe : UInt256) {mem : ByteArray} (hmem : 260 ≤ mem.size) :
    (clipperTakeVatMoveCalldataMem σ I owe mem).readWithPadding 128 100 =
      vatMoveSelector ++ UInt256.toByteArray (solcSourceWord I) ++
        UInt256.toByteArray (clipperTakeVowTarget σ I) ++ UInt256.toByteArray owe := by
  rw [byteArray_readWithPadding_split _ 128 4 96 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeVatMoveCalldataMem_size_ge σ I owe hmem]; omega)]
  rw [byteArray_readWithPadding_split _ 132 32 64 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeVatMoveCalldataMem_size_ge σ I owe hmem]; omega)]
  rw [byteArray_readWithPadding_split _ 164 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeVatMoveCalldataMem_size_ge σ I owe hmem]; omega)]
  rw [clipperTakeVatMoveCalldataMem_read128_4_ge σ I owe hmem,
    clipperTakeVatMoveCalldataMem_read132_32_ge σ I owe hmem,
    clipperTakeVatMoveCalldataMem_read164_32_ge σ I owe hmem,
    clipperTakeVatMoveCalldataMem_read196_32_ge σ I owe hmem]
  simp [ByteArray.append_assoc]

theorem clipperTakeVatMoveEncode_eq_ge (v : ClipperImmutables) (σ : AccountMap)
    (I : ExecutionEnv) (owe : UInt256) {mem : ByteArray} (hmem : 260 ≤ mem.size) :
    (config v).externalABI.encode? "move"
      [.address I.source,
        .address (AccountAddress.ofNat (clipperTakeVowTarget σ I).toNat),
        .int (Int.ofNat owe.toNat)] =
      some ((clipperTakeVatMoveCalldataMem σ I owe mem).readWithPadding 128 100) := by
  rw [clipperTakeVatMoveCalldataMem_read128_100_ge σ I owe hmem]
  let base := ffi.ByteArray.zeroes 260
  have hbase : base.size = 260 := zeroes_ofNat_size 260 (by norm_num)
  have h := clipperTakeVatMoveEncode_eq v σ I owe hbase
  rw [clipperTakeVatMoveCalldataMem_read128_100 σ I owe hbase] at h
  exact h

theorem clipperTakeVatMoveMemoryWF (σ : AccountMap) (I : ExecutionEnv)
    (owe : UInt256) {mem : ByteArray} {aw : UInt256}
    (hmem : clipperTakeMemoryWF mem aw) :
    clipperTakeMemoryWF (clipperTakeVatMoveCalldataMem σ I owe mem) aw := by
  rcases hmem with ⟨hsize, hread64, hcover, hawSmall⟩
  refine ⟨?_, ?_, ?_, hawSmall⟩
  · rw [clipperTakeVatMoveCalldataMem_size_ge σ I owe hsize]
    exact hsize
  · exact clipperTakeVatMoveCalldataMem_read64_ge σ I owe hsize hread64
  · rw [clipperTakeVatMoveCalldataMem_size_ge σ I owe hsize]
    exact hcover

theorem clipperTakeDogDigsSelectorMem_size_ge {mem : ByteArray}
    (hmem : 260 ≤ mem.size) :
    (clipperDogDigsSelectorMem mem).size = mem.size := by
  unfold clipperDogDigsSelectorMem
  exact clipperTakeWrite32_size_of_end_le mem clipperDogDigsSelectorShifted 128
    (by omega)

theorem clipperTakeDogDigsIlkMem_size_ge (v : ClipperImmutables) {mem : ByteArray}
    (hmem : 260 ≤ mem.size) :
    (clipperDogDigsIlkMem v mem).size = mem.size := by
  unfold clipperDogDigsIlkMem
  rw [clipperTakeWrite32_size_of_end_le]
  · exact clipperTakeDogDigsSelectorMem_size_ge hmem
  · rw [clipperTakeDogDigsSelectorMem_size_ge hmem]
    omega

theorem clipperTakeDogDigsCalldataMem_size_ge (v : ClipperImmutables)
    (tab : UInt256) {mem : ByteArray} (hmem : 260 ≤ mem.size) :
    (clipperDogDigsCalldataMem v tab mem).size = mem.size := by
  unfold clipperDogDigsCalldataMem
  rw [clipperTakeWrite32_size_of_end_le]
  · exact clipperTakeDogDigsIlkMem_size_ge v hmem
  · rw [clipperTakeDogDigsIlkMem_size_ge v hmem]
    omega

theorem clipperTakeDogDigsCalldataMem_read64_ge (v : ClipperImmutables)
    (tab : UInt256) {mem : ByteArray} (hmem : 260 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperDogDigsCalldataMem v tab mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold clipperDogDigsCalldataMem
  rw [toByteArray_write_read_below_of_gap tab _ 164 64
      (by rw [clipperTakeDogDigsIlkMem_size_ge v hmem]; omega) (by omega)
      (by apply lt_usize; rw [clipperTakeDogDigsIlkMem_size_ge v hmem]; omega)]
  unfold clipperDogDigsIlkMem
  rw [toByteArray_write_read_below_of_gap (clipperYankIlkWord v) _ 132 64
      (by rw [clipperTakeDogDigsSelectorMem_size_ge hmem]; omega) (by omega)
      (by apply lt_usize; rw [clipperTakeDogDigsSelectorMem_size_ge hmem]; omega)]
  unfold clipperDogDigsSelectorMem
  rw [toByteArray_write_read_below_of_gap clipperDogDigsSelectorShifted _ 128 64
      (by omega) (by omega) (by apply lt_usize; omega)]
  exact hread64

theorem clipperTakeDogDigsSelectorMem_read128_4_ge {mem : ByteArray}
    (hmem : 260 ≤ mem.size) :
    (clipperDogDigsSelectorMem mem).readWithPadding 128 4 = dogDigsSelector := by
  unfold clipperDogDigsSelectorMem
  rw [toByteArray_write_read_window_of_gap clipperDogDigsSelectorShifted mem 128 0 4
    (by norm_num) (by norm_num) (by norm_num) (by apply lt_usize; omega)]
  rw [toByteArray_eq_toBytesBE]
  native_decide

theorem clipperTakeDogDigsCalldataMem_read128_4_ge (v : ClipperImmutables)
    (tab : UInt256) {mem : ByteArray} (hmem : 260 ≤ mem.size) :
    (clipperDogDigsCalldataMem v tab mem).readWithPadding 128 4 =
      dogDigsSelector := by
  unfold clipperDogDigsCalldataMem
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [clipperTakeDogDigsIlkMem_size_ge v hmem]; omega) (by omega)
    (by rw [clipperTakeDogDigsIlkMem_size_ge v hmem]; omega) (by norm_num)
    (by norm_num)]
  unfold clipperDogDigsIlkMem
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [clipperTakeDogDigsSelectorMem_size_ge hmem]; omega) (by omega)
    (by rw [clipperTakeDogDigsSelectorMem_size_ge hmem]; omega) (by norm_num)
    (by norm_num)]
  exact clipperTakeDogDigsSelectorMem_read128_4_ge hmem

theorem clipperTakeDogDigsCalldataMem_read132_32_ge (v : ClipperImmutables)
    (tab : UInt256) {mem : ByteArray} (hmem : 260 ≤ mem.size) :
    (clipperDogDigsCalldataMem v tab mem).readWithPadding 132 32 =
      UInt256.toByteArray (clipperYankIlkWord v) := by
  unfold clipperDogDigsCalldataMem
  rw [write32_read_below _ _ 164 132 (by rw [toByteArray_size])
    (by rw [clipperTakeDogDigsIlkMem_size_ge v hmem]; omega) (by omega)]
  unfold clipperDogDigsIlkMem
  rw [write32_read_back _ _ 132 (by rw [toByteArray_size])
    (by rw [clipperTakeDogDigsSelectorMem_size_ge hmem]; omega)]
  exact toByteArray_extract_all (clipperYankIlkWord v)

theorem clipperTakeDogDigsCalldataMem_read164_32_ge (v : ClipperImmutables)
    (tab : UInt256) {mem : ByteArray} (hmem : 260 ≤ mem.size) :
    (clipperDogDigsCalldataMem v tab mem).readWithPadding 164 32 =
      UInt256.toByteArray tab := by
  unfold clipperDogDigsCalldataMem
  rw [write32_read_back _ _ 164 (by rw [toByteArray_size])
    (by rw [clipperTakeDogDigsIlkMem_size_ge v hmem]; omega)]
  exact toByteArray_extract_all tab

theorem clipperTakeDogDigsCalldataMem_read128_68_ge (v : ClipperImmutables)
    (tab : UInt256) {mem : ByteArray} (hmem : 260 ≤ mem.size) :
    (clipperDogDigsCalldataMem v tab mem).readWithPadding 128 68 =
      dogDigsSelector ++ UInt256.toByteArray (clipperYankIlkWord v) ++
        UInt256.toByteArray tab := by
  rw [byteArray_readWithPadding_split _ 128 4 64 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeDogDigsCalldataMem_size_ge v tab hmem]; omega)]
  rw [byteArray_readWithPadding_split _ 132 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeDogDigsCalldataMem_size_ge v tab hmem]; omega)]
  rw [clipperTakeDogDigsCalldataMem_read128_4_ge v tab hmem,
    clipperTakeDogDigsCalldataMem_read132_32_ge v tab hmem,
    clipperTakeDogDigsCalldataMem_read164_32_ge v tab hmem, ByteArray.append_assoc]

theorem clipperTakeDogDigsEncode_eq_ge (v : ClipperImmutables) (tab : UInt256)
    {mem : ByteArray} (hmem : 260 ≤ mem.size) :
    (config v).externalABI.encode? "digs" [v.ilk, .int (Int.ofNat tab.toNat)] =
      some ((clipperDogDigsCalldataMem v tab mem).readWithPadding 128 68) := by
  rw [clipperTakeDogDigsCalldataMem_read128_68_ge v tab hmem]
  let base := ffi.ByteArray.zeroes 260
  have hbase : base.size = 260 := zeroes_ofNat_size 260 (by norm_num)
  have h := clipperTakeDogDigsEncode_eq v tab hbase
  rw [clipperTakeDogDigsCalldataMem_read128_68 v tab hbase] at h
  exact h

theorem clipperTakeDogDigsMemoryWF (v : ClipperImmutables) (tab : UInt256)
    {mem : ByteArray} {aw : UInt256} (hmem : clipperTakeMemoryWF mem aw) :
    clipperTakeMemoryWF (clipperDogDigsCalldataMem v tab mem) aw := by
  rcases hmem with ⟨hsize, hread64, hcover, hawSmall⟩
  refine ⟨?_, ?_, ?_, hawSmall⟩
  · rw [clipperTakeDogDigsCalldataMem_size_ge v tab hsize]
    exact hsize
  · exact clipperTakeDogDigsCalldataMem_read64_ge v tab hsize hread64
  · rw [clipperTakeDogDigsCalldataMem_size_ge v tab hsize]
    exact hcover

theorem clipperTakeVatFluxSelectorMem_size_ge {mem : ByteArray}
    (hmem : 260 ≤ mem.size) :
    (clipperTakeVatFluxSelectorMem mem).size = mem.size := by
  unfold clipperTakeVatFluxSelectorMem
  exact clipperTakeWrite32_size_of_end_le mem clipperTakeVatFluxSelectorShifted 128
    (by omega)

theorem clipperTakeVatFluxIlkMem_size_ge (v : ClipperImmutables) {mem : ByteArray}
    (hmem : 260 ≤ mem.size) :
    (clipperTakeVatFluxIlkMem v mem).size = mem.size := by
  unfold clipperTakeVatFluxIlkMem
  rw [clipperTakeWrite32_size_of_end_le]
  · exact clipperTakeVatFluxSelectorMem_size_ge hmem
  · rw [clipperTakeVatFluxSelectorMem_size_ge hmem]
    omega

theorem clipperTakeVatFluxThisMem_size_ge (I : ExecutionEnv) {mem : ByteArray}
    (hmem : 260 ≤ mem.size) :
    (clipperTakeVatFluxThisMem I mem).size = mem.size := by
  unfold clipperTakeVatFluxThisMem
  exact clipperTakeWrite32_size_of_end_le mem (clipperTakeThisWord I) 164 (by omega)

theorem clipperTakeVatFluxWhoMem_size_ge (who : UInt256) {mem : ByteArray}
    (hmem : 260 ≤ mem.size) :
    (clipperTakeVatFluxWhoMem who mem).size = mem.size := by
  unfold clipperTakeVatFluxWhoMem
  exact clipperTakeWrite32_size_of_end_le mem (UInt256.land solcAddrMask who) 196
    (by omega)

theorem clipperTakeVatFluxCalldataMem_size_ge (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : 260 ≤ mem.size) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).size = mem.size := by
  unfold clipperTakeVatFluxCalldataMem
  rw [clipperTakeWrite32_size_of_end_le]
  · rw [clipperTakeVatFluxWhoMem_size_ge]
    · rw [clipperTakeVatFluxThisMem_size_ge]
      exact clipperTakeVatFluxIlkMem_size_ge v hmem
      rw [clipperTakeVatFluxIlkMem_size_ge v hmem]
      exact hmem
    · rw [clipperTakeVatFluxThisMem_size_ge]
      · rw [clipperTakeVatFluxIlkMem_size_ge v hmem]
        exact hmem
      · rw [clipperTakeVatFluxIlkMem_size_ge v hmem]
        exact hmem
  · rw [clipperTakeVatFluxWhoMem_size_ge]
    · rw [clipperTakeVatFluxThisMem_size_ge]
      · rw [clipperTakeVatFluxIlkMem_size_ge v hmem]
        omega
      · rw [clipperTakeVatFluxIlkMem_size_ge v hmem]
        exact hmem
    · rw [clipperTakeVatFluxThisMem_size_ge]
      · rw [clipperTakeVatFluxIlkMem_size_ge v hmem]
        exact hmem
      · rw [clipperTakeVatFluxIlkMem_size_ge v hmem]
        exact hmem

theorem clipperTakeVatFluxCalldataMem_read64_ge (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : 260 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [clipperTakeVatFluxCalldataMem_eq_writeCascade]
  rw [writeCascade_read_preserved mem _ 64]
  · exact hread64
  · norm_num [WindowDisjointFromWrites]
    constructor
    · apply lt_usize
      omega
    · omega

theorem clipperTakeVatFluxCalldataMem_read128_4_ge (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : 260 ≤ mem.size) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 128 4 =
      vatFluxSelector := by
  have hIlk := clipperTakeVatFluxIlkMem_size_ge v hmem
  have hThis := clipperTakeVatFluxThisMem_size_ge I (by rw [hIlk]; exact hmem)
  have hWho := clipperTakeVatFluxWhoMem_size_ge who (by rw [hThis, hIlk]; exact hmem)
  unfold clipperTakeVatFluxCalldataMem
  rw [write32_read_below_len _ _ 228 128 4 (by rw [toByteArray_size])
    (by rw [hWho, hThis, hIlk]; omega) (by omega)
    (by rw [hWho, hThis, hIlk]; omega) (by norm_num) (by norm_num)]
  unfold clipperTakeVatFluxWhoMem
  rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
    (by rw [hThis, hIlk]; omega) (by omega) (by rw [hThis, hIlk]; omega)
    (by norm_num) (by norm_num)]
  unfold clipperTakeVatFluxThisMem
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [hIlk]; omega) (by omega) (by rw [hIlk]; omega)
    (by norm_num) (by norm_num)]
  unfold clipperTakeVatFluxIlkMem
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [clipperTakeVatFluxSelectorMem_size_ge hmem]; omega) (by omega)
    (by rw [clipperTakeVatFluxSelectorMem_size_ge hmem]; omega)
    (by norm_num) (by norm_num)]
  unfold clipperTakeVatFluxSelectorMem
  rw [toByteArray_write_read_window_of_gap clipperTakeVatFluxSelectorShifted mem
    128 0 4 (by norm_num) (by norm_num) (by norm_num) (by apply lt_usize; omega)]
  rw [toByteArray_eq_toBytesBE]
  native_decide

theorem clipperTakeVatFluxCalldataMem_read132_32_ge (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : 260 ≤ mem.size) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 132 32 =
      UInt256.toByteArray (clipperTakeIlkWord v) := by
  have hIlk := clipperTakeVatFluxIlkMem_size_ge v hmem
  have hThis := clipperTakeVatFluxThisMem_size_ge I (by rw [hIlk]; exact hmem)
  have hWho := clipperTakeVatFluxWhoMem_size_ge who (by rw [hThis, hIlk]; exact hmem)
  unfold clipperTakeVatFluxCalldataMem
  rw [write32_read_below _ _ 228 132 (by rw [toByteArray_size])
    (by rw [hWho, hThis, hIlk]; omega) (by omega)]
  unfold clipperTakeVatFluxWhoMem
  rw [write32_read_below _ _ 196 132 (by rw [toByteArray_size])
    (by rw [hThis, hIlk]; omega) (by omega)]
  unfold clipperTakeVatFluxThisMem
  rw [write32_read_below _ _ 164 132 (by rw [toByteArray_size])
    (by rw [hIlk]; omega) (by omega)]
  unfold clipperTakeVatFluxIlkMem
  rw [write32_read_back _ _ 132 (by rw [toByteArray_size])
    (by rw [clipperTakeVatFluxSelectorMem_size_ge hmem]; omega)]
  exact toByteArray_extract_all _

theorem clipperTakeVatFluxCalldataMem_read164_32_ge (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : 260 ≤ mem.size) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 164 32 =
      UInt256.toByteArray (clipperTakeThisWord I) := by
  have hIlk := clipperTakeVatFluxIlkMem_size_ge v hmem
  have hThis := clipperTakeVatFluxThisMem_size_ge I (by rw [hIlk]; exact hmem)
  have hWho := clipperTakeVatFluxWhoMem_size_ge who (by rw [hThis, hIlk]; exact hmem)
  unfold clipperTakeVatFluxCalldataMem
  rw [write32_read_below _ _ 228 164 (by rw [toByteArray_size])
    (by rw [hWho, hThis, hIlk]; omega) (by omega)]
  unfold clipperTakeVatFluxWhoMem
  rw [write32_read_below _ _ 196 164 (by rw [toByteArray_size])
    (by rw [hThis, hIlk]; omega) (by omega)]
  unfold clipperTakeVatFluxThisMem
  rw [write32_read_back _ _ 164 (by rw [toByteArray_size]) (by rw [hIlk]; omega)]
  exact toByteArray_extract_all _

theorem clipperTakeVatFluxCalldataMem_read196_32_ge (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : 260 ≤ mem.size) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 196 32 =
      UInt256.toByteArray (UInt256.land solcAddrMask who) := by
  have hIlk := clipperTakeVatFluxIlkMem_size_ge v hmem
  have hThis := clipperTakeVatFluxThisMem_size_ge I (by rw [hIlk]; exact hmem)
  have hWho := clipperTakeVatFluxWhoMem_size_ge who (by rw [hThis, hIlk]; exact hmem)
  unfold clipperTakeVatFluxCalldataMem
  rw [write32_read_below _ _ 228 196 (by rw [toByteArray_size])
    (by rw [hWho, hThis, hIlk]; omega) (by omega)]
  unfold clipperTakeVatFluxWhoMem
  rw [write32_read_back _ _ 196 (by rw [toByteArray_size])
    (by rw [hThis, hIlk]; omega)]
  exact toByteArray_extract_all _

theorem clipperTakeVatFluxCalldataMem_read228_32_ge (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : 260 ≤ mem.size) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 228 32 =
      UInt256.toByteArray slice := by
  have hIlk := clipperTakeVatFluxIlkMem_size_ge v hmem
  have hThis := clipperTakeVatFluxThisMem_size_ge I (by rw [hIlk]; exact hmem)
  have hWho := clipperTakeVatFluxWhoMem_size_ge who (by rw [hThis, hIlk]; exact hmem)
  unfold clipperTakeVatFluxCalldataMem
  rw [write32_read_back _ _ 228 (by rw [toByteArray_size])
    (by rw [hWho, hThis, hIlk]; omega)]
  exact toByteArray_extract_all _

theorem clipperTakeVatFluxCalldataMem_read128_132_ge (v : ClipperImmutables)
    (I : ExecutionEnv) (who slice : UInt256) {mem : ByteArray}
    (hmem : 260 ≤ mem.size) :
    (clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 128 132 =
      vatFluxSelector ++ UInt256.toByteArray (clipperTakeIlkWord v) ++
        UInt256.toByteArray (clipperTakeThisWord I) ++
        UInt256.toByteArray (UInt256.land solcAddrMask who) ++
        UInt256.toByteArray slice := by
  rw [byteArray_readWithPadding_split _ 128 4 128 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeVatFluxCalldataMem_size_ge v I who slice hmem]; omega)]
  rw [byteArray_readWithPadding_split _ 132 32 96 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeVatFluxCalldataMem_size_ge v I who slice hmem]; omega)]
  rw [byteArray_readWithPadding_split _ 164 32 64 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeVatFluxCalldataMem_size_ge v I who slice hmem]; omega)]
  rw [byteArray_readWithPadding_split _ 196 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [clipperTakeVatFluxCalldataMem_size_ge v I who slice hmem]; omega)]
  rw [clipperTakeVatFluxCalldataMem_read128_4_ge v I who slice hmem,
    clipperTakeVatFluxCalldataMem_read132_32_ge v I who slice hmem,
    clipperTakeVatFluxCalldataMem_read164_32_ge v I who slice hmem,
    clipperTakeVatFluxCalldataMem_read196_32_ge v I who slice hmem,
    clipperTakeVatFluxCalldataMem_read228_32_ge v I who slice hmem]
  simp [ByteArray.append_assoc]

theorem clipperTakeVatFluxEncode_eq_ge (v : ClipperImmutables) (I : ExecutionEnv)
    (who slice : UInt256) {mem : ByteArray} (hmem : 260 ≤ mem.size) :
    (config v).externalABI.encode? "flux"
      [v.ilk, .address I.codeOwner, .address (AccountAddress.ofNat who.toNat),
        .int (Int.ofNat slice.toNat)] =
      some ((clipperTakeVatFluxCalldataMem v I who slice mem).readWithPadding 128 132) := by
  rw [clipperTakeVatFluxCalldataMem_read128_132_ge v I who slice hmem]
  let base := ffi.ByteArray.zeroes 260
  have hbase : base.size = 260 := zeroes_ofNat_size 260 (by norm_num)
  have h := clipperTakeVatFluxEncode_eq_260 v I who slice hbase
  rw [clipperTakeVatFluxCalldataMem_read128_132_260 v I who slice hbase] at h
  exact h

theorem clipperTakeVatFluxMemoryWF (v : ClipperImmutables) (I : ExecutionEnv)
    (who slice : UInt256) {mem : ByteArray} {aw : UInt256}
    (hmem : clipperTakeMemoryWF mem aw) :
    clipperTakeMemoryWF (clipperTakeVatFluxCalldataMem v I who slice mem) aw := by
  rcases hmem with ⟨hsize, hread64, hcover, hawSmall⟩
  refine ⟨?_, ?_, ?_, hawSmall⟩
  · rw [clipperTakeVatFluxCalldataMem_size_ge v I who slice hsize]
    exact hsize
  · exact clipperTakeVatFluxCalldataMem_read64_ge v I who slice hsize hread64
  · rw [clipperTakeVatFluxCalldataMem_size_ge v I who slice hsize]
    exact hcover

theorem clipperTakeWordAt0MemoryWF (word : UInt256) {mem : ByteArray} {aw : UInt256}
    (hmem : clipperTakeMemoryWF mem aw) :
    clipperTakeMemoryWF (wordAt0Mem word mem) aw := by
  rcases hmem with ⟨hsize, hread64, hcover, hawSmall⟩
  have hsizeEq : (wordAt0Mem word mem).size = mem.size := by
    rw [wordAt0Mem_size_of_ge_32 word]
    omega
  refine ⟨?_, ?_, ?_, hawSmall⟩
  · rw [hsizeEq]
    exact hsize
  · exact wordAt0Mem_read64_of_ge_96 word (by omega) hread64
  · rw [hsizeEq]
    exact hcover

theorem clipperTakeTwoWordHashMemoryWF (key slot : UInt256)
    {mem : ByteArray} {aw : UInt256} (hmem : clipperTakeMemoryWF mem aw) :
    clipperTakeMemoryWF (twoWordHashMem key slot mem) aw := by
  rcases hmem with ⟨hsize, hread64, hcover, hawSmall⟩
  have hsizeEq : (twoWordHashMem key slot mem).size = mem.size := by
    rw [twoWordHashMem_size_of_ge_64' key slot]
    omega
  refine ⟨?_, ?_, ?_, hawSmall⟩
  · rw [hsizeEq]
    exact hsize
  · exact twoWordHashMem_read64_of_ge_96 key slot (by omega) hread64
  · rw [hsizeEq]
    exact hcover

theorem clipperTakeRemoveMemoryWF (id move : UInt256)
    {mem : ByteArray} {aw : UInt256} (hmem : clipperTakeMemoryWF mem aw) :
    let activeMem := wordAt0Mem (⟨11⟩ : UInt256) mem
    let aw1 := UInt256.ofNat (MachineState.M aw.toNat 0 32)
    let aw2 := UInt256.ofNat (MachineState.M aw1.toNat 0 32)
    let saleHashMem := twoWordHashMem id ⟨12⟩ activeMem
    let aw3 := UInt256.ofNat (MachineState.M aw2.toNat 0 32)
    let aw4 := UInt256.ofNat (MachineState.M aw3.toNat 32 32)
    let aw5 := UInt256.ofNat (MachineState.M aw4.toNat 0 64)
    let activeIndexMem := wordAt0Mem (⟨11⟩ : UInt256) saleHashMem
    let aw6 := UInt256.ofNat (MachineState.M aw5.toNat 0 32)
    let aw7 := UInt256.ofNat (MachineState.M aw6.toNat 0 32)
    let aw8 := UInt256.ofNat (MachineState.M aw7.toNat 0 32)
    let moveHashMem := twoWordHashMem move ⟨12⟩ activeIndexMem
    let aw9 := UInt256.ofNat (MachineState.M aw8.toNat 32 32)
    let aw10 := UInt256.ofNat (MachineState.M aw9.toNat 0 64)
    clipperTakeMemoryWF moveHashMem aw10 := by
  dsimp only
  have haw0 : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw :=
    clipperTakeMemoryWF_mstore_aw mem aw ⟨0⟩ hmem (by decide)
  have haw32 : UInt256.ofNat (MachineState.M aw.toNat 32 32) = aw :=
    clipperTakeMemoryWF_mstore_aw mem aw ⟨32⟩ hmem (by decide)
  have haw64 : UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw := by
    simpa using clipperTakeM_same_of_cover aw (⟨0⟩ : UInt256) 64 (by
      change 64 ≤ aw.toNat * 32
      have hawGe := clipperTakeMemoryWF_aw_ge mem aw hmem
      omega)
  rw [haw0, haw0, haw0, haw32, haw64, haw0, haw0, haw0, haw32, haw64]
  exact clipperTakeTwoWordHashMemoryWF move ⟨12⟩
    (clipperTakeWordAt0MemoryWF ⟨11⟩
      (clipperTakeTwoWordHashMemoryWF id ⟨12⟩
        (clipperTakeWordAt0MemoryWF ⟨11⟩ hmem)))

end Benchmarks.Dss.Clipper
