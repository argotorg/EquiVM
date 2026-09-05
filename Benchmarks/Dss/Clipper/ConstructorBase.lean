import Benchmarks.Dss.Clipper.Rely
import Reasoning.MemCascade

/-!
# MakerDAO/Sky DSS Clipper constructor shared helpers

Deployment-shape, fixed-prefix decoding, constructor memory, storage, and immutable-patch facts.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

abbrev clipperCtorRayWord : UInt256 := ⟨1000000000000000000000000000⟩

def clipperCtorArgsTail (vat spotter dog : AccountAddress) (ilk : List UInt8) : ByteArray :=
  (EVM.Word.toBytesBE (EVM.word vat.val)).toByteArray ++
  (EVM.Word.toBytesBE (EVM.word spotter.val)).toByteArray ++
  (EVM.Word.toBytesBE (EVM.word dog.val)).toByteArray ++ ilk.toByteArray

noncomputable def clipperCtorCode (vat spotter dog : AccountAddress)
    (ilk : List UInt8) : ByteArray :=
  clipperCreationBytecode ++ clipperCtorArgsTail vat spotter dog ilk

private theorem byteArray_append_toList (a b : ByteArray) :
    (a ++ b).toList = a.toList ++ b.toList := by
  rw [byteArray_toList_eq, byteArray_toList_eq, byteArray_toList_eq]
  simp [ByteArray.data_append]

private theorem list_toByteArray_toList (xs : List UInt8) : xs.toByteArray.toList = xs := by
  rw [byteArray_toList_eq]
  simp

private theorem byteArray_toList_toByteArray (b : ByteArray) :
    b.toList.toByteArray = b := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [byteArray_toList_eq]

private theorem clipperCtorArgs_shape {args : List Value} {encoded : List UInt8}
    (henc : ABI.encodeABIValues? [addr, addr, addr, bytes32] args = some encoded) :
    ∃ (vat spotter dog : AccountAddress) (ilk : List UInt8),
      ilk.length = 32 ∧
      args = [.address vat, .address spotter, .address dog,
        .fixedBytes bytes32Width ilk] ∧
      encoded = (clipperCtorArgsTail vat spotter dog ilk).toList := by
  cases args with
  | nil => simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr, bytes32] at henc
  | cons a rest =>
      cases rest with
      | nil => simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr, bytes32] at henc
      | cons b rest2 =>
          cases rest2 with
          | nil => simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr, bytes32] at henc
          | cons c rest3 =>
              cases rest3 with
              | nil =>
                  simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr, bytes32] at henc
              | cons d rest4 =>
                  cases rest4 with
                  | cons _ _ =>
                      simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr, bytes32] at henc
                  | nil =>
                      cases a <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?,
                        ABI.encodeABIValue?, ABI.encodeABIWord?, addr, bytes32] at henc
                      rename_i vat
                      cases b <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?,
                        ABI.encodeABIValue?, ABI.encodeABIWord?, addr, bytes32] at henc
                      rename_i spotter
                      cases c <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?,
                        ABI.encodeABIValue?, ABI.encodeABIWord?, addr, bytes32] at henc
                      rename_i dog
                      cases d <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?,
                        ABI.encodeABIValue?, ABI.encodeABIWord?, addr, bytes32, bytes32Width]
                        at henc
                      rename_i n ilk
                      by_cases hcond : n = (31 : Fin 32) ∧ ilk.length = 32
                      · have hn : n = bytes32Width := by simpa [bytes32Width] using hcond.1
                        have hilk : ilk.length = 32 := hcond.2
                        simp [hcond, bytes32Width, ABI.encodeABIValues?,
                          ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
                          ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
                          ABI.isDynamicABIType, ABI.zeroBytes, List.append_assoc] at henc
                        cases hn
                        refine ⟨vat, spotter, dog, ilk, hilk, rfl, ?_⟩
                        simpa [clipperCtorArgsTail, ABI.zeroBytes, List.append_assoc,
                          byteArray_append_toList, list_toByteArray_toList]
                          using henc.symm
                      · simp [hcond, bytes32Width, ABI.encodeABIValues?,
                          ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
                          ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
                          ABI.isDynamicABIType, ABI.zeroBytes, List.append_assoc] at henc

theorem clipperCtorDeployment_shape (v : ClipperImmutables) {args : List Value}
    {deployedInitcode : ByteArray}
    (hdeploy : (config v).selfDeployment clipperCreationBytecode args = some deployedInitcode) :
    ∃ (vat spotter dog : AccountAddress) (ilk : List UInt8),
      ilk.length = 32 ∧
      args = [.address vat, .address spotter, .address dog,
        .fixedBytes bytes32Width ilk] ∧
      deployedInitcode = clipperCtorCode vat spotter dog ilk := by
  change Solm.genSolidityConstructorDeployment constructorDecl.params
    clipperCreationBytecode args = some deployedInitcode at hdeploy
  rw [show constructorDecl.params =
      [{ name := "vat_", ty := addr }, { name := "spotter_", ty := addr },
       { name := "dog_", ty := addr }, { name := "ilk_", ty := bytes32 }] from rfl]
    at hdeploy
  unfold Solm.genSolidityConstructorDeployment at hdeploy
  cases henc : ABI.encodeABIValues? [addr, addr, addr, bytes32] args with
  | none => simp [henc] at hdeploy
  | some encoded =>
      obtain ⟨vat, spotter, dog, ilk, hilk, hargs, hencoded⟩ :=
        clipperCtorArgs_shape henc
      refine ⟨vat, spotter, dog, ilk, hilk, hargs, ?_⟩
      simp [henc] at hdeploy
      rw [hdeploy.symm, clipperCtorCode, hencoded]
      rw [byteArray_toList_toByteArray]

macro "clipper_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [Reasoning.Theory.decode_append_left_window
          clipperCreationBytecode _ _ (by native_decide) (by native_decide)]
      | (unfold clipperCtorCode
         rw [Reasoning.Theory.decode_append_left_window
          clipperCreationBytecode _ _ (by native_decide) (by native_decide)]);
     native_decide))

macro "clipper_ctor_jd" : tactic =>
  `(tactic|
    (first
      | exact Reasoning.Theory.D_J_contains_append_left
          clipperCreationBytecode _ _ (by jump_dest)
      | (unfold clipperCtorCode
         exact Reasoning.Theory.D_J_contains_append_left
          clipperCreationBytecode _ _ (by jump_dest))))

open Lean in
macro "clipper_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) => acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump => acc ← `($(acc).jump (by clipper_ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT => acc ← `($(acc).jumpiT (by clipper_ctor_decode) $(args[0]!)
            $(args[1]!) (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by clipper_ctor_decode) $(args[0]!)
            (by evm_ov))
        | _ => acc ← `($(acc).$op $args* (by clipper_ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

theorem clipperCreationBytecode_size : clipperCreationBytecode.size = 9707 := by
  native_decide

theorem clipperBytecode_size : clipperBytecode.size = 9360 := by
  native_decide

theorem clipperCtorArgsTail_size (vat spotter dog : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    (clipperCtorArgsTail vat spotter dog ilk).size = 128 := by
  have hvat : (EVM.Word.toBytesBE (EVM.word vat.val)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (EVM.word vat.val)
  have hspotter : (EVM.Word.toBytesBE (EVM.word spotter.val)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (EVM.word spotter.val)
  have hdog : (EVM.Word.toBytesBE (EVM.word dog.val)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (EVM.word dog.val)
  simp [clipperCtorArgsTail, ByteArray.size_append, hvat, hspotter, hdog, hilk]

theorem clipperCtorCode_size (vat spotter dog : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    (clipperCtorCode vat spotter dog ilk).size = 9835 := by
  rw [clipperCtorCode, ByteArray.size_append, clipperCreationBytecode_size,
    clipperCtorArgsTail_size _ _ _ _ hilk]

theorem clipperCtorArgLen_eq (vat spotter dog : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    (UInt256.ofNat (clipperCtorCode vat spotter dog ilk).size).sub ⟨9707⟩ =
      (⟨128⟩ : UInt256) := by
  rw [clipperCtorCode_size _ _ _ _ hilk]
  native_decide

theorem clipperCreationBytecode_runtime_window :
    clipperCreationBytecode.extract 347 (347 + 9360) = clipperBytecode := by
  native_decide

theorem clipperCtorCode_runtime_window (vat spotter dog : AccountAddress) (ilk : List UInt8) :
    (clipperCtorCode vat spotter dog ilk).extract 347 (347 + 9360) = clipperBytecode := by
  unfold clipperCtorCode
  rw [extract_append_left clipperCreationBytecode (clipperCtorArgsTail vat spotter dog ilk)
    347 (347 + 9360) (by rw [clipperCreationBytecode_size])]
  exact clipperCreationBytecode_runtime_window

noncomputable def clipperCtorFreePtrMem : ByteArray :=
  writeWord ByteArray.empty 64 (⟨192⟩ : UInt256)

noncomputable def clipperCtorArgMem (vat spotter dog : AccountAddress)
    (ilk : List UInt8) : ByteArray :=
  (clipperCtorCode vat spotter dog ilk).write 9707 clipperCtorFreePtrMem 192 128

noncomputable def clipperCtorArgFreeMem (vat spotter dog : AccountAddress)
    (ilk : List UInt8) : ByteArray :=
  writeWord (clipperCtorArgMem vat spotter dog ilk) 64 (⟨320⟩ : UInt256)

private theorem byteArray_write_from_ge_eq (src base : ByteArray)
    (srcAddr destAddr len : ℕ) (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size)
    (hbase : base.size ≤ destAddr) :
    src.write srcAddr base destAddr len =
      base ++ ffi.ByteArray.zeroes (destAddr - base.size) ++
        src.extract srcAddr (srcAddr + len) := by
  have hsrcNonempty : ¬ srcAddr ≥ src.size := by omega
  have hcopy : min len (src.size - srcAddr) = len := by omega
  have htail : min base.size (destAddr + len) - (destAddr + len) = 0 := by omega
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg hsrcNonempty]
  simp only [hcopy, htail, ByteArray.data_copySlice, ByteArray.data_append,
    ByteArray.data_extract]
  have hz : (ffi.ByteArray.zeroes (destAddr - base.size)).data.size =
      destAddr - base.size := by
    rw [show (ffi.ByteArray.zeroes (destAddr - base.size)).data.size =
      (ffi.ByteArray.zeroes (destAddr - base.size)).size from rfl, ByteArray_zeroes_size]
  have hDsz :
      (base.data ++ (ffi.ByteArray.zeroes (destAddr - base.size)).data).size = destAddr := by
    rw [Array.size_append, hz, show base.data.size = base.size from rfl]
    omega
  rw [show (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
    rw [zeroes_zero (n := 0) (by rfl)]; rfl]
  simp only [Array.append_empty, Nat.add_zero]
  rw [show min len (src.data.size - srcAddr) = len by
    have : src.data.size = src.size := rfl
    omega]
  rw [Array.extract_eq_self_of_le (by rw [hDsz])]
  rw [show (base.data ++ (ffi.ByteArray.zeroes (destAddr - base.size)).data).extract
      (destAddr + len) = (#[] : Array UInt8) from by
    apply Array.extract_eq_empty_of_le
    rw [hDsz]
    omega]
  simp [Array.append_assoc]

theorem clipperCtorFreePtrMem_size : clipperCtorFreePtrMem.size = 96 := by
  unfold clipperCtorFreePtrMem
  rw [writeWord_size]
  · rfl
  · exact lt_usize _ (by norm_num)

theorem clipperCtorFreePtrMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ clipperCtorFreePtrMem.size ∨
        (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       (clipperCtorFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨192⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [clipperCtorFreePtrMem_size]
    decide
  · decide
  · change clipperCtorFreePtrMem.readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256)
    unfold clipperCtorFreePtrMem
    exact writeWord_read_back ByteArray.empty 64 (⟨192⟩ : UInt256)
      (by exact lt_usize _ (by norm_num))

theorem clipperCtorArgMem_eq (vat spotter dog : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    clipperCtorArgMem vat spotter dog ilk =
      clipperCtorFreePtrMem ++ ffi.ByteArray.zeroes 96 ++
        clipperCtorArgsTail vat spotter dog ilk := by
  rw [clipperCtorArgMem, byteArray_write_from_ge_eq]
  · unfold clipperCtorCode
    rw [extract_append_right' clipperCreationBytecode
      (clipperCtorArgsTail vat spotter dog ilk) 9707 (9707 + 128)]
    · rw [clipperCtorFreePtrMem_size]
    · exact clipperCreationBytecode_size.symm
    · rw [clipperCtorArgsTail_size _ _ _ _ hilk]
      native_decide
  · norm_num
  · rw [clipperCtorCode_size _ _ _ _ hilk]
  · rw [clipperCtorFreePtrMem_size]
    norm_num

theorem clipperCtorArgMem_size (vat spotter dog : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    (clipperCtorArgMem vat spotter dog ilk).size = 320 := by
  rw [clipperCtorArgMem_eq _ _ _ _ hilk, ByteArray.size_append,
    ByteArray.size_append, clipperCtorFreePtrMem_size, ByteArray_zeroes_size,
    clipperCtorArgsTail_size _ _ _ _ hilk]

theorem clipperCtorArgFreeMem_size (vat spotter dog : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    (clipperCtorArgFreeMem vat spotter dog ilk).size = 320 := by
  unfold clipperCtorArgFreeMem
  rw [writeWord_size]
  · rw [clipperCtorArgMem_size _ _ _ _ hilk]
    rfl
  · rw [clipperCtorArgMem_size _ _ _ _ hilk]
    exact lt_usize _ (by norm_num)

private theorem clipperCtorArgMem_readWord
    (vat spotter dog : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32)
    (off : Nat) (w : UInt256)
    (htail : (clipperCtorArgsTail vat spotter dog ilk).extract off (off + 32) =
      UInt256.toByteArray w) (hoff : off + 32 ≤ 128) :
    (clipperCtorArgMem vat spotter dog ilk).readWithPadding (192 + off) 32 =
      UInt256.toByteArray w := by
  rw [clipperCtorArgMem_eq _ _ _ _ hilk]
  let pre := clipperCtorFreePtrMem ++ ffi.ByteArray.zeroes 96
  have hpre : pre.size = 192 := by
    simp [pre, ByteArray.size_append, clipperCtorFreePtrMem_size, ByteArray_zeroes_size]
  change (pre ++ clipperCtorArgsTail vat spotter dog ilk).readWithPadding
    (192 + off) 32 = UInt256.toByteArray w
  rw [readWithPadding_eq_extract'
    (pre ++ clipperCtorArgsTail vat spotter dog ilk) (192 + off) 32
    (by omega) (by omega) (by
      rw [ByteArray.size_append, hpre, clipperCtorArgsTail_size _ _ _ _ hilk]
      omega)]
  rw [extract_append_right_window pre (clipperCtorArgsTail vat spotter dog ilk)
    (192 + off) (192 + off + 32) (by rw [hpre]; omega), hpre]
  rw [show 192 + off - 192 = off by omega,
    show 192 + off + 32 - 192 = off + 32 by omega]
  exact htail

private theorem clipperCtorTail_extract0 (vat spotter dog : AccountAddress)
    (ilk : List UInt8) :
    (clipperCtorArgsTail vat spotter dog ilk).extract 0 32 =
      UInt256.toByteArray (EVM.word vat.val) := by
  simp [clipperCtorArgsTail, word_toBytesBE_toByteArray_eq_toByteArray,
    extract_append_left, extract_append_right_window, toByteArray_extract_all]

private theorem clipperCtorTail_extract32 (vat spotter dog : AccountAddress)
    (ilk : List UInt8) :
    (clipperCtorArgsTail vat spotter dog ilk).extract 32 64 =
      UInt256.toByteArray (EVM.word spotter.val) := by
  simp [clipperCtorArgsTail, word_toBytesBE_toByteArray_eq_toByteArray,
    extract_append_left, extract_append_right_window, toByteArray_extract_all]

private theorem clipperCtorTail_extract64 (vat spotter dog : AccountAddress)
    (ilk : List UInt8) :
    (clipperCtorArgsTail vat spotter dog ilk).extract 64 96 =
      UInt256.toByteArray (EVM.word dog.val) := by
  simp [clipperCtorArgsTail, word_toBytesBE_toByteArray_eq_toByteArray,
    extract_append_left, extract_append_right_window, toByteArray_extract_all]

private theorem clipperCtorTail_extract96 (vat spotter dog : AccountAddress)
    (ilk : List UInt8) (hilk : ilk.length = 32) :
    (clipperCtorArgsTail vat spotter dog ilk).extract 96 128 =
      UInt256.toByteArray (ABI.bytesToWord ilk) := by
  unfold clipperCtorArgsTail
  rw [extract_append_right_window
    ((EVM.Word.toBytesBE (EVM.word vat.val)).toByteArray ++
      (EVM.Word.toBytesBE (EVM.word spotter.val)).toByteArray ++
      (EVM.Word.toBytesBE (EVM.word dog.val)).toByteArray)
    ilk.toByteArray 96 128 (by
      repeat rw [ByteArray.size_append]
      repeat rw [word_toBytesBE_toByteArray_size])]
  repeat rw [ByteArray.size_append]
  repeat rw [word_toBytesBE_toByteArray_size]
  norm_num
  rw [show ilk.toByteArray.extract 0 32 = ilk.toByteArray by
    rw [show 32 = ilk.toByteArray.size by simpa [list_toByteArray_size] using hilk.symm]
    exact byteArray_extract_self _]
  rw [← word_toBytesBE_toByteArray_eq_toByteArray]
  congr 1
  exact (toBytesBE_bytesToWord_of_length hilk).symm

theorem clipperCtorArgFreeMem_mload64 (vat spotter dog : AccountAddress)
    (ilk : List UInt8) (hilk : ilk.length = 32) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperCtorArgFreeMem vat spotter dog ilk).size ∨
        (⟨64⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((clipperCtorArgFreeMem vat spotter dog ilk).readWithPadding 64 32))) = ⟨320⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [clipperCtorArgFreeMem_size _ _ _ _ hilk]
    decide
  · decide
  · unfold clipperCtorArgFreeMem
    simpa using writeWord_read_back (clipperCtorArgMem vat spotter dog ilk) 64
      (⟨320⟩ : UInt256) (by
        rw [clipperCtorArgMem_size _ _ _ _ hilk]
        exact lt_usize _ (by norm_num))

private theorem clipperCtorArgFreeMem_readWord
    (vat spotter dog : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32)
    (off : Nat) (w : UInt256)
    (hread : (clipperCtorArgMem vat spotter dog ilk).readWithPadding off 32 =
      UInt256.toByteArray w) (hoff : 96 ≤ off) (hupper : off + 32 ≤ 320) :
    (clipperCtorArgFreeMem vat spotter dog ilk).readWithPadding off 32 =
      UInt256.toByteArray w := by
  unfold clipperCtorArgFreeMem
  rw [writeWord_read_preserved]
  · exact hread
  · rw [clipperCtorArgMem_size _ _ _ _ hilk]
    exact lt_usize _ (by norm_num)
  · right
    constructor
    · omega
    · rw [clipperCtorArgMem_size _ _ _ _ hilk]
      exact hupper

theorem clipperCtorArgFreeMem_mload192 (vat spotter dog : AccountAddress)
    (ilk : List UInt8) (hilk : ilk.length = 32) :
    (if (⟨192⟩ : UInt256).toNat ≥ (clipperCtorArgFreeMem vat spotter dog ilk).size ∨
        (⟨192⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((clipperCtorArgFreeMem vat spotter dog ilk).readWithPadding 192 32))) =
      EVM.word vat.val := by
  apply mloadWordValue_of_readWithPadding
  · rw [clipperCtorArgFreeMem_size _ _ _ _ hilk]
    decide
  · decide
  · apply clipperCtorArgFreeMem_readWord vat spotter dog ilk hilk 192 _ _ (by omega)
      (by omega)
    exact clipperCtorArgMem_readWord vat spotter dog ilk hilk 0 _
      (clipperCtorTail_extract0 vat spotter dog ilk) (by omega)

theorem clipperCtorArgFreeMem_mload224 (vat spotter dog : AccountAddress)
    (ilk : List UInt8) (hilk : ilk.length = 32) :
    (if (⟨224⟩ : UInt256).toNat ≥ (clipperCtorArgFreeMem vat spotter dog ilk).size ∨
        (⟨224⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((clipperCtorArgFreeMem vat spotter dog ilk).readWithPadding 224 32))) =
      EVM.word spotter.val := by
  apply mloadWordValue_of_readWithPadding
  · rw [clipperCtorArgFreeMem_size _ _ _ _ hilk]
    decide
  · decide
  · apply clipperCtorArgFreeMem_readWord vat spotter dog ilk hilk 224 _ _ (by omega)
      (by omega)
    exact clipperCtorArgMem_readWord vat spotter dog ilk hilk 32 _
      (clipperCtorTail_extract32 vat spotter dog ilk) (by omega)

theorem clipperCtorArgFreeMem_mload256 (vat spotter dog : AccountAddress)
    (ilk : List UInt8) (hilk : ilk.length = 32) :
    (if (⟨256⟩ : UInt256).toNat ≥ (clipperCtorArgFreeMem vat spotter dog ilk).size ∨
        (⟨256⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((clipperCtorArgFreeMem vat spotter dog ilk).readWithPadding 256 32))) =
      EVM.word dog.val := by
  apply mloadWordValue_of_readWithPadding
  · rw [clipperCtorArgFreeMem_size _ _ _ _ hilk]
    decide
  · decide
  · apply clipperCtorArgFreeMem_readWord vat spotter dog ilk hilk 256 _ _ (by omega)
      (by omega)
    exact clipperCtorArgMem_readWord vat spotter dog ilk hilk 64 _
      (clipperCtorTail_extract64 vat spotter dog ilk) (by omega)

theorem clipperCtorArgFreeMem_mload288 (vat spotter dog : AccountAddress)
    (ilk : List UInt8) (hilk : ilk.length = 32) :
    (if (⟨288⟩ : UInt256).toNat ≥ (clipperCtorArgFreeMem vat spotter dog ilk).size ∨
        (⟨288⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((clipperCtorArgFreeMem vat spotter dog ilk).readWithPadding 288 32))) =
      ABI.bytesToWord ilk := by
  apply mloadWordValue_of_readWithPadding
  · rw [clipperCtorArgFreeMem_size _ _ _ _ hilk]
    decide
  · decide
  · apply clipperCtorArgFreeMem_readWord vat spotter dog ilk hilk 288 _ _ (by omega)
      (by omega)
    exact clipperCtorArgMem_readWord vat spotter dog ilk hilk 96 _
      (clipperCtorTail_extract96 vat spotter dog ilk hilk) (by omega)

theorem clipperCtorAddressWord_canonical (a : AccountAddress) :
    (EVM.word a.val).toNat < EVM.addressModulus := by
  change (UInt256.ofNat a.val).toNat < EVM.addressModulus
  rw [UInt256.toNat_ofNat_of_lt]
  · exact a.isLt
  · exact lt_trans a.isLt (by decide)

private theorem clipperCtor_shiftLeft96_toNat_of_lt_160 (w : UInt256)
    (hw : w.toNat < 2 ^ (160 : Nat)) :
    (UInt256.shiftLeft w ⟨96⟩).toNat = w.toNat * 2 ^ (96 : Nat) := by
  have hprod : w.toNat * 2 ^ (96 : Nat) < UInt256.size := by
    change w.toNat * 2 ^ (96 : Nat) < 2 ^ (256 : Nat)
    nlinarith [hw,
      show (2 : Nat) ^ (256 : Nat) = 2 ^ (160 : Nat) * 2 ^ (96 : Nat) by
        norm_num [← Nat.pow_add]]
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ (⟨96⟩ : UInt256).val ≥ 256)]
  unfold UInt256.toNat
  rw [Fin.shiftLeft_val]
  rw [show (⟨96⟩ : UInt256).val.val = 96 by decide]
  rw [Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt hprod

theorem clipperCtorAddressHighShift (a : AccountAddress) :
    UInt256.land (UInt256.shiftLeft (EVM.word a.val) ⟨96⟩)
        (UInt256.lnot (UInt256.sub
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩)) =
      UInt256.shiftLeft (EVM.word a.val) ⟨96⟩ := by
  rw [show UInt256.lnot (UInt256.sub
      (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩) =
      UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ 96) by native_decide]
  apply u256_land_high_mask_eq_self (hk := by norm_num)
  have hlt : (EVM.word a.val).toNat < 2 ^ (160 : Nat) := by
    have hword : (EVM.word a.val).toNat = a.val := by
      change (UInt256.ofNat a.val).toNat = a.val
      rw [UInt256.toNat_ofNat_of_lt]
      exact lt_trans a.isLt (by decide)
    rw [hword]
    exact a.isLt
  rw [clipperCtor_shiftLeft96_toNat_of_lt_160 _ hlt]
  exact Nat.mod_eq_zero_of_dvd
    (Nat.dvd_mul_left (2 ^ 96) (EVM.word a.val).toNat)

set_option maxHeartbeats 1000000 in
theorem clipperCtorAddressHighShiftDecode (a : AccountAddress) :
    UInt256.shiftRight (UInt256.shiftLeft (EVM.word a.val) ⟨96⟩) ⟨96⟩ =
      EVM.word a.val := by
  apply u256_inj
  have hword : (EVM.word a.val).toNat = a.val := by
    change (UInt256.ofNat a.val).toNat = a.val
    rw [UInt256.toNat_ofNat_of_lt]
    exact lt_trans a.isLt (by decide)
  have hlt : (EVM.word a.val).toNat < 2 ^ (160 : Nat) := by
    rw [hword]
    exact a.isLt
  have hshift := clipperCtor_shiftLeft96_toNat_of_lt_160 (EVM.word a.val) hlt
  unfold UInt256.shiftRight
  rw [if_neg (by decide : ¬ (⟨96⟩ : UInt256).val ≥ 256)]
  unfold UInt256.toNat
  rw [Fin.shiftRight_val]
  change (UInt256.shiftLeft (EVM.word a.val) ⟨96⟩).toNat >>> 96 =
    (EVM.word a.val).toNat
  rw [Nat.shiftRight_eq_div_pow, hshift, Nat.mul_comm]
  exact Nat.mul_div_right (EVM.word a.val).toNat (by norm_num : 0 < 2 ^ 96)

noncomputable def clipperCtorVatMem (vat spotter dog : AccountAddress)
    (ilk : List UInt8) : ByteArray :=
  writeWord (clipperCtorArgFreeMem vat spotter dog ilk) 160
    (UInt256.shiftLeft (EVM.word vat.val) ⟨96⟩)

noncomputable def clipperCtorIlkMem (vat spotter dog : AccountAddress)
    (ilk : List UInt8) : ByteArray :=
  writeWord (clipperCtorVatMem vat spotter dog ilk) 128 (ABI.bytesToWord ilk)

theorem clipperCtorVatMem_size (vat spotter dog : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    (clipperCtorVatMem vat spotter dog ilk).size = 320 := by
  unfold clipperCtorVatMem
  rw [writeWord_size]
  · rw [clipperCtorArgFreeMem_size _ _ _ _ hilk]
    rfl
  · rw [clipperCtorArgFreeMem_size _ _ _ _ hilk]
    exact lt_usize _ (by norm_num)

theorem clipperCtorIlkMem_size (vat spotter dog : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    (clipperCtorIlkMem vat spotter dog ilk).size = 320 := by
  unfold clipperCtorIlkMem
  rw [writeWord_size]
  · rw [clipperCtorVatMem_size _ _ _ _ hilk]
    rfl
  · rw [clipperCtorVatMem_size _ _ _ _ hilk]
    exact lt_usize _ (by norm_num)

theorem clipperCtorVatMem_mstore160 (vat spotter dog : AccountAddress)
    (ilk : List UInt8) :
    writeWord (clipperCtorArgFreeMem vat spotter dog ilk) 160
        (UInt256.land (UInt256.shiftLeft (EVM.word vat.val) ⟨96⟩)
          (UInt256.lnot (UInt256.sub
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨96⟩) ⟨1⟩))) =
      clipperCtorVatMem vat spotter dog ilk := by
  rw [clipperCtorAddressHighShift]
  rfl

theorem clipperCtorIlkMem_read64 (vat spotter dog : AccountAddress)
    (ilk : List UInt8) (hilk : ilk.length = 32) :
    (clipperCtorIlkMem vat spotter dog ilk).readWithPadding 64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold clipperCtorIlkMem
  rw [writeWord_read_preserved]
  · unfold clipperCtorVatMem
    rw [writeWord_read_preserved]
    · unfold clipperCtorArgFreeMem
      exact writeWord_read_back (clipperCtorArgMem vat spotter dog ilk) 64
        (⟨320⟩ : UInt256) (by
          rw [clipperCtorArgMem_size _ _ _ _ hilk]
          exact lt_usize _ (by norm_num))
    · rw [clipperCtorArgFreeMem_size _ _ _ _ hilk]
      exact lt_usize _ (by norm_num)
    · left
      constructor
      · norm_num
      · rw [clipperCtorArgFreeMem_size _ _ _ _ hilk]
        omega
  · rw [clipperCtorVatMem_size _ _ _ _ hilk]
    exact lt_usize _ (by norm_num)
  · left
    constructor
    · norm_num
    · rw [clipperCtorVatMem_size _ _ _ _ hilk]
      omega

theorem clipperCtorIlkMem_read128 (vat spotter dog : AccountAddress)
    (ilk : List UInt8) (hilk : ilk.length = 32) :
    (clipperCtorIlkMem vat spotter dog ilk).readWithPadding 128 32 =
      UInt256.toByteArray (ABI.bytesToWord ilk) := by
  unfold clipperCtorIlkMem
  exact writeWord_read_back (clipperCtorVatMem vat spotter dog ilk) 128
    (ABI.bytesToWord ilk) (by
      rw [clipperCtorVatMem_size _ _ _ _ hilk]
      exact lt_usize _ (by norm_num))

theorem clipperCtorIlkMem_read160 (vat spotter dog : AccountAddress)
    (ilk : List UInt8) (hilk : ilk.length = 32) :
    (clipperCtorIlkMem vat spotter dog ilk).readWithPadding 160 32 =
      UInt256.toByteArray (UInt256.shiftLeft (EVM.word vat.val) ⟨96⟩) := by
  unfold clipperCtorIlkMem
  rw [writeWord_read_preserved]
  · exact writeWord_read_back (clipperCtorArgFreeMem vat spotter dog ilk) 160
      (UInt256.shiftLeft (EVM.word vat.val) ⟨96⟩) (by
        rw [clipperCtorArgFreeMem_size _ _ _ _ hilk]
        exact lt_usize _ (by norm_num))
  · rw [clipperCtorVatMem_size _ _ _ _ hilk]
    exact lt_usize _ (by norm_num)
  · right
    constructor
    · norm_num
    · rw [clipperCtorVatMem_size _ _ _ _ hilk]
      omega

theorem clipperCtorIlkMem_mload64 (vat spotter dog : AccountAddress)
    (ilk : List UInt8) (hilk : ilk.length = 32) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperCtorIlkMem vat spotter dog ilk).size ∨
        (⟨64⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((clipperCtorIlkMem vat spotter dog ilk).readWithPadding 64 32))) = ⟨320⟩ := by
  exact mloadWordValue_of_readWithPadding
    (by rw [clipperCtorIlkMem_size _ _ _ _ hilk]; decide) (by decide)
    (clipperCtorIlkMem_read64 vat spotter dog ilk hilk)

theorem clipperCtorIlkMem_mload128 (vat spotter dog : AccountAddress)
    (ilk : List UInt8) (hilk : ilk.length = 32) :
    (if (⟨128⟩ : UInt256).toNat ≥ (clipperCtorIlkMem vat spotter dog ilk).size ∨
        (⟨128⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((clipperCtorIlkMem vat spotter dog ilk).readWithPadding 128 32))) =
      ABI.bytesToWord ilk := by
  exact mloadWordValue_of_readWithPadding
    (by rw [clipperCtorIlkMem_size _ _ _ _ hilk]; decide) (by decide)
    (clipperCtorIlkMem_read128 vat spotter dog ilk hilk)

theorem clipperCtorIlkMem_mload160_shr96 (vat spotter dog : AccountAddress)
    (ilk : List UInt8) (hilk : ilk.length = 32) :
    UInt256.shiftRight
      (if (⟨160⟩ : UInt256).toNat ≥ (clipperCtorIlkMem vat spotter dog ilk).size ∨
          (⟨160⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((clipperCtorIlkMem vat spotter dog ilk).readWithPadding 160 32))) ⟨96⟩ =
      EVM.word vat.val := by
  have hload := mloadWordValue_of_readWithPadding
    (mem := clipperCtorIlkMem vat spotter dog ilk) (aw := UInt256.ofNat 10)
    (off := (⟨160⟩ : UInt256))
    (v := UInt256.shiftLeft (EVM.word vat.val) ⟨96⟩)
    (by rw [clipperCtorIlkMem_size _ _ _ _ hilk]; decide) (by decide)
    (by simpa using clipperCtorIlkMem_read160 vat spotter dog ilk hilk)
  change UInt256.shiftRight
    (if (⟨160⟩ : UInt256).toNat ≥ (clipperCtorIlkMem vat spotter dog ilk).size ∨
        (⟨160⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((clipperCtorIlkMem vat spotter dog ilk).readWithPadding
         (⟨160⟩ : UInt256).toNat 32))) ⟨96⟩ = EVM.word vat.val
  rw [hload]
  exact clipperCtorAddressHighShiftDecode vat

abbrev clipperCtorCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

noncomputable def clipperCtorWardsHashMem (I : ExecutionEnv)
    (vat spotter dog : AccountAddress) (ilk : List UInt8) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨0⟩ (clipperCtorIlkMem vat spotter dog ilk)

private theorem wordAt0Mem_size_320 {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 320) : (wordAt0Mem word mem).size = 320 := by
  unfold wordAt0Mem
  exact toByteArray_write32_size_of_le mem word 0 320 320 hmem
    (by rw [hmem]; omega) (by omega)

private theorem wordAt32Mem_size_320 {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 320) : (wordAt32Mem word mem).size = 320 := by
  unfold wordAt32Mem
  exact toByteArray_write32_size_of_le mem word 32 320 320 hmem
    (by rw [hmem]; omega) (by omega)

theorem clipperCtorWardsHashMem_size (I : ExecutionEnv)
    (vat spotter dog : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32) :
    (clipperCtorWardsHashMem I vat spotter dog ilk).size = 320 := by
  unfold clipperCtorWardsHashMem twoWordHashMem
  exact wordAt32Mem_size_320 ⟨0⟩
    (wordAt0Mem_size_320 (solcSourceWord I) (clipperCtorIlkMem_size _ _ _ _ hilk))

private theorem twoWordHashMem_read0_64_320 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 320) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num) (by
    unfold twoWordHashMem
    rw [wordAt32Mem_size_320]
    · omega
    · exact wordAt0Mem_size_320 key hmem)]
  have hleft : (twoWordHashMem key slot mem).extract 0 32 =
      UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0 (by
      unfold twoWordHashMem
      rw [wordAt32Mem_size_320]
      · omega
      · exact wordAt0Mem_size_320 key hmem)]
    unfold twoWordHashMem wordAt32Mem
    rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_320 key hmem]; omega) (by omega)]
    exact wordAt0Mem_read0 key mem
  have hright : (twoWordHashMem key slot mem).extract 32 64 =
      UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32 (by
      unfold twoWordHashMem
      rw [wordAt32Mem_size_320]
      · omega
      · exact wordAt0Mem_size_320 key hmem)]
    unfold twoWordHashMem wordAt32Mem
    rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_320 key hmem]; omega)]
    exact toByteArray_extract_all slot
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
      (twoWordHashMem key slot mem).extract 32 64 by
    rw [ByteArray.extract_append_extract]
    norm_num]
  rw [hleft, hright]

theorem clipperCtorWardsHashSlot (I : ExecutionEnv)
    (vat spotter dog : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32) :
    UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((clipperCtorWardsHashMem I vat spotter dog ilk).readWithPadding 0 64))) =
      clipperCtorCallerWardsSlot I := by
  unfold clipperCtorWardsHashMem clipperCtorCallerWardsSlot solcMappingSlot
  rw [twoWordHashMem_read0_64_320]
  · exact mappingSlot_single (solcSourceWord I) ⟨0⟩
  · exact clipperCtorIlkMem_size _ _ _ _ hilk

private theorem twoWordHashMem_read_preserved_320 {mem : ByteArray}
    (key slot : UInt256) (read : Nat) (hmem : mem.size = 320) (hread : 64 ≤ read)
    (hwindow : read + 32 ≤ 320) :
    (twoWordHashMem key slot mem).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above (UInt256.toByteArray slot) (wordAt0Mem key mem) 32 read
    (by rw [toByteArray_size]) (by rw [wordAt0Mem_size_320 key hmem]; omega)
    (by omega) (by rw [wordAt0Mem_size_320 key hmem]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above (UInt256.toByteArray key) mem 0 read
    (by rw [toByteArray_size]) (by rw [hmem]; omega) (by omega) (by rw [hmem]; omega)]

theorem clipperCtorWardsHashMem_read64 (I : ExecutionEnv)
    (vat spotter dog : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32) :
    (clipperCtorWardsHashMem I vat spotter dog ilk).readWithPadding 64 32 =
      UInt256.toByteArray (⟨320⟩ : UInt256) := by
  unfold clipperCtorWardsHashMem
  rw [twoWordHashMem_read_preserved_320 _ _ 64
    (clipperCtorIlkMem_size _ _ _ _ hilk) (by omega) (by omega)]
  exact clipperCtorIlkMem_read64 vat spotter dog ilk hilk

theorem clipperCtorWardsHashMem_read128 (I : ExecutionEnv)
    (vat spotter dog : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32) :
    (clipperCtorWardsHashMem I vat spotter dog ilk).readWithPadding 128 32 =
      UInt256.toByteArray (ABI.bytesToWord ilk) := by
  unfold clipperCtorWardsHashMem
  rw [twoWordHashMem_read_preserved_320 _ _ 128
    (clipperCtorIlkMem_size _ _ _ _ hilk) (by omega) (by omega)]
  exact clipperCtorIlkMem_read128 vat spotter dog ilk hilk

theorem clipperCtorWardsHashMem_read160 (I : ExecutionEnv)
    (vat spotter dog : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32) :
    (clipperCtorWardsHashMem I vat spotter dog ilk).readWithPadding 160 32 =
      UInt256.toByteArray (UInt256.shiftLeft (EVM.word vat.val) ⟨96⟩) := by
  unfold clipperCtorWardsHashMem
  rw [twoWordHashMem_read_preserved_320 _ _ 160
    (clipperCtorIlkMem_size _ _ _ _ hilk) (by omega) (by omega)]
  exact clipperCtorIlkMem_read160 vat spotter dog ilk hilk

theorem clipperCtorWardsHashMem_mload64 (I : ExecutionEnv)
    (vat spotter dog : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperCtorWardsHashMem I vat spotter dog ilk).size ∨
        (⟨64⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((clipperCtorWardsHashMem I vat spotter dog ilk).readWithPadding 64 32))) = ⟨320⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [clipperCtorWardsHashMem_size _ _ _ _ _ hilk]
    decide
  · decide
  · exact clipperCtorWardsHashMem_read64 I vat spotter dog ilk hilk

theorem clipperCtorWardsHashMem_mload128 (I : ExecutionEnv)
    (vat spotter dog : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32) :
    (if (⟨128⟩ : UInt256).toNat ≥ (clipperCtorWardsHashMem I vat spotter dog ilk).size ∨
        (⟨128⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((clipperCtorWardsHashMem I vat spotter dog ilk).readWithPadding 128 32))) =
      ABI.bytesToWord ilk := by
  apply mloadWordValue_of_readWithPadding
  · rw [clipperCtorWardsHashMem_size _ _ _ _ _ hilk]
    decide
  · decide
  · exact clipperCtorWardsHashMem_read128 I vat spotter dog ilk hilk

theorem clipperCtorWardsHashMem_mload160_shr96 (I : ExecutionEnv)
    (vat spotter dog : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32) :
    UInt256.shiftRight
      (if (⟨160⟩ : UInt256).toNat ≥ (clipperCtorWardsHashMem I vat spotter dog ilk).size ∨
          (⟨160⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((clipperCtorWardsHashMem I vat spotter dog ilk).readWithPadding 160 32))) ⟨96⟩ =
      EVM.word vat.val := by
  have hload := mloadWordValue_of_readWithPadding
    (mem := clipperCtorWardsHashMem I vat spotter dog ilk) (aw := UInt256.ofNat 10)
    (off := (⟨160⟩ : UInt256))
    (v := UInt256.shiftLeft (EVM.word vat.val) ⟨96⟩)
    (by rw [clipperCtorWardsHashMem_size _ _ _ _ _ hilk]; decide) (by decide)
    (by simpa using clipperCtorWardsHashMem_read160 I vat spotter dog ilk hilk)
  change UInt256.shiftRight
    (if (⟨160⟩ : UInt256).toNat ≥
          (clipperCtorWardsHashMem I vat spotter dog ilk).size ∨
        (⟨160⟩ : UInt256) ≥ UInt256.ofNat 10 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((clipperCtorWardsHashMem I vat spotter dog ilk).readWithPadding
         (⟨160⟩ : UInt256).toNat 32))) ⟨96⟩ = EVM.word vat.val
  rw [hload]
  exact clipperCtorAddressHighShiftDecode vat

private theorem write0_eq_extract_from_of_base_le (src base : ByteArray)
    (srcAddr len : Nat) (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size)
    (hbase : base.size ≤ len) :
    src.write srcAddr base 0 len = src.extract srcAddr (srcAddr + len) := by
  apply ByteArray.ext
  rw [write0_data_from src base srcAddr len hlen hsrc]
  rw [show base.data.extract len base.data.size = (#[] : Array UInt8) from by
    apply Array.extract_eq_empty_of_le
    rw [show base.data.size = base.size from rfl]
    simpa using hbase]
  simp

theorem clipperCtorRuntime_codecopy_mem (I : ExecutionEnv)
    (vat spotter dog : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32) :
    (clipperCtorCode vat spotter dog ilk).write 347
        (clipperCtorWardsHashMem I vat spotter dog ilk) 0 9360 = clipperBytecode := by
  rw [write0_eq_extract_from_of_base_le]
  · exact clipperCtorCode_runtime_window vat spotter dog ilk
  · norm_num
  · rw [clipperCtorCode_size _ _ _ _ hilk]
    norm_num
  · rw [clipperCtorWardsHashMem_size _ _ _ _ _ hilk]
    norm_num

def clipperCtorRuntimeWrites (vat : AccountAddress) (ilk : List UInt8) :
    List (Nat × UInt256) :=
  [ (1463, EVM.word vat.val), (2437, EVM.word vat.val),
    (3145, EVM.word vat.val), (4318, EVM.word vat.val),
    (4441, EVM.word vat.val), (4751, EVM.word vat.val),
    (5115, EVM.word vat.val), (6295, EVM.word vat.val),
    (7936, EVM.word vat.val),
    (1510, ABI.bytesToWord ilk), (1661, ABI.bytesToWord ilk),
    (2221, ABI.bytesToWord ilk), (2369, ABI.bytesToWord ilk),
    (4239, ABI.bytesToWord ilk), (4866, ABI.bytesToWord ilk),
    (5046, ABI.bytesToWord ilk), (6800, ABI.bytesToWord ilk),
    (8747, ABI.bytesToWord ilk) ]

noncomputable def clipperCtorPatchedRuntime (vat : AccountAddress)
    (ilk : List UInt8) : ByteArray :=
  writeCascade clipperBytecode (clipperCtorRuntimeWrites vat ilk)

def clipperCtorImmutables (vat : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) : ClipperImmutables :=
  { ilk := .fixedBytes bytes32Width ilk
    vat := vat
    ilk_wf := ⟨ilk, rfl, hilk⟩ }

private theorem spliceBytes_toByteArray_eq_writeWord (mem : ByteArray) (off : Nat)
    (w : UInt256) (h : off + 32 ≤ mem.size) :
    spliceBytes? mem off (UInt256.toByteArray w) = some (writeWord mem off w) := by
  unfold spliceBytes? Reasoning.Theory.writeWord
  rw [toByteArray_size, if_pos h]
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  rw [toByteArray_extract_all]

private theorem patchRuntime_wordWrites_eq_writeCascade
    (mem : ByteArray) (writes : List (Nat × UInt256))
    (hfit : ∀ p ∈ writes, p.1 + 32 ≤ mem.size) :
    patchRuntime mem (writes.map fun p => (p.1, UInt256.toByteArray p.2)) =
      some (writeCascade mem writes) := by
  induction writes generalizing mem with
  | nil => rfl
  | cons p rest ih =>
      rcases p with ⟨off, word⟩
      have hoff : off + 32 ≤ mem.size := hfit (off, word) (by simp)
      have hgap : off - mem.size < USize.size := by
        rw [Nat.sub_eq_zero_of_le (by omega)]
        exact lt_usize 0 (by norm_num)
      have hsize : (writeWord mem off word).size = mem.size := by
        rw [writeWord_size mem off word hgap]
        omega
      have hrest : ∀ p ∈ rest, p.1 + 32 ≤ (writeWord mem off word).size := by
        intro p hp
        rw [hsize]
        exact hfit p (by simp [hp])
      simp only [List.map_cons, patchRuntime, List.foldlM_cons,
        Option.bind_eq_bind, toByteArray_size, ↓reduceIte]
      rw [spliceBytes_toByteArray_eq_writeWord mem off word hoff]
      simpa [writeCascade] using ih (writeWord mem off word) hrest

private theorem word_toBytesBE_array_eq_toByteArray (w : UInt256) :
    (ByteArray.mk (EVM.Word.toBytesBE w).toArray) = UInt256.toByteArray w := by
  rw [← word_toBytesBE_toByteArray_eq_toByteArray]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [List.toList_data_toByteArray]

theorem clipperPatchRuntime_eq_ctorPatchedRuntime (vat : AccountAddress)
    (ilk : List UInt8) (hilk : ilk.length = 32) :
    patchRuntime clipperBytecode (patches (clipperCtorImmutables vat ilk hilk)) =
      some (clipperCtorPatchedRuntime vat ilk) := by
  have hpatches :
      patches (clipperCtorImmutables vat ilk hilk) =
        (clipperCtorRuntimeWrites vat ilk).map
          (fun p => (p.1, UInt256.toByteArray p.2)) := by
    simp [patches, patchesFrom, offsets, immValues, clipperCtorImmutables,
      clipperCtorRuntimeWrites, wordBytes?, valueToWord, hilk, bytes32Width,
      List.lookup_cons]
    constructor
    · exact word_toBytesBE_array_eq_toByteArray (EVM.word vat.val)
    · simpa [ABI.bytesToWord, fromByteArrayBigEndian, byteArray_toList_eq] using
        word_toBytesBE_array_eq_toByteArray
          (EVM.Word.ofNat (fromBytesBigEndian ilk))
  rw [hpatches]
  unfold clipperCtorPatchedRuntime
  apply patchRuntime_wordWrites_eq_writeCascade
  intro p hp
  simp [clipperCtorRuntimeWrites] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rw [clipperBytecode_size]
  all_goals norm_num

theorem clipperCtorPatchedRuntime_size (vat : AccountAddress) (ilk : List UInt8) :
    (clipperCtorPatchedRuntime vat ilk).size = 9360 := by
  unfold clipperCtorPatchedRuntime
  exact writeCascade_size_of_base clipperBytecode (clipperCtorRuntimeWrites vat ilk)
    (base := 9360) (out := 9360) (by native_decide)
    (by simp [clipperCtorRuntimeWrites, WriteGapsOk])
    (by simp [clipperCtorRuntimeWrites, writeCascadeSize])

theorem clipperCtorPatchedRuntime_read (vat : AccountAddress) (ilk : List UInt8) :
    (clipperCtorPatchedRuntime vat ilk).readWithPadding 0 9360 =
      clipperCtorPatchedRuntime vat ilk := by
  rw [readWithPadding_eq_extract' _ 0 9360 (by norm_num) (by norm_num)
    (by rw [clipperCtorPatchedRuntime_size])]
  rw [show 9360 = (clipperCtorPatchedRuntime vat ilk).size by
    rw [clipperCtorPatchedRuntime_size]]
  simpa using byteArray_extract_self (clipperCtorPatchedRuntime vat ilk)

end Benchmarks.Dss.Clipper
