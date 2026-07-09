import Benchmarks.Dss.Flipper.Common
import Reasoning.ExternalCall
import Reasoning.Initcode
import Reasoning.Memory
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.SolmBody
import Reasoning.Storage
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Flipper constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flipper

set_option maxRecDepth 2000000

/-! ## Constructor ABI/deployment facts -/

/-- ABI-encoded constructor arguments appended to `flipperCreationBytecode`. -/
def flipperCtorArgsTail (vat cat : Ethereum.AccountAddress) (ilk : List UInt8) : ByteArray :=
  (EVM.Word.toBytesBE (EVM.word vat.val) ++ EVM.Word.toBytesBE (EVM.word cat.val) ++ ilk).toByteArray

private theorem byteArray_append_toList (a b : ByteArray) :
    (a ++ b).toList = a.toList ++ b.toList := by
  rw [Reasoning.Theory.byteArray_toList_eq, Reasoning.Theory.byteArray_toList_eq,
    Reasoning.Theory.byteArray_toList_eq]
  simp [ByteArray.data_append]

private theorem list_toByteArray_toList (xs : List UInt8) : xs.toByteArray.toList = xs := by
  rw [Reasoning.Theory.byteArray_toList_eq]
  simp

theorem flipperCtorArgsTail_encode (vat cat : Ethereum.AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    ABI.encodeABIValues? [addr, addr, bytes32]
      [Solm.Value.address vat, Solm.Value.address cat, Solm.Value.fixedBytes bytes32Width ilk] =
      some (flipperCtorArgsTail vat cat ilk).toList := by
  simp [flipperCtorArgsTail, addr, bytes32, bytes32Width, hilk, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    ABI.zeroBytes, list_toByteArray_toList, byteArray_append_toList, List.append_assoc]

theorem flipperCtorDeployment_eq (vat cat : Ethereum.AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    config.selfDeployment flipperCreationBytecode
      [Solm.Value.address vat, Solm.Value.address cat, Solm.Value.fixedBytes bytes32Width ilk] =
      some (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) := by
  simp [config, contract, constructorDecl, Solm.genSolidityConstructorDeployment]
  simp [flipperCtorArgsTail, addr, bytes32, bytes32Width, hilk, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, ABI.zeroBytes, List.append_assoc]

theorem flipperCtorDeployment_shape {args : List Solm.Value} {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment flipperCreationBytecode args = some deployedInitcode) :
    ∃ vat cat : Ethereum.AccountAddress, ∃ ilk : List UInt8,
      args =
        [Solm.Value.address vat, Solm.Value.address cat, Solm.Value.fixedBytes bytes32Width ilk] ∧
      ilk.length = 32 ∧
      deployedInitcode = flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk := by
  simp [config, contract, constructorDecl, Solm.genSolidityConstructorDeployment] at hdeploy
  cases args with
  | nil => simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr, bytes32] at hdeploy
  | cons a rest =>
      cases rest with
      | nil => simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr, bytes32] at hdeploy
      | cons b rest2 =>
          cases rest2 with
          | nil => simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr, bytes32] at hdeploy
          | cons c rest3 =>
              cases rest3 with
              | cons _ _ =>
                  simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr, bytes32] at hdeploy
              | nil =>
                  cases a <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?,
                    ABI.encodeABIValue?, ABI.encodeABIWord?, addr, bytes32] at hdeploy
                  rename_i vat
                  cases b <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?,
                    ABI.encodeABIValue?, ABI.encodeABIWord?, addr, bytes32] at hdeploy
                  rename_i cat
                  cases c <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?,
                    ABI.encodeABIValue?, ABI.encodeABIWord?, addr, bytes32, bytes32Width] at hdeploy
                  rename_i n ilk
                  by_cases hcond : n = (31 : Fin 32) ∧ ilk.length = 32
                  · have hn : n = bytes32Width := by
                      simpa [bytes32Width] using hcond.1
                    have hilk : ilk.length = 32 := hcond.2
                    simp [hcond, bytes32Width, ABI.encodeABIValues?,
                      ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
                      ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
                      ABI.zeroBytes, List.append_assoc] at hdeploy
                    cases hn
                    refine ⟨vat, cat, ilk, rfl, hilk, ?_⟩
                    simpa [flipperCtorArgsTail, ABI.zeroBytes, List.append_assoc] using
                      hdeploy.symm
                  · simp [hcond, bytes32Width, ABI.encodeABIValues?,
                      ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
                      ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
                      ABI.zeroBytes, List.append_assoc] at hdeploy

macro "flipper_ctor_decode" : tactic =>
  `(tactic|
    (rw [Reasoning.Theory.decode_append_left_window
      flipperCreationBytecode _ _ (by native_decide) (by native_decide)]
     native_decide))

macro "flipper_ctor_jump_dest" : tactic =>
  `(tactic|
    (exact D_J_contains_append_left flipperCreationBytecode _ _ (by jump_dest)))

theorem flipperCreationBytecode_size :
    flipperCreationBytecode.size = 6596 := by
  native_decide

theorem flipperBytecode_size :
    flipperBytecode.size = 6386 := by
  native_decide

theorem flipperCreationBytecode_runtime_window :
    flipperCreationBytecode.extract 210 (210 + 6386) = flipperBytecode := by
  native_decide

theorem flipperCtorArgsTail_size (vat cat : Ethereum.AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    (flipperCtorArgsTail vat cat ilk).size = 96 := by
  unfold flipperCtorArgsTail
  rw [Reasoning.Theory.list_toByteArray_size]
  simp only [List.length_append]
  have hvat : (EVM.Word.toBytesBE (EVM.word vat.val)).length = 32 := by
    simpa [Reasoning.Theory.list_toByteArray_size] using
      word_toBytesBE_toByteArray_size (EVM.word vat.val)
  have hcat : (EVM.Word.toBytesBE (EVM.word cat.val)).length = 32 := by
    simpa [Reasoning.Theory.list_toByteArray_size] using
      word_toBytesBE_toByteArray_size (EVM.word cat.val)
  omega

theorem flipperCtorCode_size (vat cat : Ethereum.AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk).size = 6692 := by
  rw [ByteArray.size_append, flipperCreationBytecode_size,
    flipperCtorArgsTail_size vat cat ilk hilk]

theorem flipperCtorCode_tail_window (vat cat : Ethereum.AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk).extract 6596 (6596 + 96) =
      flipperCtorArgsTail vat cat ilk := by
  exact Reasoning.Theory.extract_append_right' flipperCreationBytecode
    (flipperCtorArgsTail vat cat ilk)
    6596 (6596 + 96) flipperCreationBytecode_size.symm
    (by rw [flipperCreationBytecode_size, flipperCtorArgsTail_size vat cat ilk hilk])

theorem flipperCtorCode_runtime_window (vat cat : Ethereum.AccountAddress) (ilk : List UInt8) :
    (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk).extract 210 (210 + 6386) =
      flipperBytecode := by
  rw [Reasoning.Theory.extract_append_left flipperCreationBytecode
    (flipperCtorArgsTail vat cat ilk)
    210 (210 + 6386) (by rw [flipperCreationBytecode_size])]
  exact flipperCreationBytecode_runtime_window

abbrev flipperIlkWord (ilk : List UInt8) : UInt256 :=
  UInt256.ofNat (fromBytesBigEndian ilk)

private theorem byteArray_write_from_ge_eq (src base : ByteArray) (srcAddr destAddr len : Nat)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size)
    (hbase : base.size ≤ destAddr) (_hgap : destAddr - base.size < USize.size) :
    src.write srcAddr base destAddr len =
      base ++ ffi.ByteArray.zeroes (destAddr - base.size) ++
        src.extract srcAddr (srcAddr + len) := by
  have hsrcNonempty : ¬ srcAddr ≥ src.size := by omega
  have hcopy : min len (src.size - srcAddr) = len := by
    rw [Nat.min_eq_left]
    omega
  have hcopyData : min len (src.data.size - srcAddr) = len := by
    rw [show src.data.size = src.size from rfl]
    exact hcopy
  have htail : min base.size (destAddr + len) - (destAddr + len) = 0 := by
    have hle : min base.size (destAddr + len) ≤ destAddr + len := Nat.min_le_right _ _
    omega
  have hDsz :
      (base.data ++ (ffi.ByteArray.zeroes (destAddr - base.size)).data).size =
        destAddr := by
    rw [Array.size_append]
    have hz :
        (ffi.ByteArray.zeroes (destAddr - base.size)).data.size =
          destAddr - base.size := by
      rw [show (ffi.ByteArray.zeroes (destAddr - base.size)).data.size =
          (ffi.ByteArray.zeroes (destAddr - base.size)).size from rfl,
        ByteArray_zeroes_size]
    rw [hz]
    change base.size + (destAddr - base.size) = destAddr
    omega
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg hsrcNonempty]
  simp only [ByteArray.data_copySlice, ByteArray.data_append]
  change (base.data ++
          (ffi.ByteArray.zeroes (destAddr - base.size)).data).extract 0
          destAddr ++
        (src.data ++
            (ffi.ByteArray.zeroes
              (min base.size (destAddr + len) -
                (destAddr + min len (src.size - srcAddr)))).data).extract
          srcAddr
          (srcAddr +
            (min len (src.size - srcAddr) +
              (min base.size (destAddr + len) -
                (destAddr + min len (src.size - srcAddr))))) ++
        (base.data ++
          (ffi.ByteArray.zeroes (destAddr - base.size)).data).extract
          (destAddr +
            min
              (min len (src.size - srcAddr) +
                (min base.size (destAddr + len) -
                  (destAddr + min len (src.size - srcAddr))))
              ((src.data ++
                    (ffi.ByteArray.zeroes
                      (min base.size (destAddr + len) -
                        (destAddr + min len (src.size - srcAddr)))).data).size -
                srcAddr)) =
      base.data ++ (ffi.ByteArray.zeroes (destAddr - base.size)).data ++
        (src.extract srcAddr (srcAddr + len)).data
  rw [hcopy, htail]
  rw [show (ffi.ByteArray.zeroes 0).data =
      (#[] : Array UInt8) from by
    rw [zeroes_zero (n := 0) (by rfl)]
    rfl]
  simp only [Array.append_empty, Nat.add_zero]
  rw [Array.extract_eq_self_of_le (by rw [hDsz])]
  rw [show src.data.extract srcAddr (srcAddr + len) =
      (src.extract srcAddr (srcAddr + len)).data from by rw [ByteArray.data_extract]]
  rw [hcopyData]
  rw [show
      (base.data ++
          (ffi.ByteArray.zeroes (destAddr - base.size)).data).extract
        (destAddr + len) = #[] from by
    apply Array.extract_eq_empty_of_le
    rw [hDsz]
    omega]
  simp only [Array.append_empty]

def flipperCtorCopiedMem (vat cat : AccountAddress) (ilk : List UInt8) : ByteArray :=
  (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk).write 6596 solcFreePtrMem 128 96

def flipperCtorArgsMem (vat cat : AccountAddress) (ilk : List UInt8) : ByteArray :=
  (UInt256.toByteArray ⟨224⟩).write 0 (flipperCtorCopiedMem vat cat ilk) 64 32

theorem flipperCtorCopiedMem_eq (vat cat : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    flipperCtorCopiedMem vat cat ilk =
      solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
        flipperCtorArgsTail vat cat ilk := by
  rw [flipperCtorCopiedMem]
  rw [byteArray_write_from_ge_eq]
  · rw [extract_append_right' flipperCreationBytecode (flipperCtorArgsTail vat cat ilk)
      6596 (6596 + 96)]
    · rw [solcFreePtrMem_size]
    · native_decide
    · rw [flipperCtorArgsTail_size vat cat ilk hilk]
      native_decide
  · decide
  · rw [ByteArray.size_append, flipperCtorArgsTail_size vat cat ilk hilk]
    native_decide
  · rw [solcFreePtrMem_size]
    decide
  · rw [solcFreePtrMem_size]
    exact lt_usize 32 (by norm_num)

private theorem flipperCtorArgsMem_base_size (vat cat : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    (solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
      flipperCtorArgsTail vat cat ilk).size = 224 := by
  rw [ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
    ByteArray_zeroes_size, flipperCtorArgsTail_size vat cat ilk hilk]

theorem flipperCtorArgsMem_size (vat cat : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    (flipperCtorArgsMem vat cat ilk).size = 224 := by
  rw [flipperCtorArgsMem, flipperCtorCopiedMem_eq vat cat ilk hilk]
  rw [toByteArray_write32_size_of_le
    (base := solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
      flipperCtorArgsTail vat cat ilk)
    (word := (⟨224⟩ : UInt256)) (off := 64) (baseSize := 224) (finalSize := 224)]
  · exact flipperCtorArgsMem_base_size vat cat ilk hilk
  · rw [flipperCtorArgsMem_base_size vat cat ilk hilk]
    omega
  · native_decide

private theorem flipperCtorArgsTail_extract_first (vat cat : AccountAddress) (ilk : List UInt8) :
    (flipperCtorArgsTail vat cat ilk).extract 0 32 =
      UInt256.toByteArray (EVM.word vat.val) := by
  simp [flipperCtorArgsTail, word_toBytesBE_toByteArray_eq_toByteArray, extract_append_left,
    extract_append_right_window, toByteArray_extract_all]

private theorem flipperCtorArgsTail_extract_second (vat cat : AccountAddress) (ilk : List UInt8) :
    (flipperCtorArgsTail vat cat ilk).extract 32 64 =
      UInt256.toByteArray (EVM.word cat.val) := by
  simp [flipperCtorArgsTail, word_toBytesBE_toByteArray_eq_toByteArray, extract_append_left,
    extract_append_right_window, toByteArray_extract_all]

private theorem flipperCtorArgsTail_extract_third (vat cat : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    (flipperCtorArgsTail vat cat ilk).extract 64 96 = ilk.toByteArray := by
  unfold flipperCtorArgsTail
  rw [Reasoning.Theory.list_toByteArray_append]
  rw [Reasoning.Theory.list_toByteArray_append]
  rw [extract_append_right_window]
  · have hprefix :
        ((EVM.Word.toBytesBE (EVM.word vat.val)).toByteArray ++
          (EVM.Word.toBytesBE (EVM.word cat.val)).toByteArray).size = 64 := by
      rw [ByteArray.size_append]
      have hvat :
          (EVM.Word.toBytesBE (EVM.word vat.val)).toByteArray.size = 32 :=
        word_toBytesBE_toByteArray_size (EVM.word vat.val)
      have hcat :
          (EVM.Word.toBytesBE (EVM.word cat.val)).toByteArray.size = 32 :=
        word_toBytesBE_toByteArray_size (EVM.word cat.val)
      omega
    rw [hprefix, show 64 - 64 = 0 by omega, show 96 - 64 = 32 by omega]
    have hsize : ilk.toByteArray.size = 32 := by
      simpa [Reasoning.Theory.list_toByteArray_size] using hilk
    rw [← hsize]
    exact ByteArray.extract_zero_size
  · rw [ByteArray.size_append]
    have hvat : (EVM.Word.toBytesBE (EVM.word vat.val)).length = 32 := by
      simpa [Reasoning.Theory.list_toByteArray_size] using
        word_toBytesBE_toByteArray_size (EVM.word vat.val)
    have hcat : (EVM.Word.toBytesBE (EVM.word cat.val)).length = 32 := by
      simpa [Reasoning.Theory.list_toByteArray_size] using
        word_toBytesBE_toByteArray_size (EVM.word cat.val)
    simpa [Reasoning.Theory.list_toByteArray_size, hvat, hcat]

private theorem flipperCtorArgsMem_read_word (vat cat : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) (start : Nat)
    (hstart : start + 32 ≤ 96)
    (hextract :
      (flipperCtorArgsTail vat cat ilk).extract start (start + 32) =
        if start = 0 then UInt256.toByteArray (EVM.word vat.val) else
        if start = 32 then UInt256.toByteArray (EVM.word cat.val) else ilk.toByteArray) :
    (flipperCtorArgsMem vat cat ilk).readWithPadding (128 + start) 32 =
        if start = 0 then UInt256.toByteArray (EVM.word vat.val) else
        if start = 32 then UInt256.toByteArray (EVM.word cat.val) else ilk.toByteArray := by
  rw [flipperCtorArgsMem, flipperCtorCopiedMem_eq vat cat ilk hilk]
  rw [write32_read_above_len
    (src := UInt256.toByteArray (⟨224⟩ : UInt256))
    (base := solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
      flipperCtorArgsTail vat cat ilk)
    (dest := 64) (read := 128 + start) (len := 32)]
  · have hprefix :
        (solcFreePtrMem ++ ffi.ByteArray.zeroes 32).size = 128 := by
      rw [ByteArray.size_append, solcFreePtrMem_size, ByteArray_zeroes_size]
    rw [readWithPadding_eq_extract'
      (solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
        flipperCtorArgsTail vat cat ilk)
      (128 + start) 32 (by norm_num) (by norm_num)
      (by rw [flipperCtorArgsMem_base_size vat cat ilk hilk]; omega)]
    rw [extract_append_right_window
      (solcFreePtrMem ++ ffi.ByteArray.zeroes 32)
      (flipperCtorArgsTail vat cat ilk) (128 + start) (128 + start + 32)
      (by rw [hprefix]; omega), hprefix]
    rw [show 128 + start - 128 = start by omega,
      show 128 + start + 32 - 128 = start + 32 by omega]
    exact hextract
  · rw [toByteArray_size]
  · rw [flipperCtorArgsMem_base_size vat cat ilk hilk]
    omega
  · omega
  · rw [flipperCtorArgsMem_base_size vat cat ilk hilk]
    omega
  · norm_num
  · norm_num

theorem flipperCtorArgsMem_mload_vat (vat cat : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    (if (⟨128⟩ : UInt256).toNat ≥ (flipperCtorArgsMem vat cat ilk).size ∨
        (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((flipperCtorArgsMem vat cat ilk).readWithPadding 128 32))) =
      EVM.word vat.val := by
  apply mloadWordValue_of_readWithPadding
  · rw [flipperCtorArgsMem_size vat cat ilk hilk]
    decide
  · decide
  · simpa using
      flipperCtorArgsMem_read_word vat cat ilk hilk 0 (by norm_num)
        (by simpa using flipperCtorArgsTail_extract_first vat cat ilk)

theorem flipperCtorArgsMem_mload_cat (vat cat : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    (if (⟨160⟩ : UInt256).toNat ≥ (flipperCtorArgsMem vat cat ilk).size ∨
        (⟨160⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((flipperCtorArgsMem vat cat ilk).readWithPadding 160 32))) =
      EVM.word cat.val := by
  apply mloadWordValue_of_readWithPadding
  · rw [flipperCtorArgsMem_size vat cat ilk hilk]
    decide
  · decide
  · simpa using
      flipperCtorArgsMem_read_word vat cat ilk hilk 32 (by norm_num)
        (by simpa using flipperCtorArgsTail_extract_second vat cat ilk)

theorem flipperCtorArgsMem_mload_ilk (vat cat : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) :
    (if (⟨192⟩ : UInt256).toNat ≥ (flipperCtorArgsMem vat cat ilk).size ∨
        (⟨192⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((flipperCtorArgsMem vat cat ilk).readWithPadding 192 32))) =
      flipperIlkWord ilk := by
  rw [if_neg (not_or.mpr ⟨by rw [flipperCtorArgsMem_size vat cat ilk hilk]; decide,
    by decide⟩)]
  rw [flipperCtorArgsMem_read_word vat cat ilk hilk 64 (by norm_num)]
  · simp [flipperIlkWord, fromByteArrayBigEndian, list_toByteArray_toList]
  · simpa using flipperCtorArgsTail_extract_third vat cat ilk hilk

abbrev flipperCtorCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

noncomputable def flipperCtorWardsHashMem (I : ExecutionEnv)
    (vat cat : AccountAddress) (ilk : List UInt8) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨0⟩ (flipperCtorArgsMem vat cat ilk)

theorem flipperCtorWardsHashMem_size (I : ExecutionEnv)
    (vat cat : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32) :
    (flipperCtorWardsHashMem I vat cat ilk).size = 224 := by
  have hfirstSize :
      ((UInt256.toByteArray (solcSourceWord I)).write 0
          (flipperCtorArgsMem vat cat ilk) 0 32).size = 224 := by
    exact toByteArray_write32_size_of_le
      (base := flipperCtorArgsMem vat cat ilk) (word := solcSourceWord I)
      (off := 0) (baseSize := 224) (finalSize := 224)
      (flipperCtorArgsMem_size vat cat ilk hilk)
      (by rw [flipperCtorArgsMem_size vat cat ilk hilk]; omega) (by omega)
  unfold flipperCtorWardsHashMem twoWordHashMem wordAt32Mem wordAt0Mem
  exact toByteArray_write32_size_of_le
      (base := (UInt256.toByteArray (solcSourceWord I)).write 0
        (flipperCtorArgsMem vat cat ilk) 0 32)
      (word := (⟨0⟩ : UInt256)) (off := 32) (baseSize := 224) (finalSize := 224)
      hfirstSize (by rw [hfirstSize]; omega) (by omega)

theorem flipperCtorWardsHashMem_read0 (I : ExecutionEnv)
    (vat cat : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32) :
    (flipperCtorWardsHashMem I vat cat ilk).readWithPadding 0 32 =
      UInt256.toByteArray (solcSourceWord I) := by
  unfold flipperCtorWardsHashMem twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])]
  · unfold wordAt0Mem
    rw [toByteArray_write32_read_back
      (base := flipperCtorArgsMem vat cat ilk) (word := solcSourceWord I)
      (off := 0) (Nat.zero_le _)]
  · unfold wordAt0Mem
    rw [toByteArray_write32_size_of_le
        (base := flipperCtorArgsMem vat cat ilk) (word := solcSourceWord I)
        (off := 0) (baseSize := 224) (finalSize := 224)]
    · omega
    · exact flipperCtorArgsMem_size vat cat ilk hilk
    · rw [flipperCtorArgsMem_size vat cat ilk hilk]
      omega
    · omega
  · omega

theorem flipperCtorWardsHashMem_read32 (I : ExecutionEnv)
    (vat cat : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32) :
    (flipperCtorWardsHashMem I vat cat ilk).readWithPadding 32 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold flipperCtorWardsHashMem twoWordHashMem wordAt32Mem
  rw [toByteArray_write32_read_back]
  unfold wordAt0Mem
  rw [toByteArray_write32_size_of_le
      (base := flipperCtorArgsMem vat cat ilk) (word := solcSourceWord I)
      (off := 0) (baseSize := 224) (finalSize := 224)]
  · omega
  · exact flipperCtorArgsMem_size vat cat ilk hilk
  · rw [flipperCtorArgsMem_size vat cat ilk hilk]
    omega
  · omega

theorem flipperCtorWardsHashMem_read0_64 (I : ExecutionEnv)
    (vat cat : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32) :
    (flipperCtorWardsHashMem I vat cat ilk).readWithPadding 0 64 =
      UInt256.toByteArray (solcSourceWord I) ++ UInt256.toByteArray (⟨0⟩ : UInt256) := by
  rw [byteArray_readWithPadding_split _ 0 32 32 (by omega) (by omega)
    (by norm_num) (by norm_num) (by norm_num)]
  · rw [flipperCtorWardsHashMem_read0 I vat cat ilk hilk,
      flipperCtorWardsHashMem_read32 I vat cat ilk hilk]
  · rw [flipperCtorWardsHashMem_size I vat cat ilk hilk]
    omega

theorem flipperCtorWardsHashSlot (I : ExecutionEnv)
    (vat cat : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((flipperCtorWardsHashMem I vat cat ilk).readWithPadding 0 64))) =
      flipperCtorCallerWardsSlot I := by
  rw [flipperCtorWardsHashMem_read0_64 I vat cat ilk hilk]
  unfold flipperCtorCallerWardsSlot solcMappingSlot
  exact mappingSlot_single (solcSourceWord I) ⟨0⟩

def flipperCtorRuntimeMem (vat cat : AccountAddress) (ilk : List UInt8) (mem : ByteArray) :
    ByteArray :=
  (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk).write 210 mem 0 6386

theorem flipperCtorRuntimeMem_read (vat cat : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) (mem : ByteArray) :
    (flipperCtorRuntimeMem vat cat ilk mem).readWithPadding 0 6386 = flipperBytecode := by
  rw [flipperCtorRuntimeMem]
  rw [write0_read_back_from_gen
    (src := flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk)
    (base := mem) (srcAddr := 210) (len := 6386)]
  · simpa [show 210 + 6386 = 6596 by norm_num] using
      flipperCtorCode_runtime_window vat cat ilk
  · norm_num
  · rw [ByteArray.size_append, flipperCreationBytecode_size,
      flipperCtorArgsTail_size vat cat ilk hilk]
    norm_num
  · norm_num

/-! ## Constructor revert path -/

abbrev flipperCtorLocals (vat cat : AccountAddress) (ilk : List UInt8) : Store :=
  (((∅ : Store).insert "vat_" (.address vat)).insert "cat_" (.address cat)).insert "ilk_"
    (.fixedBytes bytes32Width ilk)

private theorem evalExpr_flipperCtorLocalVat {evm : EVM.State}
    (vat cat : AccountAddress) (ilk : List UInt8) :
    evalExpr? config { contract := contract, locals := flipperCtorLocals vat cat ilk } evm
      (.var "vat_") = .ok (.address vat) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [flipperCtorLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

private theorem evalExpr_flipperCtorLocalCat {evm : EVM.State}
    (vat cat : AccountAddress) (ilk : List UInt8) :
    evalExpr? config { contract := contract, locals := flipperCtorLocals vat cat ilk } evm
      (.var "cat_") = .ok (.address cat) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [flipperCtorLocals, store_get_ne _ _ (by decide), store_get_self]

private theorem evalExpr_flipperCtorLocalIlk {evm : EVM.State}
    (vat cat : AccountAddress) (ilk : List UInt8) :
    evalExpr? config { contract := contract, locals := flipperCtorLocals vat cat ilk } evm
      (.var "ilk_") = .ok (.fixedBytes bytes32Width ilk) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [flipperCtorLocals, store_get_self]

private theorem accountAddress_of_word_val (a : AccountAddress) :
    AccountAddress.ofNat (EVM.word a.val).toNat = a := by
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
  exact accountAddress_roundtrip a

private theorem word_val_addr_canonical (a : AccountAddress) :
    (EVM.word a.val).toNat < EVM.addressModulus := by
  unfold EVM.word EVM.uintN UInt256.toNat EVM.twoPow
  change (a.val % UInt256.size) < EVM.addressModulus
  have hlt : a.val < EVM.addressModulus := by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using a.isLt
  rw [Nat.mod_eq_of_lt (lt_trans hlt (by norm_num [EVM.addressModulus, EVM.twoPow,
    UInt256.size]))]
  exact hlt

theorem assign_flipperCtorBegStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "beg" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩
      (⟨1050000000000000000⟩ : UInt256)
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage begRef (.int defaultBeg) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm begRef =
        .ok { base := "beg", steps := [] } := by
    simp [begRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc ⟨4⟩) (.int defaultBeg) = some evm' := by
    simpa [evm', wordLoc, defaultBeg, uint256Int] using
      storageLocStore_uint256 evm ⟨4⟩ (⟨1050000000000000000⟩ : UInt256)
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨4⟩)
    (hbase := by simpa [begRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

theorem assign_flipperCtorTtlStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "ttl" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
      (setUint48Offset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
        (⟨10800⟩ : UInt256))
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage ttlRef (.int defaultTtl) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm ttlRef =
        .ok { base := "ttl", steps := [] } := by
    simp [ttlRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (uint48Loc ⟨5⟩ ⟨0, by decide⟩ (by decide))
        (.int defaultTtl) = some evm' := by
    simpa [evm', defaultTtl] using
      flipperStorageLocStore_uint48_offset0 evm ⟨5⟩ (⟨10800⟩ : UInt256)
        (by native_decide)
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint48Int)) (loc := uint48Loc ⟨5⟩ ⟨0, by decide⟩ (by decide))
    (hbase := by simpa [ttlRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint48St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

theorem assign_flipperCtorTauStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "tau" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
      (setUint48Offset6Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
        (⟨172800⟩ : UInt256))
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage tauRef (.int defaultTau) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm tauRef =
        .ok { base := "tau", steps := [] } := by
    simp [tauRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (uint48Loc ⟨5⟩ ⟨6, by decide⟩ (by decide))
        (.int defaultTau) = some evm' := by
    simpa [evm', defaultTau] using
      flipperStorageLocStore_uint48_offset6 evm ⟨5⟩ (⟨172800⟩ : UInt256)
        (by native_decide)
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint48Int)) (loc := uint48Loc ⟨5⟩ ⟨6, by decide⟩ (by decide))
    (hbase := by simpa [tauRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint48St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

theorem assign_flipperCtorKicksStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "kicks" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ (⟨0⟩ : UInt256)
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage kicksRef (.int 0) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm kicksRef =
        .ok { base := "kicks", steps := [] } := by
    simp [kicksRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore : storageLocStore evm (wordLoc ⟨6⟩) (.int 0) = some evm' := by
    simpa [evm', wordLoc, uint256Int] using
      storageLocStore_uint256 evm ⟨6⟩ (⟨0⟩ : UInt256)
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨6⟩)
    (hbase := by simpa [kicksRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

private theorem assign_flipperCtorAddressStorage (evm : EVM.State) (locals : Store)
    (ref : StorageRef) (er : EvaledStorageRef) (slot : UInt256) (addrValue : AccountAddress)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot)) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        (EVM.word addrValue.val))
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage ref (.address addrValue) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have hvalue :
      (.address addrValue : Value) =
        .address (AccountAddress.ofNat (EVM.word addrValue.val).toNat) := by
    rw [accountAddress_of_word_val]
  rw [hvalue]
  have hstore :
      storageLocStore evm (addrLoc slot)
          (.address (AccountAddress.ofNat (EVM.word addrValue.val).toNat)) =
        some evm' := by
    simpa [addrLoc, evm'] using
      storageLocStore_address_offset0 evm slot (EVM.word addrValue.val)
        (word_val_addr_canonical addrValue)
  exact assignStorageRef_storage_scalar_value
    (ty := .elem .address) (loc := addrLoc slot)
    (hbase := hbase)
    (her := her)
    (hty := hty)
    (hloc := hloc)
    (hscalar := by trivial)
    (hstore := hstore)

theorem assign_flipperCtorVatStorage (evm : EVM.State) (locals : Store)
    (vat : AccountAddress) (hbase : locals.get? "vat" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
        (EVM.word vat.val))
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage vatRef (.address vat) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  exact assign_flipperCtorAddressStorage evm locals vatRef { base := "vat", steps := [] } ⟨2⟩ vat
    (by simpa [vatRef] using hbase)
    (by simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_flipperCtorCatStorage (evm : EVM.State) (locals : Store)
    (cat : AccountAddress) (hbase : locals.get? "cat" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨7⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩)
        (EVM.word cat.val))
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage catRef (.address cat) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  exact assign_flipperCtorAddressStorage evm locals catRef { base := "cat", steps := [] } ⟨7⟩ cat
    (by simpa [catRef] using hbase)
    (by simp [catRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem valueToWord_flipperIlk (ilk : List UInt8) (hilk : ilk.length = 32) :
    valueToWord (.fixedBytes bytes32Width ilk) = some (flipperIlkWord ilk) := by
  simp [flipperIlkWord, valueToWord, fixedBytesToNat?, fixedBytesValid, fixedBytesSize,
    bytes32Width, hilk]
  rfl

theorem assign_flipperCtorIlkStorage (evm : EVM.State) {locals : Store}
    (ilk : List UInt8) (hilk : ilk.length = 32) (hbase : locals.get? "ilk" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩ (flipperIlkWord ilk)
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage ilkRef (.fixedBytes bytes32Width ilk) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm ilkRef =
        .ok { base := "ilk", steps := [] } := by
    simp [ilkRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (bytes32Loc ⟨3⟩) (.fixedBytes bytes32Width ilk) = some evm' := by
    simpa [evm', bytes32Loc, Reasoning.Theory.bytes32Loc, bytes32Width] using
      storageLocStore_bytes32 evm ⟨3⟩ (flipperIlkWord ilk)
        (.fixedBytes bytes32Width ilk) (valueToWord_flipperIlk ilk hilk)
  exact assignStorageRef_storage_scalar_value
    (ty := .elem (.bytes bytes32Width)) (loc := bytes32Loc ⟨3⟩)
    (hbase := by simpa [ilkRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, bytes32St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hscalar := by trivial)
    (hstore := hstore)

theorem assign_flipperCtorWardsCaller (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "wards" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (wardsRef sender) (.int 1) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm
        (wardsRef sender) =
          .ok { base := "wards", steps := [.mindex (.address evm.executionEnv.source)] } := by
    simp [wardsRef, sender, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      evalExpr?, envValue, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc (wardsSlot (.address evm.executionEnv.source))) (.int 1) =
        some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm
      (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc (wardsSlot (.address evm.executionEnv.source)))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

abbrev flipperCtorAfterBegState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩
    (⟨1050000000000000000⟩ : UInt256)

abbrev flipperCtorAfterTtlState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
    (setUint48Offset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
      (⟨10800⟩ : UInt256))

abbrev flipperCtorAfterTauState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
    (setUint48Offset6Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
      (⟨172800⟩ : UInt256))

abbrev flipperCtorAfterKicksState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ (⟨0⟩ : UInt256)

abbrev flipperCtorAfterVatState (evm : EVM.State) (vat : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
      (EVM.word vat.val))

abbrev flipperCtorAfterCatState (evm : EVM.State) (cat : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨7⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩)
      (EVM.word cat.val))

abbrev flipperCtorAfterIlkState (evm : EVM.State) (ilk : List UInt8) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩ (flipperIlkWord ilk)

abbrev flipperCtorAfterWardsState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩

theorem flipperCtorSolmExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat cat : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) (hwv : I.weiValue = ⟨0⟩) :
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := flipperCtorAfterBegState evm0
    let evm2 := flipperCtorAfterTtlState evm1
    let evm3 := flipperCtorAfterTauState evm2
    let evm4 := flipperCtorAfterKicksState evm3
    let evm5 := flipperCtorAfterVatState evm4 vat
    let evm6 := flipperCtorAfterCatState evm5 cat
    let evm7 := flipperCtorAfterIlkState evm6 ilk
    let evm8 := flipperCtorAfterWardsState evm7
    solmCtorExec config contract
      [.address vat, .address cat, .fixedBytes bytes32Width ilk]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      (.returned { contract := contract, locals := flipperCtorLocals vat cat ilk } evm8 none) := by
  intro evm0 evm1 evm2 evm3 evm4 evm5 evm6 evm7 evm8
  let locals := flipperCtorLocals vat cat ilk
  refine solmCtorExec.intro (evmState := evm0) (argsStore := locals) ?_ rfl ?_ ?_
  · rfl
  · rfl
  · refine ?_
    have hassignBeg :
        assignStorageRef? config { contract := contract, locals := locals } evm0
          .storage begRef (.int defaultBeg) =
            .ok ({ contract := contract, locals := locals }, evm1) := by
      simpa [evm1, flipperCtorAfterBegState] using
        assign_flipperCtorBegStorage evm0 (locals := locals) (by simp [locals, flipperCtorLocals])
    have hassignTtl :
        assignStorageRef? config { contract := contract, locals := locals } evm1
          .storage ttlRef (.int defaultTtl) =
            .ok ({ contract := contract, locals := locals }, evm2) := by
      simpa [evm2, flipperCtorAfterTtlState] using
        assign_flipperCtorTtlStorage evm1 (locals := locals) (by simp [locals, flipperCtorLocals])
    have hassignTau :
        assignStorageRef? config { contract := contract, locals := locals } evm2
          .storage tauRef (.int defaultTau) =
            .ok ({ contract := contract, locals := locals }, evm3) := by
      simpa [evm3, flipperCtorAfterTauState] using
        assign_flipperCtorTauStorage evm2 (locals := locals) (by simp [locals, flipperCtorLocals])
    have hassignKicks :
        assignStorageRef? config { contract := contract, locals := locals } evm3
          .storage kicksRef (.int 0) =
            .ok ({ contract := contract, locals := locals }, evm4) := by
      simpa [evm4, flipperCtorAfterKicksState] using
        assign_flipperCtorKicksStorage evm3 (locals := locals) (by simp [locals, flipperCtorLocals])
    have hassignVat :
        assignStorageRef? config { contract := contract, locals := locals } evm4
          .storage vatRef (.address vat) =
            .ok ({ contract := contract, locals := locals }, evm5) := by
      simpa [evm5, flipperCtorAfterVatState] using
        assign_flipperCtorVatStorage evm4 locals vat (by simp [locals, flipperCtorLocals])
    have hassignCat :
        assignStorageRef? config { contract := contract, locals := locals } evm5
          .storage catRef (.address cat) =
            .ok ({ contract := contract, locals := locals }, evm6) := by
      simpa [evm6, flipperCtorAfterCatState] using
        assign_flipperCtorCatStorage evm5 locals cat (by simp [locals, flipperCtorLocals])
    have hassignIlk :
        assignStorageRef? config { contract := contract, locals := locals } evm6
          .storage ilkRef (.fixedBytes bytes32Width ilk) =
            .ok ({ contract := contract, locals := locals }, evm7) := by
      simpa [evm7, flipperCtorAfterIlkState] using
        assign_flipperCtorIlkStorage evm6 (locals := locals) ilk hilk
          (by simp [locals, flipperCtorLocals])
    have hassignWards :
        assignStorageRef? config { contract := contract, locals := locals } evm7
          .storage (wardsRef sender) (.int 1) =
            .ok ({ contract := contract, locals := locals }, evm8) := by
      simpa [evm8, flipperCtorAfterWardsState] using
        assign_flipperCtorWardsCaller evm7 (locals := locals)
          (by simp [locals, flipperCtorLocals])
    have hblock :
        ExecBlock config { contract := contract, locals := locals } evm0 constructorDecl.body
          (.ok { contract := contract, locals := locals } evm8) := by
      simp only [constructorDecl, nonpayable, List.cons_append, List.nil_append]
      refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
      · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
      refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignBeg) ?_
      refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignTtl) ?_
      refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignTau) ?_
      refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignKicks) ?_
      refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignVat) ?_
      · simpa [locals] using evalExpr_flipperCtorLocalVat (evm := evm4) vat cat ilk
      refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignCat) ?_
      · simpa [locals] using evalExpr_flipperCtorLocalCat (evm := evm5) vat cat ilk
      refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignIlk) ?_
      · simpa [locals] using evalExpr_flipperCtorLocalIlk (evm := evm6) vat cat ilk
      exact ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignWards)
        ExecBlock.nil
    simpa [ExecTransitionBody, contract, constructorDecl, locals, evm0, evm8] using
      ExecFuncBody.execBlockOK hblock

theorem flipperSolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat cat : AccountAddress) (ilk : List UInt8)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract
      [.address vat, .address cat, .fixedBytes bytes32Width ilk]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := flipperCtorLocals vat cat ilk)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl, nonpayable] using
      bodyReverts_nonPayable (cfg := config) (contract := contract)
        (evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
          (Sat256.ofUInt256 g) A I)
        (locals := flipperCtorLocals vat cat ilk) hwv

theorem flipperCtorNonpayableRDrev
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat cat : AccountAddress) (ilk : List UInt8)
    (hcode : I.code = flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk)
    (hperm : I.perm = true) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  let code := flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk
  have rd0 : RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
      ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 := by
    simpa [code] using RD.initState hcode
  have rd5 := evm_run rd0 with [
    raw push1 ⟨128⟩ (by flipper_ctor_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by flipper_ctor_decode) (by evm_ov),
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3)
      (by flipper_ctor_decode) mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd14 := rd5.pushConst (⟨1050000000000000000⟩ : UInt256)
    (width := 8) (op := .PUSH8) (by native_decide : Operation.POp.PUSH8 ≠ .PUSH0)
    (by flipper_ctor_decode) (by evm_ov)
  have rd16 := rd14.push1 ⟨4⟩ (by flipper_ctor_decode) (by evm_ov)
  obtain ⟨_, _, rd17raw⟩ := rd16.sstore hperm (by flipper_ctor_decode)
    (by simp only [List.length_nil]; omega)
  let σBeg := sstoreAccountMap I.codeOwner σ ⟨4⟩ ⟨1050000000000000000⟩
  have rd17 := by
    simpa [code, σBeg] using rd17raw
  have rd20 := evm_run rd17 with [
    raw push1 ⟨5⟩ (by flipper_ctor_decode) (by evm_ov),
    raw dup1 (by flipper_ctor_decode) (by evm_ov)]
  obtain ⟨_, _, rd21raw⟩ := rd20.sload (by flipper_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  let slot5Old := (σBeg.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨5⟩ ⟨0⟩))
  have rd21 := by
    simpa [slot5Old] using rd21raw
  have rd24 := evm_run rd21 with [
    raw push2 ⟨10800⟩ (by flipper_ctor_decode) (by evm_ov)]
  have rd31 := rd24.pushConst (⟨281474976710655⟩ : UInt256)
    (width := 6) (op := .PUSH6) (by native_decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by flipper_ctor_decode) (by evm_ov)
  have rd36 := evm_run rd31 with [
    raw not (by flipper_ctor_decode) (by evm_ov),
    raw swap1 (by flipper_ctor_decode) (by evm_ov),
    raw swap2 (by flipper_ctor_decode) (by evm_ov),
    raw and (by flipper_ctor_decode) (by evm_ov),
    raw lor (by flipper_ctor_decode) (by evm_ov)]
  have rd43 := rd36.pushConst (⟨281474976710655⟩ : UInt256)
    (width := 6) (op := .PUSH6) (by native_decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by flipper_ctor_decode) (by evm_ov)
  have rd48 := evm_run rd43 with [
    raw push1 ⟨48⟩ (by flipper_ctor_decode) (by evm_ov),
    raw shl (by flipper_ctor_decode) (by evm_ov),
    raw not (by flipper_ctor_decode) (by evm_ov),
    raw and (by flipper_ctor_decode) (by evm_ov)]
  have rd58 := rd48.pushConst (⟨0x02a300000000000000⟩ : UInt256)
    (width := 9) (op := .PUSH9) (by native_decide : Operation.POp.PUSH9 ≠ .PUSH0)
    (by flipper_ctor_decode) (by evm_ov)
  have rd60 := evm_run rd58 with [
    raw lor (by flipper_ctor_decode) (by evm_ov),
    raw swap1 (by flipper_ctor_decode) (by evm_ov)]
  let slot5New :=
    UInt256.lor (⟨0x02a300000000000000⟩ : UInt256)
      (UInt256.land
        (UInt256.lor (UInt256.land slot5Old (UInt256.lnot ⟨281474976710655⟩))
          ⟨10800⟩)
        (UInt256.lnot (UInt256.shiftLeft (⟨281474976710655⟩ : UInt256) ⟨48⟩)))
  obtain ⟨_, _, rd61raw⟩ := rd60.sstore hperm (by flipper_ctor_decode)
    (by simp only [List.length_nil]; omega)
  let σPacked := sstoreAccountMap I.codeOwner σBeg ⟨5⟩ slot5New
  have rd61 := by
    simpa [slot5New, σPacked] using rd61raw
  have rd65 := evm_run rd61 with [
    raw push1 ⟨0⟩ (by flipper_ctor_decode) (by evm_ov),
    raw push1 ⟨6⟩ (by flipper_ctor_decode) (by evm_ov)]
  obtain ⟨_, _, rd66raw⟩ := rd65.sstore hperm (by flipper_ctor_decode)
    (by simp only [List.length_nil]; omega)
  let σKicks := sstoreAccountMap I.codeOwner σPacked ⟨6⟩ ⟨0⟩
  have rd66 := by
    simpa [σKicks] using rd66raw
  have rd69 := evm_run rd66 with [
    raw callvalue (by flipper_ctor_decode) (by evm_ov),
    raw dup1 (by flipper_ctor_decode) (by evm_ov),
    raw iszero (by flipper_ctor_decode) (by evm_ov)]
  have rd72 := rd69.push2 ⟨77⟩ (by flipper_ctor_decode) (by evm_ov)
  have rd73 := rd72.jumpiNT (by flipper_ctor_decode) (isZero_eq_zero_of_ne hwv)
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [code] using
    RD.uniswapPush1Dup1Revert0 (code := code) (ee := I) (g := g)
      (s0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) rd73
      (by flipper_ctor_decode) (by flipper_ctor_decode) (by flipper_ctor_decode)
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem flipperCtorPackedWord_eq (old : UInt256) :
    UInt256.lor (⟨0x02a300000000000000⟩ : UInt256)
      (UInt256.land
        (UInt256.lor (UInt256.land old (UInt256.lnot ⟨281474976710655⟩))
          ⟨10800⟩)
        (UInt256.lnot (UInt256.shiftLeft (⟨281474976710655⟩ : UInt256) ⟨48⟩))) =
      setUint48Offset6Word
        (setUint48Offset0Word old (⟨10800⟩ : UInt256))
        (⟨172800⟩ : UInt256) := by
  unfold setUint48Offset0Word setUint48Offset6Word
  have httl :
      UInt256.land (⟨10800⟩ : UInt256) (⟨281474976710655⟩ : UInt256) =
        ⟨10800⟩ := by
    native_decide
  have htau :
      UInt256.shiftLeft
        (UInt256.land (⟨172800⟩ : UInt256) (⟨281474976710655⟩ : UInt256)) ⟨48⟩ =
        (⟨0x02a300000000000000⟩ : UInt256) := by
    native_decide
  simp only [uint48Mask]
  rw [httl, htau]
  exact u256_lor_comm _ _

theorem flipperCtorCallerWardsSlot_eq (I : ExecutionEnv) :
    wardsSlot (.address I.source) = flipperCtorCallerWardsSlot I := by
  unfold wardsSlot mapSlot flipperCtorCallerWardsSlot solcMappingSlot solcSourceWord
  rw [keyValueToWord_address]

theorem flipperCtorPackedAccountMapEquiv {σBeg : AccountMap} {evm1s : EVM.State}
    {I : ExecutionEnv}
    (hAccountsBeg : accountMapEquiv σBeg evm1s.accountMap)
    (hExec : evm1s.executionEnv = I) :
    let slot5Old := solcSlotWord σBeg I ⟨5⟩
    let slot5New :=
      UInt256.lor (⟨0x02a300000000000000⟩ : UInt256)
        (UInt256.land
          (UInt256.lor (UInt256.land slot5Old (UInt256.lnot ⟨281474976710655⟩))
            ⟨10800⟩)
          (UInt256.lnot (UInt256.shiftLeft (⟨281474976710655⟩ : UInt256) ⟨48⟩)))
    let σPacked := sstoreAccountMap I.codeOwner σBeg ⟨5⟩ slot5New
    let evm2s := flipperCtorAfterTtlState evm1s
    let evm3s := flipperCtorAfterTauState evm2s
    accountMapEquiv σPacked evm3s.accountMap := by
  intro slot5Old slot5New σPacked evm2s evm3s
  by_cases hmissing : σBeg.find? I.codeOwner = none
  · have hmissingSolm : evm1s.accountMap.find? I.codeOwner = none :=
      accountMapEquiv_find?_none hAccountsBeg hmissing
    have hmissingSolmOwner :
        evm1s.accountMap.find? evm1s.executionEnv.codeOwner = none := by
      rw [hExec]
      exact hmissingSolm
    have hevm2 : evm2s = evm1s := by
      simp [evm2s, flipperCtorAfterTtlState, storageStore_absent, hmissingSolmOwner]
    have hevm3 : evm3s = evm1s := by
      simp [evm3s, flipperCtorAfterTauState, hevm2, storageStore_absent,
        hmissingSolmOwner]
    simpa [σPacked, sstoreAccountMap_absent_same hmissing, hevm3] using hAccountsBeg
  · cases hfind : σBeg.find? I.codeOwner with
    | none => exact False.elim (hmissing hfind)
    | some acc =>
        obtain ⟨accSolm, hfindSolm⟩ :=
          accountMapEquiv_find?_some_exists hAccountsBeg hfind
        have hfindSolmOwner :
            evm1s.accountMap.find? evm1s.executionEnv.codeOwner = some accSolm := by
          rw [hExec]
          exact hfindSolm
        have hOld5 :
            slot5Old = Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨5⟩ := by
          simpa [slot5Old, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
            Account.lookupStorage, hExec] using
            accountMapEquiv_storage_findD hAccountsBeg I.codeOwner ⟨5⟩ ⟨0⟩
        let ttlWord :=
          setUint48Offset0Word
            (Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨5⟩)
            (⟨10800⟩ : UInt256)
        have hTtlLoad :
            Solm.EVM.storageLoad evm2s evm2s.executionEnv.codeOwner ⟨5⟩ =
              setUint48Offset0Word slot5Old (⟨10800⟩ : UInt256) := by
          have hload := storageLoad_storageStore_same_present evm1s
            evm1s.executionEnv.codeOwner hfindSolmOwner ⟨5⟩ ttlWord
          simpa [evm2s, flipperCtorAfterTtlState, ttlWord, hOld5,
            storageStore_executionEnv] using hload
        have hPackedVal :
            slot5New =
              setUint48Offset6Word
                (Solm.EVM.storageLoad evm2s evm2s.executionEnv.codeOwner ⟨5⟩)
                (⟨172800⟩ : UInt256) := by
          rw [hTtlLoad]
          exact flipperCtorPackedWord_eq slot5Old
        have hbase :=
          accountMapEquiv_sstoreAccountMap I.codeOwner ⟨5⟩ slot5New hAccountsBeg
        have hself :=
          accountMapEquiv_sstoreAccountMap_self_update evm1s.accountMap I.codeOwner ⟨5⟩
            ttlWord slot5New
        have hpacked := accountMapEquiv.trans hbase hself
        simpa [σPacked, evm2s, evm3s, flipperCtorAfterTtlState,
          flipperCtorAfterTauState, ttlWord, hPackedVal, hExec, storageStore_accountMap,
          storageStore_executionEnv] using hpacked

set_option maxHeartbeats 1000000 in
theorem flipperCtorInitReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat cat : AccountAddress) (ilk : List UInt8)
    (hcode : I.code = flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk)
    (hperm : I.perm = true) :
    let σBeg := sstoreAccountMap I.codeOwner σ ⟨4⟩ ⟨1050000000000000000⟩
    let slot5Old := solcSlotWord σBeg I ⟨5⟩
    let slot5New :=
      UInt256.lor (⟨0x02a300000000000000⟩ : UInt256)
        (UInt256.land
          (UInt256.lor (UInt256.land slot5Old (UInt256.lnot ⟨281474976710655⟩))
            ⟨10800⟩)
          (UInt256.lnot (UInt256.shiftLeft (⟨281474976710655⟩ : UInt256) ⟨48⟩)))
    let σPacked := sstoreAccountMap I.codeOwner σBeg ⟨5⟩ slot5New
    let σKicks := sstoreAccountMap I.codeOwner σPacked ⟨6⟩ ⟨0⟩
    ∃ k C,
      RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨66⟩ []
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (createdAccounts, σKicks) k C := by
  intro σBeg slot5Old slot5New σPacked σKicks
  let code := flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk
  have rd0 : RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
      ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 := by
    simpa [code] using RD.initState hcode
  have rd5 := evm_run rd0 with [
    raw push1 ⟨128⟩ (by flipper_ctor_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by flipper_ctor_decode) (by evm_ov),
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3)
      (by flipper_ctor_decode) mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov)]
  have rd14 := rd5.pushConst (⟨1050000000000000000⟩ : UInt256)
    (width := 8) (op := .PUSH8) (by native_decide : Operation.POp.PUSH8 ≠ .PUSH0)
    (by flipper_ctor_decode) (by evm_ov)
  have rd16 := rd14.push1 ⟨4⟩ (by flipper_ctor_decode) (by evm_ov)
  obtain ⟨_, _, rd17raw⟩ := rd16.sstore hperm (by flipper_ctor_decode)
    (by simp only [List.length_nil]; omega)
  have rd17 := by
    simpa [code, σBeg] using rd17raw
  have rd20 := evm_run rd17 with [
    raw push1 ⟨5⟩ (by flipper_ctor_decode) (by evm_ov),
    raw dup1 (by flipper_ctor_decode) (by evm_ov)]
  obtain ⟨_, _, rd21raw⟩ := rd20.sload (by flipper_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd21 := by
    simpa [slot5Old, solcSlotWord] using rd21raw
  have rd24 := evm_run rd21 with [
    raw push2 ⟨10800⟩ (by flipper_ctor_decode) (by evm_ov)]
  have rd31 := rd24.pushConst (⟨281474976710655⟩ : UInt256)
    (width := 6) (op := .PUSH6) (by native_decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by flipper_ctor_decode) (by evm_ov)
  have rd36 := evm_run rd31 with [
    raw not (by flipper_ctor_decode) (by evm_ov),
    raw swap1 (by flipper_ctor_decode) (by evm_ov),
    raw swap2 (by flipper_ctor_decode) (by evm_ov),
    raw and (by flipper_ctor_decode) (by evm_ov),
    raw lor (by flipper_ctor_decode) (by evm_ov)]
  have rd43 := rd36.pushConst (⟨281474976710655⟩ : UInt256)
    (width := 6) (op := .PUSH6) (by native_decide : Operation.POp.PUSH6 ≠ .PUSH0)
    (by flipper_ctor_decode) (by evm_ov)
  have rd48 := evm_run rd43 with [
    raw push1 ⟨48⟩ (by flipper_ctor_decode) (by evm_ov),
    raw shl (by flipper_ctor_decode) (by evm_ov),
    raw not (by flipper_ctor_decode) (by evm_ov),
    raw and (by flipper_ctor_decode) (by evm_ov)]
  have rd58 := rd48.pushConst (⟨0x02a300000000000000⟩ : UInt256)
    (width := 9) (op := .PUSH9) (by native_decide : Operation.POp.PUSH9 ≠ .PUSH0)
    (by flipper_ctor_decode) (by evm_ov)
  have rd60 := evm_run rd58 with [
    raw lor (by flipper_ctor_decode) (by evm_ov),
    raw swap1 (by flipper_ctor_decode) (by evm_ov)]
  obtain ⟨_, _, rd61raw⟩ := rd60.sstore hperm (by flipper_ctor_decode)
    (by simp only [List.length_nil]; omega)
  have rd61 := by
    simpa [slot5New, σPacked] using rd61raw
  have rd65 := evm_run rd61 with [
    raw push1 ⟨0⟩ (by flipper_ctor_decode) (by evm_ov),
    raw push1 ⟨6⟩ (by flipper_ctor_decode) (by evm_ov)]
  obtain ⟨k66, C66, rd66raw⟩ := rd65.sstore hperm (by flipper_ctor_decode)
    (by simp only [List.length_nil]; omega)
  refine ⟨k66, C66, ?_⟩
  convert rd66raw using 1
  · simp [σKicks, σPacked, σBeg, slot5New, slot5Old, solcSlotWord, u256_land_comm]

set_option maxHeartbeats 1000000 in
private theorem flipperCtorValueGuardReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σKicks : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat cat : AccountAddress) (ilk : List UInt8) {k C : ℕ}
    (hwv : I.weiValue = ⟨0⟩)
    (rd66 :
      RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨66⟩ []
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (createdAccounts, σKicks) k C) :
    ∃ k' C', RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨79⟩ []
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (createdAccounts, σKicks) k' C' := by
  let code := flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
    ⟨66⟩ [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (createdAccounts, σKicks)
    k C at rd66
  have rd72 := evm_run rd66 with [
    raw callvalue (by flipper_ctor_decode) (by evm_ov),
    raw dup1 (by flipper_ctor_decode) (by evm_ov),
    raw iszero (by flipper_ctor_decode) (by evm_ov),
    raw push2 ⟨77⟩ (by flipper_ctor_decode) (by evm_ov)]
  have rd77 := rd72.jumpiT (by flipper_ctor_decode)
    (by rw [hwv]; decide) (by flipper_ctor_jump_dest) (by evm_ov)
  have rd79 := evm_run rd77 with [
    raw jumpdest (by flipper_ctor_decode) (by evm_ov),
    raw pop (by flipper_ctor_decode) (by evm_ov)]
  exact ⟨_, _, by simpa [code] using rd79⟩

set_option maxHeartbeats 1000000 in
private theorem flipperCtorArgsSizeReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σKicks : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat cat : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32) {k C : ℕ}
    (rd79 :
      RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨79⟩ []
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (createdAccounts, σKicks) k C) :
    ∃ k' C', RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨87⟩
      [⟨96⟩, ⟨128⟩] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (createdAccounts, σKicks) k' C' := by
  let code := flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
    ⟨79⟩ [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (createdAccounts, σKicks)
    k C at rd79
  have rd87 := evm_run rd79 with [
    raw push1 ⟨64⟩ (by flipper_ctor_decode) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by flipper_ctor_decode) mem_cost
      solcFreePtrMem_mload64 (by decide) (by evm_ov),
    raw push2 ⟨6596⟩ (by flipper_ctor_decode) (by evm_ov),
    raw codesize (by flipper_ctor_decode) (by evm_ov),
    raw sub (by flipper_ctor_decode) (by evm_ov)]
  exact ⟨_, _, by
    simpa [code, ByteArray.size_append, flipperCreationBytecode_size,
      flipperCtorArgsTail_size vat cat ilk hilk] using rd87⟩

set_option maxHeartbeats 1000000 in
private theorem flipperCtorArgsCodecopyReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σKicks : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat cat : AccountAddress) (ilk : List UInt8) {k C : ℕ}
    (rd87 :
      RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨87⟩
        [⟨96⟩, ⟨128⟩] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (createdAccounts, σKicks) k C) :
    ∃ k' C', RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨93⟩
      [⟨96⟩, ⟨128⟩] (flipperCtorCopiedMem vat cat ilk) (UInt256.ofNat 7)
      ByteArray.empty (createdAccounts, σKicks) k' C' := by
  let code := flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
    ⟨87⟩ [⟨96⟩, ⟨128⟩] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
    (createdAccounts, σKicks) k C at rd87
  have hcopy : code.write 6596 solcFreePtrMem 128 96 = flipperCtorCopiedMem vat cat ilk := by
    rfl
  have rd93 := evm_run rd87 with [
    raw dup1 (by flipper_ctor_decode) (by evm_ov),
    raw push2 ⟨6596⟩ (by flipper_ctor_decode) (by evm_ov),
    raw dup4 (by flipper_ctor_decode) (by evm_ov),
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 3).toNat 128 96)) -
        Cₘ (UInt256.ofNat 3))
      (flipperCtorCopiedMem vat cat ilk) (UInt256.ofNat 7)
      (by flipper_ctor_decode) mem_cost hcopy (by decide) (by evm_ov)]
  exact ⟨_, _, by simpa [code] using rd93⟩

set_option maxHeartbeats 1000000 in
private theorem flipperCtorArgsFreePtrReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σKicks : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat cat : AccountAddress) (ilk : List UInt8) {k C : ℕ}
    (rd93 :
      RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨93⟩
        [⟨96⟩, ⟨128⟩] (flipperCtorCopiedMem vat cat ilk) (UInt256.ofNat 7)
        ByteArray.empty (createdAccounts, σKicks) k C) :
    ∃ k' C', RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨99⟩
      [⟨96⟩, ⟨128⟩] (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7)
      ByteArray.empty (createdAccounts, σKicks) k' C' := by
  let code := flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
    ⟨93⟩ [⟨96⟩, ⟨128⟩] (flipperCtorCopiedMem vat cat ilk) (UInt256.ofNat 7)
    ByteArray.empty (createdAccounts, σKicks) k C at rd93
  have hmstore :
      (UInt256.toByteArray ⟨224⟩).write 0 (flipperCtorCopiedMem vat cat ilk) 64 32 =
        flipperCtorArgsMem vat cat ilk := by
    rfl
  have rd99 := evm_run rd93 with [
    raw dup2 (by flipper_ctor_decode) (by evm_ov),
    raw dup2 (by flipper_ctor_decode) (by evm_ov),
    raw add (by flipper_ctor_decode) (by evm_ov),
    raw push1 ⟨64⟩ (by flipper_ctor_decode) (by evm_ov),
    raw mstore 0 (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7)
      (by flipper_ctor_decode) mem_cost hmstore (by decide) (by evm_ov)]
  exact ⟨_, _, by simpa [code] using rd99⟩

set_option maxHeartbeats 1000000 in
private theorem flipperCtorArgsGuardReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σKicks : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat cat : AccountAddress) (ilk : List UInt8) {k C : ℕ}
    (rd99 :
      RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨99⟩
        [⟨96⟩, ⟨128⟩] (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7)
        ByteArray.empty (createdAccounts, σKicks) k C) :
    ∃ k' C', RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨107⟩
      [⟨112⟩, ⟨1⟩, ⟨96⟩, ⟨128⟩]
      (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, σKicks) k' C' := by
  let code := flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
    ⟨99⟩ [⟨96⟩, ⟨128⟩] (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7)
    ByteArray.empty (createdAccounts, σKicks) k C at rd99
  have rd107 := evm_run rd99 with [
    raw push1 ⟨96⟩ (by flipper_ctor_decode) (by evm_ov),
    raw dup2 (by flipper_ctor_decode) (by evm_ov),
    raw lt (by flipper_ctor_decode) (by evm_ov),
    raw iszero (by flipper_ctor_decode) (by evm_ov),
    raw push2 ⟨112⟩ (by flipper_ctor_decode) (by evm_ov)]
  exact ⟨_, _, by
    simpa [code,
      show ((⟨99⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 3) = ⟨107⟩ from by native_decide,
      show (UInt256.lt (⟨96⟩ : UInt256) ⟨96⟩).isZero = ⟨1⟩ from by native_decide]
      using rd107⟩

set_option maxHeartbeats 1000000 in
private theorem flipperCtorArgsLoadReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σKicks : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat cat : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32) {k C : ℕ}
    (rd112 :
      RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨112⟩
        [⟨96⟩, ⟨128⟩] (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7)
        ByteArray.empty (createdAccounts, σKicks) k C) :
    ∃ k' C', RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨128⟩
      [flipperIlkWord ilk, EVM.word cat.val, ⟨32⟩, EVM.word vat.val, ⟨64⟩]
      (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, σKicks) k' C' := by
  let code := flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
    ⟨112⟩ [⟨96⟩, ⟨128⟩] (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7)
    ByteArray.empty (createdAccounts, σKicks) k C at rd112
  have hmloadVat := flipperCtorArgsMem_mload_vat vat cat ilk hilk
  have hmloadCat := flipperCtorArgsMem_mload_cat vat cat ilk hilk
  have hmloadIlk := flipperCtorArgsMem_mload_ilk vat cat ilk hilk
  have rd128 := evm_run rd112 with [
    raw jumpdest (by flipper_ctor_decode) (by evm_ov),
    raw pop (by flipper_ctor_decode) (by evm_ov),
    raw dup1 (by flipper_ctor_decode) (by evm_ov),
    raw mload 0 (EVM.word vat.val) (UInt256.ofNat 7)
      (by flipper_ctor_decode) mem_cost hmloadVat (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by flipper_ctor_decode) (by evm_ov),
    raw dup1 (by flipper_ctor_decode) (by evm_ov),
    raw dup4 (by flipper_ctor_decode) (by evm_ov),
    raw add (by flipper_ctor_decode) (by evm_ov),
    raw mload 0 (EVM.word cat.val) (UInt256.ofNat 7)
      (by flipper_ctor_decode) mem_cost hmloadCat (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by flipper_ctor_decode) (by evm_ov),
    raw swap4 (by flipper_ctor_decode) (by evm_ov),
    raw dup5 (by flipper_ctor_decode) (by evm_ov),
    raw add (by flipper_ctor_decode) (by evm_ov),
    raw mload 0 (flipperIlkWord ilk) (UInt256.ofNat 7)
      (by flipper_ctor_decode) mem_cost hmloadIlk (by decide) (by evm_ov)]
  exact ⟨_, _, by simpa [code] using rd128⟩

set_option maxHeartbeats 1000000 in
theorem flipperCtorArgsReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σKicks : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat cat : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32)
    (hwv : I.weiValue = ⟨0⟩) {k C : ℕ}
    (rd66 :
      RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨66⟩ []
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (createdAccounts, σKicks) k C) :
    ∃ k' C', RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨128⟩
      [flipperIlkWord ilk, EVM.word cat.val, ⟨32⟩, EVM.word vat.val, ⟨64⟩]
      (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, σKicks) k' C' := by
  obtain ⟨_, _, rd79⟩ := flipperCtorValueGuardReach vat cat ilk hwv rd66
  obtain ⟨_, _, rd87⟩ := flipperCtorArgsSizeReach vat cat ilk hilk rd79
  obtain ⟨_, _, rd93⟩ := flipperCtorArgsCodecopyReach vat cat ilk rd87
  obtain ⟨_, _, rd99⟩ := flipperCtorArgsFreePtrReach vat cat ilk rd93
  obtain ⟨_, _, rd107⟩ := flipperCtorArgsGuardReach vat cat ilk rd99
  have rd112 := rd107.jumpiT (by flipper_ctor_decode)
    (by native_decide) (by flipper_ctor_jump_dest) (by evm_ov)
  exact flipperCtorArgsLoadReach vat cat ilk hilk (by simpa using rd112)

set_option maxHeartbeats 1000000 in
theorem flipperCtorVatStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σKicks σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat cat : AccountAddress) (ilk : List UInt8) {k C : ℕ}
    (hperm : I.perm = true)
    (rd128 :
      RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨128⟩
        [flipperIlkWord ilk, EVM.word cat.val, ⟨32⟩, EVM.word vat.val, ⟨64⟩]
        (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σKicks) k C) :
    ∃ k' C', RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨159⟩
      [UInt256.lnot solcAddrMask, flipperIlkWord ilk, EVM.word cat.val, ⟨32⟩,
        solcAddrMask, ⟨64⟩]
      (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σKicks ⟨2⟩
          (setAddressOffset0Word (solcSlotWord σKicks I ⟨2⟩) (EVM.word vat.val))) k' C' := by
  let code := flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨128⟩
        [flipperIlkWord ilk, EVM.word cat.val, ⟨32⟩, EVM.word vat.val, ⟨64⟩]
        (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σKicks) k C at rd128
  have rdBeforeSload := evm_run rd128 with [
    raw push1 ⟨2⟩ (by flipper_ctor_decode) (by evm_ov),
    raw dup1 (by flipper_ctor_decode) (by evm_ov)]
  obtain ⟨_, _, rd131⟩ := rdBeforeSload.sload (by flipper_ctor_decode) (by evm_ov)
  have rdBeforeStore := evm_run rd131 with [
    raw push1 ⟨1⟩ (by flipper_ctor_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by flipper_ctor_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by flipper_ctor_decode) (by evm_ov),
    raw shl (by flipper_ctor_decode) (by evm_ov),
    raw sub (by flipper_ctor_decode) (by evm_ov),
    raw swap6 (by flipper_ctor_decode) (by evm_ov),
    raw dup7 (by flipper_ctor_decode) (by evm_ov),
    raw and (by flipper_ctor_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by flipper_ctor_decode) (by evm_ov),
    raw push1 ⟨1⟩ (by flipper_ctor_decode) (by evm_ov),
    raw push1 ⟨160⟩ (by flipper_ctor_decode) (by evm_ov),
    raw shl (by flipper_ctor_decode) (by evm_ov),
    raw sub (by flipper_ctor_decode) (by evm_ov),
    raw not (by flipper_ctor_decode) (by evm_ov),
    raw swap2 (by flipper_ctor_decode) (by evm_ov),
    raw dup3 (by flipper_ctor_decode) (by evm_ov),
    raw and (by flipper_ctor_decode) (by evm_ov),
    raw lor (by flipper_ctor_decode) (by evm_ov),
    raw swap1 (by flipper_ctor_decode) (by evm_ov),
    raw swap2 (by flipper_ctor_decode) (by evm_ov)]
  have hload :
      (σKicks.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨2⟩ ⟨0⟩)) =
        solcSlotWord σKicks I ⟨2⟩ := by
    rfl
  rw [hload] at rdBeforeStore
  have hvatMask : UInt256.land (EVM.word vat.val) solcAddrMask = EVM.word vat.val := by
    exact solcAddrMask_clean (word_val_addr_canonical vat)
  have hword :
      UInt256.lor (UInt256.land (EVM.word vat.val) solcAddrMask)
          (UInt256.land (solcSlotWord σKicks I ⟨2⟩) (UInt256.lnot solcAddrMask)) =
        setAddressOffset0Word (solcSlotWord σKicks I ⟨2⟩) (EVM.word vat.val) := by
    calc
      UInt256.lor (UInt256.land (EVM.word vat.val) solcAddrMask)
          (UInt256.land (solcSlotWord σKicks I ⟨2⟩) (UInt256.lnot solcAddrMask)) =
          UInt256.lor (UInt256.land (solcSlotWord σKicks I ⟨2⟩) (UInt256.lnot solcAddrMask))
            (UInt256.land (EVM.word vat.val) solcAddrMask) := by
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (solcSlotWord σKicks I ⟨2⟩) (EVM.word vat.val) := by
            rfl
  obtain ⟨k', C', rd159⟩ := rdBeforeStore.sstore hperm (by flipper_ctor_decode) (by evm_ov)
  have hpc159 :
      (⟨128⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨159⟩ := by
    native_decide
  rw [hpc159] at rd159
  have hwordStore :
      UInt256.lor
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σKicks I ⟨2⟩))
          (UInt256.land solcAddrMask (EVM.word vat.val)) =
        setAddressOffset0Word (solcSlotWord σKicks I ⟨2⟩) (EVM.word vat.val) := by
    calc
      UInt256.lor
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σKicks I ⟨2⟩))
          (UInt256.land solcAddrMask (EVM.word vat.val)) =
          UInt256.lor
            (UInt256.land (solcSlotWord σKicks I ⟨2⟩) (UInt256.lnot solcAddrMask))
            (UInt256.land (EVM.word vat.val) solcAddrMask) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) (solcSlotWord σKicks I ⟨2⟩),
              u256_land_comm solcAddrMask (EVM.word vat.val)]
      _ = UInt256.lor
            (UInt256.land (solcSlotWord σKicks I ⟨2⟩) (UInt256.lnot solcAddrMask))
            (EVM.word vat.val) := by
            rw [hvatMask]
      _ = setAddressOffset0Word (solcSlotWord σKicks I ⟨2⟩) (EVM.word vat.val) := by
            unfold setAddressOffset0Word
            rw [hvatMask]
  exact ⟨k', C', by
    simpa [code, solcSlotWord, setAddressOffset0Word, hwordStore, hvatMask,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide] using rd159⟩

set_option maxHeartbeats 1000000 in
theorem flipperCtorCatStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σVat σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat cat : AccountAddress) (ilk : List UInt8) {k C : ℕ}
    (hperm : I.perm = true)
    (rd159 :
      RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨159⟩
        [UInt256.lnot solcAddrMask, flipperIlkWord ilk, EVM.word cat.val, ⟨32⟩,
          solcAddrMask, ⟨64⟩]
        (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σVat) k C) :
    ∃ k' C', RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨175⟩
      [⟨32⟩, flipperIlkWord ilk, ⟨64⟩]
      (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σVat ⟨7⟩
          (setAddressOffset0Word (solcSlotWord σVat I ⟨7⟩) (EVM.word cat.val)))
      k' C' := by
  let code := flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨159⟩
        [UInt256.lnot solcAddrMask, flipperIlkWord ilk, EVM.word cat.val, ⟨32⟩,
          solcAddrMask, ⟨64⟩]
        (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σVat) k C at rd159
  have rdBeforeSload := evm_run rd159 with [
    raw push1 ⟨7⟩ (by flipper_ctor_decode) (by evm_ov),
    raw dup1 (by flipper_ctor_decode) (by evm_ov)]
  obtain ⟨_, _, rd162⟩ := rdBeforeSload.sload (by flipper_ctor_decode) (by evm_ov)
  have rdBeforeStore := evm_run rd162 with [
    raw swap6 (by flipper_ctor_decode) (by evm_ov),
    raw swap1 (by flipper_ctor_decode) (by evm_ov),
    raw swap4 (by flipper_ctor_decode) (by evm_ov),
    raw and (by flipper_ctor_decode) (by evm_ov),
    raw swap5 (by flipper_ctor_decode) (by evm_ov),
    raw and (by flipper_ctor_decode) (by evm_ov),
    raw swap4 (by flipper_ctor_decode) (by evm_ov),
    raw swap1 (by flipper_ctor_decode) (by evm_ov),
    raw swap4 (by flipper_ctor_decode) (by evm_ov),
    raw lor (by flipper_ctor_decode) (by evm_ov),
    raw swap1 (by flipper_ctor_decode) (by evm_ov)]
  have hload :
      (σVat.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨7⟩ ⟨0⟩)) =
        solcSlotWord σVat I ⟨7⟩ := by
    rfl
  rw [hload] at rdBeforeStore
  have hcatMask : UInt256.land (EVM.word cat.val) solcAddrMask = EVM.word cat.val := by
    exact solcAddrMask_clean (word_val_addr_canonical cat)
  have hword :
      UInt256.lor (UInt256.land (solcSlotWord σVat I ⟨7⟩) (UInt256.lnot solcAddrMask))
          (UInt256.land (EVM.word cat.val) solcAddrMask) =
        setAddressOffset0Word (solcSlotWord σVat I ⟨7⟩) (EVM.word cat.val) := by
    rfl
  obtain ⟨k', C', rd175⟩ := rdBeforeStore.sstore hperm (by flipper_ctor_decode) (by evm_ov)
  exact ⟨k', C', by
    simpa [code, solcSlotWord, setAddressOffset0Word, hword, hcatMask] using rd175⟩

set_option maxHeartbeats 1000000 in
theorem flipperCtorIlkStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σCat σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat cat : AccountAddress) (ilk : List UInt8) {k C : ℕ}
    (hperm : I.perm = true)
    (rd175 :
      RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨175⟩
        [⟨32⟩, flipperIlkWord ilk, ⟨64⟩]
        (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σCat) k C) :
    ∃ k' C', RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨181⟩
      [⟨32⟩, ⟨64⟩]
      (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σCat ⟨3⟩ (flipperIlkWord ilk))
      k' C' := by
  let code := flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨175⟩
        [⟨32⟩, flipperIlkWord ilk, ⟨64⟩]
        (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σCat) k C at rd175
  have rdBeforeStore := evm_run rd175 with [
    raw push1 ⟨3⟩ (by flipper_ctor_decode) (by evm_ov),
    raw swap2 (by flipper_ctor_decode) (by evm_ov),
    raw swap1 (by flipper_ctor_decode) (by evm_ov),
    raw swap2 (by flipper_ctor_decode) (by evm_ov)]
  obtain ⟨k', C', rd181⟩ := rdBeforeStore.sstore hperm (by flipper_ctor_decode) (by evm_ov)
  exact ⟨k', C', by simpa [code] using rd181⟩

set_option maxHeartbeats 1000000 in
theorem flipperCtorWardsStoreReach
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σIlk σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat cat : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32) {k C : ℕ}
    (hperm : I.perm = true)
    (rd181 :
      RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨181⟩
        [⟨32⟩, ⟨64⟩]
        (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σIlk) k C) :
    ∃ k' C', RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨196⟩ []
      (flipperCtorWardsHashMem I vat cat ilk) (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, sstoreAccountMap I.codeOwner σIlk (flipperCtorCallerWardsSlot I) ⟨1⟩)
      k' C' := by
  let code := flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨181⟩
        [⟨32⟩, ⟨64⟩]
        (flipperCtorArgsMem vat cat ilk) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σIlk) k C at rd181
  have rdBeforeHash := evm_run rd181 with [
    raw caller (by flipper_ctor_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by flipper_ctor_decode) (by evm_ov),
    raw swap1 (by flipper_ctor_decode) (by evm_ov),
    raw dup2 (by flipper_ctor_decode) (by evm_ov),
    raw mstore 0 (wordAt0Mem (solcSourceWord I) (flipperCtorArgsMem vat cat ilk))
      (UInt256.ofNat 7) (by flipper_ctor_decode) mem_cost (by rfl) (by decide)
      (by evm_ov),
    raw swap1 (by flipper_ctor_decode) (by evm_ov),
    raw dup2 (by flipper_ctor_decode) (by evm_ov),
    raw swap1 (by flipper_ctor_decode) (by evm_ov),
    raw mstore 0 (flipperCtorWardsHashMem I vat cat ilk)
      (UInt256.ofNat 7) (by flipper_ctor_decode) mem_cost (by rfl) (by decide)
      (by evm_ov)]
  have hslot := flipperCtorWardsHashSlot I vat cat ilk hilk
  have rdSlot := rdBeforeHash.keccak256 0 (flipperCtorCallerWardsSlot I) (UInt256.ofNat 7)
    (by flipper_ctor_decode) mem_cost hslot (by decide) (by evm_ov)
  have rdBeforeStore := evm_run rdSlot with [
    raw push1 ⟨1⟩ (by flipper_ctor_decode) (by evm_ov),
    raw swap1 (by flipper_ctor_decode) (by evm_ov)]
  obtain ⟨k', C', rd196⟩ := rdBeforeStore.sstore hperm (by flipper_ctor_decode) (by evm_ov)
  exact ⟨k', C', by simpa [code] using rd196⟩

set_option maxHeartbeats 1000000 in
theorem flipperCtorReturnRuntime
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ σFinal : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    {k C : ℕ}
    (vat cat : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32)
    (rd196 :
      RD (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨196⟩ []
        (flipperCtorWardsHashMem I vat cat ilk) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σFinal) k C) :
    RDret (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts, σFinal) flipperBytecode := by
  let code := flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk
  change RD code I g (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨196⟩ []
        (flipperCtorWardsHashMem I vat cat ilk) (UInt256.ofNat 7) ByteArray.empty
        (createdAccounts, σFinal) k C at rd196
  have hcopy :
      code.write 210 (flipperCtorWardsHashMem I vat cat ilk) 0 6386 =
        flipperCtorRuntimeMem vat cat ilk (flipperCtorWardsHashMem I vat cat ilk) := by
    rfl
  have rdBeforeReturn := evm_run rd196 with [
    raw push2 ⟨6386⟩ (by flipper_ctor_decode) (by evm_ov),
    raw dup1 (by flipper_ctor_decode) (by evm_ov),
    raw push2 ⟨210⟩ (by flipper_ctor_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by flipper_ctor_decode) (by evm_ov),
    raw codecopy
      (Cₘ (UInt256.ofNat (MachineState.M (UInt256.ofNat 7).toNat 0 6386)) -
        Cₘ (UInt256.ofNat 7))
      (flipperCtorRuntimeMem vat cat ilk (flipperCtorWardsHashMem I vat cat ilk))
      (UInt256.ofNat (MachineState.M (UInt256.ofNat 7).toNat 0 6386))
      (by flipper_ctor_decode) mem_cost hcopy (by decide) (by evm_ov),
    raw push1 ⟨0⟩ (by flipper_ctor_decode) (by evm_ov)]
  exact rdBeforeReturn.ret 0 flipperBytecode
    (by flipper_ctor_decode) mem_cost
    (flipperCtorRuntimeMem_read vat cat ilk hilk (flipperCtorWardsHashMem I vat cat ilk))
    (by evm_ov)

theorem RDret.xiResultAcc {cA gh bl σ σ₀ A I} {g : Sat256} {code o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hcode : I.code = code)
    (h : RDret code g (initState cA gh bl σ σ₀ g A I) acc o) :
    Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .OutOfGass
    ∨ ∃ (g' : UInt256) (A' : Substate),
        Ξ cA gh bl σ σ₀ g.toUInt256 A I =
          .ok (.success (acc.1, acc.2, g', A') o) := by
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hcA : s.createdAccounts = acc.1 := congrArg Prod.fst hacc
    have hσ : s.accountMap = acc.2 := congrArg Prod.snd hacc
    have hxi := Xi_success_of_X (g := g.toUInt256) (by
      rw [← hcode] at hX
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    rw [hcA, hσ] at hxi
    exact Or.inr ⟨_, _, hxi⟩

set_option maxHeartbeats 1000000 in
theorem flipperCtorSuccessRDret
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat cat : AccountAddress) (ilk : List UInt8)
    (hcode : I.code = flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk)
    (hperm : I.perm = true) (hilk : ilk.length = 32) (hwv : I.weiValue = ⟨0⟩) :
    let σBeg := sstoreAccountMap I.codeOwner σ ⟨4⟩ ⟨1050000000000000000⟩
    let slot5Old := solcSlotWord σBeg I ⟨5⟩
    let slot5New :=
      UInt256.lor (⟨0x02a300000000000000⟩ : UInt256)
        (UInt256.land
          (UInt256.lor (UInt256.land slot5Old (UInt256.lnot ⟨281474976710655⟩))
            ⟨10800⟩)
          (UInt256.lnot (UInt256.shiftLeft (⟨281474976710655⟩ : UInt256) ⟨48⟩)))
    let σPacked := sstoreAccountMap I.codeOwner σBeg ⟨5⟩ slot5New
    let σKicks := sstoreAccountMap I.codeOwner σPacked ⟨6⟩ ⟨0⟩
    let vatStored := setAddressOffset0Word (solcSlotWord σKicks I ⟨2⟩) (EVM.word vat.val)
    let σVat := sstoreAccountMap I.codeOwner σKicks ⟨2⟩ vatStored
    let catStored := setAddressOffset0Word (solcSlotWord σVat I ⟨7⟩) (EVM.word cat.val)
    let σCat := sstoreAccountMap I.codeOwner σVat ⟨7⟩ catStored
    let σIlk := sstoreAccountMap I.codeOwner σCat ⟨3⟩ (flipperIlkWord ilk)
    let σWards := sstoreAccountMap I.codeOwner σIlk (flipperCtorCallerWardsSlot I) ⟨1⟩
    RDret (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts, σWards) flipperBytecode := by
  intro σBeg slot5Old slot5New σPacked σKicks vatStored σVat catStored σCat σIlk σWards
  obtain ⟨_, _, rd66⟩ := flipperCtorInitReach
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    vat cat ilk hcode hperm
  have rd66' := by
    simpa [σBeg, slot5Old, slot5New, σPacked, σKicks] using rd66
  obtain ⟨_, _, rd128⟩ := flipperCtorArgsReach
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (σKicks := σKicks) vat cat ilk hilk hwv rd66'
  obtain ⟨_, _, rd159⟩ := flipperCtorVatStoreReach
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    vat cat ilk hperm rd128
  have rd159' := by
    simpa [vatStored, σVat] using rd159
  obtain ⟨_, _, rd175⟩ := flipperCtorCatStoreReach
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    vat cat ilk hperm rd159'
  have rd175' := by
    simpa [catStored, σCat] using rd175
  obtain ⟨_, _, rd181⟩ := flipperCtorIlkStoreReach
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    vat cat ilk hperm rd175'
  have rd181' := by
    simpa [σIlk] using rd181
  obtain ⟨_, _, rd196⟩ := flipperCtorWardsStoreReach
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    vat cat ilk hilk hperm rd181'
  have rd196' := by
    simpa [σWards] using rd196
  exact flipperCtorReturnRuntime
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    vat cat ilk hilk rd196'

set_option maxHeartbeats 1000000 in
theorem flipperConstructorCorrect :
    constructorEquivalence config flipperCreationBytecode contract flipperBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I args deployedInitcode
    hdeploy hcode _hcalldata hperm hAccounts
  rcases flipperCtorDeployment_shape hdeploy with ⟨vat, cat, ilk, hargs, hilk, hdeployed⟩
  subst args
  have hcodeTail : I.code = flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk := by
    simpa [hdeployed] using hcode
  by_cases hwv : I.weiValue = ⟨0⟩
  · let σBeg := sstoreAccountMap I.codeOwner σ_evm ⟨4⟩ ⟨1050000000000000000⟩
    let slot5Old := solcSlotWord σBeg I ⟨5⟩
    let slot5New :=
      UInt256.lor (⟨0x02a300000000000000⟩ : UInt256)
        (UInt256.land
          (UInt256.lor (UInt256.land slot5Old (UInt256.lnot ⟨281474976710655⟩))
            ⟨10800⟩)
          (UInt256.lnot (UInt256.shiftLeft (⟨281474976710655⟩ : UInt256) ⟨48⟩)))
    let σPacked := sstoreAccountMap I.codeOwner σBeg ⟨5⟩ slot5New
    let σKicks := sstoreAccountMap I.codeOwner σPacked ⟨6⟩ ⟨0⟩
    let vatStored := setAddressOffset0Word (solcSlotWord σKicks I ⟨2⟩) (EVM.word vat.val)
    let σVat := sstoreAccountMap I.codeOwner σKicks ⟨2⟩ vatStored
    let catStored := setAddressOffset0Word (solcSlotWord σVat I ⟨7⟩) (EVM.word cat.val)
    let σCat := sstoreAccountMap I.codeOwner σVat ⟨7⟩ catStored
    let σIlk := sstoreAccountMap I.codeOwner σCat ⟨3⟩ (flipperIlkWord ilk)
    let σWards := sstoreAccountMap I.codeOwner σIlk (flipperCtorCallerWardsSlot I) ⟨1⟩
    have hrd0 := flipperCtorSuccessRDret
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat cat ilk hcodeTail hperm hilk hwv
    have hrd :
        RDret (flipperCreationBytecode ++ flipperCtorArgsTail vat cat ilk)
          (Sat256.ofUInt256 g)
          (initState createdAccounts genesisBlockHeader blocks σ_evm σ₀
            (Sat256.ofUInt256 g) A I)
          (createdAccounts, σWards) flipperBytecode := by
      simpa [σBeg, slot5Old, slot5New, σPacked, σKicks, vatStored, σVat, catStored,
        σCat, σIlk, σWards] using hrd0
    rcases RDret.xiResultAcc hcodeTail hrd with hOOG | ⟨g', A', hsuccess⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · let evm0s :=
        initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) A I
      let evm1s := flipperCtorAfterBegState evm0s
      let evm2s := flipperCtorAfterTtlState evm1s
      let evm3s := flipperCtorAfterTauState evm2s
      let evm4s := flipperCtorAfterKicksState evm3s
      let evm5s := flipperCtorAfterVatState evm4s vat
      let evm6s := flipperCtorAfterCatState evm5s cat
      let evm7s := flipperCtorAfterIlkState evm6s ilk
      let evm8s := flipperCtorAfterWardsState evm7s
      have hAccountsBeg : accountMapEquiv σBeg evm1s.accountMap := by
        have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨4⟩
          (⟨1050000000000000000⟩ : UInt256) hAccounts
        simpa [σBeg, evm1s, evm0s, flipperCtorAfterBegState, initState,
          storageStore_accountMap, storageStore_executionEnv] using hbase
      have hEvm1Exec : evm1s.executionEnv = I := by
        simp [evm1s, evm0s, flipperCtorAfterBegState, initState, storageStore_executionEnv]
      have hEvm2Exec : evm2s.executionEnv = I := by
        simpa [evm2s, flipperCtorAfterTtlState, storageStore_executionEnv] using hEvm1Exec
      have hAccountsPacked : accountMapEquiv σPacked evm3s.accountMap := by
        have hpacked :=
          flipperCtorPackedAccountMapEquiv
            (σBeg := σBeg) (evm1s := evm1s) (I := I) hAccountsBeg hEvm1Exec
        simpa [slot5Old, slot5New, σPacked, evm2s, evm3s] using hpacked
      have hEvm3Exec : evm3s.executionEnv = I := by
        simpa [evm3s, flipperCtorAfterTauState, storageStore_executionEnv] using hEvm2Exec
      have hAccountsKicks : accountMapEquiv σKicks evm4s.accountMap := by
        have hbase :=
          accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ (⟨0⟩ : UInt256)
            hAccountsPacked
        simpa [σKicks, evm4s, evm3s, flipperCtorAfterKicksState,
          storageStore_accountMap, storageStore_executionEnv, hEvm2Exec, hEvm3Exec] using hbase
      have hEvm4Exec : evm4s.executionEnv = I := by
        simpa [evm4s, flipperCtorAfterKicksState, storageStore_executionEnv] using hEvm3Exec
      have hOldVat :
          solcSlotWord σKicks I ⟨2⟩ =
            Solm.EVM.storageLoad evm4s evm4s.executionEnv.codeOwner ⟨2⟩ := by
        simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, solcSlotWord,
          hEvm4Exec] using
          accountMapEquiv_storage_findD hAccountsKicks I.codeOwner ⟨2⟩ ⟨0⟩
      have hAccountsVat : accountMapEquiv σVat evm5s.accountMap := by
        have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm4s evm4s.executionEnv.codeOwner ⟨2⟩)
            (EVM.word vat.val))
          hAccountsKicks
        simpa [σVat, vatStored, evm5s, evm4s, flipperCtorAfterVatState,
          storageStore_accountMap, storageStore_executionEnv, hEvm3Exec, hEvm4Exec, hOldVat]
          using hbase
      have hEvm5Exec : evm5s.executionEnv = I := by
        simpa [evm5s, flipperCtorAfterVatState, storageStore_executionEnv] using hEvm4Exec
      have hOldCat :
          solcSlotWord σVat I ⟨7⟩ =
            Solm.EVM.storageLoad evm5s evm5s.executionEnv.codeOwner ⟨7⟩ := by
        simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, solcSlotWord,
          hEvm5Exec] using
          accountMapEquiv_storage_findD hAccountsVat I.codeOwner ⟨7⟩ ⟨0⟩
      have hAccountsCat : accountMapEquiv σCat evm6s.accountMap := by
        have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨7⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm5s evm5s.executionEnv.codeOwner ⟨7⟩)
            (EVM.word cat.val))
          hAccountsVat
        simpa [σCat, catStored, evm6s, evm5s, flipperCtorAfterCatState,
          storageStore_accountMap, storageStore_executionEnv, hEvm4Exec, hEvm5Exec, hOldCat]
          using hbase
      have hEvm6Exec : evm6s.executionEnv = I := by
        simpa [evm6s, flipperCtorAfterCatState, storageStore_executionEnv] using hEvm5Exec
      have hAccountsIlk : accountMapEquiv σIlk evm7s.accountMap := by
        have hbase :=
          accountMapEquiv_sstoreAccountMap I.codeOwner ⟨3⟩ (flipperIlkWord ilk)
            hAccountsCat
        simpa [σIlk, evm7s, evm6s, flipperCtorAfterIlkState, storageStore_accountMap,
          storageStore_executionEnv, hEvm5Exec, hEvm6Exec] using hbase
      have hEvm7Exec : evm7s.executionEnv = I := by
        simpa [evm7s, flipperCtorAfterIlkState, storageStore_executionEnv] using hEvm6Exec
      have hslot : wardsSlot (.address I.source) = flipperCtorCallerWardsSlot I :=
        flipperCtorCallerWardsSlot_eq I
      have hAccountsWards : accountMapEquiv σWards evm8s.accountMap := by
        have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner
          (flipperCtorCallerWardsSlot I) ⟨1⟩ hAccountsIlk
        simpa [σWards, evm8s, evm7s, flipperCtorAfterWardsState, storageStore_accountMap,
          storageStore_executionEnv, hEvm6Exec, hEvm7Exec, hslot] using hbase
      refine constructorEquivalenceFor.execution
        (by simpa [Sat256.ofUInt256] using hsuccess)
        (by
          simpa [evm0s, evm1s, evm2s, evm3s, evm4s, evm5s, evm6s, evm7s, evm8s]
            using flipperCtorSolmExecSuccess
              (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) vat cat ilk hilk hwv)
        ?_
      refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
      · simp [evm8s, evm7s, evm6s, evm5s, evm4s, evm3s, evm2s, evm1s, evm0s,
          flipperCtorAfterWardsState, flipperCtorAfterIlkState, flipperCtorAfterCatState,
          flipperCtorAfterVatState, flipperCtorAfterKicksState, flipperCtorAfterTauState,
          flipperCtorAfterTtlState, flipperCtorAfterBegState, storageStore_createdAccounts,
          initState]
      · simpa [evm8s] using hAccountsWards
  · have hrd := flipperCtorNonpayableRDrev
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat cat ilk hcodeTail hperm hwv
    rcases hrd.xiResult hcodeTail with hOOG | ⟨g', o, hrev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
        (flipperSolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) vat cat ilk hwv) ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.Flipper
