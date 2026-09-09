import Examples.TinyImmutable.Common
import Reasoning.SolmBody
import Solm.Equiv

/-!
# TinyImmutable constructor correctness stub

Parameterized over the two final immutable values. The constructor has two source paths for `scale`:
one assigns `_scale`, and the other leaves the immutable at its default `0`. The constructor returns
a runtime whose bytes depend on the final `owner` and `scale`; `constructorEquivalenceWith` checks
that the EVM-returned runtime equals `runtimeCodeOf` applied to the constructor's final
`imm_<name>` locals.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open TinyImmutable.Immutables

namespace TinyImmutable

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

noncomputable def tinyCtorTail (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) : ByteArray :=
  (EVM.Word.toBytesBE (EVM.word (↑owner : Nat))).toByteArray ++
    ((EVM.Word.toBytesBE scale).toByteArray ++
      (EVM.Word.toBytesBE useScale.toUInt256).toByteArray)

noncomputable def tinyCtorCode (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) : ByteArray :=
  tinyImmutableCreationBytecode ++ tinyCtorTail owner scale useScale

def tinyCtorArgLocals (v : TinyImmutables) (owner : AccountAddress) (scaleInt : Int)
    (useScale : Bool) : Store :=
  Std.HashMap.ofList
    (List.zip ((contract v).ctor.params.map Param.name)
      [.address owner, .int scaleInt, .bool useScale])

def tinyCtorFinalLocals (v : TinyImmutables) (owner : AccountAddress) (scaleInt : Int)
    (useScale : Bool) : Store :=
  ((tinyCtorArgLocals v owner scaleInt useScale).insert "imm_owner" (.address owner)).insert
    "imm_scale" (.int (if useScale then scaleInt else 0))

theorem tinyCtorDeployment_shape {args : List Value} {deployedInitcode : ByteArray}
    (v : TinyImmutables) :
    (config v).selfDeployment tinyImmutableCreationBytecode args = some deployedInitcode →
    ∃ owner : AccountAddress, ∃ scaleInt : Int, ∃ useScale : Bool,
      args = [.address owner, .int scaleInt, .bool useScale] ∧
      0 ≤ scaleInt ∧ scaleInt < Int.ofNat (EVM.twoPow 256) ∧
      deployedInitcode =
        tinyImmutableCreationBytecode ++ tinyCtorTail owner (EVM.word scaleInt.toNat) useScale := by
  intro h
  cases args with
  | nil =>
      simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, addr, uint256, uint256Int, boolTy,
        staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
  | cons arg rest =>
      cases rest with
      | nil =>
          cases arg <;>
            simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
              encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, addr, uint256, uint256Int,
              boolTy, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
      | cons arg2 rest2 =>
          cases rest2 with
          | nil =>
              cases arg <;>
                simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                  encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, addr, uint256,
                  uint256Int, boolTy, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
                  encodeABIWord?] at h
          | cons arg3 rest3 =>
              cases rest3 with
              | cons _ _ =>
                  cases arg <;>
                    simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                      encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, addr, uint256,
                      uint256Int, boolTy, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
                      encodeABIWord?] at h
              | nil =>
                  cases arg with
                  | address owner =>
                      cases arg2 with
                      | int scaleInt =>
                          cases arg3 with
                          | bool useScale =>
                              by_cases hbounds :
                                  0 ≤ scaleInt ∧ scaleInt < Int.ofNat (EVM.twoPow 256)
                              · simp [config, genSolidityConstructorDeployment, contract,
                                  constructorDecl, encodeABIValues?, encodeABIValuesFrom?,
                                  abiTupleHeadSize?, addr, uint256, uint256Int, boolTy,
                                  staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
                                  encodeABIWord?, hbounds] at h
                                split at h
                                · simp at h
                                  refine ⟨owner, scaleInt, useScale, rfl, hbounds.1,
                                    hbounds.2, ?_⟩
                                  simpa [tinyCtorTail] using h.symm
                                · rename_i hnot
                                  exact False.elim (hnot hbounds.2)
                              · simp [config, genSolidityConstructorDeployment, contract,
                                  constructorDecl, encodeABIValues?, encodeABIValuesFrom?,
                                  abiTupleHeadSize?, addr, uint256, uint256Int, boolTy,
                                  staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
                                  encodeABIWord?] at h
                                split at h
                                · rename_i hb
                                  exact False.elim (hbounds hb)
                                · simp at h
                          | _ =>
                              simp [config, genSolidityConstructorDeployment, contract,
                                constructorDecl, encodeABIValues?, encodeABIValuesFrom?,
                                abiTupleHeadSize?, addr, uint256, uint256Int, boolTy,
                                staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
                                encodeABIWord?] at h
                      | _ =>
                          simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                            encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, addr,
                            uint256, uint256Int, boolTy, staticABIEncodedSize?, isDynamicABIType,
                            encodeABIValue?, encodeABIWord?] at h
                  | _ =>
                      simp [config, genSolidityConstructorDeployment, contract, constructorDecl,
                        encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?, addr, uint256,
                        uint256Int, boolTy, staticABIEncodedSize?, isDynamicABIType,
                        encodeABIValue?, encodeABIWord?] at h

theorem write_from_gap_eq (src base : ByteArray) (srcAddr destAddr len : Nat)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size)
    (hge : base.size ≤ destAddr) (hgap : destAddr - base.size < USize.size) :
    src.write srcAddr base destAddr len =
      base ++ ffi.ByteArray.zeroes (destAddr - base.size) ++
        src.extract srcAddr (srcAddr + len) := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ srcAddr ≥ src.size from by omega)]
  have hcopy : min len (src.size - srcAddr) = len := by omega
  have htail : min base.size (destAddr + len) - (destAddr + len) = 0 := by omega
  simp only [hcopy, htail, ByteArray.data_copySlice, ByteArray.data_append,
    ByteArray.data_extract, show (destAddr - base.size) =
      destAddr - base.size from rfl]
  have hpz : (ffi.ByteArray.zeroes (destAddr - base.size)).data.size =
      destAddr - base.size := by
    rw [show (ffi.ByteArray.zeroes (destAddr - base.size)).data.size =
          (ffi.ByteArray.zeroes (destAddr - base.size)).size from rfl,
      ByteArray_zeroes_size]
  have hDsz : (base.data ++
        (ffi.ByteArray.zeroes (destAddr - base.size)).data).size =
      destAddr := by
    rw [Array.size_append, hpz, show base.data.size = base.size from rfl]
    omega
  rw [show (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
    rw [zeroes_zero (n := (0)) (by rfl)]
    rfl]
  simp only [Array.append_empty, Nat.add_zero]
  rw [show min len (src.data.size - srcAddr) = len by
    have : src.data.size = src.size := rfl
    omega]
  rw [Array.extract_eq_self_of_le (by rw [hDsz])]
  rw [show (base.data ++
        (ffi.ByteArray.zeroes (destAddr - base.size)).data).extract
          (destAddr + len) = (#[] : Array UInt8) from by
    apply Array.extract_eq_empty_of_le
    rw [hDsz]
    omega]
  simp [Array.append_assoc]

theorem tinyCtorTail_size (owner : AccountAddress) (scale : UInt256) (useScale : Bool) :
    (tinyCtorTail owner scale useScale).size = 96 := by
  unfold tinyCtorTail
  rw [ByteArray.size_append, ByteArray.size_append, word_toBytesBE_toByteArray_size,
    word_toBytesBE_toByteArray_size, word_toBytesBE_toByteArray_size]

theorem tinyCtorCode_size (owner : AccountAddress) (scale : UInt256) (useScale : Bool) :
    (tinyCtorCode owner scale useScale).size = 730 := by
  rw [tinyCtorCode, ByteArray.size_append, tinyImmutableCreationBytecode_size,
    tinyCtorTail_size]

theorem tinyCtorCode_tail_window (owner : AccountAddress) (scale : UInt256) (useScale : Bool) :
    (tinyCtorCode owner scale useScale).extract 634 (634 + 96) =
      tinyCtorTail owner scale useScale := by
  unfold tinyCtorCode
  exact extract_append_right' tinyImmutableCreationBytecode (tinyCtorTail owner scale useScale)
    634 (634 + 96) tinyImmutableCreationBytecode_size.symm
    (by rw [tinyImmutableCreationBytecode_size, tinyCtorTail_size])

theorem tinyCtorCreation_runtime_window :
    tinyImmutableCreationBytecode.extract 202 (202 + 432) = tinyImmutableBytecode := by
  decide +native +revert

theorem tinyCtorCode_runtime_window (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (tinyCtorCode owner scale useScale).extract 202 (202 + 432) = tinyImmutableBytecode := by
  unfold tinyCtorCode
  rw [extract_append_left tinyImmutableCreationBytecode (tinyCtorTail owner scale useScale)
    202 (202 + 432) (by rw [tinyImmutableCreationBytecode_size])]
  exact tinyCtorCreation_runtime_window

noncomputable def tinyCtorFreePtrMem : ByteArray :=
  writeWord ByteArray.empty 64 (⟨192⟩ : UInt256)

noncomputable def tinyCtorAbiMem (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) : ByteArray :=
  tinyCtorFreePtrMem ++ ffi.ByteArray.zeroes 96 ++
    tinyCtorTail owner scale useScale

noncomputable def tinyCtorAbiFreeMem (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) : ByteArray :=
  writeWord (tinyCtorAbiMem owner scale useScale) 64 (⟨288⟩ : UInt256)

theorem tinyCtorFreePtrMem_size : tinyCtorFreePtrMem.size = 96 := by
  unfold tinyCtorFreePtrMem
  rw [writeWord_size]
  · rfl
  · exact lt_usize _ (by norm_num)

theorem tinyCtorAbiMem_size (owner : AccountAddress) (scale : UInt256) (useScale : Bool) :
    (tinyCtorAbiMem owner scale useScale).size = 288 := by
  unfold tinyCtorAbiMem
  rw [ByteArray.size_append, ByteArray.size_append, tinyCtorFreePtrMem_size,
    ByteArray_zeroes_size, tinyCtorTail_size]

theorem tinyCtorAbiFreeMem_size (owner : AccountAddress) (scale : UInt256) (useScale : Bool) :
    (tinyCtorAbiFreeMem owner scale useScale).size = 288 := by
  unfold tinyCtorAbiFreeMem
  rw [writeWord_size]
  · rw [tinyCtorAbiMem_size]
    rfl
  · rw [tinyCtorAbiMem_size]
    exact lt_usize _ (by norm_num)

theorem tinyCtorFreePtrMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ tinyCtorFreePtrMem.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (tinyCtorFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨192⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [tinyCtorFreePtrMem_size]
    decide
  · decide
  · change tinyCtorFreePtrMem.readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256)
    unfold tinyCtorFreePtrMem
    exact writeWord_read_back ByteArray.empty 64 (⟨192⟩ : UInt256)
      (by exact lt_usize _ (by norm_num))

theorem tinyCtorArg_codecopy_mem (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (tinyCtorCode owner scale useScale).write 634 tinyCtorFreePtrMem 192 96 =
      tinyCtorAbiMem owner scale useScale := by
  unfold tinyCtorAbiMem
  rw [write_from_gap_eq]
  · rw [tinyCtorFreePtrMem_size]
    rw [show 192 - 96 = 96 by norm_num]
    rw [tinyCtorCode_tail_window]
  · norm_num
  · rw [tinyCtorCode_size]
  · rw [tinyCtorFreePtrMem_size]
    norm_num
  · rw [tinyCtorFreePtrMem_size]
    exact lt_usize _ (by norm_num)

theorem tinyCtorAbiMem_read192 (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (tinyCtorAbiMem owner scale useScale).readWithPadding 192 32 =
      UInt256.toByteArray (EVM.word (↑owner : Nat)) := by
  rw [readWithPadding_eq_extract' _ 192 32 (by norm_num) (by norm_num)
    (by rw [tinyCtorAbiMem_size]; norm_num)]
  unfold tinyCtorAbiMem tinyCtorTail
  rw [extract_append_right_window (tinyCtorFreePtrMem ++ ffi.ByteArray.zeroes 96)
    ((EVM.Word.toBytesBE (EVM.word (↑owner : Nat))).toByteArray ++
      ((EVM.Word.toBytesBE scale).toByteArray ++
        (EVM.Word.toBytesBE useScale.toUInt256).toByteArray)) 192 (192 + 32) (by
      rw [ByteArray.size_append, tinyCtorFreePtrMem_size, ByteArray_zeroes_size])]
  rw [show 192 - (tinyCtorFreePtrMem ++ ffi.ByteArray.zeroes 96).size = 0 by
    rw [ByteArray.size_append, tinyCtorFreePtrMem_size, ByteArray_zeroes_size]]
  rw [show 192 + 32 - (tinyCtorFreePtrMem ++ ffi.ByteArray.zeroes 96).size =
      32 by
    rw [ByteArray.size_append, tinyCtorFreePtrMem_size, ByteArray_zeroes_size]]
  rw [extract_append_left (EVM.Word.toBytesBE (EVM.word (↑owner : Nat))).toByteArray
    ((EVM.Word.toBytesBE scale).toByteArray ++
      (EVM.Word.toBytesBE useScale.toUInt256).toByteArray) 0 32
    (by rw [word_toBytesBE_toByteArray_size])]
  rw [show 32 = (EVM.Word.toBytesBE (EVM.word (↑owner : Nat))).toByteArray.size by
    rw [word_toBytesBE_toByteArray_size]]
  rw [byteArray_extract_self, word_toBytesBE_toByteArray_eq_toByteArray]

theorem tinyCtorAbiMem_read224 (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (tinyCtorAbiMem owner scale useScale).readWithPadding 224 32 =
      UInt256.toByteArray scale := by
  rw [readWithPadding_eq_extract' _ 224 32 (by norm_num) (by norm_num)
    (by rw [tinyCtorAbiMem_size]; norm_num)]
  unfold tinyCtorAbiMem tinyCtorTail
  set preBuf := tinyCtorFreePtrMem ++ ffi.ByteArray.zeroes 96
  have hpreBuf : preBuf.size = 192 := by
    unfold preBuf
    rw [ByteArray.size_append, tinyCtorFreePtrMem_size, ByteArray_zeroes_size]
  rw [extract_append_right_window preBuf
    ((EVM.Word.toBytesBE (EVM.word (↑owner : Nat))).toByteArray ++
      ((EVM.Word.toBytesBE scale).toByteArray ++
        (EVM.Word.toBytesBE useScale.toUInt256).toByteArray)) 224 (224 + 32)
    (by rw [hpreBuf]; norm_num), hpreBuf]
  norm_num
  rw [extract_append_right_window (EVM.Word.toBytesBE (EVM.word (↑owner : Nat))).toByteArray
    ((EVM.Word.toBytesBE scale).toByteArray ++
      (EVM.Word.toBytesBE useScale.toUInt256).toByteArray) 32 64
    (by rw [word_toBytesBE_toByteArray_size])]
  rw [show 32 - (EVM.Word.toBytesBE (EVM.word (↑owner : Nat))).toByteArray.size = 0 by
    rw [word_toBytesBE_toByteArray_size]]
  rw [show 64 - (EVM.Word.toBytesBE (EVM.word (↑owner : Nat))).toByteArray.size = 32 by
    rw [word_toBytesBE_toByteArray_size]]
  rw [extract_append_left (EVM.Word.toBytesBE scale).toByteArray
    (EVM.Word.toBytesBE useScale.toUInt256).toByteArray 0 32
    (by rw [word_toBytesBE_toByteArray_size])]
  rw [show 32 = (EVM.Word.toBytesBE scale).toByteArray.size by
    rw [word_toBytesBE_toByteArray_size]]
  rw [byteArray_extract_self, word_toBytesBE_toByteArray_eq_toByteArray]

theorem tinyCtorAbiMem_read256 (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (tinyCtorAbiMem owner scale useScale).readWithPadding 256 32 =
      UInt256.toByteArray useScale.toUInt256 := by
  rw [readWithPadding_eq_extract' _ 256 32 (by norm_num) (by norm_num)
    (by rw [tinyCtorAbiMem_size])]
  unfold tinyCtorAbiMem tinyCtorTail
  set preBuf := tinyCtorFreePtrMem ++ ffi.ByteArray.zeroes 96
  have hpreBuf : preBuf.size = 192 := by
    unfold preBuf
    rw [ByteArray.size_append, tinyCtorFreePtrMem_size, ByteArray_zeroes_size]
  rw [extract_append_right_window preBuf
    ((EVM.Word.toBytesBE (EVM.word (↑owner : Nat))).toByteArray ++
      ((EVM.Word.toBytesBE scale).toByteArray ++
        (EVM.Word.toBytesBE useScale.toUInt256).toByteArray)) 256 (256 + 32)
    (by rw [hpreBuf]; norm_num), hpreBuf]
  norm_num
  rw [← ByteArray.append_assoc]
  rw [extract_append_right_window
    ((EVM.Word.toBytesBE (EVM.word (↑owner : Nat))).toByteArray ++
      (EVM.Word.toBytesBE scale).toByteArray)
    (EVM.Word.toBytesBE useScale.toUInt256).toByteArray 64 96
    (by rw [ByteArray.size_append, word_toBytesBE_toByteArray_size,
      word_toBytesBE_toByteArray_size])]
  rw [show 64 - ((EVM.Word.toBytesBE (EVM.word (↑owner : Nat))).toByteArray ++
        (EVM.Word.toBytesBE scale).toByteArray).size = 0 by
    rw [ByteArray.size_append, word_toBytesBE_toByteArray_size,
      word_toBytesBE_toByteArray_size]]
  rw [show 96 - ((EVM.Word.toBytesBE (EVM.word (↑owner : Nat))).toByteArray ++
        (EVM.Word.toBytesBE scale).toByteArray).size = 32 by
    rw [ByteArray.size_append, word_toBytesBE_toByteArray_size,
      word_toBytesBE_toByteArray_size]]
  rw [show 32 = (EVM.Word.toBytesBE useScale.toUInt256).toByteArray.size by
    rw [word_toBytesBE_toByteArray_size]]
  rw [byteArray_extract_self, word_toBytesBE_toByteArray_eq_toByteArray]

theorem tinyCtorAbiFreeMem_read192 (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (tinyCtorAbiFreeMem owner scale useScale).readWithPadding 192 32 =
      UInt256.toByteArray (EVM.word (↑owner : Nat)) := by
  unfold tinyCtorAbiFreeMem
  rw [writeWord_read_preserved]
  · exact tinyCtorAbiMem_read192 owner scale useScale
  · rw [tinyCtorAbiMem_size]
    exact lt_usize _ (by norm_num)
  · right
    constructor
    · norm_num
    · rw [tinyCtorAbiMem_size]
      norm_num

theorem tinyCtorAbiFreeMem_read224 (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (tinyCtorAbiFreeMem owner scale useScale).readWithPadding 224 32 =
      UInt256.toByteArray scale := by
  unfold tinyCtorAbiFreeMem
  rw [writeWord_read_preserved]
  · exact tinyCtorAbiMem_read224 owner scale useScale
  · rw [tinyCtorAbiMem_size]
    exact lt_usize _ (by norm_num)
  · right
    constructor
    · norm_num
    · rw [tinyCtorAbiMem_size]
      norm_num

theorem tinyCtorAbiFreeMem_read256 (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (tinyCtorAbiFreeMem owner scale useScale).readWithPadding 256 32 =
      UInt256.toByteArray useScale.toUInt256 := by
  unfold tinyCtorAbiFreeMem
  rw [writeWord_read_preserved]
  · exact tinyCtorAbiMem_read256 owner scale useScale
  · rw [tinyCtorAbiMem_size]
    exact lt_usize _ (by norm_num)
  · right
    constructor
    · norm_num
    · rw [tinyCtorAbiMem_size]

theorem tinyCtorAbiFreeMem_mload192 (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (if (⟨192⟩ : UInt256).toNat ≥ (tinyCtorAbiFreeMem owner scale useScale).size
        ∨ (⟨192⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((tinyCtorAbiFreeMem owner scale useScale).readWithPadding
            (⟨192⟩ : UInt256).toNat 32)))
      = EVM.word (↑owner : Nat) := by
  apply mloadWordValue_of_readWithPadding
  · rw [tinyCtorAbiFreeMem_size]
    decide
  · decide
  · simpa [show (⟨192⟩ : UInt256).toNat = 192 from by decide] using
      tinyCtorAbiFreeMem_read192 owner scale useScale

theorem tinyCtorAbiFreeMem_mload224 (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (if (⟨224⟩ : UInt256).toNat ≥ (tinyCtorAbiFreeMem owner scale useScale).size
        ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((tinyCtorAbiFreeMem owner scale useScale).readWithPadding
            (⟨224⟩ : UInt256).toNat 32)))
      = scale := by
  apply mloadWordValue_of_readWithPadding
  · rw [tinyCtorAbiFreeMem_size]
    decide
  · decide
  · simpa [show (⟨224⟩ : UInt256).toNat = 224 from by decide] using
      tinyCtorAbiFreeMem_read224 owner scale useScale

theorem tinyCtorAbiFreeMem_mload256 (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (if (⟨256⟩ : UInt256).toNat ≥ (tinyCtorAbiFreeMem owner scale useScale).size
        ∨ (⟨256⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((tinyCtorAbiFreeMem owner scale useScale).readWithPadding
            (⟨256⟩ : UInt256).toNat 32)))
      = useScale.toUInt256 := by
  apply mloadWordValue_of_readWithPadding
  · rw [tinyCtorAbiFreeMem_size]
    decide
  · decide
  · simpa [show (⟨256⟩ : UInt256).toNat = 256 from by decide] using
      tinyCtorAbiFreeMem_read256 owner scale useScale

theorem write0_eq_extract_from_of_base_le (src base : ByteArray) (srcAddr len : Nat)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) (hbase : base.size ≤ len) :
    src.write srcAddr base 0 len = src.extract srcAddr (srcAddr + len) := by
  apply ByteArray.ext
  rw [write0_data_from src base srcAddr len hlen hsrc]
  rw [show base.data.extract len base.data.size = (#[] : Array UInt8) from by
    apply Array.extract_eq_empty_of_le
    rw [show base.data.size = base.size from rfl]
    simpa using hbase]
  simp

noncomputable def tinyCtorOwnerMem (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) : ByteArray :=
  writeWord (tinyCtorAbiFreeMem owner scale useScale) 128 (EVM.word (↑owner : Nat))

noncomputable def tinyCtorDecodedMem (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) : ByteArray :=
  if useScale then writeWord (tinyCtorOwnerMem owner scale useScale) 160 scale
  else tinyCtorOwnerMem owner scale useScale

noncomputable def tinyCtorPatchedRuntime (owner : AccountAddress) (scale : UInt256) :
    ByteArray :=
  writeCascade tinyImmutableBytecode
    [ (186, scale), (361, scale), (72, EVM.word (↑owner : Nat)),
      (245, EVM.word (↑owner : Nat)) ]

theorem tinyCtorOwnerMem_size (owner : AccountAddress) (scale : UInt256) (useScale : Bool) :
    (tinyCtorOwnerMem owner scale useScale).size = 288 := by
  unfold tinyCtorOwnerMem
  rw [writeWord_size]
  · rw [tinyCtorAbiFreeMem_size]
    rfl
  · rw [tinyCtorAbiFreeMem_size]
    exact lt_usize _ (by norm_num)

theorem tinyCtorDecodedMem_size (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (tinyCtorDecodedMem owner scale useScale).size = 288 := by
  unfold tinyCtorDecodedMem
  cases useScale <;> simp
  · exact tinyCtorOwnerMem_size owner scale false
  · rw [writeWord_size]
    · rw [tinyCtorOwnerMem_size]
      rfl
    · rw [tinyCtorOwnerMem_size]
      exact lt_usize _ (by norm_num)

theorem tinyCtorPatchedRuntime_size (owner : AccountAddress) (scale : UInt256) :
    (tinyCtorPatchedRuntime owner scale).size = 432 := by
  unfold tinyCtorPatchedRuntime
  exact writeCascade_size_of_base tinyImmutableBytecode
    [ (186, scale), (361, scale), (72, EVM.word (↑owner : Nat)),
      (245, EVM.word (↑owner : Nat)) ]
    (base := 432) (out := 432)
    (by decide +native) (by simp [WriteGapsOk]) (by simp [writeCascadeSize])

theorem tinyCtorRuntime_codecopy_mem (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (tinyCtorCode owner scale useScale).write 202 (tinyCtorDecodedMem owner scale useScale) 0 432 =
      tinyImmutableBytecode := by
  rw [write0_eq_extract_from_of_base_le]
  · exact tinyCtorCode_runtime_window owner scale useScale
  · norm_num
  · rw [tinyCtorCode_size]
    norm_num
  · rw [tinyCtorDecodedMem_size]
    norm_num

theorem tinyCtorPatchedRuntime_eq_patchedRuntime (owner : AccountAddress) (scale : UInt256) :
    tinyCtorPatchedRuntime owner scale = patchedRuntime { owner := owner, scale := scale } := by
  unfold tinyCtorPatchedRuntime patchedRuntime runtimeWrites
  rw [wordOfInt_ofNat_toNat]
  rfl

theorem tinyCtorPatchedRuntime_read (owner : AccountAddress) (scale : UInt256) :
    (tinyCtorPatchedRuntime owner scale).readWithPadding 0 432 =
      patchedRuntime { owner := owner, scale := scale } := by
  rw [readWithPadding_eq_extract' _ 0 432 (by norm_num) (by norm_num)
    (by rw [tinyCtorPatchedRuntime_size])]
  rw [show 432 = (tinyCtorPatchedRuntime owner scale).size by
    rw [tinyCtorPatchedRuntime_size]]
  have hself := byteArray_extract_self (tinyCtorPatchedRuntime owner scale)
  simpa [tinyCtorPatchedRuntime_eq_patchedRuntime, Nat.zero_add] using hself

theorem tinyCtorArgLocals_get_owner (v : TinyImmutables) (owner : AccountAddress)
    (scaleInt : Int) (useScale : Bool) :
    (tinyCtorArgLocals v owner scaleInt useScale).get? "_owner" = some (.address owner) := by
  grind [tinyCtorArgLocals, contract, constructorDecl]

theorem tinyCtorArgLocals_get_scale (v : TinyImmutables) (owner : AccountAddress)
    (scaleInt : Int) (useScale : Bool) :
    (tinyCtorArgLocals v owner scaleInt useScale).get? "_scale" = some (.int scaleInt) := by
  grind [tinyCtorArgLocals, contract, constructorDecl]

theorem tinyCtorArgLocals_get_useScale (v : TinyImmutables) (owner : AccountAddress)
    (scaleInt : Int) (useScale : Bool) :
    (tinyCtorArgLocals v owner scaleInt useScale).get? "useScale" = some (.bool useScale) := by
  grind [tinyCtorArgLocals, contract, constructorDecl]

theorem tinyCtorOwnerLocals_get_useScale (v : TinyImmutables) (owner : AccountAddress)
    (scaleInt : Int) (useScale : Bool) :
    ((tinyCtorArgLocals v owner scaleInt useScale).insert "imm_owner" (.address owner)).get?
      "useScale" = some (.bool useScale) := by
  grind [tinyCtorArgLocals, contract, constructorDecl]

theorem tinyCtorOwnerLocals_get_scale (v : TinyImmutables) (owner : AccountAddress)
    (scaleInt : Int) (useScale : Bool) :
    ((tinyCtorArgLocals v owner scaleInt useScale).insert "imm_owner" (.address owner)).get?
      "_scale" = some (.int scaleInt) := by
  grind [tinyCtorArgLocals, contract, constructorDecl]

theorem tinyCtorFinalLocals_get_owner (v : TinyImmutables) (owner : AccountAddress)
    (scaleInt : Int) (useScale : Bool) :
    (tinyCtorFinalLocals v owner scaleInt useScale).get? "imm_owner" =
      some (.address owner) := by
  grind [tinyCtorFinalLocals, tinyCtorArgLocals, contract, constructorDecl]

theorem tinyCtorFinalLocals_get_scale_true (v : TinyImmutables) (owner : AccountAddress)
    (scaleInt : Int) :
    (tinyCtorFinalLocals v owner scaleInt true).get? "imm_scale" =
      some (.int scaleInt) := by
  grind [tinyCtorFinalLocals, tinyCtorArgLocals, contract, constructorDecl]

theorem tinyCtorFinalLocals_get_scale_false (v : TinyImmutables) (owner : AccountAddress)
    (scaleInt : Int) :
    (tinyCtorFinalLocals v owner scaleInt false).get? "imm_scale" =
      some (.int 0) := by
  grind [tinyCtorFinalLocals, tinyCtorArgLocals, contract, constructorDecl]

theorem tinyCtorAbiMem_read160 (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (tinyCtorAbiMem owner scale useScale).readWithPadding 160 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 160 32 (by norm_num) (by norm_num)
    (by rw [tinyCtorAbiMem_size]; norm_num)]
  unfold tinyCtorAbiMem
  rw [ByteArray.append_assoc]
  rw [extract_append_right_window tinyCtorFreePtrMem
    (ffi.ByteArray.zeroes 96 ++ tinyCtorTail owner scale useScale)
    160 (160 + 32) (by rw [tinyCtorFreePtrMem_size]; norm_num)]
  rw [show 160 - tinyCtorFreePtrMem.size = 64 by rw [tinyCtorFreePtrMem_size]]
  rw [show 160 + 32 - tinyCtorFreePtrMem.size = 96 by rw [tinyCtorFreePtrMem_size]]
  rw [extract_append_left (ffi.ByteArray.zeroes 96)
    (tinyCtorTail owner scale useScale) 64 96 (by
      rw [zeroes_ofNat_size 96 (by norm_num)])]
  decide +native

theorem tinyCtorAbiFreeMem_read160 (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (tinyCtorAbiFreeMem owner scale useScale).readWithPadding 160 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold tinyCtorAbiFreeMem
  rw [writeWord_read_preserved]
  · exact tinyCtorAbiMem_read160 owner scale useScale
  · rw [tinyCtorAbiMem_size]
    exact lt_usize _ (by norm_num)
  · right
    constructor
    · norm_num
    · rw [tinyCtorAbiMem_size]
      norm_num

theorem tinyCtorOwnerMem_read128 (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (tinyCtorOwnerMem owner scale useScale).readWithPadding 128 32 =
      UInt256.toByteArray (EVM.word (↑owner : Nat)) := by
  unfold tinyCtorOwnerMem
  rw [writeWord_read_back]
  rw [tinyCtorAbiFreeMem_size]
  exact lt_usize _ (by norm_num)

theorem tinyCtorOwnerMem_read160 (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (tinyCtorOwnerMem owner scale useScale).readWithPadding 160 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold tinyCtorOwnerMem
  rw [writeWord_read_preserved]
  · exact tinyCtorAbiFreeMem_read160 owner scale useScale
  · rw [tinyCtorAbiFreeMem_size]
    exact lt_usize _ (by norm_num)
  · right
    constructor
    · norm_num
    · rw [tinyCtorAbiFreeMem_size]
      norm_num

theorem tinyCtorDecodedMem_read128 (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (tinyCtorDecodedMem owner scale useScale).readWithPadding 128 32 =
      UInt256.toByteArray (EVM.word (↑owner : Nat)) := by
  unfold tinyCtorDecodedMem
  cases useScale
  · exact tinyCtorOwnerMem_read128 owner scale false
  · simp
    rw [writeWord_read_preserved]
    · exact tinyCtorOwnerMem_read128 owner scale true
    · rw [tinyCtorOwnerMem_size]
      exact lt_usize _ (by norm_num)
    · left
      constructor
      · norm_num
      · rw [tinyCtorOwnerMem_size]
        norm_num

theorem tinyCtorDecodedMem_read160_true (owner : AccountAddress) (scale : UInt256) :
    (tinyCtorDecodedMem owner scale true).readWithPadding 160 32 =
      UInt256.toByteArray scale := by
  unfold tinyCtorDecodedMem
  simp
  rw [writeWord_read_back]
  rw [tinyCtorOwnerMem_size]
  exact lt_usize _ (by norm_num)

theorem tinyCtorDecodedMem_read160_false (owner : AccountAddress) (scale : UInt256) :
    (tinyCtorDecodedMem owner scale false).readWithPadding 160 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold tinyCtorDecodedMem
  exact tinyCtorOwnerMem_read160 owner scale false

theorem tinyCtorDecodedMem_mload128 (owner : AccountAddress) (scale : UInt256)
    (useScale : Bool) :
    (if (⟨128⟩ : UInt256).toNat ≥ (tinyCtorDecodedMem owner scale useScale).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((tinyCtorDecodedMem owner scale useScale).readWithPadding
            (⟨128⟩ : UInt256).toNat 32)))
      = EVM.word (↑owner : Nat) := by
  apply mloadWordValue_of_readWithPadding
  · rw [tinyCtorDecodedMem_size]
    decide
  · decide
  · simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
      tinyCtorDecodedMem_read128 owner scale useScale

theorem tinyCtorDecodedMem_mload160_true (owner : AccountAddress) (scale : UInt256) :
    (if (⟨160⟩ : UInt256).toNat ≥ (tinyCtorDecodedMem owner scale true).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((tinyCtorDecodedMem owner scale true).readWithPadding
            (⟨160⟩ : UInt256).toNat 32)))
      = scale := by
  apply mloadWordValue_of_readWithPadding
  · rw [tinyCtorDecodedMem_size]
    decide
  · decide
  · simpa [show (⟨160⟩ : UInt256).toNat = 160 from by decide] using
      tinyCtorDecodedMem_read160_true owner scale

theorem tinyCtorDecodedMem_mload160_false (owner : AccountAddress) (scale : UInt256) :
    (if (⟨160⟩ : UInt256).toNat ≥ (tinyCtorDecodedMem owner scale false).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((tinyCtorDecodedMem owner scale false).readWithPadding
            (⟨160⟩ : UInt256).toNat 32)))
      = ⟨0⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [tinyCtorDecodedMem_size]
    decide
  · decide
  · simpa [show (⟨160⟩ : UInt256).toNat = 160 from by decide] using
      tinyCtorDecodedMem_read160_false owner scale

theorem tinyCtorRuntimeCodeOf_true (v : TinyImmutables) (owner : AccountAddress)
    (scaleInt : Int) (h0 : 0 ≤ scaleInt)
    (hlt : scaleInt < Int.ofNat (EVM.twoPow 256)) :
    runtimeCodeOf tinyImmutableBytecode (tinyCtorFinalLocals v owner scaleInt true) =
      some (patchedRuntime { owner := owner, scale := EVM.word scaleInt.toNat }) := by
  have hword : (EVM.word scaleInt.toNat).toNat = scaleInt.toNat :=
    constructorUInt256Word_toNat scaleInt h0 hlt
  unfold runtimeCodeOf patchesFrom offsets wordBytes?
  simp [List.foldrM]
  rw [show (tinyCtorFinalLocals v owner scaleInt true)["imm_owner"]? =
      some (.address owner) by
    exact tinyCtorFinalLocals_get_owner v owner scaleInt true]
  rw [show (tinyCtorFinalLocals v owner scaleInt true)["imm_scale"]? =
      some (.int scaleInt) by
    exact tinyCtorFinalLocals_get_scale_true v owner scaleInt]
  simp [valueToWord, wordOfInt_nonneg _ h0]
  simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
    List.lookup_cons,
    hword, Int.toNat_of_nonneg h0, wordOfInt_nonneg _ h0] using
    (patchRuntime_eq_patchedRuntime
      (v := { owner := owner, scale := EVM.word scaleInt.toNat }))

theorem tinyCtorRuntimeCodeOf_false (v : TinyImmutables) (owner : AccountAddress)
    (scaleInt : Int) :
    runtimeCodeOf tinyImmutableBytecode (tinyCtorFinalLocals v owner scaleInt false) =
      some (patchedRuntime { owner := owner, scale := ⟨0⟩ }) := by
  unfold runtimeCodeOf patchesFrom offsets wordBytes?
  simp [List.foldrM]
  rw [show (tinyCtorFinalLocals v owner scaleInt false)["imm_owner"]? =
      some (.address owner) by
    exact tinyCtorFinalLocals_get_owner v owner scaleInt false]
  rw [show (tinyCtorFinalLocals v owner scaleInt false)["imm_scale"]? =
      some (.int 0) by
    exact tinyCtorFinalLocals_get_scale_false v owner scaleInt]
  simp [valueToWord]
  simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
    show EVM.wordOfInt 0 = (⟨0⟩ : UInt256) by decide] using
    (patchRuntime_eq_patchedRuntime
      (v := { owner := owner, scale := (⟨0⟩ : UInt256) }))

theorem tinyCtorBodyReturns (v : TinyImmutables) (evm : EVM.State)
    (owner : AccountAddress) (scaleInt : Int) (useScale : Bool)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v) evm
      (tinyCtorArgLocals v owner scaleInt useScale) (contract v).ctor.body
      (.returned
        { contract := contract v
          locals := tinyCtorFinalLocals v owner scaleInt useScale }
        evm none) := by
  simp only [contract, constructorDecl, nonpayable, List.append_assoc, List.nil_append]
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .address owner) ?_) ?_
  · show evalExpr? (config v)
        { contract := contract v, locals := tinyCtorArgLocals v owner scaleInt useScale } evm
        (.var "_owner") = .ok (.address owner)
    simp [evalExpr?, EvalResult.ofOption]
    rw [show (tinyCtorArgLocals v owner scaleInt useScale)["_owner"]? =
        some (.address owner) by
      exact tinyCtorArgLocals_get_owner v owner scaleInt useScale]
  · cases useScale
    · refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ?_) ExecBlock.nil
      · show evalExpr? (config v)
            { contract := contract v
              locals := (tinyCtorArgLocals v owner scaleInt false).insert "imm_owner"
                (.address owner) } evm
            (.var "useScale") = .ok (.bool false)
        simp [evalExpr?, EvalResult.ofOption]
        rw [show ((tinyCtorArgLocals v owner scaleInt false).insert "imm_owner"
            (.address owner))["useScale"]? = some (.bool false) by
          exact tinyCtorOwnerLocals_get_useScale v owner scaleInt false]
      · simpa [tinyCtorFinalLocals] using
          (ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by
            show evalExpr? (config v)
              { contract := contract v
                locals := (tinyCtorArgLocals v owner scaleInt false).insert "imm_owner"
                  (.address owner) } evm
              (.intLit 0) = .ok (.int 0)
            simp [evalExpr?, pure])) ExecBlock.nil)
    · refine ExecBlock.consNormal (ExecStmt.iteTrue ?_ ?_) ExecBlock.nil
      · show evalExpr? (config v)
            { contract := contract v
              locals := (tinyCtorArgLocals v owner scaleInt true).insert "imm_owner"
                (.address owner) } evm
            (.var "useScale") = .ok (.bool true)
        simp [evalExpr?, EvalResult.ofOption]
        rw [show ((tinyCtorArgLocals v owner scaleInt true).insert "imm_owner"
            (.address owner))["useScale"]? = some (.bool true) by
          exact tinyCtorOwnerLocals_get_useScale v owner scaleInt true]
      · simpa [tinyCtorFinalLocals] using
          (ExecBlock.consNormal (ExecStmt.letDecl (value := .int scaleInt) (by
            show evalExpr? (config v)
              { contract := contract v
                locals := (tinyCtorArgLocals v owner scaleInt true).insert "imm_owner"
                  (.address owner) } evm
              (.var "_scale") = .ok (.int scaleInt)
            simp [evalExpr?, EvalResult.ofOption]
            rw [show ((tinyCtorArgLocals v owner scaleInt true).insert "imm_owner"
                (.address owner))["_scale"]? = some (.int scaleInt) by
              exact tinyCtorOwnerLocals_get_scale v owner scaleInt true]))
          ExecBlock.nil)

theorem tinySolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (v : TinyImmutables) (owner : AccountAddress) (scaleInt : Int) (useScale : Bool)
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec (config v) (contract v) [.address owner, .int scaleInt, .bool useScale]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      (.returned
        { contract := contract v
          locals := tinyCtorFinalLocals v owner scaleInt useScale }
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := tinyCtorArgLocals v owner scaleInt useScale)
    ?_ rfl ?_ ?_
  · rfl
  · simp [tinyCtorArgLocals, contract, constructorDecl]
  · exact tinyCtorBodyReturns v _ owner scaleInt useScale (by simp [initState, hwv])

theorem tinySolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (v : TinyImmutables) (owner : AccountAddress) (scaleInt : Int) (useScale : Bool)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec (config v) (contract v) [.address owner, .int scaleInt, .bool useScale]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := tinyCtorArgLocals v owner scaleInt useScale)
    ?_ rfl ?_ ?_
  · rfl
  · simp [tinyCtorArgLocals, contract, constructorDecl]
  · simpa [contract, constructorDecl, nonpayable] using
      (bodyReverts_nonPayable (cfg := config v) (contract := contract v)
        (evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
          (Sat256.ofUInt256 g) A I)
        (locals := tinyCtorArgLocals v owner scaleInt useScale)
        (rest :=
          [ .letDecl "imm_owner" (some addr) (.var "_owner"),
            .ite (.var "useScale")
              [ .letDecl "imm_scale" (some uint256) (.var "_scale") ]
              [ .letDecl "imm_scale" (some uint256) (.intLit 0) ] ])
        (by simp [initState, hwv]))

theorem tinyCtorCreation_decode_append (tail : ByteArray) (pc : UInt256)
    (hpc : pc.toNat + 33 ≤ tinyImmutableCreationBytecode.size) :
    decode (tinyImmutableCreationBytecode ++ tail) pc =
      decode tinyImmutableCreationBytecode pc :=
  Reasoning.Theory.decode_append_left_window tinyImmutableCreationBytecode tail pc hpc
    (by rw [tinyImmutableCreationBytecode_size]; norm_num)

macro "tiny_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [tinyCtorCreation_decode_append _ _ (by
          rw [tinyImmutableCreationBytecode_size]
          decide +native)]
      | (unfold tinyCtorCode; rw [tinyCtorCreation_decode_append _ _ (by
          rw [tinyImmutableCreationBytecode_size]
          decide +native)]);
     decide +native))

macro "tiny_ctor_jd" : tactic =>
  `(tactic|
    (first
      | (apply Reasoning.Theory.D_J_contains_append_left; decide +native)
      | (unfold tinyCtorCode; apply Reasoning.Theory.D_J_contains_append_left; decide +native)))

open Lean in
macro "tiny_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by tiny_ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by tiny_ctor_decode) $(args[0]!) $(args[1]!)
                            (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by tiny_ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by tiny_ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

theorem tinyCtorInitcodeToBody
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (owner : AccountAddress) (scale : UInt256) (useScale : Bool)
    (hcode : I.code = tinyCtorCode owner scale useScale)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (tinyCtorCode owner scale useScale) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨46⟩
      [useScale.toUInt256, scale, EVM.word (↑owner : Nat)]
      (tinyCtorAbiFreeMem owner scale useScale) (UInt256.ofNat 9)
      ByteArray.empty (createdAccounts, σ) k C := by
  have rd0 :
      RD (tinyCtorCode owner scale useScale) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd79 := tiny_ctor_run rd0 with [
    push1 ⟨192⟩, push1 ⟨64⟩,
    raw mstore 9 tinyCtorFreePtrMem (UInt256.ofNat 3) (by tiny_ctor_decode) mem_cost
      (by
        unfold tinyCtorFreePtrMem Reasoning.Theory.writeWord
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
      (by decide) (by evm_ov),
    callvalue, dup1, iszero, push2 ⟨15⟩,
    jumpiT (by rw [hwv]; decide) (by tiny_ctor_jd),
    jumpdest, pop, push1 ⟨64⟩,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 3) (by tiny_ctor_decode) mem_cost
      tinyCtorFreePtrMem_mload64 (by decide) (by evm_ov),
    push2 ⟨634⟩, codesize, sub, dup1, push2 ⟨634⟩, dup4,
    raw codecopy 18 (tinyCtorAbiMem owner scale useScale) (UInt256.ofNat 9)
      (by tiny_ctor_decode)
      (fun s haws hstks => by
        set_option linter.unusedSimpArgs false in
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
            List.getElem!_cons_zero, List.getElem!_cons_succ]
        rw [tinyCtorCode_size]
        decide)
      (by
        rw [show ((UInt256.ofNat (tinyCtorCode owner scale useScale).size).sub
            (⟨634⟩ : UInt256)).toNat = 96 by
          rw [tinyCtorCode_size]
          decide]
        exact tinyCtorArg_codecopy_mem owner scale useScale)
      (by
        rw [tinyCtorCode_size]
        decide)
      (by evm_ov),
    dup2, add, push1 ⟨64⟩, dup2, swap1,
    raw mstore 0 (tinyCtorAbiFreeMem owner scale useScale) (UInt256.ofNat 9)
      (by tiny_ctor_decode) mem_cost
      (by
        rw [show (⟨192⟩ : UInt256) +
            (UInt256.ofNat (tinyCtorCode owner scale useScale).size).sub ⟨634⟩ =
            (⟨288⟩ : UInt256) by
          rw [tinyCtorCode_size]
          decide]
        unfold tinyCtorAbiFreeMem Reasoning.Theory.writeWord
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
      (by decide) (by evm_ov),
    push2 ⟨46⟩, swap2, push2 ⟨79⟩, jump (by tiny_ctor_jd)]
  have rd46 := tiny_ctor_run rd79 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨97⟩, jumpiT (by
      rw [show (⟨192⟩ : UInt256) +
          (UInt256.ofNat (tinyCtorCode owner scale useScale).size).sub ⟨634⟩ =
          (⟨288⟩ : UInt256) by
        rw [tinyCtorCode_size]
        decide]
      decide) (by tiny_ctor_jd),
    jumpdest, dup4,
    raw mload 0 (EVM.word (↑owner : Nat)) (UInt256.ofNat 9) (by tiny_ctor_decode)
      mem_cost (tinyCtorAbiFreeMem_mload192 owner scale useScale) (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq,
    push2 ⟨119⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask by decide]
      rw [show UInt256.land (EVM.word (↑owner : Nat)) solcAddrMask =
          EVM.word (↑owner : Nat) by
        exact tinyOwnerWord_clean { owner := owner, scale := scale }]
      rw [show UInt256.eq (EVM.word (↑owner : Nat)) (EVM.word (↑owner : Nat)) =
          (⟨1⟩ : UInt256) by
        simp [UInt256.eq]
        decide]
      decide) (by tiny_ctor_jd),
    jumpdest, push1 ⟨32⟩, dup6, add,
    raw mload 0 scale (UInt256.ofNat 9) (by tiny_ctor_decode)
      mem_cost (tinyCtorAbiFreeMem_mload224 owner scale useScale) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup7, add,
    raw mload 0 useScale.toUInt256 (UInt256.ofNat 9) (by tiny_ctor_decode)
      mem_cost (tinyCtorAbiFreeMem_mload256 owner scale useScale) (by decide) (by evm_ov),
    swap2, swap5, pop, swap3, pop, dup1, iszero, iszero, dup2, eq,
    push2 ⟨147⟩, jumpiT (by cases useScale <;> decide) (by tiny_ctor_jd),
    jumpdest, dup1, swap2, pop, pop, swap3, pop, swap3, pop, swap3,
    jump (by tiny_ctor_jd)]
  exact ⟨_, _, by simpa [tinyOwnerWord_clean { owner := owner, scale := scale }] using rd46⟩

theorem tinyCtorInitcodeSuccessTrue
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (owner : AccountAddress) (scale : UInt256)
    (hcode : I.code = tinyCtorCode owner scale true)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret (tinyCtorCode owner scale true) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) (createdAccounts, σ)
      (patchedRuntime { owner := owner, scale := scale }) := by
  obtain ⟨_, _, rd46⟩ := tinyCtorInitcodeToBody
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    owner scale true hcode hwv
  have rd158 := tiny_ctor_run rd46 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and,
    push1 ⟨128⟩,
    raw mstore 0 (tinyCtorOwnerMem owner scale true) (UInt256.ofNat 9)
      (by tiny_ctor_decode) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask by decide]
        rw [show UInt256.land (EVM.word (↑owner : Nat)) solcAddrMask =
            EVM.word (↑owner : Nat) by
          exact tinyOwnerWord_clean { owner := owner, scale := scale }]
        unfold tinyCtorOwnerMem Reasoning.Theory.writeWord
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide])
      (by decide) (by evm_ov),
    dup1, iszero, push2 ⟨71⟩, jumpiNT (by decide),
    push1 ⟨160⟩, dup3, swap1,
    raw mstore 0 (tinyCtorDecodedMem owner scale true) (UInt256.ofNat 9)
      (by tiny_ctor_decode) mem_cost
      (by
        unfold tinyCtorDecodedMem Reasoning.Theory.writeWord
        simp
        rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide])
      (by decide) (by evm_ov),
    jumpdest, pop, pop, pop, push2 ⟨158⟩, jump (by tiny_ctor_jd)]
  exact tiny_ctor_run rd158 with [
    jumpdest, push1 ⟨128⟩,
    raw mload 0 (EVM.word (↑owner : Nat)) (UInt256.ofNat 9)
      (by tiny_ctor_decode) mem_cost (tinyCtorDecodedMem_mload128 owner scale true)
      (by decide) (by evm_ov),
    push1 ⟨160⟩,
    raw mload 0 scale (UInt256.ofNat 9)
      (by tiny_ctor_decode) mem_cost (tinyCtorDecodedMem_mload160_true owner scale)
      (by decide) (by evm_ov),
    push2 ⟨432⟩, push2 ⟨202⟩, push0,
    raw codecopy 15 tinyImmutableBytecode (UInt256.ofNat 14)
      (by tiny_ctor_decode) mem_cost (tinyCtorRuntime_codecopy_mem owner scale true)
      (by decide) (by evm_ov),
    push0, dup2, dup2, push1 ⟨186⟩, add,
    raw mstore 0 (writeWord tinyImmutableBytecode 186 scale) (UInt256.ofNat 14)
      (by tiny_ctor_decode) mem_cost
      (by
        unfold Reasoning.Theory.writeWord
        rw [show ((⟨186⟩ : UInt256) + ⟨0⟩).toNat = 186 from by decide])
      (by decide) (by evm_ov),
    push2 ⟨361⟩, add,
    raw mstore 0 (writeWord (writeWord tinyImmutableBytecode 186 scale) 361 scale)
      (UInt256.ofNat 14)
      (by tiny_ctor_decode) mem_cost
      (by
        unfold Reasoning.Theory.writeWord
        rw [show ((⟨361⟩ : UInt256) + ⟨0⟩).toNat = 361 from by decide])
      (by decide) (by evm_ov),
    push0, dup2, dup2, push1 ⟨72⟩, add,
    raw mstore 0
      (writeWord (writeWord (writeWord tinyImmutableBytecode 186 scale) 361 scale) 72
        (EVM.word (↑owner : Nat)))
      (UInt256.ofNat 14)
      (by tiny_ctor_decode) mem_cost
      (by
        unfold Reasoning.Theory.writeWord
        rw [show ((⟨72⟩ : UInt256) + ⟨0⟩).toNat = 72 from by decide])
      (by decide) (by evm_ov),
    push1 ⟨245⟩, add,
    raw mstore 0 (tinyCtorPatchedRuntime owner scale) (UInt256.ofNat 14)
      (by tiny_ctor_decode) mem_cost
      (by
        simp [tinyCtorPatchedRuntime, Reasoning.Theory.writeCascade,
          Reasoning.Theory.writeWord,
          show ((⟨245⟩ : UInt256) + ⟨0⟩).toNat = 245 from by decide])
      (by decide) (by evm_ov),
    push2 ⟨432⟩, push0,
    raw ret 0 (patchedRuntime { owner := owner, scale := scale })
      (by tiny_ctor_decode) mem_cost (tinyCtorPatchedRuntime_read owner scale) (by evm_ov)]

theorem tinyCtorInitcodeSuccessFalse
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (owner : AccountAddress) (scale : UInt256)
    (hcode : I.code = tinyCtorCode owner scale false)
    (hwv : I.weiValue = ⟨0⟩) :
    RDret (tinyCtorCode owner scale false) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) (createdAccounts, σ)
      (patchedRuntime { owner := owner, scale := (⟨0⟩ : UInt256) }) := by
  obtain ⟨_, _, rd46⟩ := tinyCtorInitcodeToBody
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    owner scale false hcode hwv
  have rd158Raw := tiny_ctor_run rd46 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and,
    push1 ⟨128⟩,
    raw mstore 0 (tinyCtorOwnerMem owner scale false) (UInt256.ofNat 9)
      (by tiny_ctor_decode) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask by decide]
        rw [show UInt256.land (EVM.word (↑owner : Nat)) solcAddrMask =
            EVM.word (↑owner : Nat) by
          exact tinyOwnerWord_clean { owner := owner, scale := scale }]
        unfold tinyCtorOwnerMem Reasoning.Theory.writeWord
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide])
      (by decide) (by evm_ov),
    dup1, iszero, push2 ⟨71⟩, jumpiT (by decide) (by tiny_ctor_jd),
    jumpdest, pop, pop, pop, push2 ⟨158⟩, jump (by tiny_ctor_jd)]
  have rd158 := by
    simpa [tinyCtorDecodedMem] using rd158Raw
  exact tiny_ctor_run rd158 with [
    jumpdest, push1 ⟨128⟩,
    raw mload 0 (EVM.word (↑owner : Nat)) (UInt256.ofNat 9)
      (by tiny_ctor_decode) mem_cost (tinyCtorDecodedMem_mload128 owner scale false)
      (by decide) (by evm_ov),
    push1 ⟨160⟩,
    raw mload 0 (⟨0⟩ : UInt256) (UInt256.ofNat 9)
      (by tiny_ctor_decode) mem_cost (tinyCtorDecodedMem_mload160_false owner scale)
      (by decide) (by evm_ov),
    push2 ⟨432⟩, push2 ⟨202⟩, push0,
    raw codecopy 15 tinyImmutableBytecode (UInt256.ofNat 14)
      (by tiny_ctor_decode) mem_cost (tinyCtorRuntime_codecopy_mem owner scale false)
      (by decide) (by evm_ov),
    push0, dup2, dup2, push1 ⟨186⟩, add,
    raw mstore 0 (writeWord tinyImmutableBytecode 186 (⟨0⟩ : UInt256)) (UInt256.ofNat 14)
      (by tiny_ctor_decode) mem_cost
      (by
        unfold Reasoning.Theory.writeWord
        rw [show ((⟨186⟩ : UInt256) + ⟨0⟩).toNat = 186 from by decide])
      (by decide) (by evm_ov),
    push2 ⟨361⟩, add,
    raw mstore 0 (writeWord (writeWord tinyImmutableBytecode 186 (⟨0⟩ : UInt256)) 361
        (⟨0⟩ : UInt256)) (UInt256.ofNat 14)
      (by tiny_ctor_decode) mem_cost
      (by
        unfold Reasoning.Theory.writeWord
        rw [show ((⟨361⟩ : UInt256) + ⟨0⟩).toNat = 361 from by decide])
      (by decide) (by evm_ov),
    push0, dup2, dup2, push1 ⟨72⟩, add,
    raw mstore 0
      (writeWord (writeWord (writeWord tinyImmutableBytecode 186 (⟨0⟩ : UInt256)) 361
        (⟨0⟩ : UInt256)) 72 (EVM.word (↑owner : Nat)))
      (UInt256.ofNat 14)
      (by tiny_ctor_decode) mem_cost
      (by
        unfold Reasoning.Theory.writeWord
        rw [show ((⟨72⟩ : UInt256) + ⟨0⟩).toNat = 72 from by decide])
      (by decide) (by evm_ov),
    push1 ⟨245⟩, add,
    raw mstore 0 (tinyCtorPatchedRuntime owner (⟨0⟩ : UInt256)) (UInt256.ofNat 14)
      (by tiny_ctor_decode) mem_cost
      (by
        simp [tinyCtorPatchedRuntime, Reasoning.Theory.writeCascade,
          Reasoning.Theory.writeWord,
          show ((⟨245⟩ : UInt256) + ⟨0⟩).toNat = 245 from by decide])
      (by decide) (by evm_ov),
    push2 ⟨432⟩, push0,
    raw ret 0 (patchedRuntime { owner := owner, scale := (⟨0⟩ : UInt256) })
      (by tiny_ctor_decode) mem_cost (tinyCtorPatchedRuntime_read owner (⟨0⟩ : UInt256))
      (by evm_ov)]

theorem tinyCtorInitcodeNonpayableRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (tail : ByteArray)
    (hcode : I.code = tinyImmutableCreationBytecode ++ tail)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (tinyImmutableCreationBytecode ++ tail) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd0 :
      RD (tinyImmutableCreationBytecode ++ tail) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd12 := tiny_ctor_run rd0 with [
    push1 ⟨192⟩, push1 ⟨64⟩,
    raw mstore 9 tinyCtorFreePtrMem (UInt256.ofNat 3)
      (by tiny_ctor_decode)
      mem_cost
      (by
        unfold tinyCtorFreePtrMem Reasoning.Theory.writeWord
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
      (by decide) (by evm_ov),
    callvalue, dup1, iszero, push2 ⟨15⟩, jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd12.revertStub (by tiny_ctor_decode) (by tiny_ctor_decode) (by tiny_ctor_decode)
    (by simp)

theorem tinyImmutableConstructorCorrect (v : TinyImmutables) :
    constructorEquivalenceWith (config v) tinyImmutableCreationBytecode (contract v)
      (runtimeCodeOf tinyImmutableBytecode) := by
  refine constructorEquivalenceWith.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
      args deployedInitcode hdeploy hcode _hcalldata _hperm hσ
  rcases tinyCtorDeployment_shape v hdeploy with
    ⟨owner, scaleInt, useScale, hargs, h0, hlt, hdeployed⟩
  subst args
  rw [hdeployed] at hcode
  by_cases hwv : I.weiValue = ⟨0⟩
  · cases useScale
    · have hcodeCtor :
          I.code = tinyCtorCode owner (EVM.word scaleInt.toNat) false := by
        simpa [tinyCtorCode] using hcode
      have hrd := tinyCtorInitcodeSuccessFalse
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) owner (EVM.word scaleInt.toNat) hcodeCtor hwv
      rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', A', hsuccess⟩
      · exact constructorEquivalenceForWith.outOfGas
          (by simpa [Sat256.ofUInt256] using hOOG)
      · refine constructorEquivalenceForWith.execution
          (by simpa [Sat256.ofUInt256] using hsuccess)
          (tinySolmCtorExecSuccess
            (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
            (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
            v owner scaleInt false hwv) ?_
        refine ctorResultEquivWith.success rfl rfl ?_ ?_ ?_
        · rfl
        · simpa [initState] using hσ
        · exact tinyCtorRuntimeCodeOf_false v owner scaleInt
    · have hcodeCtor :
          I.code = tinyCtorCode owner (EVM.word scaleInt.toNat) true := by
        simpa [tinyCtorCode] using hcode
      have hrd := tinyCtorInitcodeSuccessTrue
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) owner (EVM.word scaleInt.toNat) hcodeCtor hwv
      rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', A', hsuccess⟩
      · exact constructorEquivalenceForWith.outOfGas
          (by simpa [Sat256.ofUInt256] using hOOG)
      · refine constructorEquivalenceForWith.execution
          (by simpa [Sat256.ofUInt256] using hsuccess)
          (tinySolmCtorExecSuccess
            (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
            (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
            v owner scaleInt true hwv) ?_
        refine ctorResultEquivWith.success rfl rfl ?_ ?_ ?_
        · rfl
        · simpa [initState] using hσ
        · exact tinyCtorRuntimeCodeOf_true v owner scaleInt h0 hlt
  · have hrd := tinyCtorInitcodeNonpayableRevert
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g)
      (tail := tinyCtorTail owner (EVM.word scaleInt.toNat) useScale) hcode hwv
    rcases hrd.xiResult hcode with hOOG | ⟨g', o, hrev⟩
    · exact constructorEquivalenceForWith.outOfGas
        (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceForWith.execution
        (by simpa [Sat256.ofUInt256] using hrev)
        (tinySolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
          v owner scaleInt useScale hwv) ?_
      exact ctorResultEquivWith.revert rfl rfl

end TinyImmutable
