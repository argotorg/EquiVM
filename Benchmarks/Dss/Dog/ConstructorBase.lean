import Reasoning.WordArithmetic
import Benchmarks.Dss.Dog.Common
import Reasoning.MemCascade

/-!
# MakerDAO/Sky DSS Dog constructor shared helpers

Shared bytecode, memory, immutable-patching, and storage-slot facts for the Dog constructor trace.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

theorem wordAt0Mem_size_192 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 192) :
    (wordAt0Mem word mem).size = 192 := by
  unfold wordAt0Mem
  exact toByteArray_write32_size_of_le mem word 0 192 192 hmem
    (by rw [hmem]; omega) (by omega)

theorem wordAt32Mem_size_192 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 192) :
    (wordAt32Mem word mem).size = 192 := by
  unfold wordAt32Mem
  exact toByteArray_write32_size_of_le mem word 32 192 192 hmem
    (by rw [hmem]; omega) (by omega)

theorem twoWordHashMem_read0_192 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 192) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_192 key hmem]; omega) (by omega)]
  exact wordAt0Mem_read0 key mem

theorem twoWordHashMem_read32_192 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 192) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_192 key hmem]; omega)]
  exact toByteArray_extract_all slot

theorem twoWordHashMem_read0_64_192 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 192) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by
        unfold twoWordHashMem
        rw [wordAt32Mem_size_192]
        · omega
        · exact wordAt0Mem_size_192 key hmem)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0 (by
        unfold twoWordHashMem
        rw [wordAt32Mem_size_192]
        · omega
        · exact wordAt0Mem_size_192 key hmem),
      twoWordHashMem_read0_192 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32 (by
        unfold twoWordHashMem
        rw [wordAt32Mem_size_192]
        · omega
        · exact wordAt0Mem_size_192 key hmem),
      twoWordHashMem_read32_192 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
    rw [ByteArray.extract_append_extract]
    norm_num]
  rw [hleft, hright]

end Benchmarks.Dss.Dog

end

namespace Benchmarks.Dss.Dog

set_option maxRecDepth 2000000

/-- ABI-encoded constructor argument appended to `dogCreationBytecode`. -/
def dogCtorArgsTail (vat : AccountAddress) : ByteArray :=
  (EVM.Word.toBytesBE (EVM.word vat.val)).toByteArray

def dogCtorCode (vat : AccountAddress) : ByteArray :=
  dogCreationBytecode ++ dogCtorArgsTail vat

theorem dogCtorDeployment_shape {args : List Value}
    {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment dogCreationBytecode args = some deployedInitcode) :
    ∃ vat : AccountAddress,
      args = [.address vat] ∧ deployedInitcode = dogCtorCode vat := by
  simp [config, constructorDecl, Solm.genSolidityConstructorDeployment] at hdeploy
  cases args with
  | nil =>
      simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr] at hdeploy
  | cons a rest =>
      cases rest with
      | cons _ _ =>
          cases a <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr,
            ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
            ABI.encodeABIValue?, ABI.encodeABIWord?] at hdeploy
      | nil =>
          cases a <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr,
            ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
            ABI.encodeABIValue?, ABI.encodeABIWord?] at hdeploy
          rename_i vat
          refine ⟨vat, rfl, ?_⟩
          simpa [dogCtorCode, dogCtorArgsTail] using hdeploy.symm

macro "dog_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [Reasoning.Theory.decode_append_left_window
          dogCreationBytecode _ _ (by native_decide) (by native_decide)]
      | (unfold dogCtorCode
         rw [Reasoning.Theory.decode_append_left_window
          dogCreationBytecode _ _ (by native_decide) (by native_decide)]);
     native_decide))

macro "dog_ctor_jd" : tactic =>
  `(tactic|
    (first
      | exact Reasoning.Theory.D_J_contains_append_left dogCreationBytecode _ _ (by jump_dest)
      | (unfold dogCtorCode
         exact Reasoning.Theory.D_J_contains_append_left dogCreationBytecode _ _ (by jump_dest))))

open Lean in
macro "dog_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by dog_ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by dog_ctor_decode) $(args[0]!) $(args[1]!)
                            (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by dog_ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by dog_ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

theorem dogCreationBytecode_size : dogCreationBytecode.size = 4927 := by
  native_decide

theorem dogBytecode_size : dogBytecode.size = 4745 := by
  native_decide

theorem dogCtorArgsTail_size (vat : AccountAddress) : (dogCtorArgsTail vat).size = 32 := by
  simpa [dogCtorArgsTail] using word_toBytesBE_toByteArray_size (EVM.word vat.val)

theorem dogCtorCode_size (vat : AccountAddress) : (dogCtorCode vat).size = 4959 := by
  unfold dogCtorCode
  rw [ByteArray.size_append, dogCreationBytecode_size, dogCtorArgsTail_size]

theorem dogCtorArgLen_eq (vat : AccountAddress) :
    (UInt256.ofNat (dogCtorCode vat).size).sub ⟨4927⟩ = (⟨32⟩ : UInt256) := by
  rw [dogCtorCode_size]
  native_decide

theorem dogCreationBytecode_runtime_window :
    dogCreationBytecode.extract 182 (182 + 4745) = dogBytecode := by
  native_decide

theorem dogCtorCode_runtime_window (vat : AccountAddress) :
    (dogCtorCode vat).extract 182 (182 + 4745) = dogBytecode := by
  unfold dogCtorCode
  rw [extract_append_left dogCreationBytecode (dogCtorArgsTail vat) 182 (182 + 4745)
    (by rw [dogCreationBytecode_size])]
  exact dogCreationBytecode_runtime_window

def dogCtorFreePtrMem : ByteArray :=
  writeWord ByteArray.empty 64 (⟨160⟩ : UInt256)

def dogCtorArgMem (vat : AccountAddress) : ByteArray :=
  dogCtorFreePtrMem ++ ByteArray.zeroes 64 ++ dogCtorArgsTail vat

def dogCtorArgFreeMem (vat : AccountAddress) : ByteArray :=
  writeWord (dogCtorArgMem vat) 64 (⟨192⟩ : UInt256)

def dogCtorVatMem (vat : AccountAddress) : ByteArray :=
  writeWord (dogCtorArgFreeMem vat) 128 (UInt256.shiftLeft (EVM.word vat.val) ⟨96⟩)

def dogRuntimeWrites (vat : AccountAddress) : List (Nat × UInt256) :=
  [ (1405, EVM.word vat.val), (2890, EVM.word vat.val), (3170, EVM.word vat.val),
    (3965, EVM.word vat.val) ]

def dogCtorPatchedRuntime (vat : AccountAddress) : ByteArray :=
  writeCascade dogBytecode (dogRuntimeWrites vat)

theorem dogCtorFreePtrMem_size : dogCtorFreePtrMem.size = 96 := by
  unfold dogCtorFreePtrMem
  rw [writeWord_size]
  · rfl
  · exact lt_usize _ (by norm_num)

theorem dogCtorArgMem_size (vat : AccountAddress) :
    (dogCtorArgMem vat).size = 192 := by
  unfold dogCtorArgMem
  rw [ByteArray.size_append, ByteArray.size_append, dogCtorFreePtrMem_size,
    ByteArray_zeroes_size, dogCtorArgsTail_size]

theorem dogCtorArgFreeMem_size (vat : AccountAddress) :
    (dogCtorArgFreeMem vat).size = 192 := by
  unfold dogCtorArgFreeMem
  rw [writeWord_size]
  · rw [dogCtorArgMem_size]
    rfl
  · rw [dogCtorArgMem_size]
    exact lt_usize _ (by norm_num)

theorem dogCtorVatMem_size (vat : AccountAddress) :
    (dogCtorVatMem vat).size = 192 := by
  unfold dogCtorVatMem
  rw [writeWord_size]
  · rw [dogCtorArgFreeMem_size]
    rfl
  · rw [dogCtorArgFreeMem_size]
    exact lt_usize _ (by norm_num)

theorem dogCtorFreePtrMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ dogCtorFreePtrMem.size then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (dogCtorFreePtrMem.readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [dogCtorFreePtrMem_size]
    decide
  · change dogCtorFreePtrMem.readWithPadding 64 32 =
      UInt256.toByteArray (⟨160⟩ : UInt256)
    unfold dogCtorFreePtrMem
    exact writeWord_read_back ByteArray.empty 64 (⟨160⟩ : UInt256)
      (by exact lt_usize _ (by norm_num))


theorem dogCtorArg_codecopy_mem (vat : AccountAddress) :
    (dogCtorCode vat).write 4927 dogCtorFreePtrMem 160 32 =
      dogCtorArgMem vat := by
  unfold dogCtorArgMem
  rw [write_from_gap_eq]
  · rw [dogCtorFreePtrMem_size]
    rw [show 160 - 96 = 64 by norm_num]
    unfold dogCtorCode
    rw [extract_append_right' dogCreationBytecode (dogCtorArgsTail vat) 4927 (4927 + 32)]
    · exact dogCreationBytecode_size.symm
    · rw [dogCtorArgsTail_size]
      native_decide
  · norm_num
  · rw [dogCtorCode_size]
  · rw [dogCtorFreePtrMem_size]
    norm_num
  · rw [dogCtorFreePtrMem_size]
    exact lt_usize _ (by norm_num)

theorem dogCtorArgMem_read160 (vat : AccountAddress) :
    (dogCtorArgMem vat).readWithPadding 160 32 =
      UInt256.toByteArray (EVM.word vat.val) := by
  rw [readWithPadding_eq_extract' _ 160 32 (by norm_num) (by norm_num)
    (by rw [dogCtorArgMem_size])]
  unfold dogCtorArgMem dogCtorArgsTail
  set preBuf := dogCtorFreePtrMem ++ ByteArray.zeroes 64
  have hpreBuf : preBuf.size = 160 := by
    unfold preBuf
    rw [ByteArray.size_append, dogCtorFreePtrMem_size, ByteArray_zeroes_size]
  rw [extract_append_right_window preBuf (EVM.Word.toBytesBE (EVM.word vat.val)).toByteArray
    160 (160 + 32) (by rw [hpreBuf]), hpreBuf]
  norm_num
  have hself := byteArray_extract_self (EVM.Word.toBytesBE (EVM.word vat.val)).toByteArray
  simpa [word_toBytesBE_toByteArray_eq_toByteArray] using hself

theorem dogCtorArgFreeMem_read160 (vat : AccountAddress) :
    (dogCtorArgFreeMem vat).readWithPadding 160 32 =
      UInt256.toByteArray (EVM.word vat.val) := by
  unfold dogCtorArgFreeMem
  rw [writeWord_read_preserved]
  · exact dogCtorArgMem_read160 vat
  · rw [dogCtorArgMem_size]
    exact lt_usize _ (by norm_num)
  · right
    constructor
    · norm_num
    · rw [dogCtorArgMem_size]

theorem dogCtorArgFreeMem_mload64 (vat : AccountAddress) :
    (if (⟨64⟩ : UInt256).toNat ≥ (dogCtorArgFreeMem vat).size then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((dogCtorArgFreeMem vat).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨192⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [dogCtorArgFreeMem_size]
    decide
  · change (dogCtorArgFreeMem vat).readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256)
    unfold dogCtorArgFreeMem
    rw [writeWord_read_back]
    rw [dogCtorArgMem_size]
    exact lt_usize _ (by norm_num)

theorem dogCtorArgFreeMem_mload160 (vat : AccountAddress) :
    (if (⟨160⟩ : UInt256).toNat ≥ (dogCtorArgFreeMem vat).size then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((dogCtorArgFreeMem vat).readWithPadding (⟨160⟩ : UInt256).toNat 32)))
      = EVM.word vat.val := by
  apply mloadWordValue_of_readWithPadding
  · rw [dogCtorArgFreeMem_size]
    decide
  · simpa [show (⟨160⟩ : UInt256).toNat = 160 from by decide] using
      dogCtorArgFreeMem_read160 vat


theorem dogCtorVatMem_read128 (vat : AccountAddress) :
    (dogCtorVatMem vat).readWithPadding 128 32 =
      UInt256.toByteArray (UInt256.shiftLeft (EVM.word vat.val) ⟨96⟩) := by
  unfold dogCtorVatMem
  rw [writeWord_read_back]
  rw [dogCtorArgFreeMem_size]
  exact lt_usize _ (by norm_num)

theorem dogCtorVatMem_mload128_shr96 (vat : AccountAddress) :
    UInt256.shiftRight
      (if (⟨128⟩ : UInt256).toNat ≥ (dogCtorVatMem vat).size then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((dogCtorVatMem vat).readWithPadding (⟨128⟩ : UInt256).toNat 32)))
      ⟨96⟩ = EVM.word vat.val := by
  rw [mloadWordValue_of_readWithPadding
      (mem := dogCtorVatMem vat) (off := ⟨128⟩)
      (v := UInt256.shiftLeft (EVM.word vat.val) ⟨96⟩)
      (by rw [dogCtorVatMem_size]; decide)
      (by simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
        dogCtorVatMem_read128 vat)]
  exact addressWord_shiftLeft96_shiftRight96 vat

abbrev dogCtorCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

def dogCtorWardsHashMem (I : ExecutionEnv) (vat : AccountAddress) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨0⟩ (dogCtorVatMem vat)


theorem dogCtorWardsHashMem_size (I : ExecutionEnv) (vat : AccountAddress) :
    (dogCtorWardsHashMem I vat).size = 192 := by
  unfold dogCtorWardsHashMem twoWordHashMem
  exact wordAt32Mem_size_192 ⟨0⟩
    (wordAt0Mem_size_192 (solcSourceWord I) (dogCtorVatMem_size vat))


theorem dogCtorWardsHashSlot (I : ExecutionEnv) (vat : AccountAddress) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((dogCtorWardsHashMem I vat).readWithPadding 0 64))) =
      dogCtorCallerWardsSlot I := by
  unfold dogCtorWardsHashMem dogCtorCallerWardsSlot solcMappingSlot
  rw [twoWordHashMem_read0_64_192]
  · exact mappingSlot_single (solcSourceWord I) ⟨0⟩
  · exact dogCtorVatMem_size vat

theorem dogCtorWardsHashMem_read128 (I : ExecutionEnv) (vat : AccountAddress) :
    (dogCtorWardsHashMem I vat).readWithPadding 128 32 =
      UInt256.toByteArray (UInt256.shiftLeft (EVM.word vat.val) ⟨96⟩) := by
  unfold dogCtorWardsHashMem twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 128 (by rw [toByteArray_size])
      (by
        rw [wordAt0Mem_size_192 (solcSourceWord I) (dogCtorVatMem_size vat)]
        omega)
      (by omega)
      (by
        rw [wordAt0Mem_size_192 (solcSourceWord I) (dogCtorVatMem_size vat)]
        omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 128 (by rw [toByteArray_size])
      (by rw [dogCtorVatMem_size]; omega) (by omega)
      (by rw [dogCtorVatMem_size]; omega)]
  exact dogCtorVatMem_read128 vat

theorem dogCtorWardsHashMem_mload128_shr96 (I : ExecutionEnv) (vat : AccountAddress) :
    UInt256.shiftRight
      (if (⟨128⟩ : UInt256).toNat ≥ (dogCtorWardsHashMem I vat).size then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((dogCtorWardsHashMem I vat).readWithPadding (⟨128⟩ : UInt256).toNat 32)))
      ⟨96⟩ = EVM.word vat.val := by
  rw [mloadWordValue_of_readWithPadding
      (mem := dogCtorWardsHashMem I vat) (off := ⟨128⟩)
      (v := UInt256.shiftLeft (EVM.word vat.val) ⟨96⟩)
      (by rw [dogCtorWardsHashMem_size]; decide)
      (by simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
        dogCtorWardsHashMem_read128 I vat)]
  exact addressWord_shiftLeft96_shiftRight96 vat

theorem dogCtorVatMem_read64 (vat : AccountAddress) :
    (dogCtorVatMem vat).readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  unfold dogCtorVatMem
  rw [writeWord_read_preserved]
  · change (dogCtorArgFreeMem vat).readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256)
    unfold dogCtorArgFreeMem
    rw [writeWord_read_back]
    rw [dogCtorArgMem_size]
    exact lt_usize _ (by norm_num)
  · rw [dogCtorArgFreeMem_size]
    exact lt_usize _ (by norm_num)
  · left
    constructor
    · norm_num
    · rw [dogCtorArgFreeMem_size]
      norm_num

theorem dogCtorWardsHashMem_read64 (I : ExecutionEnv) (vat : AccountAddress) :
    (dogCtorWardsHashMem I vat).readWithPadding 64 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  unfold dogCtorWardsHashMem twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by
        rw [wordAt0Mem_size_192 (solcSourceWord I) (dogCtorVatMem_size vat)]
        omega)
      (by omega)
      (by
        rw [wordAt0Mem_size_192 (solcSourceWord I) (dogCtorVatMem_size vat)]
        omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [dogCtorVatMem_size]; omega) (by omega)
      (by rw [dogCtorVatMem_size]; omega)]
  exact dogCtorVatMem_read64 vat

theorem dogCtorWardsHashMem_mload64 (I : ExecutionEnv) (vat : AccountAddress) :
    (if (⟨64⟩ : UInt256).toNat ≥ (dogCtorWardsHashMem I vat).size then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((dogCtorWardsHashMem I vat).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨192⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [dogCtorWardsHashMem_size]
    decide
  · simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      dogCtorWardsHashMem_read64 I vat


theorem dogCtorRuntime_codecopy_mem (I : ExecutionEnv) (vat : AccountAddress) :
    (dogCtorCode vat).write 182 (dogCtorWardsHashMem I vat) 0 4745 =
      dogBytecode := by
  rw [write0_eq_extract_from_of_base_le]
  · exact dogCtorCode_runtime_window vat
  · norm_num
  · rw [dogCtorCode_size]
    norm_num
  · rw [dogCtorWardsHashMem_size]
    norm_num


theorem dogPatchRuntime_eq_ctorPatchedRuntime (vat : AccountAddress) :
    patchRuntime dogBytecode (patches { vat := vat }) =
      some (dogCtorPatchedRuntime vat) := by
  simp [dogCtorPatchedRuntime, patchRuntime, patches, patchesFrom, offsets, immValues,
    Reasoning.Theory.wordBytes?, valueToWord, List.lookup_cons, dogRuntimeWrites, writeCascade]
  rw [← toByteArray_eq_toBytesBE (EVM.Word.ofNat vat.val)]
  rw [spliceBytes_toByteArray_eq_writeWord dogBytecode 1405]
  · simp
    have hgap1405 : 1405 - dogBytecode.size < USize.size := by
      rw [dogBytecode_size]
      norm_num
    have hsize1405 : (writeWord dogBytecode 1405 (EVM.word vat.val)).size = 4745 := by
      rw [writeWord_size _ _ _ hgap1405]
      rw [dogBytecode_size]
      norm_num
    have h2890 := spliceBytes_toByteArray_eq_writeWord
      (writeWord dogBytecode 1405 (EVM.word vat.val)) 2890 (EVM.word vat.val)
      (by rw [hsize1405]; norm_num)
    cases hsp2890 :
        spliceBytes? (writeWord dogBytecode 1405 (EVM.word vat.val)) 2890
          (UInt256.toByteArray (EVM.word vat.val)) with
    | none =>
        rw [hsp2890] at h2890
        cases h2890
    | some p2890 =>
        rw [hsp2890] at h2890
        cases h2890
        have hgap2890 :
            2890 - (writeWord dogBytecode 1405 (EVM.word vat.val)).size < USize.size := by
          rw [hsize1405]
          norm_num
        have hsize2890 :
            (writeWord (writeWord dogBytecode 1405 (EVM.word vat.val)) 2890
              (EVM.word vat.val)).size = 4745 := by
          rw [writeWord_size _ _ _ hgap2890]
          rw [hsize1405]
          norm_num
        have h3170 := spliceBytes_toByteArray_eq_writeWord
          (writeWord (writeWord dogBytecode 1405 (EVM.word vat.val)) 2890
            (EVM.word vat.val)) 3170 (EVM.word vat.val)
          (by rw [hsize2890]; norm_num)
        cases hsp3170 :
            spliceBytes?
              (writeWord (writeWord dogBytecode 1405 (EVM.word vat.val)) 2890
                (EVM.word vat.val)) 3170 (UInt256.toByteArray (EVM.word vat.val)) with
        | none =>
            rw [hsp3170] at h3170
            cases h3170
        | some p3170 =>
            rw [hsp3170] at h3170
            cases h3170
            have hgap3170 :
                3170 - (writeWord
                  (writeWord dogBytecode 1405 (EVM.word vat.val)) 2890
                  (EVM.word vat.val)).size < USize.size := by
              rw [hsize2890]
              norm_num
            have hsize3170 :
                (writeWord
                  (writeWord
                    (writeWord dogBytecode 1405 (EVM.word vat.val)) 2890
                    (EVM.word vat.val)) 3170 (EVM.word vat.val)).size = 4745 := by
              rw [writeWord_size _ _ _ hgap3170]
              rw [hsize2890]
              norm_num
            have h3965 := spliceBytes_toByteArray_eq_writeWord
              (writeWord
                (writeWord
                  (writeWord dogBytecode 1405 (EVM.word vat.val)) 2890
                  (EVM.word vat.val)) 3170 (EVM.word vat.val)) 3965 (EVM.word vat.val)
              (by rw [hsize3170]; norm_num)
            cases hsp3965 :
                spliceBytes?
                  (writeWord
                    (writeWord
                      (writeWord dogBytecode 1405 (EVM.word vat.val)) 2890
                      (EVM.word vat.val)) 3170 (EVM.word vat.val)) 3965
                  (UInt256.toByteArray (EVM.word vat.val)) with
            | none =>
                rw [hsp3965] at h3965
                cases h3965
            | some p3965 =>
                rw [hsp3965] at h3965
                cases h3965
                change
                  (spliceBytes? (writeWord dogBytecode 1405 (EVM.word vat.val)) 2890
                    (UInt256.toByteArray (EVM.word vat.val))).bind
                    (fun init =>
                      (spliceBytes? init 3170 (UInt256.toByteArray (EVM.word vat.val))).bind
                        (fun init =>
                          spliceBytes? init 3965 (UInt256.toByteArray (EVM.word vat.val)))) =
                    some
                      (writeWord
                        (writeWord
                          (writeWord
                            (writeWord dogBytecode 1405 (EVM.word vat.val)) 2890
                            (EVM.word vat.val)) 3170 (EVM.word vat.val)) 3965
                        (EVM.word vat.val))
                rw [hsp2890]
                simp only [Option.bind]
                rw [hsp3170]
                change
                  spliceBytes?
                    (writeWord
                      (writeWord
                        (writeWord dogBytecode 1405 (EVM.word vat.val)) 2890
                        (EVM.word vat.val)) 3170 (EVM.word vat.val)) 3965
                    (UInt256.toByteArray (EVM.word vat.val)) =
                    some
                      (writeWord
                        (writeWord
                          (writeWord
                            (writeWord dogBytecode 1405 (EVM.word vat.val)) 2890
                            (EVM.word vat.val)) 3170 (EVM.word vat.val)) 3965
                        (EVM.word vat.val))
                rw [hsp3965]
  · rw [dogBytecode_size]
    norm_num

theorem dogCtorPatchedRuntime_size (vat : AccountAddress) :
    (dogCtorPatchedRuntime vat).size = 4745 := by
  unfold dogCtorPatchedRuntime
  exact writeCascade_size_of_base dogBytecode (dogRuntimeWrites vat) (base := 4745) (out := 4745)
    (by native_decide) (by simp [dogRuntimeWrites, WriteGapsOk])
    (by simp [dogRuntimeWrites, writeCascadeSize])

theorem dogCtorPatchedRuntime_read (vat : AccountAddress) :
    (dogCtorPatchedRuntime vat).readWithPadding 0 4745 =
      dogCtorPatchedRuntime vat := by
  rw [readWithPadding_eq_extract' _ 0 4745 (by norm_num) (by norm_num)
    (by rw [dogCtorPatchedRuntime_size])]
  rw [show 4745 = (dogCtorPatchedRuntime vat).size by rw [dogCtorPatchedRuntime_size]]
  simpa [Nat.zero_add] using byteArray_extract_self (dogCtorPatchedRuntime vat)

end Benchmarks.Dss.Dog
