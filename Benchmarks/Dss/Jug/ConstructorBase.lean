import Benchmarks.Dss.Jug.Common
import Reasoning.ExternalCall
import Reasoning.Initcode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Jug constructor shared helpers

Shared bytecode, memory, and storage-slot facts used by the Jug constructor trace and source
semantics proofs.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

set_option maxRecDepth 2000000

/-- ABI-encoded constructor argument appended to `jugCreationBytecode`. -/
def jugCtorArgsTail (vat : AccountAddress) : ByteArray :=
  (EVM.Word.toBytesBE (EVM.word vat.val)).toByteArray

noncomputable def jugCtorCode (vat : AccountAddress) : ByteArray :=
  jugCreationBytecode ++ jugCtorArgsTail vat

theorem jugCtorDeployment_shape {args : List Value} {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment jugCreationBytecode args = some deployedInitcode) :
    ∃ vat : AccountAddress,
      args = [.address vat] ∧ deployedInitcode = jugCtorCode vat := by
  simp [config, contract, constructorDecl, Solm.genSolidityConstructorDeployment] at hdeploy
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
          simpa [jugCtorCode, jugCtorArgsTail] using hdeploy.symm

macro "jug_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [Reasoning.Theory.decode_append_left_window
          jugCreationBytecode _ _ (by native_decide) (by native_decide)]
      | (unfold jugCtorCode
         rw [Reasoning.Theory.decode_append_left_window
          jugCreationBytecode _ _ (by native_decide) (by native_decide)]);
     native_decide))

macro "jug_ctor_jd" : tactic =>
  `(tactic|
    (first
      | exact Reasoning.Theory.D_J_contains_append_left jugCreationBytecode _ _ (by jump_dest)
      | (unfold jugCtorCode
         exact Reasoning.Theory.D_J_contains_append_left jugCreationBytecode _ _ (by jump_dest))))

open Lean in
macro "jug_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by jug_ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by jug_ctor_decode) $(args[0]!) $(args[1]!)
                            (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by jug_ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by jug_ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

theorem jugCreationBytecode_size : jugCreationBytecode.size = 2560 := by
  native_decide

theorem jugBytecode_size : jugBytecode.size = 2440 := by
  native_decide

theorem jugCtorArgsTail_size (vat : AccountAddress) : (jugCtorArgsTail vat).size = 32 := by
  simpa [jugCtorArgsTail] using word_toBytesBE_toByteArray_size (EVM.word vat.val)

theorem jugCtorCode_size (vat : AccountAddress) : (jugCtorCode vat).size = 2592 := by
  unfold jugCtorCode
  rw [ByteArray.size_append, jugCreationBytecode_size, jugCtorArgsTail_size]

theorem jugCtorArgLen_eq (vat : AccountAddress) :
    (UInt256.ofNat (jugCtorCode vat).size).sub ⟨2560⟩ = (⟨32⟩ : UInt256) := by
  rw [jugCtorCode_size]
  native_decide

theorem jugCreationBytecode_runtime_window :
    jugCreationBytecode.extract 120 (120 + 2440) = jugBytecode := by
  native_decide

-- LIBRARY CANDIDATE: a generic `ByteArray.write` normalization when a copy extends a base.
private theorem byteArray_write_from_ge_eq (src base : ByteArray) (srcAddr destAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size)
    (hbase : base.size ≤ destAddr) (hgap : destAddr - base.size < USize.size) :
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
  rw [show (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
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

noncomputable def jugCtorArgMem (vat : AccountAddress) : ByteArray :=
  (jugCtorCode vat).write 2560 solcFreePtrMem 128 32

noncomputable def jugCtorArgFreeMem (vat : AccountAddress) : ByteArray :=
  (UInt256.toByteArray ⟨160⟩).write 0 (jugCtorArgMem vat) 64 32

theorem jugCtorArgMem_eq (vat : AccountAddress) :
    jugCtorArgMem vat =
      solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++ jugCtorArgsTail vat := by
  rw [jugCtorArgMem, jugCtorCode, byteArray_write_from_ge_eq]
  · rw [extract_append_right' jugCreationBytecode (jugCtorArgsTail vat) 2560 (2560 + 32)]
    · rw [solcFreePtrMem_size]
    · exact jugCreationBytecode_size.symm
    · rw [jugCtorArgsTail_size]
      native_decide
  · decide
  · rw [ByteArray.size_append, jugCreationBytecode_size, jugCtorArgsTail_size]
  · rw [solcFreePtrMem_size]
    decide
  · rw [solcFreePtrMem_size]
    exact lt_usize 32 (by norm_num)

theorem jugCtorArgMem_size (vat : AccountAddress) : (jugCtorArgMem vat).size = 160 := by
  rw [jugCtorArgMem_eq, ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
    zeroes_ofNat_size 32 (by norm_num), jugCtorArgsTail_size]

theorem jugCtorArgFreeMem_size (vat : AccountAddress) :
    (jugCtorArgFreeMem vat).size = 160 := by
  unfold jugCtorArgFreeMem
  exact toByteArray_write32_size_of_le (base := jugCtorArgMem vat) (word := (⟨160⟩ : UInt256))
    (off := 64) (baseSize := 160) (finalSize := 160) (jugCtorArgMem_size vat)
    (by rw [jugCtorArgMem_size]; omega) (by omega)

theorem jugCtorArgMem_read128 (vat : AccountAddress) :
    (jugCtorArgMem vat).readWithPadding 128 32 =
      UInt256.toByteArray (EVM.word vat.val) := by
  rw [jugCtorArgMem_eq]
  have hprefix :
      (solcFreePtrMem ++ ffi.ByteArray.zeroes 32).size = 128 := by
    rw [ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size 32 (by norm_num)]
  rw [readWithPadding_eq_extract'
    (solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++ jugCtorArgsTail vat)
    128 32 (by norm_num) (by norm_num) (by
      rw [ByteArray.size_append, hprefix, jugCtorArgsTail_size])]
  rw [extract_append_right_window
    (solcFreePtrMem ++ ffi.ByteArray.zeroes 32) (jugCtorArgsTail vat) 128
    (128 + 32) (by rw [hprefix]), hprefix]
  rw [show 128 - 128 = 0 by omega, show 128 + 32 - 128 = 32 by omega]
  simp [jugCtorArgsTail, word_toBytesBE_toByteArray_eq_toByteArray, toByteArray_extract_all]

theorem jugCtorArgFreeMem_read128 (vat : AccountAddress) :
    (jugCtorArgFreeMem vat).readWithPadding 128 32 =
      UInt256.toByteArray (EVM.word vat.val) := by
  unfold jugCtorArgFreeMem
  rw [write32_read_above _ _ 64 128 (by rw [toByteArray_size])
    (by rw [jugCtorArgMem_size]; omega) (by omega) (by rw [jugCtorArgMem_size])]
  exact jugCtorArgMem_read128 vat

theorem jugCtorArgFreeMem_mload128 (vat : AccountAddress) :
    (if (⟨128⟩ : UInt256).toNat ≥ (jugCtorArgFreeMem vat).size ∨
        (⟨128⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((jugCtorArgFreeMem vat).readWithPadding 128 32))) =
      EVM.word vat.val := by
  exact mloadWordValue_of_readWithPadding
    (mem := jugCtorArgFreeMem vat) (aw := UInt256.ofNat 5) (off := ⟨128⟩)
    (v := EVM.word vat.val)
    (by rw [jugCtorArgFreeMem_size]; decide)
    (by decide)
    (jugCtorArgFreeMem_read128 vat)

abbrev jugCtorCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

noncomputable def jugCtorWardsHashMem (I : ExecutionEnv) (vat : AccountAddress) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨0⟩ (jugCtorArgFreeMem vat)

private theorem wordAt0Mem_size_160 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 160) :
    (wordAt0Mem word mem).size = 160 := by
  unfold wordAt0Mem
  exact toByteArray_write32_size_of_le mem word 0 160 160 hmem
    (by rw [hmem]; omega) (by omega)

private theorem wordAt32Mem_size_160 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 160) :
    (wordAt32Mem word mem).size = 160 := by
  unfold wordAt32Mem
  exact toByteArray_write32_size_of_le mem word 32 160 160 hmem
    (by rw [hmem]; omega) (by omega)

theorem jugCtorWardsHashMem_size (I : ExecutionEnv) (vat : AccountAddress) :
    (jugCtorWardsHashMem I vat).size = 160 := by
  unfold jugCtorWardsHashMem twoWordHashMem
  exact wordAt32Mem_size_160 ⟨0⟩
    (wordAt0Mem_size_160 (solcSourceWord I) (jugCtorArgFreeMem_size vat))

private theorem twoWordHashMem_read0_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_160 key hmem]; omega) (by omega)]
  exact wordAt0Mem_read0 key mem

private theorem twoWordHashMem_read32_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_160 key hmem]; omega)]
  exact toByteArray_extract_all slot

private theorem twoWordHashMem_read0_64_160 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 160) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by
        unfold twoWordHashMem
        rw [wordAt32Mem_size_160]
        · omega
        · exact wordAt0Mem_size_160 key hmem)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0 (by
        unfold twoWordHashMem
        rw [wordAt32Mem_size_160]
        · omega
        · exact wordAt0Mem_size_160 key hmem),
      twoWordHashMem_read0_160 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32 (by
        unfold twoWordHashMem
        rw [wordAt32Mem_size_160]
        · omega
        · exact wordAt0Mem_size_160 key hmem),
      twoWordHashMem_read32_160 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
    rw [ByteArray.extract_append_extract]
    norm_num]
  rw [hleft, hright]

theorem jugCtorWardsHashSlot (I : ExecutionEnv) (vat : AccountAddress) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((jugCtorWardsHashMem I vat).readWithPadding 0 64))) =
      jugCtorCallerWardsSlot I := by
  unfold jugCtorWardsHashMem jugCtorCallerWardsSlot solcMappingSlot
  rw [twoWordHashMem_read0_64_160]
  · exact mappingSlot_single (solcSourceWord I) ⟨0⟩
  · exact jugCtorArgFreeMem_size vat

noncomputable def jugCtorReturnMem (I : ExecutionEnv) (vat : AccountAddress) : ByteArray :=
  (jugCtorCode vat).write 120 (jugCtorWardsHashMem I vat) 0 2440

theorem jugCtorReturnMem_read (I : ExecutionEnv) (vat : AccountAddress) :
    (jugCtorReturnMem I vat).readWithPadding 0 2440 = jugBytecode := by
  unfold jugCtorReturnMem
  rw [write0_read_back_from_gen (jugCtorCode vat) (jugCtorWardsHashMem I vat) 120 2440
    (by decide) (by
      unfold jugCtorCode
      rw [ByteArray.size_append, jugCreationBytecode_size, jugCtorArgsTail_size]
      omega) (by decide)]
  have hleft :
      (jugCtorCode vat).extract 120 (120 + 2440) =
        jugCreationBytecode.extract 120 (120 + 2440) := by
    unfold jugCtorCode
    exact extract_append_left jugCreationBytecode (jugCtorArgsTail vat) 120 (120 + 2440)
      (by rw [jugCreationBytecode_size])
  rw [hleft, jugCreationBytecode_runtime_window]

theorem word_val_addr_canonical (a : AccountAddress) :
    (EVM.word a.val).toNat < EVM.addressModulus := by
  have hsize : AccountAddress.size < UInt256.size := by decide
  have hval : (EVM.word a.val).toNat = a.val := by
    change (UInt256.ofNat a.val).toNat = a.val
    rw [UInt256.toNat_ofNat_of_lt (lt_trans a.isLt hsize)]
  rw [hval]
  exact a.isLt

abbrev jugCtorVatStored (σ : AccountMap) (I : ExecutionEnv) (vat : AccountAddress) : UInt256 :=
  setAddressOffset0Word (solcSlotWord σ I ⟨2⟩) (EVM.word vat.val)

end Benchmarks.Dss.Jug
