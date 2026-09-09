import Benchmarks.Dss.Flapper.Common
import Reasoning.Initcode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Flapper constructor shared helpers
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

set_option maxRecDepth 2000000

abbrev flapperCtorBegWord : UInt256 := ⟨1050000000000000000⟩
abbrev flapperCtorTtlWord : UInt256 := ⟨10800⟩
abbrev flapperCtorTauWord : UInt256 := ⟨172800⟩

def flapperCtorArgsTail (vat gem : AccountAddress) : ByteArray :=
  (EVM.Word.toBytesBE (EVM.word vat.val) ++
    EVM.Word.toBytesBE (EVM.word gem.val)).toByteArray

noncomputable def flapperCtorCode (vat gem : AccountAddress) : ByteArray :=
  flapperCreationBytecode ++ flapperCtorArgsTail vat gem

private theorem byteArray_append_toList (a b : ByteArray) :
    (a ++ b).toList = a.toList ++ b.toList := by
  rw [byteArray_toList_eq, byteArray_toList_eq, byteArray_toList_eq]
  simp [ByteArray.data_append]

private theorem list_toByteArray_toList (xs : List UInt8) : xs.toByteArray.toList = xs := by
  rw [byteArray_toList_eq]
  simp

theorem flapperCtorDeployment_shape {args : List Value} {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment flapperCreationBytecode args = some deployedInitcode) :
    ∃ vat gem : AccountAddress,
      args = [.address vat, .address gem] ∧
      deployedInitcode = flapperCtorCode vat gem := by
  simp [config, contract, constructorDecl, Solm.genSolidityConstructorDeployment] at hdeploy
  cases args with
  | nil =>
      simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr] at hdeploy
  | cons a rest =>
      cases rest with
      | nil =>
          simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr] at hdeploy
      | cons b rest2 =>
          cases rest2 with
          | cons _ _ =>
              cases a <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr,
                ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
                ABI.encodeABIValue?, ABI.encodeABIWord?] at hdeploy
          | nil =>
              cases a <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr,
                ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
                ABI.encodeABIValue?, ABI.encodeABIWord?] at hdeploy
              rename_i vat
              cases b <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr,
                ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
                ABI.encodeABIValue?, ABI.encodeABIWord?] at hdeploy
              rename_i gem
              refine ⟨vat, gem, rfl, ?_⟩
              simpa [flapperCtorCode, flapperCtorArgsTail] using hdeploy.symm

macro "flapper_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [Reasoning.Theory.decode_append_left_window
          flapperCreationBytecode _ _ (by decide +native) (by decide +native)]
      | (unfold flapperCtorCode
         rw [Reasoning.Theory.decode_append_left_window
          flapperCreationBytecode _ _ (by decide +native) (by decide +native)]);
     decide +native))

macro "flapper_ctor_jd" : tactic =>
  `(tactic|
    (first
      | exact Reasoning.Theory.D_J_contains_append_left flapperCreationBytecode _ _ (by jump_dest)
      | (unfold flapperCtorCode
         exact Reasoning.Theory.D_J_contains_append_left flapperCreationBytecode _ _ (by jump_dest))))

open Lean in
macro "flapper_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by flapper_ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by flapper_ctor_decode) $(args[0]!) $(args[1]!)
                            (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by flapper_ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by flapper_ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

theorem flapperCreationBytecode_size : flapperCreationBytecode.size = 5216 := by
  decide +native

theorem flapperBytecode_size : flapperBytecode.size = 5008 := by
  decide +native

theorem flapperCtorArgsTail_size (vat gem : AccountAddress) :
    (flapperCtorArgsTail vat gem).size = 64 := by
  rw [flapperCtorArgsTail, list_toByteArray_size]
  simp only [List.length_append]
  have h1 : (EVM.Word.toBytesBE (EVM.word vat.val)).length = 32 := by
    simpa [list_toByteArray_size] using word_toBytesBE_toByteArray_size (EVM.word vat.val)
  have h2 : (EVM.Word.toBytesBE (EVM.word gem.val)).length = 32 := by
    simpa [list_toByteArray_size] using word_toBytesBE_toByteArray_size (EVM.word gem.val)
  omega

theorem flapperCtorCode_size (vat gem : AccountAddress) :
    (flapperCtorCode vat gem).size = 5280 := by
  unfold flapperCtorCode
  rw [ByteArray.size_append, flapperCreationBytecode_size, flapperCtorArgsTail_size]

theorem flapperCtorArgLen_eq (vat gem : AccountAddress) :
    (UInt256.ofNat (flapperCtorCode vat gem).size).sub ⟨5216⟩ = (⟨64⟩ : UInt256) := by
  rw [flapperCtorCode_size]
  decide +native

theorem flapperCreationBytecode_runtime_window :
    flapperCreationBytecode.extract 208 (208 + 5008) = flapperBytecode := by
  decide +native

private theorem byteArray_write_from_ge_eq (src base : ByteArray) (srcAddr destAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size)
    (hbase : base.size ≤ destAddr) (hgap : destAddr - base.size < USize.size) :
    src.write srcAddr base destAddr len =
      base ++ ffi.ByteArray.zeroes (destAddr - base.size) ++
        src.extract srcAddr (srcAddr + len) := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ srcAddr ≥ src.size from by omega)]
  have hcopy : min len (src.size - srcAddr) = len := by omega
  have htail : min base.size (destAddr + len) - (destAddr + len) = 0 := by omega
  simp only [hcopy, htail, ByteArray.data_copySlice, ByteArray.data_append,
    ByteArray.data_extract]
  have hpz : (ffi.ByteArray.zeroes (destAddr - base.size)).data.size =
      destAddr - base.size := by
    rw [show (ffi.ByteArray.zeroes (destAddr - base.size)).data.size =
          (ffi.ByteArray.zeroes (destAddr - base.size)).size from rfl,
      ByteArray_zeroes_size]
  have hDsz :
      (base.data ++ (ffi.ByteArray.zeroes (destAddr - base.size)).data).size =
        destAddr := by
    rw [Array.size_append, hpz, show base.data.size = base.size from rfl]
    omega
  rw [show (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
    rw [zeroes_zero (n := 0) (by rfl)]
    rfl]
  simp only [Array.append_empty, Nat.add_zero]
  rw [show min len (src.data.size - srcAddr) = len by
    have : src.data.size = src.size := rfl
    omega]
  rw [Array.extract_eq_self_of_le (by rw [hDsz])]
  rw [show
      (base.data ++ (ffi.ByteArray.zeroes (destAddr - base.size)).data).extract
        (destAddr + len) = #[] from by
    apply Array.extract_eq_empty_of_le
    rw [hDsz]
    omega]
  simp [Array.append_assoc]

noncomputable def flapperCtorCopiedMem (vat gem : AccountAddress) : ByteArray :=
  (flapperCtorCode vat gem).write 5216 solcFreePtrMem 128 64

noncomputable def flapperCtorArgsMem (vat gem : AccountAddress) : ByteArray :=
  (UInt256.toByteArray ⟨192⟩).write 0 (flapperCtorCopiedMem vat gem) 64 32

theorem flapperCtorCopiedMem_eq (vat gem : AccountAddress) :
    flapperCtorCopiedMem vat gem =
      solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
        flapperCtorArgsTail vat gem := by
  rw [flapperCtorCopiedMem, flapperCtorCode, byteArray_write_from_ge_eq]
  · rw [extract_append_right' flapperCreationBytecode (flapperCtorArgsTail vat gem)
      5216 (5216 + 64)]
    · rw [solcFreePtrMem_size]
    · exact flapperCreationBytecode_size.symm
    · rw [flapperCtorArgsTail_size]
      decide +native
  · decide
  · rw [ByteArray.size_append, flapperCreationBytecode_size, flapperCtorArgsTail_size]
  · rw [solcFreePtrMem_size]
    decide
  · rw [solcFreePtrMem_size]
    exact lt_usize 32 (by norm_num)

private theorem flapperCtorArgsMem_base_size (vat gem : AccountAddress) :
    (solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
      flapperCtorArgsTail vat gem).size = 192 := by
  rw [ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
    zeroes_ofNat_size _ (by norm_num), flapperCtorArgsTail_size]

theorem flapperCtorArgsMem_size (vat gem : AccountAddress) :
    (flapperCtorArgsMem vat gem).size = 192 := by
  rw [flapperCtorArgsMem, flapperCtorCopiedMem_eq]
  rw [toByteArray_write32_size_of_le
    (base := solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
      flapperCtorArgsTail vat gem)
    (word := (⟨192⟩ : UInt256)) (off := 64) (baseSize := 192) (finalSize := 192)]
  · exact flapperCtorArgsMem_base_size vat gem
  · rw [flapperCtorArgsMem_base_size]
    omega
  · decide +native

private theorem flapperCtorArgsTail_extract_first (vat gem : AccountAddress) :
    (flapperCtorArgsTail vat gem).extract 0 32 =
      UInt256.toByteArray (EVM.word vat.val) := by
  simp [flapperCtorArgsTail, word_toBytesBE_toByteArray_eq_toByteArray, extract_append_left,
    extract_append_right_window, toByteArray_extract_all]

private theorem flapperCtorArgsTail_extract_second (vat gem : AccountAddress) :
    (flapperCtorArgsTail vat gem).extract 32 64 =
      UInt256.toByteArray (EVM.word gem.val) := by
  simp [flapperCtorArgsTail, word_toBytesBE_toByteArray_eq_toByteArray, extract_append_left,
    extract_append_right_window, toByteArray_extract_all]

private theorem flapperCtorArgsMem_read_word (vat gem : AccountAddress)
    (start : Nat)
    (hstart : start + 32 ≤ 64)
    (hextract :
      (flapperCtorArgsTail vat gem).extract start (start + 32) =
        UInt256.toByteArray (if start = 0 then EVM.word vat.val else EVM.word gem.val)) :
    (flapperCtorArgsMem vat gem).readWithPadding (128 + start) 32 =
      UInt256.toByteArray (if start = 0 then EVM.word vat.val else EVM.word gem.val) := by
  rw [flapperCtorArgsMem, flapperCtorCopiedMem_eq]
  rw [write32_read_above_len
    (src := UInt256.toByteArray (⟨192⟩ : UInt256))
    (base := solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
      flapperCtorArgsTail vat gem)
    (dest := 64) (read := 128 + start) (len := 32)]
  · have hprefix :
        (solcFreePtrMem ++ ffi.ByteArray.zeroes 32).size = 128 := by
      rw [ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size 32 (by norm_num)]
    rw [readWithPadding_eq_extract'
      (solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
        flapperCtorArgsTail vat gem)
      (128 + start) 32 (by norm_num) (by norm_num)
      (by rw [flapperCtorArgsMem_base_size]; omega)]
    rw [extract_append_right_window
      (solcFreePtrMem ++ ffi.ByteArray.zeroes 32)
      (flapperCtorArgsTail vat gem) (128 + start) (128 + start + 32)
      (by rw [hprefix]; omega), hprefix]
    rw [show 128 + start - 128 = start by omega,
      show 128 + start + 32 - 128 = start + 32 by omega]
    exact hextract
  · rw [toByteArray_size]
  · rw [flapperCtorArgsMem_base_size]
    omega
  · omega
  · rw [flapperCtorArgsMem_base_size]
    omega
  · norm_num
  · norm_num

theorem flapperCtorArgsMem_mload_vat (vat gem : AccountAddress) :
    (if (⟨128⟩ : UInt256).toNat ≥ (flapperCtorArgsMem vat gem).size ∨
        (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((flapperCtorArgsMem vat gem).readWithPadding 128 32))) =
      EVM.word vat.val := by
  apply mloadWordValue_of_readWithPadding
  · rw [flapperCtorArgsMem_size]
    decide
  · decide
  · simpa using
      flapperCtorArgsMem_read_word vat gem 0 (by norm_num)
        (by simpa using flapperCtorArgsTail_extract_first vat gem)

theorem flapperCtorArgsMem_mload_gem (vat gem : AccountAddress) :
    (if (⟨160⟩ : UInt256).toNat ≥ (flapperCtorArgsMem vat gem).size ∨
        (⟨160⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((flapperCtorArgsMem vat gem).readWithPadding 160 32))) =
      EVM.word gem.val := by
  apply mloadWordValue_of_readWithPadding
  · rw [flapperCtorArgsMem_size]
    decide
  · decide
  · simpa using
      flapperCtorArgsMem_read_word vat gem 32 (by norm_num)
        (by simpa using flapperCtorArgsTail_extract_second vat gem)

abbrev flapperCtorCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

noncomputable def flapperCtorWardsHashMem (I : ExecutionEnv) (vat gem : AccountAddress) :
    ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨0⟩ (flapperCtorArgsMem vat gem)

theorem flapperCtorWardsHashMem_size (I : ExecutionEnv) (vat gem : AccountAddress) :
    (flapperCtorWardsHashMem I vat gem).size = 192 := by
  have hfirstSize :
      ((UInt256.toByteArray (solcSourceWord I)).write 0
          (flapperCtorArgsMem vat gem) 0 32).size = 192 := by
    exact toByteArray_write32_size_of_le
      (base := flapperCtorArgsMem vat gem) (word := solcSourceWord I)
      (off := 0) (baseSize := 192) (finalSize := 192)
      (flapperCtorArgsMem_size vat gem)
      (by rw [flapperCtorArgsMem_size]; omega) (by omega)
  unfold flapperCtorWardsHashMem twoWordHashMem wordAt32Mem wordAt0Mem
  exact toByteArray_write32_size_of_le
      (base := (UInt256.toByteArray (solcSourceWord I)).write 0
        (flapperCtorArgsMem vat gem) 0 32)
      (word := (⟨0⟩ : UInt256)) (off := 32) (baseSize := 192) (finalSize := 192)
      hfirstSize (by rw [hfirstSize]; omega) (by omega)

private theorem wordAt0Mem_size_192 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 192) :
    (wordAt0Mem word mem).size = 192 := by
  unfold wordAt0Mem
  exact toByteArray_write32_size_of_le mem word 0 192 192 hmem
    (by rw [hmem]; omega) (by omega)

private theorem wordAt32Mem_size_192 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 192) :
    (wordAt32Mem word mem).size = 192 := by
  unfold wordAt32Mem
  exact toByteArray_write32_size_of_le mem word 32 192 192 hmem
    (by rw [hmem]; omega) (by omega)

private theorem twoWordHashMem_read0_192 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 192) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_192 key hmem]; omega) (by omega)]
  exact wordAt0Mem_read0 key mem

private theorem twoWordHashMem_read32_192 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 192) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_192 key hmem]; omega)]
  exact toByteArray_extract_all slot

private theorem twoWordHashMem_read0_64_192 {mem : ByteArray} (key slot : UInt256)
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

theorem flapperCtorWardsHashSlot (I : ExecutionEnv) (vat gem : AccountAddress) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((flapperCtorWardsHashMem I vat gem).readWithPadding 0 64))) =
      flapperCtorCallerWardsSlot I := by
  unfold flapperCtorWardsHashMem flapperCtorCallerWardsSlot solcMappingSlot
  rw [twoWordHashMem_read0_64_192]
  · exact mappingSlot_single (solcSourceWord I) ⟨0⟩
  · exact flapperCtorArgsMem_size vat gem

noncomputable def flapperCtorReturnMem (I : ExecutionEnv) (vat gem : AccountAddress) : ByteArray :=
  (flapperCtorCode vat gem).write 208 (flapperCtorWardsHashMem I vat gem) 0 5008

theorem flapperCtorReturnMem_read (I : ExecutionEnv) (vat gem : AccountAddress) :
    (flapperCtorReturnMem I vat gem).readWithPadding 0 5008 = flapperBytecode := by
  unfold flapperCtorReturnMem
  rw [write0_read_back_from_gen (flapperCtorCode vat gem) (flapperCtorWardsHashMem I vat gem)
    208 5008
    (by decide) (by
      unfold flapperCtorCode
      rw [ByteArray.size_append, flapperCreationBytecode_size, flapperCtorArgsTail_size]
      omega) (by decide)]
  have hleft :
      (flapperCtorCode vat gem).extract 208 (208 + 5008) =
        flapperCreationBytecode.extract 208 (208 + 5008) := by
    unfold flapperCtorCode
    exact extract_append_left flapperCreationBytecode (flapperCtorArgsTail vat gem) 208
      (208 + 5008) (by rw [flapperCreationBytecode_size])
  rw [hleft, flapperCreationBytecode_runtime_window]

theorem word_val_addr_canonical (a : AccountAddress) :
    (EVM.word a.val).toNat < EVM.addressModulus := by
  have hsize : AccountAddress.size < UInt256.size := by decide
  have hval : (EVM.word a.val).toNat = a.val := by
    change (UInt256.ofNat a.val).toNat = a.val
    rw [UInt256.toNat_ofNat_of_lt (lt_trans a.isLt hsize)]
  rw [hval]
  exact a.isLt

abbrev flapperCtorVatStored (σ : AccountMap) (I : ExecutionEnv) (vat : AccountAddress) :
    UInt256 :=
  setAddressOffset0Word (solcSlotWord σ I ⟨2⟩) (EVM.word vat.val)

abbrev flapperCtorGemStored (σ : AccountMap) (I : ExecutionEnv) (gem : AccountAddress) :
    UInt256 :=
  setAddressOffset0Word (solcSlotWord σ I ⟨3⟩) (EVM.word gem.val)

abbrev flapperCtorDefaultsSlot5Word (old : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.shiftLeft ⟨172800⟩ ⟨48⟩)
    (UInt256.land
      (UInt256.lnot (UInt256.shiftLeft flapperUint48Mask ⟨48⟩))
      (UInt256.lor (UInt256.land old (UInt256.lnot flapperUint48Mask)) ⟨10800⟩))

abbrev flapperCtorAfterBegMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨4⟩ flapperCtorBegWord

abbrev flapperCtorAfterPackedDefaultsMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (flapperCtorAfterBegMap σ I) ⟨5⟩
    (flapperCtorDefaultsSlot5Word (solcSlotWord (flapperCtorAfterBegMap σ I) I ⟨5⟩))

abbrev flapperCtorAfterKicksMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (flapperCtorAfterPackedDefaultsMap σ I) ⟨6⟩ ⟨0⟩

abbrev flapperCtorAfterWardsMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (flapperCtorCallerWardsSlot I) ⟨1⟩

abbrev flapperCtorAfterVatMap (σ : AccountMap) (I : ExecutionEnv) (vat : AccountAddress) :
    AccountMap :=
  sstoreAccountMap I.codeOwner (flapperCtorAfterWardsMap σ I) ⟨2⟩
    (flapperCtorVatStored (flapperCtorAfterWardsMap σ I) I vat)

abbrev flapperCtorAfterGemMap
    (σ : AccountMap) (I : ExecutionEnv) (vat gem : AccountAddress) : AccountMap :=
  sstoreAccountMap I.codeOwner (flapperCtorAfterVatMap σ I vat) ⟨3⟩
    (flapperCtorGemStored (flapperCtorAfterVatMap σ I vat) I gem)

abbrev flapperCtorFinalMap
    (σ : AccountMap) (I : ExecutionEnv) (vat gem : AccountAddress) : AccountMap :=
  sstoreAccountMap I.codeOwner (flapperCtorAfterGemMap σ I vat gem) ⟨7⟩ ⟨1⟩

theorem flapperCtorCallerWardsSlot_eq (I : ExecutionEnv) :
    wardsSlot (.address I.source) = flapperCtorCallerWardsSlot I := by
  unfold wardsSlot mapSlot flapperCtorCallerWardsSlot solcMappingSlot solcSourceWord
  rw [keyValueToWord_address]

end Benchmarks.Dss.Flapper
