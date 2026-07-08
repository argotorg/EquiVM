import Benchmarks.Dss.Flopper.Common
import Reasoning.Initcode
import Solm.Equiv

/-!
# MakerDAO/Sky DSS Flopper constructor shared helpers
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flopper

set_option maxRecDepth 2000000

abbrev flopperCtorBegWord : UInt256 := ⟨1050000000000000000⟩
abbrev flopperCtorPadWord : UInt256 := ⟨1500000000000000000⟩
abbrev flopperCtorTtlWord : UInt256 := ⟨10800⟩
abbrev flopperCtorTauWord : UInt256 := ⟨172800⟩

def flopperCtorArgsTail (vat gem : AccountAddress) : ByteArray :=
  (EVM.Word.toBytesBE (EVM.word vat.val) ++
    EVM.Word.toBytesBE (EVM.word gem.val)).toByteArray

noncomputable def flopperCtorCode (vat gem : AccountAddress) : ByteArray :=
  flopperCreationBytecode ++ flopperCtorArgsTail vat gem

private theorem byteArray_append_toList (a b : ByteArray) :
    (a ++ b).toList = a.toList ++ b.toList := by
  rw [byteArray_toList_eq, byteArray_toList_eq, byteArray_toList_eq]
  simp [ByteArray.data_append]

private theorem list_toByteArray_toList (xs : List UInt8) : xs.toByteArray.toList = xs := by
  rw [byteArray_toList_eq]
  simp

theorem flopperCtorDeployment_shape {args : List Value} {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment flopperCreationBytecode args = some deployedInitcode) :
    ∃ vat gem : AccountAddress,
      args = [.address vat, .address gem] ∧
      deployedInitcode = flopperCtorCode vat gem := by
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
              simpa [flopperCtorCode, flopperCtorArgsTail] using hdeploy.symm

macro "flopper_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [Reasoning.Theory.decode_append_left_window
          flopperCreationBytecode _ _ (by native_decide) (by native_decide)]
      | (unfold flopperCtorCode
         rw [Reasoning.Theory.decode_append_left_window
          flopperCreationBytecode _ _ (by native_decide) (by native_decide)]);
     native_decide))

macro "flopper_ctor_jd" : tactic =>
  `(tactic|
    (first
      | exact Reasoning.Theory.D_J_contains_append_left flopperCreationBytecode _ _ (by jump_dest)
      | (unfold flopperCtorCode
         exact Reasoning.Theory.D_J_contains_append_left flopperCreationBytecode _ _ (by jump_dest))))

open Lean in
macro "flopper_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by flopper_ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by flopper_ctor_decode) $(args[0]!) $(args[1]!)
                            (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by flopper_ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by flopper_ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

theorem flopperCreationBytecode_size : flopperCreationBytecode.size = 5000 := by
  native_decide

theorem flopperBytecode_size : flopperBytecode.size = 4780 := by
  native_decide

theorem flopperCtorArgsTail_size (vat gem : AccountAddress) :
    (flopperCtorArgsTail vat gem).size = 64 := by
  rw [flopperCtorArgsTail, list_toByteArray_size]
  simp only [List.length_append]
  have h1 : (EVM.Word.toBytesBE (EVM.word vat.val)).length = 32 := by
    simpa [list_toByteArray_size] using word_toBytesBE_toByteArray_size (EVM.word vat.val)
  have h2 : (EVM.Word.toBytesBE (EVM.word gem.val)).length = 32 := by
    simpa [list_toByteArray_size] using word_toBytesBE_toByteArray_size (EVM.word gem.val)
  omega

theorem flopperCtorCode_size (vat gem : AccountAddress) :
    (flopperCtorCode vat gem).size = 5064 := by
  unfold flopperCtorCode
  rw [ByteArray.size_append, flopperCreationBytecode_size, flopperCtorArgsTail_size]

theorem flopperCtorArgLen_eq (vat gem : AccountAddress) :
    (UInt256.ofNat (flopperCtorCode vat gem).size).sub ⟨5000⟩ = (⟨64⟩ : UInt256) := by
  rw [flopperCtorCode_size]
  native_decide

theorem flopperCreationBytecode_runtime_window :
    flopperCreationBytecode.extract 220 (220 + 4780) = flopperBytecode := by
  native_decide

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

noncomputable def flopperCtorCopiedMem (vat gem : AccountAddress) : ByteArray :=
  (flopperCtorCode vat gem).write 5000 solcFreePtrMem 128 64

noncomputable def flopperCtorArgsMem (vat gem : AccountAddress) : ByteArray :=
  (UInt256.toByteArray ⟨192⟩).write 0 (flopperCtorCopiedMem vat gem) 64 32

theorem flopperCtorCopiedMem_eq (vat gem : AccountAddress) :
    flopperCtorCopiedMem vat gem =
      solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
        flopperCtorArgsTail vat gem := by
  rw [flopperCtorCopiedMem, flopperCtorCode, byteArray_write_from_ge_eq]
  · rw [extract_append_right' flopperCreationBytecode (flopperCtorArgsTail vat gem)
      5000 (5000 + 64)]
    · rw [solcFreePtrMem_size]
    · exact flopperCreationBytecode_size.symm
    · rw [flopperCtorArgsTail_size]
      native_decide
  · decide
  · rw [ByteArray.size_append, flopperCreationBytecode_size, flopperCtorArgsTail_size]
  · rw [solcFreePtrMem_size]
    decide
  · rw [solcFreePtrMem_size]
    exact lt_usize 32 (by norm_num)

private theorem flopperCtorArgsMem_base_size (vat gem : AccountAddress) :
    (solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
      flopperCtorArgsTail vat gem).size = 192 := by
  rw [ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
    zeroes_ofNat_size _ (by norm_num), flopperCtorArgsTail_size]

theorem flopperCtorArgsMem_size (vat gem : AccountAddress) :
    (flopperCtorArgsMem vat gem).size = 192 := by
  rw [flopperCtorArgsMem, flopperCtorCopiedMem_eq]
  rw [toByteArray_write32_size_of_le
    (base := solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
      flopperCtorArgsTail vat gem)
    (word := (⟨192⟩ : UInt256)) (off := 64) (baseSize := 192) (finalSize := 192)]
  · exact flopperCtorArgsMem_base_size vat gem
  · rw [flopperCtorArgsMem_base_size]
    omega
  · native_decide

private theorem flopperCtorArgsTail_extract_first (vat gem : AccountAddress) :
    (flopperCtorArgsTail vat gem).extract 0 32 =
      UInt256.toByteArray (EVM.word vat.val) := by
  simp [flopperCtorArgsTail, word_toBytesBE_toByteArray_eq_toByteArray, extract_append_left,
    extract_append_right_window, toByteArray_extract_all]

private theorem flopperCtorArgsTail_extract_second (vat gem : AccountAddress) :
    (flopperCtorArgsTail vat gem).extract 32 64 =
      UInt256.toByteArray (EVM.word gem.val) := by
  simp [flopperCtorArgsTail, word_toBytesBE_toByteArray_eq_toByteArray, extract_append_left,
    extract_append_right_window, toByteArray_extract_all]

private theorem flopperCtorArgsMem_read_word (vat gem : AccountAddress)
    (start : Nat)
    (hstart : start + 32 ≤ 64)
    (hextract :
      (flopperCtorArgsTail vat gem).extract start (start + 32) =
        UInt256.toByteArray (if start = 0 then EVM.word vat.val else EVM.word gem.val)) :
    (flopperCtorArgsMem vat gem).readWithPadding (128 + start) 32 =
      UInt256.toByteArray (if start = 0 then EVM.word vat.val else EVM.word gem.val) := by
  rw [flopperCtorArgsMem, flopperCtorCopiedMem_eq]
  rw [write32_read_above_len
    (src := UInt256.toByteArray (⟨192⟩ : UInt256))
    (base := solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
      flopperCtorArgsTail vat gem)
    (dest := 64) (read := 128 + start) (len := 32)]
  · have hprefix :
        (solcFreePtrMem ++ ffi.ByteArray.zeroes 32).size = 128 := by
      rw [ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size 32 (by norm_num)]
    rw [readWithPadding_eq_extract'
      (solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
        flopperCtorArgsTail vat gem)
      (128 + start) 32 (by norm_num) (by norm_num)
      (by rw [flopperCtorArgsMem_base_size]; omega)]
    rw [extract_append_right_window
      (solcFreePtrMem ++ ffi.ByteArray.zeroes 32)
      (flopperCtorArgsTail vat gem) (128 + start) (128 + start + 32)
      (by rw [hprefix]; omega), hprefix]
    rw [show 128 + start - 128 = start by omega,
      show 128 + start + 32 - 128 = start + 32 by omega]
    exact hextract
  · rw [toByteArray_size]
  · rw [flopperCtorArgsMem_base_size]
    omega
  · omega
  · rw [flopperCtorArgsMem_base_size]
    omega
  · norm_num
  · norm_num

theorem flopperCtorArgsMem_mload_vat (vat gem : AccountAddress) :
    (if (⟨128⟩ : UInt256).toNat ≥ (flopperCtorArgsMem vat gem).size ∨
        (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((flopperCtorArgsMem vat gem).readWithPadding 128 32))) =
      EVM.word vat.val := by
  apply mloadWordValue_of_readWithPadding
  · rw [flopperCtorArgsMem_size]
    decide
  · decide
  · simpa using
      flopperCtorArgsMem_read_word vat gem 0 (by norm_num)
        (by simpa using flopperCtorArgsTail_extract_first vat gem)

theorem flopperCtorArgsMem_mload_gem (vat gem : AccountAddress) :
    (if (⟨160⟩ : UInt256).toNat ≥ (flopperCtorArgsMem vat gem).size ∨
        (⟨160⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((flopperCtorArgsMem vat gem).readWithPadding 160 32))) =
      EVM.word gem.val := by
  apply mloadWordValue_of_readWithPadding
  · rw [flopperCtorArgsMem_size]
    decide
  · decide
  · simpa using
      flopperCtorArgsMem_read_word vat gem 32 (by norm_num)
        (by simpa using flopperCtorArgsTail_extract_second vat gem)

abbrev flopperCtorCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

noncomputable def flopperCtorWardsHashMem (I : ExecutionEnv) (vat gem : AccountAddress) :
    ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨0⟩ (flopperCtorArgsMem vat gem)

theorem flopperCtorWardsHashMem_size (I : ExecutionEnv) (vat gem : AccountAddress) :
    (flopperCtorWardsHashMem I vat gem).size = 192 := by
  have hfirstSize :
      ((UInt256.toByteArray (solcSourceWord I)).write 0
          (flopperCtorArgsMem vat gem) 0 32).size = 192 := by
    exact toByteArray_write32_size_of_le
      (base := flopperCtorArgsMem vat gem) (word := solcSourceWord I)
      (off := 0) (baseSize := 192) (finalSize := 192)
      (flopperCtorArgsMem_size vat gem)
      (by rw [flopperCtorArgsMem_size]; omega) (by omega)
  unfold flopperCtorWardsHashMem twoWordHashMem wordAt32Mem wordAt0Mem
  exact toByteArray_write32_size_of_le
      (base := (UInt256.toByteArray (solcSourceWord I)).write 0
        (flopperCtorArgsMem vat gem) 0 32)
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

theorem flopperCtorWardsHashSlot (I : ExecutionEnv) (vat gem : AccountAddress) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((flopperCtorWardsHashMem I vat gem).readWithPadding 0 64))) =
      flopperCtorCallerWardsSlot I := by
  unfold flopperCtorWardsHashMem flopperCtorCallerWardsSlot solcMappingSlot
  rw [twoWordHashMem_read0_64_192]
  · exact mappingSlot_single (solcSourceWord I) ⟨0⟩
  · exact flopperCtorArgsMem_size vat gem

noncomputable def flopperCtorReturnMem (I : ExecutionEnv) (vat gem : AccountAddress) : ByteArray :=
  (flopperCtorCode vat gem).write 220 (flopperCtorWardsHashMem I vat gem) 0 4780

theorem flopperCtorReturnMem_read (I : ExecutionEnv) (vat gem : AccountAddress) :
    (flopperCtorReturnMem I vat gem).readWithPadding 0 4780 = flopperBytecode := by
  unfold flopperCtorReturnMem
  rw [write0_read_back_from_gen (flopperCtorCode vat gem) (flopperCtorWardsHashMem I vat gem)
    220 4780
    (by decide) (by
      unfold flopperCtorCode
      rw [ByteArray.size_append, flopperCreationBytecode_size, flopperCtorArgsTail_size]
      omega) (by decide)]
  have hleft :
      (flopperCtorCode vat gem).extract 220 (220 + 4780) =
        flopperCreationBytecode.extract 220 (220 + 4780) := by
    unfold flopperCtorCode
    exact extract_append_left flopperCreationBytecode (flopperCtorArgsTail vat gem) 220
      (220 + 4780) (by rw [flopperCreationBytecode_size])
  rw [hleft, flopperCreationBytecode_runtime_window]

theorem word_val_addr_canonical (a : AccountAddress) :
    (EVM.word a.val).toNat < EVM.addressModulus := by
  have hsize : AccountAddress.size < UInt256.size := by decide
  have hval : (EVM.word a.val).toNat = a.val := by
    change (UInt256.ofNat a.val).toNat = a.val
    rw [UInt256.toNat_ofNat_of_lt (lt_trans a.isLt hsize)]
  rw [hval]
  exact a.isLt

abbrev flopperCtorVatStored (σ : AccountMap) (I : ExecutionEnv) (vat : AccountAddress) :
    UInt256 :=
  setAddressOffset0Word (solcSlotWord σ I ⟨2⟩) (EVM.word vat.val)

abbrev flopperCtorGemStored (σ : AccountMap) (I : ExecutionEnv) (gem : AccountAddress) :
    UInt256 :=
  setAddressOffset0Word (solcSlotWord σ I ⟨3⟩) (EVM.word gem.val)

abbrev flopperCtorDefaultsSlot6Word (old : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.shiftLeft ⟨172800⟩ ⟨48⟩)
    (UInt256.land
      (UInt256.lnot (UInt256.shiftLeft flopperUint48Mask ⟨48⟩))
      (UInt256.lor (UInt256.land old (UInt256.lnot flopperUint48Mask)) ⟨10800⟩))

abbrev flopperCtorAfterBegMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨4⟩ flopperCtorBegWord

abbrev flopperCtorAfterPadMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (flopperCtorAfterBegMap σ I) ⟨5⟩ flopperCtorPadWord

abbrev flopperCtorAfterPackedDefaultsMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (flopperCtorAfterPadMap σ I) ⟨6⟩
    (flopperCtorDefaultsSlot6Word (solcSlotWord (flopperCtorAfterPadMap σ I) I ⟨6⟩))

abbrev flopperCtorAfterKicksMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (flopperCtorAfterPackedDefaultsMap σ I) ⟨7⟩ ⟨0⟩

abbrev flopperCtorAfterWardsMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (flopperCtorCallerWardsSlot I) ⟨1⟩

abbrev flopperCtorAfterVatMap (σ : AccountMap) (I : ExecutionEnv) (vat : AccountAddress) :
    AccountMap :=
  sstoreAccountMap I.codeOwner (flopperCtorAfterWardsMap σ I) ⟨2⟩
    (flopperCtorVatStored (flopperCtorAfterWardsMap σ I) I vat)

abbrev flopperCtorAfterGemMap
    (σ : AccountMap) (I : ExecutionEnv) (vat gem : AccountAddress) : AccountMap :=
  sstoreAccountMap I.codeOwner (flopperCtorAfterVatMap σ I vat) ⟨3⟩
    (flopperCtorGemStored (flopperCtorAfterVatMap σ I vat) I gem)

abbrev flopperCtorFinalMap
    (σ : AccountMap) (I : ExecutionEnv) (vat gem : AccountAddress) : AccountMap :=
  sstoreAccountMap I.codeOwner (flopperCtorAfterGemMap σ I vat gem) ⟨8⟩ ⟨1⟩

theorem flopperCtorCallerWardsSlot_eq (I : ExecutionEnv) :
    wardsSlot (.address I.source) = flopperCtorCallerWardsSlot I := by
  unfold wardsSlot mapSlot flopperCtorCallerWardsSlot solcMappingSlot solcSourceWord
  rw [keyValueToWord_address]

end Benchmarks.Dss.Flopper
