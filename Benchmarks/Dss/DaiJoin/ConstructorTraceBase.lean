import Benchmarks.Dss.DaiJoin.ConstructorSource

/-!
# MakerDAO/Sky DSS DaiJoin constructor EVM trace base

Shared bytecode, memory, and storage-slot facts for the constructor EVM trace.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.DaiJoin

set_option maxRecDepth 2000000

macro "daiJoin_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [Reasoning.Theory.decode_append_left_window
          daiJoinCreationBytecode _ _ (by native_decide) (by native_decide)]
      | (unfold daiJoinCtorCode
         rw [Reasoning.Theory.decode_append_left_window
          daiJoinCreationBytecode _ _ (by native_decide) (by native_decide)]);
     native_decide))

macro "daiJoin_ctor_jd" : tactic =>
  `(tactic|
    (first
      | exact Reasoning.Theory.D_J_contains_append_left daiJoinCreationBytecode _ _ (by jump_dest)
      | (unfold daiJoinCtorCode
         exact Reasoning.Theory.D_J_contains_append_left daiJoinCreationBytecode _ _
          (by jump_dest))))

open Lean in
macro "daiJoin_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by daiJoin_ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by daiJoin_ctor_decode) $(args[0]!)
                            $(args[1]!) (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by daiJoin_ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by daiJoin_ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

theorem daiJoinCreationBytecode_size : daiJoinCreationBytecode.size = 1876 := by
  native_decide

theorem daiJoinBytecode_size : daiJoinBytecode.size = 1733 := by
  native_decide

theorem daiJoinCtorArgsTail_size (vat dai : AccountAddress) :
    (daiJoinCtorArgsTail vat dai).size = 64 := by
  unfold daiJoinCtorArgsTail
  rw [ByteArray.size_append]
  have hvat : (EVM.Word.toBytesBE (EVM.word vat.val)).toByteArray.size = 32 :=
    word_toBytesBE_toByteArray_size (EVM.word vat.val)
  have hdai : (EVM.Word.toBytesBE (EVM.word dai.val)).toByteArray.size = 32 :=
    word_toBytesBE_toByteArray_size (EVM.word dai.val)
  rw [hvat, hdai]

theorem daiJoinCtorCode_size (vat dai : AccountAddress) :
    (daiJoinCtorCode vat dai).size = 1940 := by
  unfold daiJoinCtorCode
  rw [ByteArray.size_append, daiJoinCreationBytecode_size, daiJoinCtorArgsTail_size]

theorem daiJoinCtorArgLen_eq (vat dai : AccountAddress) :
    (UInt256.ofNat (daiJoinCtorCode vat dai).size).sub ⟨1876⟩ = (⟨64⟩ : UInt256) := by
  rw [daiJoinCtorCode_size]
  native_decide

theorem daiJoinCreationBytecode_runtime_window :
    daiJoinCreationBytecode.extract 143 (143 + 1733) = daiJoinBytecode := by
  native_decide

private theorem byteArray_write_from_ge_eq (src base : ByteArray) (srcAddr destAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size)
    (hbase : base.size ≤ destAddr) (_hgap : destAddr - base.size < USize.size) :
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

noncomputable def daiJoinCtorArgMem (vat dai : AccountAddress) : ByteArray :=
  (daiJoinCtorCode vat dai).write 1876 solcFreePtrMem 128 64

noncomputable def daiJoinCtorArgFreeMem (vat dai : AccountAddress) : ByteArray :=
  (UInt256.toByteArray ⟨192⟩).write 0 (daiJoinCtorArgMem vat dai) 64 32

theorem daiJoinCtorArgMem_eq (vat dai : AccountAddress) :
    daiJoinCtorArgMem vat dai =
      solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
        daiJoinCtorArgsTail vat dai := by
  rw [daiJoinCtorArgMem, daiJoinCtorCode, byteArray_write_from_ge_eq]
  · rw [extract_append_right' daiJoinCreationBytecode (daiJoinCtorArgsTail vat dai)
      1876 (1876 + 64)]
    · rw [solcFreePtrMem_size]
    · exact daiJoinCreationBytecode_size.symm
    · rw [daiJoinCtorArgsTail_size]
      native_decide
  · decide
  · rw [ByteArray.size_append, daiJoinCreationBytecode_size, daiJoinCtorArgsTail_size]
  · rw [solcFreePtrMem_size]
    decide
  · rw [solcFreePtrMem_size]
    exact lt_usize 32 (by norm_num)

theorem daiJoinCtorArgMem_size (vat dai : AccountAddress) :
    (daiJoinCtorArgMem vat dai).size = 192 := by
  rw [daiJoinCtorArgMem_eq, ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
    zeroes_ofNat_size 32 (by norm_num), daiJoinCtorArgsTail_size]

theorem daiJoinCtorArgFreeMem_size (vat dai : AccountAddress) :
    (daiJoinCtorArgFreeMem vat dai).size = 192 := by
  unfold daiJoinCtorArgFreeMem
  exact toByteArray_write32_size_of_le (base := daiJoinCtorArgMem vat dai)
    (word := (⟨192⟩ : UInt256)) (off := 64) (baseSize := 192) (finalSize := 192)
    (daiJoinCtorArgMem_size vat dai)
    (by rw [daiJoinCtorArgMem_size]; omega) (by omega)

theorem daiJoinCtorArgMem_read128 (vat dai : AccountAddress) :
    (daiJoinCtorArgMem vat dai).readWithPadding 128 32 =
      UInt256.toByteArray (EVM.word vat.val) := by
  rw [daiJoinCtorArgMem_eq]
  have hprefix :
      (solcFreePtrMem ++ ffi.ByteArray.zeroes 32).size = 128 := by
    rw [ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size 32 (by norm_num)]
  rw [readWithPadding_eq_extract'
    (solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
      daiJoinCtorArgsTail vat dai)
    128 32 (by norm_num) (by norm_num) (by
      rw [ByteArray.size_append, hprefix, daiJoinCtorArgsTail_size]
      omega)]
  rw [extract_append_right_window
    (solcFreePtrMem ++ ffi.ByteArray.zeroes 32)
    (daiJoinCtorArgsTail vat dai) 128 (128 + 32) (by rw [hprefix]), hprefix]
  rw [show 128 - 128 = 0 by omega, show 128 + 32 - 128 = 32 by omega]
  unfold daiJoinCtorArgsTail
  rw [word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray]
  rw [extract_append_left _ _ 0 32 (by rw [toByteArray_size])]
  exact toByteArray_extract_all (EVM.word vat.val)

theorem daiJoinCtorArgMem_read160 (vat dai : AccountAddress) :
    (daiJoinCtorArgMem vat dai).readWithPadding 160 32 =
      UInt256.toByteArray (EVM.word dai.val) := by
  rw [daiJoinCtorArgMem_eq]
  have hprefix :
      (solcFreePtrMem ++ ffi.ByteArray.zeroes 32).size = 128 := by
    rw [ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size 32 (by norm_num)]
  rw [readWithPadding_eq_extract'
    (solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
      daiJoinCtorArgsTail vat dai)
    160 32 (by norm_num) (by norm_num) (by
      rw [ByteArray.size_append, hprefix, daiJoinCtorArgsTail_size])]
  rw [extract_append_right_window
    (solcFreePtrMem ++ ffi.ByteArray.zeroes 32)
    (daiJoinCtorArgsTail vat dai) 160 (160 + 32)
    (by rw [hprefix]; omega), hprefix]
  rw [show 160 - 128 = 32 by omega, show 160 + 32 - 128 = 64 by omega]
  unfold daiJoinCtorArgsTail
  rw [word_toBytesBE_toByteArray_eq_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray]
  rw [extract_append_right_window _ _ 32 64 (by rw [toByteArray_size]),
    toByteArray_size]
  rw [show 32 - 32 = 0 by omega, show 64 - 32 = 32 by omega]
  exact toByteArray_extract_all (EVM.word dai.val)

theorem daiJoinCtorArgFreeMem_read128 (vat dai : AccountAddress) :
    (daiJoinCtorArgFreeMem vat dai).readWithPadding 128 32 =
      UInt256.toByteArray (EVM.word vat.val) := by
  unfold daiJoinCtorArgFreeMem
  rw [write32_read_above _ _ 64 128 (by rw [toByteArray_size])
    (by rw [daiJoinCtorArgMem_size]; norm_num) (by omega)
    (by rw [daiJoinCtorArgMem_size]; norm_num)]
  exact daiJoinCtorArgMem_read128 vat dai

theorem daiJoinCtorArgFreeMem_read160 (vat dai : AccountAddress) :
    (daiJoinCtorArgFreeMem vat dai).readWithPadding 160 32 =
      UInt256.toByteArray (EVM.word dai.val) := by
  unfold daiJoinCtorArgFreeMem
  rw [write32_read_above _ _ 64 160 (by rw [toByteArray_size])
    (by rw [daiJoinCtorArgMem_size]; norm_num) (by omega)
    (by rw [daiJoinCtorArgMem_size])]
  exact daiJoinCtorArgMem_read160 vat dai

theorem daiJoinCtorArgFreeMem_mload128 (vat dai : AccountAddress) :
    (if (⟨128⟩ : UInt256).toNat ≥ (daiJoinCtorArgFreeMem vat dai).size ∨
        (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((daiJoinCtorArgFreeMem vat dai).readWithPadding 128 32))) =
      EVM.word vat.val := by
  exact mloadWordValue_of_readWithPadding
    (mem := daiJoinCtorArgFreeMem vat dai) (aw := UInt256.ofNat 6) (off := ⟨128⟩)
    (v := EVM.word vat.val)
    (by rw [daiJoinCtorArgFreeMem_size]; decide)
    (by decide)
    (daiJoinCtorArgFreeMem_read128 vat dai)

theorem daiJoinCtorArgFreeMem_mload160 (vat dai : AccountAddress) :
    (if (⟨160⟩ : UInt256).toNat ≥ (daiJoinCtorArgFreeMem vat dai).size ∨
        (⟨160⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((daiJoinCtorArgFreeMem vat dai).readWithPadding 160 32))) =
      EVM.word dai.val := by
  exact mloadWordValue_of_readWithPadding
    (mem := daiJoinCtorArgFreeMem vat dai) (aw := UInt256.ofNat 6) (off := ⟨160⟩)
    (v := EVM.word dai.val)
    (by rw [daiJoinCtorArgFreeMem_size]; decide)
    (by decide)
    (daiJoinCtorArgFreeMem_read160 vat dai)

abbrev daiJoinCtorCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

noncomputable def daiJoinCtorWardsHashMem (I : ExecutionEnv) (vat dai : AccountAddress) :
    ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨0⟩ (daiJoinCtorArgFreeMem vat dai)

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

theorem daiJoinCtorWardsHashMem_size (I : ExecutionEnv) (vat dai : AccountAddress) :
    (daiJoinCtorWardsHashMem I vat dai).size = 192 := by
  unfold daiJoinCtorWardsHashMem twoWordHashMem
  exact wordAt32Mem_size_192 ⟨0⟩
    (wordAt0Mem_size_192 (solcSourceWord I) (daiJoinCtorArgFreeMem_size vat dai))

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

theorem daiJoinCtorWardsHashSlot (I : ExecutionEnv) (vat dai : AccountAddress) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((daiJoinCtorWardsHashMem I vat dai).readWithPadding 0 64))) =
      daiJoinCtorCallerWardsSlot I := by
  unfold daiJoinCtorWardsHashMem daiJoinCtorCallerWardsSlot solcMappingSlot
  rw [twoWordHashMem_read0_64_192]
  · exact mappingSlot_single (solcSourceWord I) ⟨0⟩
  · exact daiJoinCtorArgFreeMem_size vat dai

noncomputable def daiJoinCtorReturnMem (I : ExecutionEnv) (vat dai : AccountAddress) :
    ByteArray :=
  (daiJoinCtorCode vat dai).write 143 (daiJoinCtorWardsHashMem I vat dai) 0 1733

theorem daiJoinCtorReturnMem_read (I : ExecutionEnv) (vat dai : AccountAddress) :
    (daiJoinCtorReturnMem I vat dai).readWithPadding 0 1733 = daiJoinBytecode := by
  unfold daiJoinCtorReturnMem
  rw [write0_read_back_from_gen (daiJoinCtorCode vat dai)
    (daiJoinCtorWardsHashMem I vat dai) 143 1733
    (by decide) (by
      unfold daiJoinCtorCode
      rw [ByteArray.size_append, daiJoinCreationBytecode_size, daiJoinCtorArgsTail_size]
      omega) (by decide)]
  have hleft :
      (daiJoinCtorCode vat dai).extract 143 (143 + 1733) =
        daiJoinCreationBytecode.extract 143 (143 + 1733) := by
    unfold daiJoinCtorCode
    exact extract_append_left daiJoinCreationBytecode (daiJoinCtorArgsTail vat dai) 143
      (143 + 1733) (by rw [daiJoinCreationBytecode_size])
  rw [hleft, daiJoinCreationBytecode_runtime_window]

abbrev daiJoinCtorVatStored (σ : AccountMap) (I : ExecutionEnv) (vat : AccountAddress) :
    UInt256 :=
  setAddressOffset0Word (solcSlotWord σ I ⟨1⟩) (EVM.word vat.val)

abbrev daiJoinCtorDaiStored (σ : AccountMap) (I : ExecutionEnv) (dai : AccountAddress) :
    UInt256 :=
  setAddressOffset0Word (solcSlotWord σ I ⟨2⟩) (EVM.word dai.val)

end Benchmarks.Dss.DaiJoin
