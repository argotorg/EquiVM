import Benchmarks.CompoundIII.CometRewards.Common
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 10000000

namespace Benchmarks.CompoundIII.CometRewards

/-! ## `rewardConfig(address)` public mapping getter -/

abbrev rewardConfigArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev rewardConfigArgValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (rewardConfigArgWord I).toNat)

abbrev rewardConfigStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (rewardConfigArgValue I)

def rewardConfigSlotOf (I : ExecutionEnv) : UInt256 :=
  rewardConfigSlot (.address (AccountAddress.ofNat (rewardConfigArgWord I).toNat))

def rewardConfigSlot0Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (rewardConfigSlotOf I) ⟨0⟩)

def rewardConfigMultiplierWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (rewardConfigSlotOf I + ⟨1⟩) ⟨0⟩)

abbrev rewardConfigTokenWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (rewardConfigSlot0Word σ I) solcAddrMask

abbrev rewardConfigRescaleWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.shiftRight (rewardConfigSlot0Word σ I) ⟨160⟩)
    (UInt256.ofNat (2 ^ 64 - 1))

abbrev rewardConfigShouldUpscaleRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.shiftRight (rewardConfigSlot0Word σ I) ⟨224⟩) ⟨255⟩

abbrev rewardConfigShouldUpscaleWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.isZero (UInt256.isZero (rewardConfigShouldUpscaleRawWord σ I))

abbrev rewardConfigTokenFromSlot0 (slot0 : UInt256) : UInt256 :=
  UInt256.land slot0 solcAddrMask

abbrev rewardConfigRescaleFromSlot0 (slot0 : UInt256) : UInt256 :=
  UInt256.land (UInt256.shiftRight slot0 ⟨160⟩) (UInt256.ofNat (2 ^ 64 - 1))

abbrev rewardConfigShouldUpscaleRawFromSlot0 (slot0 : UInt256) : UInt256 :=
  UInt256.land (UInt256.shiftRight slot0 ⟨224⟩) ⟨255⟩

abbrev rewardConfigShouldUpscaleFromSlot0 (slot0 : UInt256) : UInt256 :=
  UInt256.isZero (UInt256.isZero (rewardConfigShouldUpscaleRawFromSlot0 slot0))

def rewardConfigReturnValues (slot0 multiplier : UInt256) : List Value :=
  [ .address (AccountAddress.ofNat (rewardConfigTokenFromSlot0 slot0).toNat),
    .int (↑(rewardConfigRescaleFromSlot0 slot0).toNat),
    wordToElem .bool (rewardConfigShouldUpscaleRawFromSlot0 slot0),
    .int (↑multiplier.toNat) ]

noncomputable def rewardConfigHashMem (comet : UInt256) : ByteArray :=
  twoWordHashMem comet ⟨1⟩ solcFreePtrMem

def rewardConfigReturnWrites
    (token rescale shouldUpscale multiplier : UInt256) : List (Nat × UInt256) :=
  [(128, token), (160, rescale), (192, shouldUpscale), (224, multiplier)]

noncomputable def rewardConfigReturnMem
    (comet token rescale shouldUpscale multiplier : UInt256) : ByteArray :=
  writeCascade (rewardConfigHashMem comet)
    (rewardConfigReturnWrites token rescale shouldUpscale multiplier)

def rewardConfigReturnBytes (token rescale shouldUpscale multiplier : UInt256) : ByteArray :=
  UInt256.toByteArray token ++
    (UInt256.toByteArray rescale ++
      (UInt256.toByteArray shouldUpscale ++ UInt256.toByteArray multiplier))

theorem rewardConfigShiftRight160_eq_div (w : UInt256) :
    UInt256.shiftRight w (⟨160⟩ : UInt256) =
      UInt256.div w (UInt256.ofNat (256 ^ 20)) := by
  apply u256_inj
  unfold UInt256.shiftRight UInt256.div UInt256.toNat
  simp [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow,
    show 160 % UInt256.size = 160 by native_decide]
  norm_num [UInt256.ofNat, Id.run]
  rw [show 1461501637330902918203684832716283019655932542976 % UInt256.size =
      1461501637330902918203684832716283019655932542976 by native_decide]

theorem rewardConfigShiftRight224_eq_div (w : UInt256) :
    UInt256.shiftRight w (⟨224⟩ : UInt256) =
      UInt256.div w (UInt256.ofNat (256 ^ 28)) := by
  apply u256_inj
  unfold UInt256.shiftRight UInt256.div UInt256.toNat
  simp [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow,
    show 224 % UInt256.size = 224 by native_decide]
  norm_num [UInt256.ofNat, Id.run]
  rw [show 26959946667150639794667015087019630673637144422540572481103610249216 %
      UInt256.size =
      26959946667150639794667015087019630673637144422540572481103610249216 by native_decide]

theorem cometRewardsStorageLocLoad_uint64_offset20 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (fieldLoc slot 20 8 (by decide) (.int uint64Int)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.shiftRight (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨160⟩)
        (UInt256.ofNat (2 ^ 64 - 1))).toNat) := by
  rw [rewardConfigShiftRight160_eq_div]
  simpa [fieldLoc, loc] using
    @storageLocLoad_uint_offset evm slot (⟨20, by decide⟩ : Fin 32)
      (⟨8, by decide⟩ : Fin 33) (⟨64, by decide⟩ : ABI.BitWidth)
      (by decide) (by decide) (by decide)

theorem cometRewardsStorageLocLoad_bool_offset28 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (fieldLoc slot 28 1 (by decide) .bool) =
      wordToElem .bool (UInt256.land
        (UInt256.shiftRight (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨224⟩)
        ⟨255⟩) := by
  rw [rewardConfigShiftRight224_eq_div]
  unfold storageLocLoad fieldLoc loc
  apply congrArg (wordToElem .bool)
  apply u256_inj
  change fromBytes'
        ((EVM.Word.toBytesLEWithSizeProof
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract 28 (28 + 1)) = _
  rw [List.extract_eq_take_drop]
  simpa [Nat.add_sub_cancel_left] using
    fromBytes'_drop_take_wordLE_land_div_mask
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) 28 1
      (by decide) (by decide)

theorem rewardConfigSlotOf_eq_solc (I : ExecutionEnv)
    (hcanon : (rewardConfigArgWord I).toNat < EVM.addressModulus) :
    rewardConfigSlotOf I = solcMappingSlot ⟨1⟩ (rewardConfigArgWord I) := by
  unfold rewardConfigSlotOf rewardConfigSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]
  rfl

theorem rewardConfigHashMem_size (comet : UInt256) :
    (rewardConfigHashMem comet).size = 96 := by
  exact twoWordHashMem_size_96 comet ⟨1⟩ solcFreePtrMem_size

theorem rewardConfigHashMem_read64 (comet : UInt256) :
    (rewardConfigHashMem comet).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 comet ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64

theorem rewardConfigHashMem_mload64 (comet : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (rewardConfigHashMem comet).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
      (fromByteArrayBigEndian ((rewardConfigHashMem comet).readWithPadding
        (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
  exact mloadFreePtrValue (by rw [rewardConfigHashMem_size]; decide) (by decide)
    (rewardConfigHashMem_read64 comet)

theorem rewardConfigKeccakSlot (comet : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((rewardConfigHashMem comet).readWithPadding 0 64))) =
      solcMappingSlot ⟨1⟩ comet := by
  rw [rewardConfigHashMem, twoWordHashMem_read0_64 comet ⟨1⟩ solcFreePtrMem_size]
  unfold solcMappingSlot
  exact mappingSlot_single comet ⟨1⟩

theorem rewardConfigReturnMem_size (comet token rescale shouldUpscale multiplier : UInt256) :
    (rewardConfigReturnMem comet token rescale shouldUpscale multiplier).size = 256 := by
  unfold rewardConfigReturnMem rewardConfigReturnWrites
  exact writeCascade_size_of_base (rewardConfigHashMem comet)
    [(128, token), (160, rescale), (192, shouldUpscale), (224, multiplier)]
    (rewardConfigHashMem_size comet)
    (by simpa [WriteGapsOk] using (lt_usize 32 (by norm_num))) (by rfl)

theorem rewardConfigReturnMem_readWord128
    (comet token rescale shouldUpscale multiplier : UInt256) :
    (rewardConfigReturnMem comet token rescale shouldUpscale multiplier).readWithPadding 128 32 =
      UInt256.toByteArray token := by
  unfold rewardConfigReturnMem rewardConfigReturnWrites
  exact writeCascade_read_word_of_head_of_base (rewardConfigHashMem comet) token
    [(160, rescale), (192, shouldUpscale), (224, multiplier)]
    (rewardConfigHashMem_size comet) (by exact lt_usize _ (by norm_num)) (by
      simp [WindowDisjointFromWrites])

theorem rewardConfigReturnMem_readWord160
    (comet token rescale shouldUpscale multiplier : UInt256) :
    (rewardConfigReturnMem comet token rescale shouldUpscale multiplier).readWithPadding 160 32 =
      UInt256.toByteArray rescale := by
  unfold rewardConfigReturnMem rewardConfigReturnWrites
  rw [writeCascade_cons]
  have hbase : (writeWord (rewardConfigHashMem comet) 128 token).size = 160 := by
    rw [writeWord_size]
    · rw [rewardConfigHashMem_size]
      norm_num
    · rw [rewardConfigHashMem_size]
      native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord (rewardConfigHashMem comet) 128 token) rescale
    [(192, shouldUpscale), (224, multiplier)] hbase (by exact lt_usize _ (by norm_num)) (by
      simp [WindowDisjointFromWrites])

theorem rewardConfigReturnMem_readWord192
    (comet token rescale shouldUpscale multiplier : UInt256) :
    (rewardConfigReturnMem comet token rescale shouldUpscale multiplier).readWithPadding 192 32 =
      UInt256.toByteArray shouldUpscale := by
  unfold rewardConfigReturnMem rewardConfigReturnWrites
  rw [writeCascade_cons, writeCascade_cons]
  have hbase0 : (writeWord (rewardConfigHashMem comet) 128 token).size = 160 := by
    rw [writeWord_size]
    · rw [rewardConfigHashMem_size]
      norm_num
    · rw [rewardConfigHashMem_size]
      native_decide
  have hbase :
      (writeWord (writeWord (rewardConfigHashMem comet) 128 token) 160 rescale).size =
        192 := by
    rw [writeWord_size]
    · rw [hbase0]
      norm_num
    · rw [hbase0]
      native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord (writeWord (rewardConfigHashMem comet) 128 token) 160 rescale)
    shouldUpscale [(224, multiplier)] hbase (by exact lt_usize _ (by norm_num)) (by
      simp [WindowDisjointFromWrites])

theorem rewardConfigReturnMem_readWord224
    (comet token rescale shouldUpscale multiplier : UInt256) :
    (rewardConfigReturnMem comet token rescale shouldUpscale multiplier).readWithPadding 224 32 =
      UInt256.toByteArray multiplier := by
  unfold rewardConfigReturnMem rewardConfigReturnWrites
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
  have hbase0 : (writeWord (rewardConfigHashMem comet) 128 token).size = 160 := by
    rw [writeWord_size]
    · rw [rewardConfigHashMem_size]
      norm_num
    · rw [rewardConfigHashMem_size]
      native_decide
  have hbase1 :
      (writeWord (writeWord (rewardConfigHashMem comet) 128 token) 160 rescale).size =
        192 := by
    rw [writeWord_size]
    · rw [hbase0]
      norm_num
    · rw [hbase0]
      native_decide
  have hbase :
      (writeWord
        (writeWord (writeWord (rewardConfigHashMem comet) 128 token) 160 rescale)
        192 shouldUpscale).size = 224 := by
    rw [writeWord_size]
    · rw [hbase1]
      norm_num
    · rw [hbase1]
      native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord (writeWord (rewardConfigHashMem comet) 128 token) 160 rescale)
      192 shouldUpscale)
    multiplier [] hbase (by exact lt_usize _ (by norm_num)) (by
      simp [WindowDisjointFromWrites])

theorem rewardConfigReturnMem_read128 (comet token rescale shouldUpscale multiplier : UInt256) :
    (rewardConfigReturnMem comet token rescale shouldUpscale multiplier).readWithPadding 128 128 =
      rewardConfigReturnBytes token rescale shouldUpscale multiplier := by
  rw [byteArray_readWithPadding_split _ 128 32 96 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by
      rw [rewardConfigReturnMem_size])]
  rw [byteArray_readWithPadding_split _ 160 32 64 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by
      rw [rewardConfigReturnMem_size])]
  rw [byteArray_readWithPadding_split _ 192 32 32 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by
      rw [rewardConfigReturnMem_size])]
  rw [rewardConfigReturnMem_readWord128, rewardConfigReturnMem_readWord160,
    rewardConfigReturnMem_readWord192, rewardConfigReturnMem_readWord224]
  rfl

theorem rewardConfigRescaleWord_lt (w : UInt256) :
    (UInt256.land (UInt256.shiftRight w ⟨160⟩)
      (UInt256.ofNat (2 ^ 64 - 1))).toNat < EVM.twoPow 64 := by
  rw [u256_land_toNat]
  have hmask :
      (UInt256.ofNat (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 := by
    exact ulit_toNat' _ (by norm_num [UInt256.size])
  rw [hmask]
  have hle : Nat.land (UInt256.shiftRight w ⟨160⟩).toNat (2 ^ 64 - 1) ≤ 2 ^ 64 - 1 :=
    nat_land_le_right _ _
  have hltSize :
      Nat.land (UInt256.shiftRight w ⟨160⟩).toNat (2 ^ 64 - 1) < UInt256.size := by
    exact lt_of_le_of_lt hle (by norm_num [UInt256.size])
  rw [Nat.mod_eq_of_lt hltSize]
  change _ < 2 ^ 64
  omega

theorem rewardConfigEncodeABIWord_uint64 (v : UInt256) (h64 : v.toNat < EVM.twoPow 64) :
    encodeABIWord? (.elem (.int uint64Int)) (.int (↑v.toNat)) = some v := by
  have hword : EVM.word v.toNat = v := by
    show UInt256.ofNat v.toNat = v
    exact u256_ofNat_toNat v
  rw [uint64Int]
  simp only [encodeABIWord?, Int.ofNat_eq_natCast]
  rw [if_neg (by norm_num : ¬ (64 = 0))]
  rw [if_pos]
  · exact congrArg some hword
  · constructor
    · exact Int.natCast_nonneg _
    · exact_mod_cast h64

theorem rewardConfigEncodeABIValue_uint64 (v : UInt256) (h64 : v.toNat < EVM.twoPow 64) :
    encodeABIValue? (.elem (.int uint64Int)) (.int (↑v.toNat)) =
      some (EVM.Word.toBytesBE v) := by
  simp [encodeABIValue?, rewardConfigEncodeABIWord_uint64 v h64]

theorem rewardConfigEncodeABIWord_uint256 (v : UInt256) :
    encodeABIWord? (.elem (.int uint256Int)) (.int (↑v.toNat)) = some v := by
  have hword : EVM.word v.toNat = v := by
    show UInt256.ofNat v.toNat = v
    exact u256_ofNat_toNat v
  have hltNat : v.toNat < EVM.twoPow 256 := by
    change v.val.val < EVM.twoPow 256
    exact v.val.isLt
  rw [uint256Int]
  simp only [encodeABIWord?, Int.ofNat_eq_natCast]
  rw [if_neg (by norm_num : ¬ (256 = 0))]
  rw [if_pos]
  · exact congrArg some hword
  · constructor
    · exact Int.natCast_nonneg _
    · exact_mod_cast hltNat

theorem rewardConfigEncodeABIValue_uint256 (v : UInt256) :
    encodeABIValue? (.elem (.int uint256Int)) (.int (↑v.toNat)) =
      some (EVM.Word.toBytesBE v) := by
  simp [encodeABIValue?, rewardConfigEncodeABIWord_uint256 v]

theorem rewardConfigEncodeABIWord_bool_word (w : UInt256) :
    encodeABIWord? (.elem .bool) (wordToElem .bool w) =
      some (UInt256.isZero (UInt256.isZero w)) := by
  by_cases hval : w.val = 0
  · have hz : w = ⟨0⟩ := by
      apply u256_inj
      exact congrArg Fin.val hval
    simp [encodeABIWord?, wordToElem, hz,
      show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide,
      show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide]
    native_decide
  · have hnz : w ≠ ⟨0⟩ := by
      intro hz
      apply hval
      rw [hz]
    have hiz : UInt256.isZero w = ⟨0⟩ := isZero_eq_zero_of_ne hnz
    simp [encodeABIWord?, wordToElem, hval, hiz,
      show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide]
    native_decide

theorem rewardConfigEncodeABIValue_bool_word (w : UInt256) :
    encodeABIValue? (.elem .bool) (wordToElem .bool w) =
      some (EVM.Word.toBytesBE (UInt256.isZero (UInt256.isZero w))) := by
  simp [encodeABIValue?, rewardConfigEncodeABIWord_bool_word w]

theorem rewardConfigEncodeABIWord_masked_address (w : UInt256) :
    encodeABIWord? (.elem .address)
        (.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)) =
      some (UInt256.land w solcAddrMask) := by
  have hcanon := solcAddrMask_result_canonical w
  have haddrMod : (UInt256.land w solcAddrMask).toNat % AccountAddress.size =
      (UInt256.land w solcAddrMask).toNat := by
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
  have hword : EVM.word (UInt256.land w solcAddrMask).toNat = UInt256.land w solcAddrMask :=
    u256_ofNat_toNat _
  simp [encodeABIWord?, AccountAddress.ofNat, haddrMod, hword]

theorem rewardConfigEncodeABIValue_masked_address (w : UInt256) :
    encodeABIValue? (.elem .address)
        (.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)) =
      some (EVM.Word.toBytesBE (UInt256.land w solcAddrMask)) := by
  simp [encodeABIValue?, rewardConfigEncodeABIWord_masked_address w]

theorem encodeReturnValues_four_static {ty0 ty1 ty2 ty3 : ABIType}
    {v0 v1 v2 v3 : Value} {w0 w1 w2 w3 : UInt256}
    (hhead : abiTupleHeadSize? [ty0, ty1, ty2, ty3] = some 128)
    (hd0 : isDynamicABIType ty0 = false) (hd1 : isDynamicABIType ty1 = false)
    (hd2 : isDynamicABIType ty2 = false) (hd3 : isDynamicABIType ty3 = false)
    (h0 : encodeABIValue? ty0 v0 = some (EVM.Word.toBytesBE w0))
    (h1 : encodeABIValue? ty1 v1 = some (EVM.Word.toBytesBE w1))
    (h2 : encodeABIValue? ty2 v2 = some (EVM.Word.toBytesBE w2))
    (h3 : encodeABIValue? ty3 v3 = some (EVM.Word.toBytesBE w3)) :
    encodeReturnValues? [ty0, ty1, ty2, ty3] [v0, v1, v2, v3] =
      some (UInt256.toByteArray w0 ++
        (UInt256.toByteArray w1 ++ (UInt256.toByteArray w2 ++ UInt256.toByteArray w3))) := by
  rw [toByteArray_eq_toBytesBE w0, toByteArray_eq_toBytesBE w1,
    toByteArray_eq_toBytesBE w2, toByteArray_eq_toBytesBE w3]
  simp only [encodeReturnValues?, encodeABIValues?, hhead, bind, Option.bind]
  simp only [encodeABIValuesFrom?, h0, h1, h2, h3, hd0, hd1, hd2, hd3,
    Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append]

theorem rewardConfigReturnEncoding (slot0 multiplier : UInt256) :
    encodeReturnValues? [addr, uint64, boolTy, uint256]
      (rewardConfigReturnValues slot0 multiplier) =
      some (rewardConfigReturnBytes (rewardConfigTokenFromSlot0 slot0)
        (rewardConfigRescaleFromSlot0 slot0) (rewardConfigShouldUpscaleFromSlot0 slot0)
        multiplier) := by
  unfold rewardConfigReturnValues rewardConfigReturnBytes rewardConfigTokenFromSlot0
    rewardConfigRescaleFromSlot0 rewardConfigShouldUpscaleRawFromSlot0
    rewardConfigShouldUpscaleFromSlot0
  exact encodeReturnValues_four_static
    (ty0 := addr) (ty1 := uint64) (ty2 := boolTy) (ty3 := uint256)
    (hhead := by native_decide)
    (hd0 := by native_decide) (hd1 := by native_decide)
    (hd2 := by native_decide) (hd3 := by native_decide)
    (h0 := rewardConfigEncodeABIValue_masked_address slot0)
    (h1 := rewardConfigEncodeABIValue_uint64 _
      (by simpa using rewardConfigRescaleWord_lt slot0))
    (h2 := rewardConfigEncodeABIValue_bool_word _)
    (h3 := rewardConfigEncodeABIValue_uint256 multiplier)

theorem cometRewardsDecode_rewardConfig_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (rewardConfigArgWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (rewardConfigTransition.params.map Param.name)
      (transitionSignature rewardConfigTransition).paramTypes I.calldata =
        some (rewardConfigStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0"] [addr] I.calldata = _
  simpa [config, rewardConfigStore, rewardConfigArgValue, rewardConfigArgWord, calldataWord]
    using decodeCalldata_address_ok (cd := I.calldata) (x := "arg0") hsz36 hbig hcanon

theorem cometRewardsDecode_rewardConfig_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (rewardConfigTransition.params.map Param.name)
      (transitionSignature rewardConfigTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0"] [addr] I.calldata = none
  simpa [config, addr] using decodeCalldata_address_none_short
    (cd := I.calldata) (x := "arg0") hsz4 hshort

theorem cometRewardsDecode_rewardConfig_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (rewardConfigArgWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (rewardConfigTransition.params.map Param.name)
      (transitionSignature rewardConfigTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0"] [addr] I.calldata = none
  simpa [config, addr, rewardConfigArgWord, calldataWord]
    using decodeCalldata_address_none_noncanon
      (cd := I.calldata) (x := "arg0") hsz36 hbig hnc

theorem cometRewardsDecode_rewardConfig_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (rewardConfigTransition.params.map Param.name)
      (transitionSignature rewardConfigTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0"] [addr] I.calldata = none
  simpa [config, addr] using decodeCalldata_address_none_huge
    (cd := I.calldata) (x := "arg0") hbig

theorem cometRewardsRewardConfigSelector_size {I : ExecutionEnv}
    (hsel : selIs I (cometRewardsSelBytes 2)) :
    4 ≤ I.calldata.size :=
  calldata_size_ge_of_selIs I (cometRewardsSelBytes 2) rfl hsel

theorem cometRewardsDispatch_rewardConfig {cd : ByteArray}
    (hsel : (cometRewardsSelBytes 2 == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some rewardConfigTransition := by
  have hcd : cd.extract 0 4 = cometRewardsSelBytes 2 :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [claimTransition, claimToTransition, getRewardOwedTransition, governorTransition])
    (post := [rewardsClaimedTransition, setRewardConfigTransition,
      setRewardConfigWithMultiplierTransition, setRewardsClaimedTransition,
      transferGovernorTransition, withdrawTokenTransition])
    rfl rfl ?_ (by rw [selectorOf, rewardConfigSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rw [selectorOf, claimSelectorBytes, hcd]
    decide
  · rw [selectorOf, claimToSelectorBytes, hcd]
    decide
  · rw [selectorOf, getRewardOwedSelectorBytes, hcd]
    decide
  · rw [selectorOf, governorSelectorBytes, hcd]
    decide

theorem cometRewardsRewardConfigCalldataCheckOk {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨32⟩ = ⟨0⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨32⟩ = ⟨0⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 (by omega) hsize]
  exact solcDecodeLenCheckOk_4_32 hsz36 hhi hsize

theorem cometRewardsRewardConfigCalldataCheckShort {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨32⟩ = ⟨1⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨32⟩ = ⟨1⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 hsz4 hsize]
  exact solcDecodeLenCheckShort_4_32 hsz4 hshort hsize

theorem cometRewardsRewardConfigCalldataCheckHuge {I : ExecutionEnv}
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    UInt256.slt
        ((UInt256.ofNat I.calldata.size) + (UInt256.lnot (⟨3⟩ : UInt256)))
        ⟨32⟩ = ⟨1⟩ := by
  change UInt256.slt
      (UInt256.add (UInt256.ofNat I.calldata.size) (UInt256.lnot (⟨3⟩ : UInt256)))
      ⟨32⟩ = ⟨1⟩
  rw [cometRewardsCalldataSizeAddNot3_eq_sub4 (by omega) hsize]
  exact solcDecodeLenCheckHuge_4_32 hbig hsize

theorem cometRewardsRewardConfigX_dec2831_arg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) rewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2831⟩
      [⟨2661⟩, solcAddrMask, ⟨0⟩, ⟨64⟩, ⟨255⟩, ⟨64⟩, ⟨224⟩,
        solcAddrMask, ⟨128⟩, cometRewardsSelWord I, ⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt := cometRewardsRewardConfigCalldataCheckOk (I := I) hsz36 hsize hhi
  obtain ⟨_, _, rd2615⟩ := hreach
  have rd2624 := evm_run rd2615 with [
    jumpdest, dup4, dup6, dup5, callvalue]
  rw [hwv] at rd2624
  have rd2636 := evm_run rd2624 with [
    push2 ⟨670⟩, jumpiNT (by decide),
    push1 ⟨32⟩, calldatasize, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd2636
  rw [hslt] at rd2636
  have rd2660 := evm_run rd2636 with [
    push2 ⟨670⟩, jumpiNT (by decide),
    push1 ⟨128⟩, swap3,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap3,
    push1 ⟨255⟩, swap1, dup3, swap1, dup6,
    push2 ⟨2661⟩, push2 ⟨2831⟩]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by decide] at rd2660
  exact ⟨_, _, evm_run rd2660 with [jump (by native_decide)]⟩

theorem cometRewardsRewardConfigX_dec2661_arg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (rewardConfigArgWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) rewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD cometRewardsBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2661⟩
      [rewardConfigArgWord I, solcAddrMask, ⟨0⟩, ⟨64⟩, ⟨255⟩, ⟨64⟩, ⟨224⟩,
        solcAddrMask, ⟨128⟩, cometRewardsSelWord I, ⟨4⟩, ⟨224⟩, ⟨64⟩, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2831⟩ :=
    cometRewardsRewardConfigX_dec2831_arg (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz36 hsize hhi hreach
  exact ⟨_, _, evm_run rd2831 with [
    jumpdest, push1 ⟨4⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, dup3, sub,
    push2 ⟨1004⟩,
    jumpiNT (by
      have hclean :
          UInt256.land
            (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
            solcAddrMask =
          uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) := by
        exact solcAddrMask_clean (by
          simpa [rewardConfigArgWord, calldataWord] using hcanon)
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hclean]
      exact u256_sub_self _),
    jump (by native_decide)]⟩

theorem cometRewardsRewardConfigX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) rewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsRewardConfigCalldataCheckShort (I := I) hsz4 hsize hshort
  obtain ⟨_, _, rd2615⟩ := hreach
  have rd2624 := evm_run rd2615 with [
    jumpdest, dup4, dup6, dup5, callvalue]
  rw [hwv] at rd2624
  have rd2636 := evm_run rd2624 with [
    push2 ⟨670⟩, jumpiNT (by decide),
    push1 ⟨32⟩, calldatasize, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd2636
  rw [hslt] at rd2636
  exact evm_run rd2636 with [
    push2 ⟨670⟩, jumpiT (by decide) (by native_decide),
    jumpdest, pop, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

theorem cometRewardsRewardConfigX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) rewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt := cometRewardsRewardConfigCalldataCheckHuge (I := I) hsize hbig
  obtain ⟨_, _, rd2615⟩ := hreach
  have rd2624 := evm_run rd2615 with [
    jumpdest, dup4, dup6, dup5, callvalue]
  rw [hwv] at rd2624
  have rd2636 := evm_run rd2624 with [
    push2 ⟨670⟩, jumpiNT (by decide),
    push1 ⟨32⟩, calldatasize, push1 ⟨3⟩, not, add, slt]
  rw [show UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat I.calldata.size =
      UInt256.ofNat I.calldata.size + UInt256.lnot (⟨3⟩ : UInt256)
      from u256_add_comm _ _] at rd2636
  rw [hslt] at rd2636
  exact evm_run rd2636 with [
    push2 ⟨670⟩, jumpiT (by decide) (by native_decide),
    jumpdest, pop, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem cometRewardsRewardConfigX_noncanon_arg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (rewardConfigArgWord I)
      (UInt256.land (rewardConfigArgWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) rewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2831⟩ :=
    cometRewardsRewardConfigX_dec2831_arg (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hsz36 hsize hhi hreach
  exact evm_run rd2831 with [
    jumpdest, push1 ⟨4⟩, calldataload, swap1,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, dup3, sub,
    push2 ⟨1004⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      exact u256_sub_ne_zero_of_ne (by
        intro heq
        have hclean :
            UInt256.eq (rewardConfigArgWord I)
              (UInt256.land (rewardConfigArgWord I) solcAddrMask) = ⟨1⟩ := by
          have heq' : rewardConfigArgWord I =
              UInt256.land (rewardConfigArgWord I) solcAddrMask := by
            simpa [rewardConfigArgWord, calldataWord] using heq
          rw [← heq']
          exact uInt256_eq_self _
        rw [hclean] at hnc
        exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hnc))
      (by native_decide),
    jumpdest, push1 ⟨0⟩, dup1, raw rev 0 (by decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 2000000 in
theorem cometRewardsX_rewardConfig {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (rewardConfigArgWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD cometRewardsBytecode I g
      (initState cA gh bl σ σ₀ g A I) rewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDret cometRewardsBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (rewardConfigReturnBytes
        (rewardConfigTokenWord σ I) (rewardConfigRescaleWord σ I)
        (rewardConfigShouldUpscaleWord σ I) (rewardConfigMultiplierWord σ I)) := by
  obtain ⟨_, _, rd2661⟩ :=
    cometRewardsRewardConfigX_dec2661_arg (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hsz36 hsize hhi hcanon hreach
  have hslot := rewardConfigSlotOf_eq_solc I hcanon
  have hkeccak := rewardConfigKeccakSlot (rewardConfigArgWord I)
  have rd2674 := evm_run rd2661 with [
    jumpdest, and, dup2,
    raw mstore 0 (wordAt0Mem (rewardConfigArgWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [solcAddrMask_clean hcanon]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩,
    raw mstore 0 (rewardConfigHashMem (rewardConfigArgWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (rewardConfigArgWord I))
      (UInt256.ofNat 3) (by decide) mem_cost hkeccak (by decide) (by evm_ov)]
  rw [← hslot] at rd2674
  have rd2675 := evm_run rd2674 with [push1 ⟨1⟩, dup2]
  obtain ⟨_, _, rd2676⟩ := rd2675.sload (by decide) (by evm_ov)
  have rd2677 := evm_run rd2676 with [swap2, add]
  obtain ⟨_, _, rd2678⟩ := rd2677.sload (by decide) (by evm_ov)
  have rd2716 := evm_run rd2678 with [
    swap4, dup4,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost
      (rewardConfigHashMem_mload64 (rewardConfigArgWord I)) (by decide) (by evm_ov),
    swap6, dup3, and, dup7,
    raw mstore 6
      (writeCascade (rewardConfigHashMem (rewardConfigArgWord I))
        [(128, rewardConfigTokenWord σ I)])
      (UInt256.ofNat 5) (by decide) mem_cost
      (by rfl)
      (by decide) (by evm_ov),
    push1 ⟨1⟩, dup1, push1 ⟨64⟩, shl, sub, dup3, push1 ⟨160⟩, shr, and,
    push1 ⟨32⟩, dup8, add,
    raw mstore 3
      (writeCascade (rewardConfigHashMem (rewardConfigArgWord I))
        [(128, rewardConfigTokenWord σ I), (160, rewardConfigRescaleWord σ I)])
      (UInt256.ofNat 6) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩ =
          UInt256.ofNat (2 ^ 64 - 1) from by native_decide]
        rfl)
      (by decide) (by evm_ov),
    shr, and, iszero, iszero, swap1, dup4, add,
    raw mstore 3
      (writeCascade (rewardConfigHashMem (rewardConfigArgWord I))
        [(128, rewardConfigTokenWord σ I), (160, rewardConfigRescaleWord σ I),
          (192, rewardConfigShouldUpscaleWord σ I)])
      (UInt256.ofNat 7) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨96⟩, dup3, add,
    raw mstore 3
      (rewardConfigReturnMem (rewardConfigArgWord I)
        (rewardConfigTokenWord σ I) (rewardConfigRescaleWord σ I)
        (rewardConfigShouldUpscaleWord σ I) (rewardConfigMultiplierWord σ I))
      (UInt256.ofNat 8) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov)]
  exact evm_run rd2716 with [
    raw ret 0
      (rewardConfigReturnBytes
        (rewardConfigTokenWord σ I) (rewardConfigRescaleWord σ I)
        (rewardConfigShouldUpscaleWord σ I) (rewardConfigMultiplierWord σ I))
      (by decide) mem_cost
      (by
        exact rewardConfigReturnMem_read128 (rewardConfigArgWord I)
          (rewardConfigTokenWord σ I) (rewardConfigRescaleWord σ I)
          (rewardConfigShouldUpscaleWord σ I) (rewardConfigMultiplierWord σ I))
      (by evm_ov)]

theorem slotAdd_zero (slot : UInt256) :
    slotAdd slot 0 = slot := by
  unfold slotAdd
  rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_comm, u256_zero_add]

theorem slotAdd_one (slot : UInt256) :
    slotAdd slot 1 = slot + ⟨1⟩ := by
  rfl

theorem rewardConfigStore_arg0 (I : ExecutionEnv) :
    (rewardConfigStore I).get? "arg0" = some (rewardConfigArgValue I) := by
  rw [rewardConfigStore, store_get_self]

theorem evalStorageRef_rewardConfig_field (evm : EVM.State) (I : ExecutionEnv)
    (field : Ident) :
    evalStorageRef config
      { contract := contract,
        locals := (rewardConfigStore I).insert "__calldata" (.bytes evm.executionEnv.calldata) }
      evm (rewardConfigF (.var "arg0") field) =
        .ok { base := "rewardConfig",
              steps := [.mindex (.address (AccountAddress.ofNat
                          (rewardConfigArgWord I).toNat)), .field field] } := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, rewardConfigF,
    evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, valueToKey?,
    Std.HashMap.get?_eq_getElem?]
  rw [← Std.HashMap.get?_eq_getElem?]
  rw [store_get_ne _ _ (by decide), rewardConfigStore_arg0]

theorem evalExpr_rewardConfig_token (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract,
        locals := (rewardConfigStore I).insert "__calldata" (.bytes evm.executionEnv.calldata) }
      evm (.storage (rewardConfigF (.var "arg0") "token")) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (rewardConfigSlotOf I))
            solcAddrMask).toNat)) := by
  have her := evalStorageRef_rewardConfig_field evm I "token"
  have hty : storageTypeAt? contract.storage
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat (rewardConfigArgWord I).toNat)),
                  .field "token"] } =
      some (.elem .address) := by
    simp [storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hloc : config.storage.layout
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat (rewardConfigArgWord I).toNat)),
                  .field "token"] } =
      fun _ => some (fieldLoc (slotAdd (rewardConfigSlotOf I) 0) 0 20
        (by decide) .address) := by
    rfl
  rw [evalExpr_storage_scalar
    (hbase := by
      change ((rewardConfigStore I).insert "__calldata"
        (.bytes evm.executionEnv.calldata)).get? "rewardConfig" = none
      rw [store_get_ne _ _ (by decide)]
      rw [rewardConfigStore, store_get_ne _ _ (by decide)]
      simp)
    (her := her) (hty := hty) (hloc := hloc)]
  congr 1
  rw [slotAdd_zero]
  exact cometRewardsStorageLocLoad_address_offset0 evm (rewardConfigSlotOf I)

theorem evalExpr_rewardConfig_rescale (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract,
        locals := (rewardConfigStore I).insert "__calldata" (.bytes evm.executionEnv.calldata) }
      evm (.storage (rewardConfigF (.var "arg0") "rescaleFactor")) =
        .ok (.int (Int.ofNat
          (UInt256.land
            (UInt256.shiftRight
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (rewardConfigSlotOf I))
              ⟨160⟩)
            (UInt256.ofNat (2 ^ 64 - 1))).toNat)) := by
  have her := evalStorageRef_rewardConfig_field evm I "rescaleFactor"
  have hty : storageTypeAt? contract.storage
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat (rewardConfigArgWord I).toNat)),
                  .field "rescaleFactor"] } =
      some (.elem (.int uint64Int)) := by
    simp [storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hloc : config.storage.layout
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat (rewardConfigArgWord I).toNat)),
                  .field "rescaleFactor"] } =
      fun _ => some (fieldLoc (slotAdd (rewardConfigSlotOf I) 0) 20 8
        (by decide) (.int uint64Int)) := by
    rfl
  rw [evalExpr_storage_scalar
    (hbase := by
      change ((rewardConfigStore I).insert "__calldata"
        (.bytes evm.executionEnv.calldata)).get? "rewardConfig" = none
      rw [store_get_ne _ _ (by decide)]
      rw [rewardConfigStore, store_get_ne _ _ (by decide)]
      simp)
    (her := her) (hty := hty) (hloc := hloc)]
  congr 1
  rw [slotAdd_zero]
  exact cometRewardsStorageLocLoad_uint64_offset20 evm (rewardConfigSlotOf I)

theorem evalExpr_rewardConfig_shouldUpscale (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract,
        locals := (rewardConfigStore I).insert "__calldata" (.bytes evm.executionEnv.calldata) }
      evm (.storage (rewardConfigF (.var "arg0") "shouldUpscale")) =
        .ok (wordToElem .bool
          (UInt256.land
            (UInt256.shiftRight
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (rewardConfigSlotOf I))
              ⟨224⟩)
            ⟨255⟩)) := by
  have her := evalStorageRef_rewardConfig_field evm I "shouldUpscale"
  have hty : storageTypeAt? contract.storage
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat (rewardConfigArgWord I).toNat)),
                  .field "shouldUpscale"] } =
      some (.elem .bool) := by
    simp [storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hloc : config.storage.layout
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat (rewardConfigArgWord I).toNat)),
                  .field "shouldUpscale"] } =
      fun _ => some (fieldLoc (slotAdd (rewardConfigSlotOf I) 0) 28 1
        (by decide) .bool) := by
    rfl
  rw [evalExpr_storage_scalar
    (hbase := by
      change ((rewardConfigStore I).insert "__calldata"
        (.bytes evm.executionEnv.calldata)).get? "rewardConfig" = none
      rw [store_get_ne _ _ (by decide)]
      rw [rewardConfigStore, store_get_ne _ _ (by decide)]
      simp)
    (her := her) (hty := hty) (hloc := hloc)]
  congr 1
  rw [slotAdd_zero]
  exact cometRewardsStorageLocLoad_bool_offset28 evm (rewardConfigSlotOf I)

theorem evalExpr_rewardConfig_multiplier (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config
      { contract := contract,
        locals := (rewardConfigStore I).insert "__calldata" (.bytes evm.executionEnv.calldata) }
      evm (.storage (rewardConfigF (.var "arg0") "multiplier")) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (rewardConfigSlotOf I + ⟨1⟩)).toNat)) := by
  have her := evalStorageRef_rewardConfig_field evm I "multiplier"
  have hty : storageTypeAt? contract.storage
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat (rewardConfigArgWord I).toNat)),
                  .field "multiplier"] } =
      some (.elem (.int uint256Int)) := by
    simp [storageTypeAt?, contract, storageDecls, RewardConfigStructTy, storageTypeStep?]
  have hloc : config.storage.layout
      { base := "rewardConfig",
        steps := [.mindex (.address (AccountAddress.ofNat (rewardConfigArgWord I).toNat)),
                  .field "multiplier"] } =
      fun _ => some (fieldLoc (slotAdd (rewardConfigSlotOf I) 1) 0 32
        (by decide) (.int uint256Int)) := by
    rfl
  rw [evalExpr_storage_scalar
    (hbase := by
      change ((rewardConfigStore I).insert "__calldata"
        (.bytes evm.executionEnv.calldata)).get? "rewardConfig" = none
      rw [store_get_ne _ _ (by decide)]
      rw [rewardConfigStore, store_get_ne _ _ (by decide)]
      simp)
    (her := her) (hty := hty) (hloc := hloc)]
  congr 1
  rw [slotAdd_one]
  rw [cometRewardsStorageLocLoad_uint256]

abbrev rewardConfigSourceReturnValues (evm : EVM.State) (I : ExecutionEnv) : List Value :=
  rewardConfigReturnValues
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (rewardConfigSlotOf I))
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (rewardConfigSlotOf I + ⟨1⟩))

theorem evalExprList_rewardConfig_return (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config
      { contract := contract,
        locals := (rewardConfigStore I).insert "__calldata" (.bytes evm.executionEnv.calldata) }
      evm
      [.storage (rewardConfigF (.var "arg0") "token"),
       .storage (rewardConfigF (.var "arg0") "rescaleFactor"),
       .storage (rewardConfigF (.var "arg0") "shouldUpscale"),
       .storage (rewardConfigF (.var "arg0") "multiplier")] =
        .ok (rewardConfigSourceReturnValues evm I) := by
  simp only [evalExprs?, evalExpr_rewardConfig_token, evalExpr_rewardConfig_rescale,
    evalExpr_rewardConfig_shouldUpscale, evalExpr_rewardConfig_multiplier, EvalResult.bind,
    bind, pure, rewardConfigSourceReturnValues, rewardConfigReturnValues,
    rewardConfigTokenFromSlot0, rewardConfigRescaleFromSlot0,
    rewardConfigShouldUpscaleRawFromSlot0, Int.ofNat_eq_natCast]

theorem cometRewardsRewardConfigBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ExecTransitionBody config contract evm (rewardConfigStore I) rewardConfigTransition.body
      (.returned
        { contract := contract,
          locals := (rewardConfigStore I).insert "__calldata"
            (.bytes evm.executionEnv.calldata) }
        evm
        (some (rewardConfigSourceReturnValues evm I))) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [rewardConfigTransition, externalEntryGuard, nonpayable, calldataSizeGuard,
    rewardConfigF] using
    (((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep (by
      simp [evalExpr?, envValue, pure])).requireStep
        (cometRewardsCalldataGuard_true evm (rewardConfigStore I) hsize)).run
      (ExecBlock.consReturn
        (ExecStmt.return (evalExprList_rewardConfig_return evm I)))

set_option maxHeartbeats 4000000
/-- `rewardConfig(address)` body, reached at pc 2615. -/
theorem cometRewardsRewardConfigBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cometRewardsBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (cometRewardsSelBytes 2))
    (hreach : ∃ k C, RD cometRewardsBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) rewardConfigPc
      (dispatchArmMidStack I) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hperm : I.perm = true := hperm
  have hsz4 := cometRewardsRewardConfigSelector_size hsel
  have hd := cometRewardsDispatch_rewardConfig (cd := I.calldata) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (rewardConfigArgWord I).toNat < EVM.addressModulus
      · have hdec := cometRewardsDecode_rewardConfig_ok (I := I) hsz36 hhi hcanon
        have hword0 :
            rewardConfigSlot0Word σ_evm I = rewardConfigSlot0Word σ_solm I :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner (rewardConfigSlotOf I) ⟨0⟩
        have hword1 :
            rewardConfigMultiplierWord σ_evm I = rewardConfigMultiplierWord σ_solm I :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner
            (rewardConfigSlotOf I + (⟨1⟩ : UInt256)) ⟨0⟩
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (rewardConfigStore I)
              rewardConfigTransition.body
              (.returned
                { contract := contract,
                  locals := (rewardConfigStore I).insert "__calldata" (.bytes I.calldata) }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (some (rewardConfigReturnValues
                  (rewardConfigSlot0Word σ_solm I)
                  (rewardConfigMultiplierWord σ_solm I)))) := by
          simpa [rewardConfigSourceReturnValues, rewardConfigSlot0Word,
            rewardConfigMultiplierWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
            using cometRewardsRewardConfigBodyReturns
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv)
              (by simp only [initState]; exact hhi)
        exact (cometRewardsX_rewardConfig (g := Sat256.ofUInt256 g)
            hwv hsz36 hsize hhi hcanon hreach)
          |>.reEquivExecutionTransport hcode hd hdec hbody
            (by rw [← hword0, ← hword1])
            hAccounts
            (returnEquiv.returned rfl
              (by
                simpa [rewardConfigReturnValues, rewardConfigTokenFromSlot0,
                  rewardConfigRescaleFromSlot0, rewardConfigShouldUpscaleFromSlot0,
                  rewardConfigShouldUpscaleRawFromSlot0, addr, uint64, boolTy, uint256]
                  using rewardConfigReturnEncoding
                    (rewardConfigSlot0Word σ_evm I) (rewardConfigMultiplierWord σ_evm I)))
      · have hdec := cometRewardsDecode_rewardConfig_none_noncanon
          (I := I) hsz36 hhi hcanon
        have hnc : UInt256.eq (rewardConfigArgWord I)
            (UInt256.land (rewardConfigArgWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne
            (fun he => hcanon (solcAddrCanonical_of_clean he))
        exact (cometRewardsRewardConfigX_noncanon_arg (g := Sat256.ofUInt256 g)
            hwv hsz36 hsize hhi hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := cometRewardsDecode_rewardConfig_none_huge (I := I) hbig
      exact (cometRewardsRewardConfigX_hugearg (g := Sat256.ofUInt256 g)
          hwv hsize hbig hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := cometRewardsDecode_rewardConfig_none_short (I := I) hsz4 hshort
    exact (cometRewardsRewardConfigX_shortarg (g := Sat256.ofUInt256 g)
        hwv hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.CompoundIII.CometRewards
