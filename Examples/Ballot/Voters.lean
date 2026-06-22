import Examples.Ballot.Common
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Ballot

/-! ## `voters(address)` getter -/

abbrev votersArgWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4

abbrev votersArgValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (votersArgWord I).toNat)

abbrev votersStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "a" (votersArgValue I)

def votersEvaledRef (I : ExecutionEnv) (field : Ident) : EvaledStorageRef :=
  { base := "voters",
    steps := [.mindex (.address (AccountAddress.ofNat (votersArgWord I).toNat)), .field field] }

theorem evalStorageRef_votersField (evm : EVM.State) (I : ExecutionEnv) (field : Ident) :
    evalStorageRef ballotConfig { contract := ballotContract, locals := votersStore I } evm
      (voterF (.var "a") field) = .ok (votersEvaledRef I field) := by
  simp [evalStorageRef, evalStorageRefStep, voterF, votersEvaledRef, votersStore,
    votersArgValue, valueToKey?, EvalResult.bind, EvalResult.ofOption,
    bind, pure, evalExpr?]

def votersBaseSlot (I : ExecutionEnv) : UInt256 :=
  voterBase (.address (AccountAddress.ofNat (votersArgWord I).toNat))

def votersPackedSlot (I : ExecutionEnv) : UInt256 := votersBaseSlot I + ⟨1⟩

def votersVoteSlot (I : ExecutionEnv) : UInt256 := votersBaseSlot I + ⟨2⟩

def votersWeightWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (votersBaseSlot I) ⟨0⟩)

def votersPackedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (votersPackedSlot I) ⟨0⟩)

def votersVoteWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (votersVoteSlot I) ⟨0⟩)

def votersVotedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (votersPackedWord σ I) ⟨255⟩

def votersDelegateWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (votersPackedWord σ I) ⟨256⟩) solcAddrMask

theorem votersDelegateWord_doubleMask (w : UInt256) :
    UInt256.land solcAddrMask (UInt256.land solcAddrMask (UInt256.div w ⟨256⟩)) =
      UInt256.land (UInt256.div w ⟨256⟩) solcAddrMask := by
  rw [u256_land_comm solcAddrMask (UInt256.land solcAddrMask (UInt256.div w ⟨256⟩))]
  rw [u256_land_comm solcAddrMask (UInt256.div w ⟨256⟩)]
  exact solcAddrMask_clean (solcAddrMask_result_canonical (UInt256.div w ⟨256⟩))

abbrev votersBoolWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.isZero (UInt256.isZero (votersVotedWord σ I))

-- SHARED-HELPER CANDIDATE: duplicate of ERC20's canonical address-key bridge.
theorem ballotKeyValueToWord_address_of_canonical (w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    keyValueToWord (.address (AccountAddress.ofNat w.toNat)) = w := by
  apply u256_inj
  unfold keyValueToWord AccountAddress.ofNat
  exact Nat.mod_eq_of_lt (by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)

theorem votersBaseSlot_spec (I : ExecutionEnv)
    (hcanon : (votersArgWord I).toNat < EVM.addressModulus) :
    votersBaseSlot I =
      uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (votersArgWord I) ++
        UInt256.toByteArray (⟨1⟩ : UInt256))) := by
  unfold votersBaseSlot voterBase mapSlot
  rw [ballotKeyValueToWord_address_of_canonical (votersArgWord I) hcanon]

-- LIBRARY CANDIDATE: `Reasoning.Memory`, generalizing `fromBytes'_take20_wordLE`.
theorem fromBytes'_take1_wordLE (w : UInt256) :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof w).1.take 1) =
      (UInt256.land w ⟨255⟩).toNat := by
  let bs := (EVM.Word.toBytesLEWithSizeProof w).1
  have hfull : Nat.ofDigits 256 (bs.map (fun b : UInt8 => b.toNat)) = w.toNat := by
    rw [← fromBytes'_eq_ofDigits bs]
    exact fromBytes'_toBytesLEWithSizeProof w
  have hlt : ∀ l ∈ bs.map (fun b : UInt8 => b.toNat), l < 256 := by
    intro l hl
    simp only [List.mem_map] at hl
    rcases hl with ⟨b, _hb, rfl⟩
    exact b.toFin.isLt
  have htake := Nat.ofDigits_mod_pow_eq_ofDigits_take (p := 256) 1 (by decide)
    (bs.map (fun b : UInt8 => b.toNat)) hlt
  rw [fromBytes'_eq_ofDigits ((EVM.Word.toBytesLEWithSizeProof w).1.take 1)]
  change Nat.ofDigits 256 ((bs.take 1).map fun b : UInt8 => b.toNat) = _
  rw [List.map_take, ← htake, hfull]
  show w.toNat % 256 ^ 1 = (Nat.land w.toNat (⟨255⟩ : UInt256).toNat) % UInt256.size
  rw [show 256 ^ 1 = 2 ^ 8 by norm_num]
  rw [show (⟨255⟩ : UInt256).toNat = 2 ^ 8 - 1 by decide]
  rw [nat_land_mask_eq_mod]
  have hsmall : w.toNat % 2 ^ 8 < UInt256.size :=
    lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 8)) (by norm_num [UInt256.size])
  conv_rhs => rw [Nat.mod_eq_of_lt hsmall]

-- LIBRARY CANDIDATE: `Reasoning.Memory`, packed address at byte offset 1.
theorem fromBytes'_drop1_take20_wordLE (w : UInt256) :
    fromBytes' (((EVM.Word.toBytesLEWithSizeProof w).1.drop 1).take 20) =
      (UInt256.land (UInt256.div w ⟨256⟩) solcAddrMask).toNat := by
  let bs := (EVM.Word.toBytesLEWithSizeProof w).1
  have hfull : Nat.ofDigits 256 (bs.map (fun b : UInt8 => b.toNat)) = w.toNat := by
    rw [← fromBytes'_eq_ofDigits bs]
    exact fromBytes'_toBytesLEWithSizeProof w
  have hlt : ∀ l ∈ bs.map (fun b : UInt8 => b.toNat), l < 256 := by
    intro l hl
    simp only [List.mem_map] at hl
    rcases hl with ⟨b, _hb, rfl⟩
    exact b.toFin.isLt
  have hdrop := Nat.ofDigits_div_pow_eq_ofDigits_drop (p := 256) 1 (by decide)
    (bs.map (fun b : UInt8 => b.toNat)) hlt
  have htake := Nat.ofDigits_mod_pow_eq_ofDigits_take (p := 256) 20 (by decide)
    ((bs.map (fun b : UInt8 => b.toNat)).drop 1)
    (fun l hl => hlt l (List.mem_of_mem_drop hl))
  rw [fromBytes'_eq_ofDigits (((EVM.Word.toBytesLEWithSizeProof w).1.drop 1).take 20)]
  change Nat.ofDigits 256 ((((bs.drop 1).take 20).map fun b : UInt8 => b.toNat)) = _
  rw [List.map_take, List.map_drop, ← htake, ← hdrop, hfull]
  show w.toNat / 256 % 256 ^ 20 =
    (Nat.land (UInt256.div w ⟨256⟩).toNat solcAddrMask.toNat) % UInt256.size
  unfold UInt256.div UInt256.toNat
  simp only
  change w.toNat / 256 % 256 ^ 20 = Nat.land (w.toNat / 256) solcAddrMask.toNat % UInt256.size
  rw [show 256 ^ 20 = 2 ^ 160 by norm_num]
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
  rw [nat_land_mask_eq_mod]
  have hsmall : w.toNat / 256 % 2 ^ 160 < UInt256.size :=
    lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 160)) (by norm_num [UInt256.size])
  conv_rhs => rw [Nat.mod_eq_of_lt hsmall]

theorem ballotStorageLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 1, hbound := by decide, type := .bool }
      = wordToElem .bool
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) := by
  unfold storageLocLoad
  simp only [Fin.val_zero, Nat.zero_add]
  congr
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 1) = _
  rw [fromBytes'_take1_wordLE]
  rfl

theorem ballotStorageLocLoad_address_offset1 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm
        { slot := slot, offset := 1, size := 20, hbound := by decide, type := .address }
      = .address (AccountAddress.ofNat
          (UInt256.land
          (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨256⟩)
            solcAddrMask).toNat) := by
  unfold storageLocLoad wordToElem
  simp only [Fin.val_one]
  change Value.address (AccountAddress.ofNat
      (fromBytes' (((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1).extract 1 21))) = _
  rw [List.extract_eq_take_drop, fromBytes'_drop1_take20_wordLE]

theorem ballotVotersBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (_hcanon : (votersArgWord I).toNat < EVM.addressModulus) :
    ExecTransitionBody ballotConfig ballotContract evm (votersStore I) votersGetter.body
      (.returned { contract := ballotContract, locals := votersStore I } evm
        (some (.tuple [
          .int (Int.ofNat (votersWeightWord evm.accountMap I).toNat),
          wordToElem .bool (votersVotedWord evm.accountMap I),
          .address (AccountAddress.ofNat (votersDelegateWord evm.accountMap I).toNat),
          .int (Int.ofNat (votersVoteWord evm.accountMap I).toNat)]))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have hweight :
          evalExpr? ballotConfig { contract := ballotContract, locals := votersStore I } evm
            (.storage (voterF (.var "a") "weight")) =
              .ok (.int (Int.ofNat (votersWeightWord evm.accountMap I).toNat)) := by
        rw [evalExpr_storage_scalar (t := .int uint256Int)
          (hbase := by simp [votersStore, voterF])
          (her := evalStorageRef_votersField evm I "weight")
          (hty := by simp [storageTypeAt?, votersEvaledRef, ballotContract, ballotStorageDecls,
            voterStructTy, uint256St, storageTypeStep?])
          (hloc := by funext evm'; rfl),
          ballotStorageLocLoad_uint256]
        simp [votersWeightWord, votersBaseSlot, howner, Solm.EVM.storageLoad,
          State.lookupAccount, Account.lookupStorage]
      have hvoted :
          evalExpr? ballotConfig { contract := ballotContract, locals := votersStore I } evm
            (.storage (voterF (.var "a") "voted")) =
              .ok (wordToElem .bool (votersVotedWord evm.accountMap I)) := by
        rw [evalExpr_storage_scalar (t := .bool)
          (hbase := by simp [votersStore, voterF])
          (her := evalStorageRef_votersField evm I "voted")
          (hty := by simp [storageTypeAt?, votersEvaledRef, ballotContract, ballotStorageDecls,
            voterStructTy, boolSt, storageTypeStep?])
          (hloc := by funext evm'; rfl),
          ballotStorageLocLoad_bool_offset0]
        simp [votersVotedWord, votersPackedWord, votersPackedSlot, votersBaseSlot, howner,
          Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      have hdelegate :
          evalExpr? ballotConfig { contract := ballotContract, locals := votersStore I } evm
            (.storage (voterF (.var "a") "delegate")) =
              .ok (.address (AccountAddress.ofNat (votersDelegateWord evm.accountMap I).toNat)) := by
        rw [evalExpr_storage_scalar (t := .address)
          (hbase := by simp [votersStore, voterF])
          (her := evalStorageRef_votersField evm I "delegate")
          (hty := by simp [storageTypeAt?, votersEvaledRef, ballotContract, ballotStorageDecls,
            voterStructTy, addrSt, storageTypeStep?])
          (hloc := by funext evm'; rfl),
          ballotStorageLocLoad_address_offset1]
        simp [votersDelegateWord, votersPackedWord, votersPackedSlot, votersBaseSlot, howner,
          Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      have hvote :
          evalExpr? ballotConfig { contract := ballotContract, locals := votersStore I } evm
            (.storage (voterF (.var "a") "vote")) =
              .ok (.int (Int.ofNat (votersVoteWord evm.accountMap I).toNat)) := by
        rw [evalExpr_storage_scalar (t := .int uint256Int)
          (hbase := by simp [votersStore, voterF])
          (her := evalStorageRef_votersField evm I "vote")
          (hty := by simp [storageTypeAt?, votersEvaledRef, ballotContract, ballotStorageDecls,
            voterStructTy, uint256St, storageTypeStep?])
          (hloc := by funext evm'; rfl),
          ballotStorageLocLoad_uint256]
        simp [votersVoteWord, votersVoteSlot, votersBaseSlot, howner, Solm.EVM.storageLoad,
          State.lookupAccount, Account.lookupStorage]
      simp [evalExpr?, evalExprList?, EvalResult.bind, bind, pure,
        hweight, hvoted, hdelegate, hvote])

/-! ## Memory used by the voter getter -/

noncomputable def votersBaseSlotMem : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 solcFreePtrMem 32 32

noncomputable def votersHashMem (a : UInt256) : ByteArray :=
  (UInt256.toByteArray a).write 0 votersBaseSlotMem 0 32

noncomputable def votersReturnWeightMem (scratch weight : UInt256) : ByteArray :=
  (UInt256.toByteArray weight).write 0 (votersHashMem scratch) 128 32

noncomputable def votersReturnVotedMem (scratch weight voted : UInt256) : ByteArray :=
  (UInt256.toByteArray voted).write 0 (votersReturnWeightMem scratch weight) 160 32

noncomputable def votersReturnDelegateMem (scratch weight voted delegate : UInt256) : ByteArray :=
  (UInt256.toByteArray delegate).write 0 (votersReturnVotedMem scratch weight voted) 192 32

noncomputable def votersReturnMem (scratch weight voted delegate vote : UInt256) : ByteArray :=
  (UInt256.toByteArray vote).write 0 (votersReturnDelegateMem scratch weight voted delegate) 224 32

theorem votersBaseSlotMem_size : votersBaseSlotMem.size = 96 := by
  unfold votersBaseSlotMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  omega

theorem votersHashMem_size (a : UInt256) : (votersHashMem a).size = 96 := by
  unfold votersHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [votersBaseSlotMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, votersBaseSlotMem_size, toByteArray_size]
  omega

theorem votersBaseSlotMem_read32 :
    votersBaseSlotMem.readWithPadding 32 32 = UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold votersBaseSlotMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    show (UInt256.toByteArray (⟨1⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
          rw [toByteArray_size])]

theorem votersBaseSlotMem_read64 :
    votersBaseSlotMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold votersBaseSlotMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega) (by omega)
      (by rw [solcFreePtrMem_size]),
    solcFreePtrMem_read64]

theorem votersHashMem_read0 (a : UInt256) :
    (votersHashMem a).readWithPadding 0 32 = UInt256.toByteArray a := by
  unfold votersHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega),
    show (UInt256.toByteArray a).extract 0 32 = UInt256.toByteArray a from by
      apply ByteArray.ext
      rw [ByteArray.data_extract]
      exact Array.extract_eq_self_of_le (by
        change (UInt256.toByteArray a).size ≤ 32
        rw [toByteArray_size])]

theorem votersHashMem_read32 (a : UInt256) :
    (votersHashMem a).readWithPadding 32 32 = UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold votersHashMem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
      (by rw [votersBaseSlotMem_size]; omega) (by omega)
      (by rw [votersBaseSlotMem_size]; omega),
    votersBaseSlotMem_read32]

theorem votersHashMem_read64 (a : UInt256) :
    (votersHashMem a).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold votersHashMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [votersBaseSlotMem_size]; omega) (by omega)
      (by rw [votersBaseSlotMem_size]),
    votersBaseSlotMem_read64]

theorem votersHashMem_mload64 (a : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (votersHashMem a).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((votersHashMem a).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [votersHashMem_size]; decide) (by decide)
    (votersHashMem_read64 a)

theorem votersKeccakSlot' (I : ExecutionEnv)
    (hcanon : (votersArgWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((votersHashMem (votersArgWord I)).readWithPadding 0 64)))
      = votersBaseSlot I := by
  have hread :
      (votersHashMem (votersArgWord I)).readWithPadding 0 64 =
        UInt256.toByteArray (votersArgWord I) ++ UInt256.toByteArray (⟨1⟩ : UInt256) := by
    rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [votersHashMem_size]; omega)]
    unfold votersHashMem
    rw [write32_eq _ _ _ (by rw [toByteArray_size])
        (by rw [votersBaseSlotMem_size]; omega)]
    have hempty : votersBaseSlotMem.extract 0 0 = ByteArray.empty := by
      apply ByteArray.ext
      rw [ByteArray.data_extract]
      exact Array.extract_eq_empty_of_le (by omega)
    have hkeyFull : (UInt256.toByteArray (votersArgWord I)).extract 0 32 =
        UInt256.toByteArray (votersArgWord I) := by
      apply ByteArray.ext
      rw [ByteArray.data_extract]
      exact Array.extract_eq_self_of_le (by
        change (UInt256.toByteArray (votersArgWord I)).size ≤ 32
        rw [toByteArray_size])
    rw [hempty, empty_append, hkeyFull]
    rw [extract_append_span (UInt256.toByteArray (votersArgWord I))
        (votersBaseSlotMem.extract 32 votersBaseSlotMem.size) 0 64
        (by omega) (by rw [toByteArray_size]; omega)]
    rw [show (UInt256.toByteArray (votersArgWord I)).extract 0
        (UInt256.toByteArray (votersArgWord I)).size =
          UInt256.toByteArray (votersArgWord I) by
      apply ByteArray.ext
      rw [ByteArray.data_extract]
      exact Array.extract_eq_self_of_le (by
        show (UInt256.toByteArray (votersArgWord I)).data.size ≤
          (UInt256.toByteArray (votersArgWord I)).size
        rfl)]
    have htail :
        (votersBaseSlotMem.extract 32 votersBaseSlotMem.size).extract 0
            (64 - (UInt256.toByteArray (votersArgWord I)).size) =
          UInt256.toByteArray (⟨1⟩ : UInt256) := by
      rw [toByteArray_size]
      rw [extract_extract_BA]
      rw [show 32 + 0 = 32 by norm_num]
      rw [show min (32 + 32) votersBaseSlotMem.size = 64 by
        rw [votersBaseSlotMem_size]; norm_num]
      rw [← readWithPadding_eq_extract votersBaseSlotMem 32
        (by rw [votersBaseSlotMem_size]; omega)]
      exact votersBaseSlotMem_read32
    rw [htail]
  rw [hread, votersBaseSlot_spec I hcanon]
  exact keccakSlot_eq _

theorem votersReturnWeightMem_size (scratch weight : UInt256) :
    (votersReturnWeightMem scratch weight).size = 160 := by
  unfold votersReturnWeightMem
  rw [toByteArray_write_eq _ _ _ (by rw [votersHashMem_size]; omega)
      (by rw [votersHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, votersHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem votersReturnWeightMem_read64 (scratch weight : UInt256) :
    (votersReturnWeightMem scratch weight).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold votersReturnWeightMem
  rw [toByteArray_write_eq _ _ _ (by rw [votersHashMem_size]; omega)
      (by rw [votersHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.append_assoc]
  rw [readWithPadding_eq_extract' _ 64 32 (by norm_num) (by norm_num) (by
    rw [ByteArray.size_append, votersHashMem_size, ByteArray.size_append,
      ByteArray_zeroes_size,
      show (USize.ofNat (128 - 96)).toNat = 32 from by
        exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
      toByteArray_size]
    omega)]
  rw [extract_append_left (votersHashMem scratch)
      (ffi.ByteArray.zeroes (USize.ofNat (128 - (votersHashMem scratch).size)) ++
        UInt256.toByteArray weight)
      64 96 (by rw [votersHashMem_size])]
  rw [← readWithPadding_eq_extract' (votersHashMem scratch) 64 32
      (by norm_num) (by norm_num) (by rw [votersHashMem_size])]
  exact votersHashMem_read64 scratch

theorem votersReturnVotedMem_size (scratch weight voted : UInt256) :
    (votersReturnVotedMem scratch weight voted).size = 192 := by
  unfold votersReturnVotedMem
  rw [toByteArray_write_eq _ _ _ (by rw [votersReturnWeightMem_size])
      (by rw [votersReturnWeightMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, votersReturnWeightMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (160 - 160)).toNat = 0 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem votersReturnDelegateMem_size (scratch weight voted delegate : UInt256) :
    (votersReturnDelegateMem scratch weight voted delegate).size = 224 := by
  unfold votersReturnDelegateMem
  rw [toByteArray_write_eq _ _ _ (by rw [votersReturnVotedMem_size])
      (by rw [votersReturnVotedMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, votersReturnVotedMem_size,
    ByteArray_zeroes_size,
    show (USize.ofNat (192 - 192)).toNat = 0 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem votersReturnMem_size (scratch weight voted delegate vote : UInt256) :
    (votersReturnMem scratch weight voted delegate vote).size = 256 := by
  unfold votersReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [votersReturnDelegateMem_size])
      (by rw [votersReturnDelegateMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, votersReturnDelegateMem_size,
    ByteArray_zeroes_size,
    show (USize.ofNat (224 - 224)).toNat = 0 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem votersReturnMem_read64 (scratch weight voted delegate vote : UInt256) :
    (votersReturnMem scratch weight voted delegate vote).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold votersReturnMem
  rw [write32_read_below _ _ 224 64 (by rw [toByteArray_size])
      (by rw [votersReturnDelegateMem_size]) (by omega)]
  unfold votersReturnDelegateMem
  rw [write32_read_below _ _ 192 64 (by rw [toByteArray_size])
      (by rw [votersReturnVotedMem_size]) (by omega)]
  unfold votersReturnVotedMem
  rw [write32_read_below _ _ 160 64 (by rw [toByteArray_size])
      (by rw [votersReturnWeightMem_size]) (by omega)]
  exact votersReturnWeightMem_read64 scratch weight

theorem votersReturnMem_mload64 (scratch weight voted delegate vote : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (votersReturnMem scratch weight voted delegate vote).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((votersReturnMem scratch weight voted delegate vote).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [votersReturnMem_size]; decide) (by decide)
    (votersReturnMem_read64 scratch weight voted delegate vote)

theorem votersReturnMem_read128_128 (scratch weight voted delegate vote : UInt256) :
    (votersReturnMem scratch weight voted delegate vote).readWithPadding 128 128 =
      UInt256.toByteArray weight ++ UInt256.toByteArray voted ++
        UInt256.toByteArray delegate ++ UInt256.toByteArray vote := by
  rw [readWithPadding_eq_extract' _ 128 128 (by norm_num) (by norm_num)
      (by rw [votersReturnMem_size])]
  unfold votersReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [votersReturnDelegateMem_size])
      (by rw [votersReturnDelegateMem_size]; exact lt_usize _ (by norm_num))]
  rw [extract_append_span
      (votersReturnDelegateMem scratch weight voted delegate ++
        ffi.ByteArray.zeroes
          (USize.ofNat (224 - (votersReturnDelegateMem scratch weight voted delegate).size)))
      (UInt256.toByteArray vote) 128 256 (by
        rw [ByteArray.size_append, votersReturnDelegateMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (224 - 224)).toNat = 0 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
        omega) (by
        rw [ByteArray.size_append, votersReturnDelegateMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (224 - 224)).toNat = 0 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
        omega)]
  rw [ByteArray.size_append, votersReturnDelegateMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (224 - 224)).toNat = 0 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  rw [show ffi.ByteArray.zeroes (USize.ofNat (224 - 224)) =
      ByteArray.empty by
        exact zeroes_zero (n := USize.ofNat 0)
          (by exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)))]
  simp
  unfold votersReturnDelegateMem
  rw [toByteArray_write_eq _ _ _ (by rw [votersReturnVotedMem_size])
      (by rw [votersReturnVotedMem_size]; exact lt_usize _ (by norm_num))]
  rw [extract_append_span
      (votersReturnVotedMem scratch weight voted ++
        ffi.ByteArray.zeroes
          (USize.ofNat (192 - (votersReturnVotedMem scratch weight voted).size)))
      (UInt256.toByteArray delegate) 128 224 (by
        rw [ByteArray.size_append, votersReturnVotedMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (192 - 192)).toNat = 0 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
        omega) (by
        rw [ByteArray.size_append, votersReturnVotedMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (192 - 192)).toNat = 0 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
        omega)]
  rw [ByteArray.size_append, votersReturnVotedMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (192 - 192)).toNat = 0 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  rw [show ffi.ByteArray.zeroes (USize.ofNat (192 - 192)) =
      ByteArray.empty by
        exact zeroes_zero (n := USize.ofNat 0)
          (by exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)))]
  simp
  unfold votersReturnVotedMem
  rw [toByteArray_write_eq _ _ _ (by rw [votersReturnWeightMem_size])
      (by rw [votersReturnWeightMem_size]; exact lt_usize _ (by norm_num))]
  rw [extract_append_span
      (votersReturnWeightMem scratch weight ++
        ffi.ByteArray.zeroes (USize.ofNat (160 - (votersReturnWeightMem scratch weight).size)))
      (UInt256.toByteArray voted) 128 192 (by
        rw [ByteArray.size_append, votersReturnWeightMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (160 - 160)).toNat = 0 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
        omega) (by
        rw [ByteArray.size_append, votersReturnWeightMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (160 - 160)).toNat = 0 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
        omega)]
  rw [ByteArray.size_append, votersReturnWeightMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (160 - 160)).toNat = 0 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  rw [show ffi.ByteArray.zeroes (USize.ofNat (160 - 160)) =
      ByteArray.empty by
        exact zeroes_zero (n := USize.ofNat 0)
          (by exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)))]
  simp
  unfold votersReturnWeightMem
  rw [toByteArray_write_eq _ _ _ (by rw [votersHashMem_size]; omega)
      (by rw [votersHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [extract_append_right_window
      (votersHashMem scratch ++ ffi.ByteArray.zeroes (USize.ofNat (128 - (votersHashMem scratch).size)))
      (UInt256.toByteArray weight) 128 160 (by
        rw [ByteArray.size_append, votersHashMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (128 - 96)).toNat = 32 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))])]
  rw [ByteArray.size_append, votersHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  norm_num
  repeat'
    first
    | rw [show (UInt256.toByteArray weight).extract 0 32 = UInt256.toByteArray weight from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray weight).size ≤ 32
          rw [toByteArray_size])]
    | rw [show (UInt256.toByteArray voted).extract 0 32 = UInt256.toByteArray voted from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray voted).size ≤ 32
          rw [toByteArray_size])]
    | rw [show (UInt256.toByteArray delegate).extract 0 32 = UInt256.toByteArray delegate from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray delegate).size ≤ 32
          rw [toByteArray_size])]
    | rw [show (UInt256.toByteArray vote).extract 0 32 = UInt256.toByteArray vote from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray vote).size ≤ 32
          rw [toByteArray_size])]

theorem votersSubRet128_toNat :
    (UInt256.sub ((⟨128⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 128 := by
  decide

theorem ballotBoolWordEncoding (w : UInt256) :
    encodeABIValue? boolTy (wordToElem .bool (UInt256.land w ⟨255⟩)) =
      some (EVM.Word.toBytesBE (UInt256.isZero (UInt256.isZero (UInt256.land w ⟨255⟩)))) := by
  by_cases hval : (UInt256.land w ⟨255⟩).val = 0
  · have hz : UInt256.land w ⟨255⟩ = ⟨0⟩ := by
      apply u256_inj
      exact congrArg Fin.val hval
    have hnorm : UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256)) = ⟨0⟩ := by decide
    simp [boolTy, wordToElem, hz, hnorm, encodeABIValue?, encodeABIWord?,
      Bool.toUInt256_false]
    rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl]
  · have hz : UInt256.land w ⟨255⟩ ≠ ⟨0⟩ := by
      intro hx
      apply hval
      rw [hx]
    have hiz : UInt256.isZero (UInt256.land w ⟨255⟩) = ⟨0⟩ := isZero_eq_zero_of_ne hz
    have hnorm : UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ := by decide
    simp [boolTy, wordToElem, hval, hiz, hnorm, encodeABIValue?, encodeABIWord?,
      Bool.toUInt256_true]
    rw [show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl]

theorem ballotVotersReturnEncoding (weight packed vote : UInt256) :
    encodeReturnValue? (.tuple [uint256, boolTy, addr, uint256])
      (.tuple [.int (Int.ofNat weight.toNat),
        wordToElem .bool (UInt256.land packed ⟨255⟩),
        .address (AccountAddress.ofNat
          (UInt256.land (UInt256.div packed ⟨256⟩) solcAddrMask).toNat),
        .int (Int.ofNat vote.toNat)]) =
      some (UInt256.toByteArray weight ++
        UInt256.toByteArray (UInt256.isZero (UInt256.isZero (UInt256.land packed ⟨255⟩))) ++
        UInt256.toByteArray (UInt256.land (UInt256.div packed ⟨256⟩) solcAddrMask) ++
        UInt256.toByteArray vote) := by
  have hweight : EVM.word weight.toNat = weight := u256_ofNat_toNat weight
  have hvote : EVM.word vote.toNat = vote := u256_ofNat_toNat vote
  have hdelegateCanon := solcAddrMask_result_canonical (UInt256.div packed ⟨256⟩)
  have hdelegateMod :
      (UInt256.land (UInt256.div packed ⟨256⟩) solcAddrMask).toNat % AccountAddress.size =
        (UInt256.land (UInt256.div packed ⟨256⟩) solcAddrMask).toNat := by
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hdelegateCanon
  have hdelegateWord :
      EVM.word (UInt256.land (UInt256.div packed ⟨256⟩) solcAddrMask).toNat =
        UInt256.land (UInt256.div packed ⟨256⟩) solcAddrMask :=
    u256_ofNat_toNat _
  have hweightLt : weight.toNat < EVM.twoPow 256 := by
    change weight.val.val < EVM.twoPow 256
    exact weight.val.isLt
  have hvoteLt : vote.toNat < EVM.twoPow 256 := by
    change vote.val.val < EVM.twoPow 256
    exact vote.val.isLt
  have hencWeight :
      encodeABIValue? uint256 (.int (Int.ofNat weight.toNat)) =
        some (EVM.Word.toBytesBE weight) := by
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hweight, hweightLt]
  have hencBool :
      encodeABIValue? boolTy (wordToElem .bool (UInt256.land packed ⟨255⟩)) =
        some (EVM.Word.toBytesBE
          (UInt256.isZero (UInt256.isZero (UInt256.land packed ⟨255⟩)))) := by
    simpa [toByteArray_eq_toBytesBE] using ballotBoolWordEncoding packed
  have hencDelegate :
      encodeABIValue? addr (.address (AccountAddress.ofNat
        (UInt256.land (UInt256.div packed ⟨256⟩) solcAddrMask).toNat)) =
        some (EVM.Word.toBytesBE (UInt256.land (UInt256.div packed ⟨256⟩) solcAddrMask)) := by
    simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, hdelegateMod,
      hdelegateWord]
  have hencVote :
      encodeABIValue? uint256 (.int (Int.ofNat vote.toNat)) =
        some (EVM.Word.toBytesBE vote) := by
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hvote, hvoteLt]
  have hheadInner :
      abiTupleHeadSize? [uint256, boolTy, addr, uint256] = some 128 := by native_decide
  have hheadOuter :
      abiTupleHeadSize? [(.tuple [uint256, boolTy, addr, uint256])] = some 128 := by
    native_decide
  have hdynUint : isDynamicABIType uint256 = false := by native_decide
  have hdynBool : isDynamicABIType boolTy = false := by native_decide
  have hdynAddr : isDynamicABIType addr = false := by native_decide
  have hdynTuple : isDynamicABIType (.tuple [uint256, boolTy, addr, uint256]) = false := by
    native_decide
  have hinner :
      encodeABIValue? (.tuple [uint256, boolTy, addr, uint256])
        (.tuple [.int (Int.ofNat weight.toNat),
          wordToElem .bool (UInt256.land packed ⟨255⟩),
          .address (AccountAddress.ofNat
            (UInt256.land (UInt256.div packed ⟨256⟩) solcAddrMask).toNat),
          .int (Int.ofNat vote.toNat)]) =
        some (EVM.Word.toBytesBE weight ++
          EVM.Word.toBytesBE (UInt256.isZero (UInt256.isZero (UInt256.land packed ⟨255⟩))) ++
          EVM.Word.toBytesBE (UInt256.land (UInt256.div packed ⟨256⟩) solcAddrMask) ++
          EVM.Word.toBytesBE vote) := by
    simp only [encodeABIValue?, encodeABIValues?, encodeABIValuesFrom?,
      hheadInner, hencWeight, hencBool, hencDelegate, hencVote, hdynUint, hdynBool,
      hdynAddr, bind, Option.bind, Bool.false_eq_true, if_false, List.nil_append,
      List.append_nil]
  rw [toByteArray_eq_toBytesBE weight,
    toByteArray_eq_toBytesBE (UInt256.isZero (UInt256.isZero (UInt256.land packed ⟨255⟩))),
    toByteArray_eq_toBytesBE (UInt256.land (UInt256.div packed ⟨256⟩) solcAddrMask),
    toByteArray_eq_toBytesBE vote]
  simp only [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?,
    hheadOuter, hinner, hdynTuple, bind, Option.bind, Bool.false_eq_true, if_false,
    List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

end Ballot

namespace Reasoning.Theory

open Ethereum Ethereum.EVM

-- LIBRARY CANDIDATE: `Reasoning.Stepping`, generic `DIV` xstep.
theorem ballotDiv_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DIV, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 5 then .error .OutOfGass
         else .ok (stMul s (UInt256.div a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DIV, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_div s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Glow, stMul]

-- LIBRARY CANDIDATE: `Reasoning.Stepping`, generic `SWAP5` xstep.
theorem ballotSwap5_xstep {s : State} {code : ByteArray} {pcv a b c d e f : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP5, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: t)
    (hov : t.length + 6 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (f :: b :: c :: d :: e :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP5, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap5 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: t).length - 6 + 6 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

-- LIBRARY CANDIDATE: `Reasoning.Memory`, literal-stack `MSTORE` memory expansion costs.
theorem ballotMstoreCost_of_stack {s : State} {aw off val : UInt256} {t : List UInt256}
    {mcost : ℕ}
    (haw : s.machineState.activeWords = aw)
    (hstk : s.machineState.stack = off :: val :: t)
    (hcost : Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) - Cₘ aw = mcost) :
    memoryExpansionCost s .MSTORE = mcost := by
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ']
  have htop : s.machineState.stack[0]! = off := by
    rw [hstk]
    rfl
  rw [htop, haw]
  exact hcost

end Reasoning.Theory

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

-- LIBRARY CANDIDATE: `Reasoning.Reach`, generic `RD.div`.
theorem RD.ballotDiv {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.DIV, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.div a b :: t) mem aw rdata acc (k + 1) (C + 5) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := Reasoning.Theory.ballotDiv_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 5
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stMul s (UInt256.div a b) t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stMul]; exact hcode
      · simp only [stMul]; rw [hpc]
      · rfl
      · simp only [stMul]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stMul]; exact hmem
      · simp only [stMul]; exact haw
      · simp only [stMul]; exact hrdata
      · simp only [stMul]; exact hacc
      · exact hee
      · exact hworld

-- LIBRARY CANDIDATE: `Reasoning.Reach`, generic `RD.swap5`.
theorem RD.swap5 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP5, .none)) (hov : t.length + 6 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (f :: b :: c :: d :: e :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => ballotSwap5_xstep hc hp hdec hs hov)

set_option maxHeartbeats 500000 in
/-- Ballot's shared solc one-address decoder at pc 1770, success branch. -/
theorem RD.ballotDecodeAddressOk1770 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨1770⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩)
    (hcanon : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hret : (D_J ballotBytecode 0).contains ret = true) (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD ballotBytecode ee g s0 ret (calldataWord ee.calldata 4 :: R)
      mem aw rdata acc k' C' := by
  have hclean : UInt256.eq (calldataWord ee.calldata 4)
      (UInt256.land (calldataWord ee.calldata 4) solcAddrMask) = ⟨1⟩ :=
    solcAddrCanon_eq hcanon
  have hclean' : UInt256.eq
        (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
        (UInt256.land
          (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨1⟩ := by
    simpa [calldataWord, solcAddrMask] using hclean
  exact ⟨_, _, evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨1786⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup2, and, dup2, eq, push2 ⟨1808⟩, jumpiT (by rw [hclean']; decide) (by jump_dest),
    jumpdest, swap4, swap3, pop, pop, pop, jump hret ]⟩

theorem RD.ballotDecodeAddressLenRevert1770 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨1770⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩)
    (hov : R.length + 10 ≤ 1024) :
    RDrev ballotBytecode g s0 :=
  evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨1786⟩,
    jumpiNT (by rw [hsltval]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by
      have hR : R.length ≤ 1024 - 10 := Nat.le_sub_of_add_le hov
      simp only [List.length_cons]
      omega) ]

set_option maxHeartbeats 300000 in
theorem RD.ballotDecodeAddressNoncanonRevert1770 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ballotBytecode ee g s0 ⟨1770⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩)
    (hnc : UInt256.eq (calldataWord ee.calldata 4)
        (UInt256.land (calldataWord ee.calldata 4) solcAddrMask) = ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev ballotBytecode g s0 :=
  have hnc' : UInt256.eq
        (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
        (UInt256.land
          (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨0⟩ := by
    simpa [calldataWord, solcAddrMask] using hnc
  evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨1786⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest),
    jumpdest, dup2, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup2, and, dup2, eq, push2 ⟨1808⟩, jumpiNT (by rw [hnc']),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

end Reasoning.Reach

namespace Ballot

/-! ## EVM trace -/

theorem ballotVotersX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨305⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1770⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨319⟩, ⟨370⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd305⟩ := hreach
  exact ⟨_, _, evm_run rd305 with [
    jumpdest, push2 ⟨370⟩, push2 ⟨319⟩, calldatasize, push1 ⟨4⟩, push2 ⟨1770⟩,
    jump (by jump_dest) ]⟩

theorem ballotVotersX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (votersArgWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨305⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨319⟩
      [votersArgWord I, ⟨370⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd1770⟩ := ballotVotersX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  simpa [votersArgWord, calldataWord] using
    RD.ballotDecodeAddressOk1770 (R := [⟨370⟩, sel]) rd1770 hslt hcanon (by jump_dest)
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem ballotVotersX_decodeRevert_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨305⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨_, _, rd1770⟩ := ballotVotersX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact RD.ballotDecodeAddressLenRevert1770 (R := [⟨370⟩, sel]) rd1770 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ballotVotersX_decodeRevert_huge {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨305⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨_, _, rd1770⟩ := ballotVotersX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact RD.ballotDecodeAddressLenRevert1770 (R := [⟨370⟩, sel]) rd1770 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ballotVotersX_decodeRevert_noncanon {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (votersArgWord I) (UInt256.land (votersArgWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨305⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ballotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨_, _, rd1770⟩ := ballotVotersX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact RD.ballotDecodeAddressNoncanonRevert1770 (R := [⟨370⟩, sel]) rd1770 hslt
    (by simpa [votersArgWord] using hnc) (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 500000 in
theorem ballotX_voters_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (votersArgWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ballotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨305⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret ballotBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (votersWeightWord σ I) ++
        UInt256.toByteArray (votersBoolWord σ I) ++
        UInt256.toByteArray (votersDelegateWord σ I) ++
        UInt256.toByteArray (votersVoteWord σ I)) := by
  obtain ⟨_, _, rd319⟩ := ballotVotersX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz36 hsize hszhi hcanon hreach
  have hslot := votersKeccakSlot' I hcanon
  have rd335 := evm_run rd319 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1,
    raw mstore 0 votersBaseSlotMem (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push0, swap2, dup3,
    raw mstore 0 (votersHashMem (votersArgWord I)) (UInt256.ofNat 3) (by decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, swap1, swap2,
    raw keccak256 0 (votersBaseSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hslot (by decide) (by evm_ov) ]
  have rd337 := evm_run rd335 with [dup1]
  obtain ⟨_, _, rd338⟩ := rd337.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd342⟩ := (evm_run rd338 with [swap2, dup2, add]).sload
    (by decide) (by evm_ov)
  obtain ⟨_, _, rd348⟩ := (evm_run rd342 with [
    push1 ⟨2⟩, swap1, swap2, add ]).sload (by decide) (by evm_ov)
  have rd353 := evm_run rd348 with [push1 ⟨255⟩, dup3, and, swap2, push2 ⟨256⟩, swap1]
  have rd358 := RD.ballotDiv rd353 (by decide) (by evm_ov)
  have rd370 := evm_run rd358 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, swap1, dup5,
    jump (by jump_dest) ]
  have rd384 := evm_run rd370 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost
      (votersHashMem_mload64 (votersArgWord I)) (by decide) (by evm_ov),
    push2 ⟨194⟩, swap5, swap4, swap3, swap2, swap1, swap4, dup5]
  have rd385 := evm_run rd384 with [
    raw mstore 6 (votersReturnWeightMem (votersArgWord I) (votersWeightWord σ I)) (UInt256.ofNat 5)
      (by decide) (fun s haw hstk => ballotMstoreCost_of_stack haw hstk (by decide))
      (by rfl) (by decide) (by evm_ov)]
  have rd392 := evm_run rd385 with [
    swap2, iszero, iszero, push1 ⟨32⟩, dup5, add]
  have rd393 := evm_run rd392 with [
    raw mstore 3
      (votersReturnVotedMem (votersArgWord I) (votersWeightWord σ I) (votersBoolWord σ I))
      (UInt256.ofNat 6) (by decide)
      (fun s haw hstk => ballotMstoreCost_of_stack haw hstk (by decide))
      (by rfl) (by decide) (by evm_ov)]
  have rd405 := evm_run rd393 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, push1 ⟨64⟩, dup4, add]
  have rd406 := evm_run rd405 with [
    raw mstore 3
      (votersReturnDelegateMem (votersArgWord I) (votersWeightWord σ I) (votersBoolWord σ I)
        (votersDelegateWord σ I))
      (UInt256.ofNat 7) (by decide)
      (fun s haw hstk => ballotMstoreCost_of_stack haw hstk (by decide))
      (by
        change (UInt256.toByteArray
            (UInt256.land solcAddrMask
              (UInt256.land solcAddrMask (UInt256.div (votersPackedWord σ I) ⟨256⟩)))).write
            0 (votersReturnVotedMem (votersArgWord I) (votersWeightWord σ I) (votersBoolWord σ I))
            192 32 =
          votersReturnDelegateMem (votersArgWord I) (votersWeightWord σ I) (votersBoolWord σ I)
            (votersDelegateWord σ I)
        rw [votersDelegateWord_doubleMask]
        rfl)
      (by decide) (by evm_ov)]
  have rd411 := evm_run rd406 with [push1 ⟨96⟩, dup3, add]
  have rd412 := evm_run rd411 with [
    raw mstore 3
      (votersReturnMem (votersArgWord I) (votersWeightWord σ I) (votersBoolWord σ I)
        (votersDelegateWord σ I) (votersVoteWord σ I))
      (UInt256.ofNat 8) (by decide)
      (fun s haw hstk => ballotMstoreCost_of_stack haw hstk (by decide))
      (by rfl) (by decide) (by evm_ov)]
  have rd416 := evm_run rd412 with [push1 ⟨128⟩, add, swap1, jump (by jump_dest)]
  have rd423 := evm_run rd416 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide) mem_cost
      (votersReturnMem_mload64 (votersArgWord I) (votersWeightWord σ I) (votersBoolWord σ I)
        (votersDelegateWord σ I) (votersVoteWord σ I))
      (by decide) (by evm_ov)]
  exact evm_run rd423 with [
    dup1, swap2, sub, swap1,
    raw ret 0
      (UInt256.toByteArray (votersWeightWord σ I) ++
        UInt256.toByteArray (votersBoolWord σ I) ++
        UInt256.toByteArray (votersDelegateWord σ I) ++
        UInt256.toByteArray (votersVoteWord σ I))
      (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, votersSubRet128_toNat]
        exact votersReturnMem_read128_128 (votersArgWord I) (votersWeightWord σ I) (votersBoolWord σ I)
          (votersDelegateWord σ I) (votersVoteWord σ I))
      (by evm_ov) ]

/-! ## Dispatch/decode bridge -/

theorem ballotVotersSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0xa3, 0xec, 0x13, 0x8d]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xa3, 0xec, 0x13, 0x8d]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ballotDispatch_voters {cd : ByteArray}
    (hsel : ((⟨#[0xa3, 0xec, 0x13, 0x8d]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg ballotContract cd = some votersGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0xa3, 0xec, 0x13, 0x8d]⟩ : ByteArray) :=
    (ballotByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [voteTransition, proposalsGetter, chairpersonGetter, delegateTransition,
      winningProposalTransition, giveRightToVoteTransition])
    (post := [winnerNameTransition])
    rfl ?_ (by rw [selectorOf, ballotVotersSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, ballotVoteSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotProposalsSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotChairpersonSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotDelegateSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotWinningProposalSelectorBytes, hcd]; decide
  · rw [selectorOf, ballotGiveRightToVoteSelectorBytes, hcd]; decide

theorem ballotDecode_voters_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (votersArgWord I).toNat < EVM.addressModulus) :
    decodeCalldata (votersGetter.params.map Param.name)
      (transitionSignature votersGetter).paramTypes I.calldata = some (votersStore I) := by
  show decodeCalldata ["a"] [addr] I.calldata = some (votersStore I)
  simpa [votersStore, votersArgValue, votersArgWord, calldataWord]
    using decodeCalldata_address_ok (cd := I.calldata) (x := "a") hsz36 hbig hcanon

theorem ballotDecode_voters_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (votersGetter.params.map Param.name)
      (transitionSignature votersGetter).paramTypes I.calldata = none := by
  show decodeCalldata ["a"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_short (cd := I.calldata) (x := "a") hsz4 hshort

theorem ballotDecode_voters_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (votersArgWord I).toNat < EVM.addressModulus) :
    decodeCalldata (votersGetter.params.map Param.name)
      (transitionSignature votersGetter).paramTypes I.calldata = none := by
  show decodeCalldata ["a"] [addr] I.calldata = none
  simpa [addr, votersArgWord, calldataWord]
    using decodeCalldata_address_none_noncanon (cd := I.calldata) (x := "a") hsz36 hbig hnc

theorem ballotDecode_voters_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (votersGetter.params.map Param.name)
      (transitionSignature votersGetter).paramTypes I.calldata = none := by
  show decodeCalldata ["a"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_huge (cd := I.calldata) (x := "a") hbig

theorem ballotVotersBodyCore {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = ballotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0xa3, 0xec, 0x13, 0x8d]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD ballotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨305⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    runtimeEquivalenceFor ballotConfig ballotContract cA gh bl σ σ₀ g A I := by
  have hsz4 := ballotVotersSelector_size hsel
  have hd := ballotDispatch_voters (cd := I.calldata) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (votersArgWord I).toNat < EVM.addressModulus
      · have hdec := ballotDecode_voters_ok (I := I) hsz36 hbig hcanon
        have hbody₀ := ballotVotersBodyReturns
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv) (by simp [initState]) hcanon
        have hbody :
            ExecTransitionBody ballotConfig ballotContract
              (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (votersStore I)
              votersGetter.body
              (.returned { contract := ballotContract, locals := votersStore I }
                (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
                (some (.tuple [
                  .int (Int.ofNat (votersWeightWord σ I).toNat),
                  wordToElem .bool (votersVotedWord σ I),
                  .address (AccountAddress.ofNat (votersDelegateWord σ I).toNat),
                  .int (Int.ofNat (votersVoteWord σ I).toNat)]))) := by
          simpa [votersWeightWord, votersPackedWord, votersVoteWord, votersBaseSlot,
            votersPackedSlot, votersVoteSlot, votersVotedWord, votersDelegateWord] using hbody₀
        exact (ballotX_voters_ok (g := Sat256.ofUInt256 g) hsz36 hsize hbig hcanon hreach)
          |>.reEquivExecution hcode hd hdec hbody
            (returnEquiv_of_encode
              (ballotVotersReturnEncoding (votersWeightWord σ I) (votersPackedWord σ I)
                (votersVoteWord σ I)))
      · have hdec := ballotDecode_voters_none_noncanon (I := I) hsz36 hbig hcanon
        have hnc : UInt256.eq (votersArgWord I)
            (UInt256.land (votersArgWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanon (solcAddrCanonical_of_clean he))
        exact (ballotVotersX_decodeRevert_noncanon (g := Sat256.ofUInt256 g)
            hsz36 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := ballotDecode_voters_none_huge (I := I) hbigge
      exact (ballotVotersX_decodeRevert_huge (g := Sat256.ofUInt256 g) hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := ballotDecode_voters_none_short (I := I) hsz4 hshort
    exact (ballotVotersX_decodeRevert_short (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Ballot
