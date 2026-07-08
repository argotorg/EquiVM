import Benchmarks.Dss.Cure.Rely
import Benchmarks.Dss.Cure.Trusted

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Cure

/-! ## `drop(address)` -/

abbrev dropSrc (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 4).toNat

abbrev dropLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "src" (.address (dropSrc I))

abbrev dropKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (calldataWord I.calldata 4)

abbrev dropPosEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "pos", steps := [.mindex (.address (dropSrc I))] }

abbrev dropPosSlotFor (I : ExecutionEnv) : UInt256 :=
  posSlot (.address (dropSrc I))

abbrev dropAmtSlotFor (I : ExecutionEnv) : UInt256 :=
  amtSlot (.address (dropSrc I))

abbrev dropSrcsLastSlot (len : UInt256) : UInt256 :=
  srcElemSlot (.int (Int.ofNat len.toNat - 1))

abbrev dropAfterPopClearState (evm : EVM.State) (len : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (dropSrcsLastSlot len)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (dropSrcsLastSlot len)) ⟨0⟩)

abbrev dropAfterPopState (evm : EVM.State) (len : UInt256) : EVM.State :=
  Solm.EVM.storageStore (dropAfterPopClearState evm len)
    (dropAfterPopClearState evm len).executionEnv.codeOwner ⟨2⟩
    (UInt256.ofNat (len.toNat - 1))

abbrev dropAfterDeletePosState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (dropPosSlotFor I) ⟨0⟩

abbrev dropAfterDeleteAmtState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (dropAmtSlotFor I) ⟨0⟩

abbrev dropSrcsSlotForIndex (idx : UInt256) : UInt256 :=
  srcElemSlot (.int (Int.ofNat idx.toNat))

abbrev dropLastIndex (len : UInt256) : UInt256 :=
  UInt256.ofNat (len.toNat - 1)

abbrev dropDstIndex (pos : UInt256) : UInt256 :=
  UInt256.ofNat (pos.toNat - 1)

abbrev dropMoveWord (evm : EVM.State) (len : UInt256) : UInt256 :=
  UInt256.land
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (dropSrcsSlotForIndex (dropLastIndex len)))
    solcAddrMask

abbrev dropMoveAddr (evm : EVM.State) (len : UInt256) : AccountAddress :=
  AccountAddress.ofNat (dropMoveWord evm len).toNat

abbrev dropAfterMoveElemState (evm : EVM.State) (pos len : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (dropSrcsSlotForIndex (dropDstIndex pos))
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (dropSrcsSlotForIndex (dropDstIndex pos)))
      (dropMoveWord evm len))

abbrev dropAfterMovePosState (srcEvm evm : EVM.State) (pos len : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (solcMappingSlot ⟨5⟩ (dropMoveWord srcEvm len)) pos

abbrev dropMoveWordFor (σ : AccountMap) (I : ExecutionEnv) (len : UInt256) : UInt256 :=
  UInt256.land
    (solcSlotWord σ I (dropSrcsSlotForIndex (dropLastIndex len)))
    solcAddrMask

abbrev dropMoveElemAccountMapFor
    (σ : AccountMap) (I : ExecutionEnv) (pos len : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (dropSrcsSlotForIndex (dropDstIndex pos))
    (setAddressOffset0Word
      (solcSlotWord σ I (dropSrcsSlotForIndex (dropDstIndex pos)))
      (dropMoveWordFor σ I len))

abbrev dropMovePosAccountMapFor
    (σ : AccountMap) (I : ExecutionEnv) (pos len : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner (dropMoveElemAccountMapFor σ I pos len)
    (solcMappingSlot ⟨5⟩ (dropMoveWordFor σ I len)) pos

abbrev dropSwapPopLenState (evm : EVM.State) (pos len : UInt256) : UInt256 :=
  Solm.EVM.storageLoad
    (dropAfterMovePosState evm (dropAfterMoveElemState evm pos len) pos len)
    evm.executionEnv.codeOwner ⟨2⟩

abbrev dropSwapPopLenAccountMapFor
    (σ : AccountMap) (I : ExecutionEnv) (pos len : UInt256) : UInt256 :=
  solcSlotWord (dropMovePosAccountMapFor σ I pos len) I ⟨2⟩

theorem dropSwapPopLenState_initState_eq
    {cA gh bl σ σ₀ A I} {g pos len : UInt256} :
    dropSwapPopLenState (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) pos len =
      dropSwapPopLenAccountMapFor σ I pos len := by
  simp [dropSwapPopLenState, dropSwapPopLenAccountMapFor, dropAfterMovePosState,
    dropAfterMoveElemState, dropMovePosAccountMapFor, dropMoveElemAccountMapFor,
    dropMoveWordFor, dropMoveWord, storageStore_accountMap, storageStore_executionEnv,
    initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    solcSlotWord]

abbrev dropPopClearAccountMap (σ : AccountMap) (I : ExecutionEnv) (len : UInt256) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ (dropSrcsLastSlot len)
    (setAddressOffset0Word (solcSlotWord σ I (dropSrcsLastSlot len)) ⟨0⟩)

abbrev dropPopAccountMap (σ : AccountMap) (I : ExecutionEnv) (len : UInt256) :
    AccountMap :=
  sstoreAccountMap I.codeOwner (dropPopClearAccountMap σ I len) ⟨2⟩
    (UInt256.ofNat (len.toNat - 1))

abbrev dropDeletePosAccountMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (dropPosSlotFor I) ⟨0⟩

abbrev dropDeleteAmtAccountMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (dropAmtSlotFor I) ⟨0⟩

abbrev dropNoSwapFinalAccountMap (σ : AccountMap) (I : ExecutionEnv) (len : UInt256) :
    AccountMap :=
  dropDeleteAmtAccountMap (dropDeletePosAccountMap (dropPopAccountMap σ I len) I) I

abbrev dropDeletePosAccountMapFor (σ : AccountMap) (I : ExecutionEnv) (key : UInt256) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨5⟩ key) ⟨0⟩

abbrev dropDeleteAmtAccountMapFor (σ : AccountMap) (I : ExecutionEnv) (key : UInt256) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨6⟩ key) ⟨0⟩

abbrev dropNoSwapFinalAccountMapFor
    (σ : AccountMap) (I : ExecutionEnv) (key len : UInt256) : AccountMap :=
  dropDeleteAmtAccountMapFor
    (dropDeletePosAccountMapFor (dropPopAccountMap σ I len) I key) I key

abbrev dropSwapFinalAccountMap (σ : AccountMap) (I : ExecutionEnv) (pos len : UInt256) :
    AccountMap :=
  dropDeleteAmtAccountMap
    (dropDeletePosAccountMap
      (dropPopAccountMap (dropMovePosAccountMapFor σ I pos len) I
        (dropSwapPopLenAccountMapFor σ I pos len)) I) I

abbrev dropSwapFinalAccountMapFor
    (σ : AccountMap) (I : ExecutionEnv) (key pos len : UInt256) : AccountMap :=
  dropDeleteAmtAccountMapFor
    (dropDeletePosAccountMapFor
      (dropPopAccountMap (dropMovePosAccountMapFor σ I pos len) I
        (dropSwapPopLenAccountMapFor σ I pos len)) I key) I key

theorem dropPosSlotFor_eq (I : ExecutionEnv) :
    dropPosSlotFor I = solcMappingSlot ⟨5⟩ (dropKey I) := by
  unfold dropPosSlotFor dropSrc dropKey posSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem dropAmtSlotFor_eq (I : ExecutionEnv) :
    dropAmtSlotFor I = solcMappingSlot ⟨6⟩ (dropKey I) := by
  unfold dropAmtSlotFor dropSrc dropKey amtSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_ofNat_mask]

theorem dropWordOfInt_pred (w : UInt256) (hpos : 0 < w.toNat) :
    EVM.wordOfInt (Int.ofNat w.toNat - 1) = UInt256.ofNat (w.toNat - 1) := by
  have hleNat : 1 ≤ w.toNat := Nat.succ_le_of_lt hpos
  have hle : (1 : Int) ≤ Int.ofNat w.toNat := by
    simpa using (show (1 : Int) ≤ (w.toNat : Int) by exact_mod_cast hleNat)
  have hnonneg : 0 ≤ Int.ofNat w.toNat - 1 := sub_nonneg.mpr hle
  rw [wordOfInt_nonneg (Int.ofNat w.toNat - 1) hnonneg]
  have hto : (Int.ofNat w.toNat - 1).toNat = w.toNat - 1 := by
    have hcast :
        (((Int.ofNat w.toNat - 1).toNat : Nat) : Int) =
          ((w.toNat - 1 : Nat) : Int) := by
      rw [Int.toNat_sub_of_le hle]
      rw [Nat.cast_sub hleNat]
      simp
    exact Int.ofNat.inj hcast
  rw [hto]
  rfl

theorem dropLenAddLnotZero_eq_pred (len : UInt256) (hpos : 0 < len.toNat) :
    len + UInt256.lnot ⟨0⟩ = UInt256.ofNat (len.toNat - 1) := by
  apply u256_inj
  rw [uadd_toNat]
  have hlnot : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    native_decide
  have hmod :
      (len.toNat + (UInt256.size - 1)) % UInt256.size = len.toNat - 1 := by
    have hsizePos : 0 < UInt256.size := by native_decide
    have hsum : len.toNat + (UInt256.size - 1) =
        UInt256.size + (len.toNat - 1) := by
      omega
    rw [hsum, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by
      have hlt : len.toNat < UInt256.size := len.val.isLt
      omega)
  rw [hlnot, hmod]
  exact (ulit_toNat' (len.toNat - 1) (by
    have hlt : len.toNat < UInt256.size := len.val.isLt
    omega)).symm

theorem dropSubOne_eq_pred (w : UInt256) (hpos : 0 < w.toNat) :
    UInt256.sub w ⟨1⟩ = UInt256.ofNat (w.toNat - 1) := by
  apply u256_inj
  rw [usub_toNat (by simpa using Nat.succ_le_of_lt hpos)]
  rw [ulit_toNat' (w.toNat - 1) (by
    have hlt : w.toNat < UInt256.size := w.val.isLt
    omega)]
  rfl

theorem dropSrcsLastSlot_eq (len : UInt256) (hpos : 0 < len.toNat) :
    dropSrcsLastSlot len = srcsDataSlot + UInt256.ofNat (len.toNat - 1) := by
  unfold dropSrcsLastSlot srcElemSlot
  change srcsDataSlot + EVM.wordOfInt (Int.ofNat len.toNat - 1) =
    srcsDataSlot + UInt256.ofNat (len.toNat - 1)
  rw [dropWordOfInt_pred len hpos]

theorem dropSrcsSlotForIndex_eq_add (idx : UInt256) :
    dropSrcsSlotForIndex idx = srcsDataSlot + idx := by
  unfold dropSrcsSlotForIndex srcElemSlot
  rw [keyValueToWord_uint256]

theorem dropSrcsSlotForLastIndex_eq (len : UInt256) (hpos : 0 < len.toNat) :
    dropSrcsSlotForIndex (dropLastIndex len) = dropSrcsLastSlot len := by
  rw [dropSrcsSlotForIndex_eq_add, dropSrcsLastSlot_eq len hpos]

theorem dropWordAt32TwoWordHashMem_read0_64 {mem : ByteArray}
    (key oldSlot newSlot : UInt256) (hmem : mem.size = 96) :
    (wordAt32Mem newSlot (twoWordHashMem key oldSlot mem)).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray newSlot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by
        rw [wordAt32Mem_size_96 newSlot (twoWordHashMem_size_96 key oldSlot hmem)]
        omega)]
  have hleft :
      (wordAt32Mem newSlot (twoWordHashMem key oldSlot mem)).extract 0 32 =
        UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by
          rw [wordAt32Mem_size_96 newSlot (twoWordHashMem_size_96 key oldSlot hmem)]
          omega)]
    unfold wordAt32Mem
    rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [twoWordHashMem_size_96 key oldSlot hmem]; omega) (by omega)]
    exact twoWordHashMem_read0 key oldSlot hmem
  have hright :
      (wordAt32Mem newSlot (twoWordHashMem key oldSlot mem)).extract 32 64 =
        UInt256.toByteArray newSlot := by
    rw [← readWithPadding_eq_extract _ 32
        (by
          rw [wordAt32Mem_size_96 newSlot (twoWordHashMem_size_96 key oldSlot hmem)]
          omega)]
    unfold wordAt32Mem
    rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [twoWordHashMem_size_96 key oldSlot hmem]; omega)]
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray newSlot).size ≤ 32
      rw [toByteArray_size])
  rw [show (wordAt32Mem newSlot (twoWordHashMem key oldSlot mem)).extract 0 64 =
      (wordAt32Mem newSlot (twoWordHashMem key oldSlot mem)).extract 0 32 ++
        (wordAt32Mem newSlot (twoWordHashMem key oldSlot mem)).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem dropWordAt32TwoWordHashMem_solcMappingSlot {mem : ByteArray}
    (baseSlot key oldSlot : UInt256) (hmem : mem.size = 96) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt32Mem baseSlot (twoWordHashMem key oldSlot mem)).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [dropWordAt32TwoWordHashMem_read0_64 key oldSlot baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem dropWordAt32TwoWordHashMem_read64 {mem : ByteArray}
    (key oldSlot newSlot : UInt256) (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (wordAt32Mem newSlot (twoWordHashMem key oldSlot mem)).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [twoWordHashMem_size_96 key oldSlot hmem]; omega) (by omega)
    (by rw [twoWordHashMem_size_96 key oldSlot hmem])]
  exact twoWordHashMem_read64 key oldSlot hmem hread64

theorem dropWordAt0Mem_read64_of_size96 {mem : ByteArray}
    (word : UInt256) (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (wordAt0Mem word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega) (by rw [hmem])]
  exact hread64

theorem dropStorageLocStore_uint256_pred (evm : EVM.State) (slot len : UInt256)
    (hpos : 0 < len.toNat) :
    storageLocStore evm (wordLoc slot) (.int (Int.ofNat len.toNat - 1)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.ofNat (len.toNat - 1))) := by
  unfold storageLocStore storageLocWriteWord wordLoc
  simp only [valueToWord, dropWordOfInt_pred len hpos, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat (len.toNat - 1))).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) =
        (UInt256.ofNat (len.toNat - 1)).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

theorem dropStorageLocStore_address_offset0_zero (evm : EVM.State) (slot : UInt256) :
    storageLocStore evm (addressOffset0Loc slot) (.int 0) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨0⟩)) := by
  unfold storageLocStore storageLocWriteWord addressOffset0Loc
  have hzeroWord : EVM.wordOfInt 0 = (⟨0⟩ : UInt256) := by native_decide
  simp only [valueToWord, hzeroWord, bind, Option.bind]
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (20 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (20 : Fin 33).val) _) =
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨0⟩).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (20 : Fin 33).val = 20 from rfl,
    List.take_zero, List.nil_append]
  rw [fromBytes'_append, fromBytes'_take20_wordLE_solcAddrMask, fromBytes'_drop_wordLE]
  have hclean : (UInt256.land (⟨0⟩ : UInt256) solcAddrMask).toNat = 0 := by native_decide
  rw [hclean]
  have hlen20 : ((EVM.Word.toBytesLEWithSizeProof (⟨0⟩ : UInt256)).1.take 20).length = 20 := by
    rw [List.length_take, hvlen]
    norm_num
  rw [hlen20]
  rw [show 2 ^ (8 * 20) = 2 ^ 160 by norm_num]
  rw [show 256 ^ 20 = 2 ^ 160 by norm_num]
  rw [setAddressOffset0Word_toNat _ _ (by native_decide)]
  rw [show ({ val := 0 } : UInt256).toNat = 0 from rfl]
  ring_nf

theorem dropStorageLocLoad_addrLoc (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (addrLoc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  simpa [addrLoc, addressOffset0Loc] using storageLocLoad_address_offset0 evm slot

theorem dropEvalExpr_sub256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b)
    (hle : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (sub256 x y) =
      .ok (.int (Int.ofNat diff.toNat)) := by
  have hdiffNat : diff.toNat = a.toNat - b.toNat := by
    rw [hdiff, usub_toNat hle]
  have hsubInt : (a.toNat : Int) - (b.toNat : Int) = ((a.toNat - b.toNat : Nat) : Int) :=
    (Int.ofNat_sub hle).symm
  have hltNat : a.toNat - b.toNat < UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    omega
  have hlt : ¬ ((a.toNat - b.toNat : Nat) : Int) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hltNat))
  simp [sub256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  rw [if_neg]
  · rw [hsubInt, ← hdiffNat]
    rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_le.mpr hbad) hle
    · rw [hsubInt] at hbad
      exact hlt hbad

theorem evalExpr_dropPosStorage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dropLocals I } evm
      (.storage (posRef (.var "src"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (dropPosSlotFor I)).toNat)) := by
  rw [evalExpr_storage_scalar
    (er := dropPosEvaledRef I) (t := .int uint256Int) (loc := wordLoc (dropPosSlotFor I))]
  · exact congrArg EvalResult.ok (cureStorageLocLoad_uint256 evm (dropPosSlotFor I))
  · simp [dropLocals, posRef]
  · simp [dropPosEvaledRef, dropSrc, posRef, evalStorageRef, evalStorageRefSteps,
      evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind,
      pure, bind, dropLocals]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
      dropPosEvaledRef, dropPosSlotFor]

theorem evalExpr_dropPosGtZero_false (evm : EVM.State) (I : ExecutionEnv)
    (hpos : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (dropPosSlotFor I) = ⟨0⟩) :
    evalExpr? config
      { contract := contract
        locals := (dropLocals I).insert "pos_"
          (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (dropPosSlotFor I)).toNat)) }
      evm (.binary .gt (.var "pos_") (.intLit 0)) = .ok (.bool false) := by
  rw [hpos]
  simp [evalExpr?, evalBinaryOp?, dropLocals, EvalResult.ofOption]
  native_decide

theorem evalExpr_gt_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hgt : b.toNat < a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .gt lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hgt

theorem evalExpr_lt_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : a.toNat < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .lt lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hlt

theorem evalExpr_lt_uint256_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hle : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .lt lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact hle

theorem evalExpr_dropPosGtZero_true (evm : EVM.State) (I : ExecutionEnv)
    (hpos : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (dropPosSlotFor I) ≠ ⟨0⟩) :
    evalExpr? config
      { contract := contract
        locals := (dropLocals I).insert "pos_"
          (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (dropPosSlotFor I)).toNat)) }
      evm (.binary .gt (.var "pos_") (.intLit 0)) = .ok (.bool true) := by
  have hnat : 0 < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (dropPosSlotFor I)).toNat := by
    have hz :
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (dropPosSlotFor I)).toNat ≠ 0 := by
      intro hzero
      apply hpos
      apply u256_inj
      simpa using hzero
    omega
  exact evalExpr_gt_uint256_true
    (a := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (dropPosSlotFor I))
    (b := ⟨0⟩)
    (lhs := .var "pos_") (rhs := .intLit 0)
    (by simp [evalExpr?, dropLocals, EvalResult.ofOption])
    (by simp [evalExpr?, pure])
    (by simpa using hnat)

theorem evalExpr_dropSrcsLength (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := ((dropLocals I).insert "pos_"
        (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (dropPosSlotFor I)).toNat))) }
      evm (.arrayLength .storage srcsRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)) := by
  simp [evalExpr?, dropLocals, srcsRef, config, contract, storageDecls, storageLayout,
    solidityStorageLayout, storageLayoutRaw, readStorageArrayLength?, resolveStorageRef?,
    storageTypeAt?, evalStorageRef, evalStorageRefSteps, wordLoc, EvalResult.ofOption,
    EvalResult.bind, pure, bind]
  change
    (match storageLocLoad evm (wordLoc ⟨2⟩) with
    | Value.int n => EvalResult.ok (Value.int n)
    | _ => EvalResult.error EvalError.storageError) =
      EvalResult.ok (Value.int ↑(Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
  rw [cureStorageLocLoad_uint256]
  rfl

theorem evalExpr_dropSrcElemStorage_lastIndex (evm : EVM.State) {locals : Store}
    {idx len : UInt256}
    (hbase : locals.get? "srcs" = none)
    (hidx : locals.get? "lastIndex" = some (.int (Int.ofNat idx.toNat)))
    (hlen : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = len)
    (hidxLt : idx.toNat < len.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (srcElemRef (.var "lastIndex"))) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (dropSrcsSlotForIndex idx))
            solcAddrMask).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (er := { base := "srcs", steps := [.aindex (.int (Int.ofNat idx.toNat))] })
    (t := .address) (loc := addrLoc (dropSrcsSlotForIndex idx))]
  · exact hbase
  · have hidx' : locals["lastIndex"]? = some (.int (Int.ofNat idx.toNat)) := hidx
    have hstep :
        evalStorageRefStep config { contract := contract, locals := locals } evm
            "srcs" [] (.aindex (.var "lastIndex")) =
          .ok (.aindex (.int (Int.ofNat idx.toNat))) := by
      unfold evalStorageRefStep
      rw [show evalExpr? config { contract := contract, locals := locals } evm
          (.var "lastIndex") = .ok (.int (Int.ofNat idx.toNat)) by
        rw [evalExpr?, hidx]
        rfl]
      simp only [EvalResult.bind, bind, pure, valueToKey?, EvalResult.ofOption]
      simp [arrayIndexInBounds?, storageTypeAt?, storageTypeStep?, contract,
        storageDecls, config, storageLayout, solidityStorageLayout, storageLayoutRaw]
      rw [cureStorageLocLoad_uint256, hlen]
      simp only [EvalResult.bind, bind, pure]
      rw [if_pos (by exact Int.ofNat_lt.mpr hidxLt)]
    unfold evalStorageRef srcElemRef
    rw [show evalStorageRefSteps config { contract := contract, locals := locals } evm
        "srcs" [] [.aindex (.var "lastIndex")] =
      .ok [.aindex (.int (Int.ofNat idx.toNat))] by
        simp only [evalStorageRefSteps, hstep, EvalResult.bind, bind, pure]]
    rfl
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, addrSt]
  · funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
      dropSrcsSlotForIndex]
  · exact dropStorageLocLoad_addrLoc evm (dropSrcsSlotForIndex idx)

theorem evalExpr_dropPosLtLast_true {evm : EVM.State} {locals : Store}
    {pos last : UInt256}
    (hpos : locals.get? "pos_" = some (.int (Int.ofNat pos.toNat)))
    (hlast : locals.get? "last" = some (.int (Int.ofNat last.toNat)))
    (hlt : pos.toNat < last.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .lt (.var "pos_") (.var "last")) = .ok (.bool true) := by
  exact evalExpr_lt_uint256_true
    (a := pos) (b := last) (lhs := .var "pos_") (rhs := .var "last")
    (by rw [evalExpr?, hpos]; rfl)
    (by rw [evalExpr?, hlast]; rfl)
    hlt

theorem evalExpr_dropPosLtLast_false {evm : EVM.State} {locals : Store}
    {pos last : UInt256}
    (hpos : locals.get? "pos_" = some (.int (Int.ofNat pos.toNat)))
    (hlast : locals.get? "last" = some (.int (Int.ofNat last.toNat)))
    (hle : last.toNat ≤ pos.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .lt (.var "pos_") (.var "last")) = .ok (.bool false) := by
  exact evalExpr_lt_uint256_false
    (a := pos) (b := last) (lhs := .var "pos_") (rhs := .var "last")
    (by rw [evalExpr?, hpos]; rfl)
    (by rw [evalExpr?, hlast]; rfl)
    hle

theorem dropPopArray_ok (evm : EVM.State) (locals : Store) (len : UInt256)
    (hbase : locals["srcs"]? = none)
    (hlen : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = len)
    (hpos : 0 < len.toNat) :
    popArray? config { contract := contract, locals := locals } evm srcsRef =
      .ok (dropAfterPopState evm len) := by
  unfold popArray? resolveStorageRef? evalStorageRef evalStorageRefSteps srcsRef
    storageTypeAt? storageTypeStep? contract storageDecls config storageLayout
    solidityStorageLayout storageLayoutRaw clearStorage? dropAfterPopState
    dropAfterPopClearState dropSrcsLastSlot
  simp [hbase, EvalResult.bind, bind, pure, EvalResult.ofOption, wordLoc, addrSt]
  have hlenLoad :
      storageLocLoad evm
        { slot := (⟨2⟩ : UInt256), offset := 0, size := 32, hbound := by decide,
          type := .int uint256Int } =
        .int (Int.ofNat len.toNat) := by
    change storageLocLoad evm (wordLoc ⟨2⟩) = .int (Int.ofNat len.toNat)
    rw [cureStorageLocLoad_uint256, hlen]
  rw [hlenLoad]
  simp [Nat.ne_of_gt hpos]
  rw [show ∀ slot, addrLoc slot = addressOffset0Loc slot by intro slot; rfl]
  rw [dropStorageLocStore_address_offset0_zero]
  change
      (match storageLocStore (dropAfterPopClearState evm len) (wordLoc ⟨2⟩)
          (.int (Int.ofNat len.toNat - 1)) with
        | some a => EvalResult.ok a
        | none => EvalResult.error EvalError.storageError) =
        EvalResult.ok (dropAfterPopState evm len)
  rw [dropStorageLocStore_uint256_pred _ _ _ hpos]

theorem dropPopArray_revert_zero (evm : EVM.State) (locals : Store)
    (hbase : locals["srcs"]? = none)
    (hlen : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = ⟨0⟩) :
    popArray? config { contract := contract, locals := locals } evm srcsRef = .revert := by
  unfold popArray? resolveStorageRef? evalStorageRef evalStorageRefSteps srcsRef
    storageTypeAt? storageTypeStep? contract storageDecls config storageLayout
    solidityStorageLayout storageLayoutRaw clearStorage?
  simp [hbase, EvalResult.bind, bind, pure, EvalResult.ofOption, wordLoc, addrSt]
  have hlenLoad :
      storageLocLoad evm
        { slot := (⟨2⟩ : UInt256), offset := 0, size := 32, hbound := by decide,
          type := .int uint256Int } =
        .int 0 := by
    change storageLocLoad evm (wordLoc ⟨2⟩) = .int 0
    rw [cureStorageLocLoad_uint256, hlen]
    rfl
  rw [hlenLoad]
  simp

theorem dropAssignMoveElem_ok (evm : EVM.State) {locals : Store} (pos len : UInt256)
    (hbase : locals["srcs"]? = none)
    (hdst : locals["dstIndex"]? = some (.int (Int.ofNat (dropDstIndex pos).toNat)))
    (hlen : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = len)
    (hdstLt : (dropDstIndex pos).toNat < len.toNat) :
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (srcElemRef (.var "dstIndex"))
      (.address (dropMoveAddr evm len)) =
        .ok ({ contract := contract, locals := locals }, dropAfterMoveElemState evm pos len) := by
  have hcanonMove : (dropMoveWord evm len).toNat < EVM.addressModulus := by
    unfold dropMoveWord
    exact solcAddrMask_result_canonical
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (dropSrcsSlotForIndex (dropLastIndex len)))
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm
          (srcElemRef (.var "dstIndex")) =
        .ok { base := "srcs", steps := [.aindex (.int (Int.ofNat (dropDstIndex pos).toNat))] } := by
    have hdst' :
        Std.HashMap.get? locals "dstIndex" =
          some (.int (Int.ofNat (dropDstIndex pos).toNat)) := hdst
    have hstep :
        evalStorageRefStep config { contract := contract, locals := locals } evm
            "srcs" [] (.aindex (.var "dstIndex")) =
          .ok (.aindex (.int (Int.ofNat (dropDstIndex pos).toNat))) := by
      unfold evalStorageRefStep
      rw [show evalExpr? config { contract := contract, locals := locals } evm
          (.var "dstIndex") = .ok (.int (Int.ofNat (dropDstIndex pos).toNat)) by
        rw [evalExpr?, hdst']
        rfl]
      simp only [EvalResult.bind, bind, pure, valueToKey?, EvalResult.ofOption]
      simp [arrayIndexInBounds?, storageTypeAt?, contract, storageDecls, config,
        storageLayout, solidityStorageLayout, storageLayoutRaw]
      rw [cureStorageLocLoad_uint256, hlen]
      simp only [EvalResult.bind, bind, pure]
      rw [if_pos (by exact Int.ofNat_lt.mpr hdstLt)]
    unfold evalStorageRef srcElemRef
    rw [show evalStorageRefSteps config { contract := contract, locals := locals } evm
        "srcs" [] [.aindex (.var "dstIndex")] =
      .ok [.aindex (.int (Int.ofNat (dropDstIndex pos).toNat))] by
        simp only [evalStorageRefSteps, hstep, EvalResult.bind, bind, pure]]
    rfl
  have hstore :
      storageLocStore evm (addrLoc (dropSrcsSlotForIndex (dropDstIndex pos)))
          (.address (dropMoveAddr evm len)) =
        some (dropAfterMoveElemState evm pos len) := by
    simpa [addrLoc, dropAfterMoveElemState, dropMoveAddr] using
      storageLocStore_address_offset0 evm
        (dropSrcsSlotForIndex (dropDstIndex pos)) (dropMoveWord evm len) hcanonMove
  exact assignStorageRef_storage_scalar_value
    (ty := .elem .address) (loc := addrLoc (dropSrcsSlotForIndex (dropDstIndex pos)))
    (value := .address (dropMoveAddr evm len))
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, addrSt])
    (hloc := by
      funext evm'
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        dropSrcsSlotForIndex])
    (hscalar := by trivial)
    (hstore := hstore)

theorem dropAssignMovePos_ok (evm0 evm : EVM.State) {locals : Store} (pos len : UInt256)
    (hbase : locals["pos"]? = none)
    (hmove : locals["move"]? = some (.address (dropMoveAddr evm0 len)))
    (hpos : locals["pos_"]? = some (.int (Int.ofNat pos.toNat))) :
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (posRef (.var "move")) (.int (Int.ofNat pos.toNat)) =
        .ok ({ contract := contract, locals := locals }, dropAfterMovePosState evm0 evm pos len) := by
  have hcanonMove : (dropMoveWord evm0 len).toNat < EVM.addressModulus := by
    unfold dropMoveWord
    exact solcAddrMask_result_canonical
      (Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner
        (dropSrcsSlotForIndex (dropLastIndex len)))
  have hcleanMove :
      UInt256.land solcAddrMask (dropMoveWord evm0 len) = dropMoveWord evm0 len :=
    solcAddrMask_clean_left hcanonMove
  have hslot :
      posSlot (.address (dropMoveAddr evm0 len)) =
        solcMappingSlot ⟨5⟩ (dropMoveWord evm0 len) := by
    unfold posSlot mapSlot solcMappingSlot dropMoveAddr
    rw [keyValueToWord_address_ofNat_mask]
    rw [hcleanMove]
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm
          (posRef (.var "move")) =
        .ok { base := "pos", steps := [.mindex (.address (dropMoveAddr evm0 len))] } := by
    have hmove' :
        Std.HashMap.get? locals "move" =
          some (.address (dropMoveAddr evm0 len)) := hmove
    have hstep :
        evalStorageRefStep config { contract := contract, locals := locals } evm
            "pos" [] (.mindex (.var "move")) =
          .ok (.mindex (.address (dropMoveAddr evm0 len))) := by
      unfold evalStorageRefStep
      rw [show evalExpr? config { contract := contract, locals := locals } evm
          (.var "move") = .ok (.address (dropMoveAddr evm0 len)) by
        rw [evalExpr?, hmove']
        rfl]
      simp only [EvalResult.bind, bind, pure, valueToKey?, EvalResult.ofOption]
    unfold evalStorageRef posRef
    rw [show evalStorageRefSteps config { contract := contract, locals := locals } evm
        "pos" [] [.mindex (.var "move")] =
      .ok [.mindex (.address (dropMoveAddr evm0 len))] by
        simp only [evalStorageRefSteps, hstep, EvalResult.bind, bind, pure]]
    rfl
  have hstore :
      storageLocStore evm (wordLoc (solcMappingSlot ⟨5⟩ (dropMoveWord evm0 len)))
          (.int (Int.ofNat pos.toNat)) =
        some (dropAfterMovePosState evm0 evm pos len) := by
    simpa [dropAfterMovePosState] using
      storageLocStore_uint256 evm (solcMappingSlot ⟨5⟩ (dropMoveWord evm0 len)) pos
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int))
    (loc := wordLoc (solcMappingSlot ⟨5⟩ (dropMoveWord evm0 len)))
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm'
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, hslot])
    (hstore := hstore)

theorem dropDeletePos_ok (evm : EVM.State) (locals : Store) (I : ExecutionEnv)
    (hbase : locals["pos"]? = none)
    (hsrc : locals["src"]? = some (.address (dropSrc I))) :
    deleteStorage? config { contract := contract, locals := locals } evm (posRef (.var "src")) =
      .ok (dropAfterDeletePosState evm I) := by
  unfold deleteStorage? resolveStorageRef? evalStorageRef evalStorageRefSteps evalStorageRefStep
    posRef storageTypeAt? storageTypeStep? contract storageDecls config storageLayout
    solidityStorageLayout storageLayoutRaw clearStorage? dropAfterDeletePosState dropPosSlotFor
  simp [hbase, hsrc, evalExpr?, EvalResult.bind, bind, pure, EvalResult.ofOption, valueToKey?,
    wordLoc]
  change
    (match storageLocStore evm (wordLoc (posSlot (.address (dropSrc I)))) (.int 0) with
      | some a => EvalResult.ok a
      | none => EvalResult.error EvalError.storageError) =
      EvalResult.ok (dropAfterDeletePosState evm I)
  have hstore :
      storageLocStore evm (wordLoc (posSlot (.address (dropSrc I)))) (.int 0) =
        some (dropAfterDeletePosState evm I) := by
    simpa [wordLoc, uint256Loc, dropAfterDeletePosState, dropPosSlotFor] using
      storageLocStore_uint256 evm (posSlot (.address (dropSrc I))) ⟨0⟩
  rw [hstore]

theorem dropDeleteAmt_ok (evm : EVM.State) (locals : Store) (I : ExecutionEnv)
    (hbase : locals["amt"]? = none)
    (hsrc : locals["src"]? = some (.address (dropSrc I))) :
    deleteStorage? config { contract := contract, locals := locals } evm (amtRef (.var "src")) =
      .ok (dropAfterDeleteAmtState evm I) := by
  unfold deleteStorage? resolveStorageRef? evalStorageRef evalStorageRefSteps evalStorageRefStep
    amtRef storageTypeAt? storageTypeStep? contract storageDecls config storageLayout
    solidityStorageLayout storageLayoutRaw clearStorage? dropAfterDeleteAmtState dropAmtSlotFor
  simp [hbase, hsrc, evalExpr?, EvalResult.bind, bind, pure, EvalResult.ofOption, valueToKey?,
    wordLoc]
  change
    (match storageLocStore evm (wordLoc (amtSlot (.address (dropSrc I)))) (.int 0) with
      | some a => EvalResult.ok a
      | none => EvalResult.error EvalError.storageError) =
      EvalResult.ok (dropAfterDeleteAmtState evm I)
  have hstore :
      storageLocStore evm (wordLoc (amtSlot (.address (dropSrc I)))) (.int 0) =
        some (dropAfterDeleteAmtState evm I) := by
    simpa [wordLoc, uint256Loc, dropAfterDeleteAmtState, dropAmtSlotFor] using
      storageLocStore_uint256 evm (amtSlot (.address (dropSrc I))) ⟨0⟩
  rw [hstore]

theorem cureDropSourceBodyPosZeroRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨1⟩)
    (hpos : cureSlotWord (dropPosSlotFor I) σ I = ⟨0⟩) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (dropLocals I)
      dropTransition.body .reverted := by
  let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
  have hguardAuth := cureAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := dropLocals I) (by simp [dropLocals]) hauth
  have hguardLive := cureLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := dropLocals I) (by simp [dropLocals]) hlive
  have hposLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (dropPosSlotFor I) = ⟨0⟩ := by
    simpa [evm0, cureSlotWord] using hpos
  have hposExpr := evalExpr_dropPosStorage evm0 I
  let localsPos : Store := (dropLocals I).insert "pos_"
    (.int (Int.ofNat
      (Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (dropPosSlotFor I)).toNat))
  have hguardPos :
      evalExpr? config { contract := contract, locals := localsPos } evm0
        (.binary .gt (.var "pos_") (.intLit 0)) = .ok (.bool false) := by
    simpa [localsPos] using evalExpr_dropPosGtZero_false evm0 I hposLoad
  have hblock :
      ExecBlock config { contract := contract, locals := dropLocals I } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
          .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .letDecl "pos_" (some uint256) (.storage (posRef (.var "src"))),
          .require (.binary .gt (.var "pos_") (.intLit 0)),
          .letDecl "last" (some uint256) (.arrayLength .storage srcsRef),
          .ite
            (.binary .lt (.var "pos_") (.var "last"))
            [ .letDecl "lastIndex" (some uint256) (sub256 (.var "last") (.intLit 1)),
              .letDecl "move" (some addr) (.storage (srcElemRef (.var "lastIndex"))),
              .letDecl "dstIndex" (some uint256) (sub256 (.var "pos_") (.intLit 1)),
              .assign .storage (srcElemRef (.var "dstIndex")) (.var "move"),
              .assign .storage (posRef (.var "move")) (.var "pos_") ]
            [],
          .pop srcsRef,
          .delete (posRef (.var "src")),
          .delete (amtRef (.var "src")) ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hposExpr) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardPos)
  simpa [ExecTransitionBody, dropTransition, nonpayable, auth, live, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem cureDropSourceBodyOkNoSwap {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨1⟩)
    (hposNe : cureSlotWord (dropPosSlotFor I) σ I ≠ ⟨0⟩)
    (hlenPos : 0 < (cureSlotWord ⟨2⟩ σ I).toNat)
    (hnoSwap :
      (cureSlotWord ⟨2⟩ σ I).toNat ≤
        (cureSlotWord (dropPosSlotFor I) σ I).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let posWord := cureSlotWord (dropPosSlotFor I) σ I
    let lenWord := cureSlotWord ⟨2⟩ σ I
    let localsPos : Store := (dropLocals I).insert "pos_" (.int (Int.ofNat posWord.toNat))
    let localsLast : Store := localsPos.insert "last" (.int (Int.ofNat lenWord.toNat))
    let evmPop := dropAfterPopState evm0 lenWord
    let evmPos := dropAfterDeletePosState evmPop I
    let evmAmt := dropAfterDeleteAmtState evmPos I
    ExecTransitionBody config contract evm0 (dropLocals I) dropTransition.body
      (.returned { contract := contract, locals := localsLast } evmAmt none) := by
  intro evm0 posWord lenWord localsPos localsLast evmPop evmPos evmAmt
  have hguardAuth := cureAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := dropLocals I) (by simp [dropLocals]) hauth
  have hguardLive := cureLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := dropLocals I) (by simp [dropLocals]) hlive
  have hposLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (dropPosSlotFor I) =
        posWord := by
    simp [evm0, posWord, cureSlotWord, solcSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
  have hlenLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨2⟩ = lenWord := by
    simp [evm0, lenWord, cureSlotWord, solcSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
  have hposLoadNe :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (dropPosSlotFor I) ≠ ⟨0⟩ := by
    simpa [hposLoad] using hposNe
  have hposExpr :
      evalExpr? config { contract := contract, locals := dropLocals I } evm0
        (.storage (posRef (.var "src"))) =
          .ok (.int (Int.ofNat posWord.toNat)) := by
    simpa [hposLoad] using evalExpr_dropPosStorage evm0 I
  have hguardPos :
      evalExpr? config { contract := contract, locals := localsPos } evm0
        (.binary .gt (.var "pos_") (.intLit 0)) = .ok (.bool true) := by
    simpa [localsPos, hposLoad] using evalExpr_dropPosGtZero_true evm0 I hposLoadNe
  have hlenExpr :
      evalExpr? config { contract := contract, locals := localsPos } evm0
        (.arrayLength .storage srcsRef) =
          .ok (.int (Int.ofNat lenWord.toNat)) := by
    simpa [localsPos, hposLoad, hlenLoad] using evalExpr_dropSrcsLength evm0 I
  have hnoSwapExpr :
      evalExpr? config { contract := contract, locals := localsLast } evm0
        (.binary .lt (.var "pos_") (.var "last")) = .ok (.bool false) := by
    exact evalExpr_dropPosLtLast_false
      (pos := posWord) (last := lenWord)
      (by
        dsimp [localsLast, localsPos]
        rw [Std.HashMap.getElem?_insert]
        simp)
      (by
        exact store_get_self localsPos "last" (.int (Int.ofNat lenWord.toNat)))
      (by simpa [posWord, lenWord] using hnoSwap)
  have hpop :
      popArray? config { contract := contract, locals := localsLast } evm0 srcsRef =
        .ok evmPop := by
    simpa [evmPop, lenWord] using
      dropPopArray_ok evm0 localsLast lenWord
        (by simp [localsLast, localsPos, dropLocals])
        hlenLoad
        (by simpa [lenWord] using hlenPos)
  have hdelPos :
      deleteStorage? config { contract := contract, locals := localsLast } evmPop
        (posRef (.var "src")) = .ok evmPos := by
    simpa [evmPos] using
      dropDeletePos_ok evmPop localsLast I
        (by simp [localsLast, localsPos, dropLocals])
        (by
          dsimp [localsLast, localsPos, dropLocals]
          rw [Std.HashMap.getElem?_insert]
          simp
          rw [Std.HashMap.getElem_insert]
          simp)
  have hdelAmt :
      deleteStorage? config { contract := contract, locals := localsLast } evmPos
        (amtRef (.var "src")) = .ok evmAmt := by
    simpa [evmAmt] using
      dropDeleteAmt_ok evmPos localsLast I
        (by simp [localsLast, localsPos, dropLocals])
        (by
          dsimp [localsLast, localsPos, dropLocals]
          rw [Std.HashMap.getElem?_insert]
          simp
          rw [Std.HashMap.getElem_insert]
          simp)
  have hblock :
      ExecBlock config { contract := contract, locals := dropLocals I } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
          .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .letDecl "pos_" (some uint256) (.storage (posRef (.var "src"))),
          .require (.binary .gt (.var "pos_") (.intLit 0)),
          .letDecl "last" (some uint256) (.arrayLength .storage srcsRef),
          .ite
            (.binary .lt (.var "pos_") (.var "last"))
            [ .letDecl "lastIndex" (some uint256) (sub256 (.var "last") (.intLit 1)),
              .letDecl "move" (some addr) (.storage (srcElemRef (.var "lastIndex"))),
              .letDecl "dstIndex" (some uint256) (sub256 (.var "pos_") (.intLit 1)),
              .assign .storage (srcElemRef (.var "dstIndex")) (.var "move"),
              .assign .storage (posRef (.var "move")) (.var "pos_") ]
            [],
          .pop srcsRef,
          .delete (posRef (.var "src")),
          .delete (amtRef (.var "src")) ]
        (.ok { contract := contract, locals := localsLast } evmAmt) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hposExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardPos) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hlenExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.iteFalse hnoSwapExpr ExecBlock.nil) ?_
    refine ExecBlock.consNormal (ExecStmt.pop hpop) ?_
    refine ExecBlock.consNormal (ExecStmt.delete hdelPos) ?_
    exact ExecBlock.consNormal (ExecStmt.delete hdelAmt) ExecBlock.nil
  simpa [ExecTransitionBody, dropTransition, nonpayable, auth, live, evm0, posWord, lenWord,
    localsPos, localsLast, evmPop, evmPos, evmAmt] using
    ExecFuncBody.execBlockOK hblock

theorem cureDropSourceBodyNoSwapPopZeroRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨1⟩)
    (hposNe : cureSlotWord (dropPosSlotFor I) σ I ≠ ⟨0⟩)
    (hlenZero : cureSlotWord ⟨2⟩ σ I = ⟨0⟩)
    (hnoSwap :
      (cureSlotWord ⟨2⟩ σ I).toNat ≤
        (cureSlotWord (dropPosSlotFor I) σ I).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let posWord := cureSlotWord (dropPosSlotFor I) σ I
    let lenWord := cureSlotWord ⟨2⟩ σ I
    let localsPos : Store := (dropLocals I).insert "pos_" (.int (Int.ofNat posWord.toNat))
    let localsLast : Store := localsPos.insert "last" (.int (Int.ofNat lenWord.toNat))
    ExecTransitionBody config contract evm0 (dropLocals I) dropTransition.body .reverted := by
  intro evm0 posWord lenWord localsPos localsLast
  have hguardAuth := cureAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := dropLocals I) (by simp [dropLocals]) hauth
  have hguardLive := cureLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := dropLocals I) (by simp [dropLocals]) hlive
  have hposLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (dropPosSlotFor I) =
        posWord := by
    simp [evm0, posWord, cureSlotWord, solcSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
  have hlenLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨2⟩ = lenWord := by
    simp [evm0, lenWord, cureSlotWord, solcSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
  have hposLoadNe :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (dropPosSlotFor I) ≠ ⟨0⟩ := by
    simpa [hposLoad] using hposNe
  have hposExpr :
      evalExpr? config { contract := contract, locals := dropLocals I } evm0
        (.storage (posRef (.var "src"))) =
          .ok (.int (Int.ofNat posWord.toNat)) := by
    simpa [hposLoad] using evalExpr_dropPosStorage evm0 I
  have hguardPos :
      evalExpr? config { contract := contract, locals := localsPos } evm0
        (.binary .gt (.var "pos_") (.intLit 0)) = .ok (.bool true) := by
    simpa [localsPos, hposLoad] using evalExpr_dropPosGtZero_true evm0 I hposLoadNe
  have hlenExpr :
      evalExpr? config { contract := contract, locals := localsPos } evm0
        (.arrayLength .storage srcsRef) =
          .ok (.int (Int.ofNat lenWord.toNat)) := by
    simpa [localsPos, hposLoad, hlenLoad] using evalExpr_dropSrcsLength evm0 I
  have hnoSwapExpr :
      evalExpr? config { contract := contract, locals := localsLast } evm0
        (.binary .lt (.var "pos_") (.var "last")) = .ok (.bool false) := by
    exact evalExpr_dropPosLtLast_false
      (pos := posWord) (last := lenWord)
      (by
        dsimp [localsLast, localsPos]
        rw [Std.HashMap.getElem?_insert]
        simp)
      (by
        exact store_get_self localsPos "last" (.int (Int.ofNat lenWord.toNat)))
      (by simpa [posWord, lenWord] using hnoSwap)
  have hpop :
      popArray? config { contract := contract, locals := localsLast } evm0 srcsRef =
        .revert := by
    simpa [lenWord] using
      dropPopArray_revert_zero evm0 localsLast
        (by simp [localsLast, localsPos, dropLocals])
        (by simpa [evm0, lenWord] using hlenZero)
  have hblock :
      ExecBlock config { contract := contract, locals := dropLocals I } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
          .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .letDecl "pos_" (some uint256) (.storage (posRef (.var "src"))),
          .require (.binary .gt (.var "pos_") (.intLit 0)),
          .letDecl "last" (some uint256) (.arrayLength .storage srcsRef),
          .ite
            (.binary .lt (.var "pos_") (.var "last"))
            [ .letDecl "lastIndex" (some uint256) (sub256 (.var "last") (.intLit 1)),
              .letDecl "move" (some addr) (.storage (srcElemRef (.var "lastIndex"))),
              .letDecl "dstIndex" (some uint256) (sub256 (.var "pos_") (.intLit 1)),
              .assign .storage (srcElemRef (.var "dstIndex")) (.var "move"),
              .assign .storage (posRef (.var "move")) (.var "pos_") ]
            [],
          .pop srcsRef,
          .delete (posRef (.var "src")),
          .delete (amtRef (.var "src")) ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hposExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardPos) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hlenExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.iteFalse hnoSwapExpr ExecBlock.nil) ?_
    exact ExecBlock.consRevert (ExecStmt.popRevert hpop)
  simpa [ExecTransitionBody, dropTransition, nonpayable, auth, live, evm0, posWord, lenWord,
    localsPos, localsLast] using
    ExecFuncBody.execBlockRevert hblock

theorem cureDropSourceBodyOkSwap {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨1⟩)
    (hposNe : cureSlotWord (dropPosSlotFor I) σ I ≠ ⟨0⟩)
    (hlenPos : 0 < (cureSlotWord ⟨2⟩ σ I).toNat)
    (hswap :
      (cureSlotWord (dropPosSlotFor I) σ I).toNat <
        (cureSlotWord ⟨2⟩ σ I).toNat)
    (hpopLenPos :
      0 <
        (dropSwapPopLenState
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
          (cureSlotWord (dropPosSlotFor I) σ I)
          (cureSlotWord ⟨2⟩ σ I)).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let posWord := cureSlotWord (dropPosSlotFor I) σ I
    let lenWord := cureSlotWord ⟨2⟩ σ I
    let lastIndex := dropLastIndex lenWord
    let dstIndex := dropDstIndex posWord
    let localsPos : Store := (dropLocals I).insert "pos_" (.int (Int.ofNat posWord.toNat))
    let localsLast : Store := localsPos.insert "last" (.int (Int.ofNat lenWord.toNat))
    let localsLastIndex : Store :=
      localsLast.insert "lastIndex" (.int (Int.ofNat lastIndex.toNat))
    let localsMove : Store :=
      localsLastIndex.insert "move" (.address (dropMoveAddr evm0 lenWord))
    let localsDst : Store :=
      localsMove.insert "dstIndex" (.int (Int.ofNat dstIndex.toNat))
    let evmMoveElem := dropAfterMoveElemState evm0 posWord lenWord
    let evmMovePos := dropAfterMovePosState evm0 evmMoveElem posWord lenWord
    let popLen := dropSwapPopLenState evm0 posWord lenWord
    let evmPop := dropAfterPopState evmMovePos popLen
    let evmPos := dropAfterDeletePosState evmPop I
    let evmAmt := dropAfterDeleteAmtState evmPos I
    ExecTransitionBody config contract evm0 (dropLocals I) dropTransition.body
      (.returned { contract := contract, locals := localsDst } evmAmt none) := by
  intro evm0 posWord lenWord lastIndex dstIndex localsPos localsLast localsLastIndex
    localsMove localsDst evmMoveElem evmMovePos popLen evmPop evmPos evmAmt
  have hposNat : 0 < posWord.toNat := by
    by_contra hnot
    have hz : posWord.toNat = 0 := by omega
    have hzero : posWord = ⟨0⟩ := by
      rw [← u256_ofNat_toNat posWord, hz]
      rfl
    exact hposNe (by simpa [posWord] using hzero)
  have hlenPos' : 0 < lenWord.toNat := by
    simpa [lenWord] using hlenPos
  have hswap' : posWord.toNat < lenWord.toNat := by
    simpa [posWord, lenWord] using hswap
  have hguardAuth := cureAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := dropLocals I) (by simp [dropLocals]) hauth
  have hguardLive := cureLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := dropLocals I) (by simp [dropLocals]) hlive
  have hposLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (dropPosSlotFor I) =
        posWord := by
    simp [evm0, posWord, cureSlotWord, solcSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
  have hlenLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨2⟩ = lenWord := by
    simp [evm0, lenWord, cureSlotWord, solcSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
  have hposLoadNe :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (dropPosSlotFor I) ≠ ⟨0⟩ := by
    simpa [hposLoad] using hposNe
  have hlastIndexSub : lastIndex = UInt256.sub lenWord ⟨1⟩ := by
    simpa [lastIndex, dropLastIndex] using (dropSubOne_eq_pred lenWord hlenPos).symm
  have hdstIndexSub : dstIndex = UInt256.sub posWord ⟨1⟩ := by
    simpa [dstIndex, dropDstIndex] using (dropSubOne_eq_pred posWord hposNat).symm
  have hlastIdxLt : lastIndex.toNat < lenWord.toNat := by
    dsimp [lastIndex, dropLastIndex]
    rw [ulit_toNat' (lenWord.toNat - 1) (by
      have hlt : lenWord.toNat < UInt256.size := lenWord.val.isLt
      omega)]
    omega
  have hdstIdxLt : dstIndex.toNat < lenWord.toNat := by
    dsimp [dstIndex, dropDstIndex]
    rw [ulit_toNat' (posWord.toNat - 1) (by
      have hlt : posWord.toNat < UInt256.size := posWord.val.isLt
      omega)]
    omega
  have hposExpr :
      evalExpr? config { contract := contract, locals := dropLocals I } evm0
        (.storage (posRef (.var "src"))) =
          .ok (.int (Int.ofNat posWord.toNat)) := by
    simpa [hposLoad] using evalExpr_dropPosStorage evm0 I
  have hguardPos :
      evalExpr? config { contract := contract, locals := localsPos } evm0
        (.binary .gt (.var "pos_") (.intLit 0)) = .ok (.bool true) := by
    simpa [localsPos, hposLoad] using evalExpr_dropPosGtZero_true evm0 I hposLoadNe
  have hlenExpr :
      evalExpr? config { contract := contract, locals := localsPos } evm0
        (.arrayLength .storage srcsRef) =
          .ok (.int (Int.ofNat lenWord.toNat)) := by
    simpa [localsPos, hposLoad, hlenLoad] using evalExpr_dropSrcsLength evm0 I
  have hswapExpr :
      evalExpr? config { contract := contract, locals := localsLast } evm0
        (.binary .lt (.var "pos_") (.var "last")) = .ok (.bool true) := by
    exact evalExpr_dropPosLtLast_true
      (pos := posWord) (last := lenWord)
      (by
        dsimp [localsLast, localsPos]
        rw [Std.HashMap.getElem?_insert]
        simp)
      (by exact store_get_self localsPos "last" (.int (Int.ofNat lenWord.toNat)))
      (by simpa [posWord, lenWord] using hswap)
  have honeToNat : (⟨1⟩ : UInt256).toNat = 1 := by native_decide
  have hlastIndexExpr :
      evalExpr? config { contract := contract, locals := localsLast } evm0
        (sub256 (.var "last") (.intLit 1)) =
          .ok (.int (Int.ofNat lastIndex.toNat)) := by
    exact dropEvalExpr_sub256_ok
      (a := lenWord) (b := ⟨1⟩) (diff := lastIndex)
      (by
        rw [evalExpr?, store_get_self localsPos "last" (.int (Int.ofNat lenWord.toNat))]
        rfl)
      (by
        rw [evalExpr?]
        change pure (Value.int 1) =
          EvalResult.ok (Value.int (Int.ofNat (⟨1⟩ : UInt256).toNat))
        rw [honeToNat]
        rfl)
      hlastIndexSub
      (by simpa using Nat.succ_le_of_lt hlenPos)
  have hmoveExpr :
      evalExpr? config { contract := contract, locals := localsLastIndex } evm0
        (.storage (srcElemRef (.var "lastIndex"))) =
          .ok (.address (dropMoveAddr evm0 lenWord)) := by
    simpa [lastIndex, dropMoveAddr, dropMoveWord] using
      evalExpr_dropSrcElemStorage_lastIndex (evm := evm0) (idx := lastIndex)
        (hlen := hlenLoad)
        (hbase := by simp [localsLastIndex, localsLast, localsPos, dropLocals])
        (hidx := by
          change (localsLast.insert "lastIndex" (.int (Int.ofNat lastIndex.toNat)))["lastIndex"]? =
            some (.int (Int.ofNat lastIndex.toNat))
          exact store_get_self localsLast "lastIndex" (.int (Int.ofNat lastIndex.toNat)))
        (hidxLt := hlastIdxLt)
  have hdstIndexExpr :
      evalExpr? config { contract := contract, locals := localsMove } evm0
        (sub256 (.var "pos_") (.intLit 1)) =
          .ok (.int (Int.ofNat dstIndex.toNat)) := by
    exact dropEvalExpr_sub256_ok
      (a := posWord) (b := ⟨1⟩) (diff := dstIndex)
      (by
        simp [evalExpr?, localsMove, localsLastIndex, localsLast, localsPos, dropLocals,
          EvalResult.ofOption, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert,
          Std.HashMap.get?_eq_getElem?])
      (by
        rw [evalExpr?]
        change pure (Value.int 1) =
          EvalResult.ok (Value.int (Int.ofNat (⟨1⟩ : UInt256).toNat))
        rw [honeToNat]
        rfl)
      hdstIndexSub
      (by simpa using Nat.succ_le_of_lt hposNat)
  have hassignMoveElem :
      assignStorageRef? config { contract := contract, locals := localsDst } evm0 .storage
        (srcElemRef (.var "dstIndex")) (.address (dropMoveAddr evm0 lenWord)) =
          .ok ({ contract := contract, locals := localsDst }, evmMoveElem) := by
    simpa [evmMoveElem, dstIndex] using
      dropAssignMoveElem_ok evm0 (locals := localsDst) posWord lenWord
        (by simp [localsDst, localsMove, localsLastIndex, localsLast, localsPos, dropLocals])
        (by
          change (localsMove.insert "dstIndex" (.int (Int.ofNat dstIndex.toNat)))["dstIndex"]? =
            some (.int (Int.ofNat dstIndex.toNat))
          exact store_get_self localsMove "dstIndex" (.int (Int.ofNat dstIndex.toNat)))
        hlenLoad
        (by simpa [dstIndex] using hdstIdxLt)
  have hmoveVar :
      evalExpr? config { contract := contract, locals := localsDst } evm0 (.var "move") =
        .ok (.address (dropMoveAddr evm0 lenWord)) := by
    simp [evalExpr?, localsDst, localsMove, EvalResult.ofOption,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, Std.HashMap.get?_eq_getElem?]
  have hposVar :
      evalExpr? config { contract := contract, locals := localsDst } evmMoveElem (.var "pos_") =
        .ok (.int (Int.ofNat posWord.toNat)) := by
    simp [evalExpr?, localsDst, localsMove, localsLastIndex, localsLast, localsPos,
      dropLocals, EvalResult.ofOption, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem_insert, Std.HashMap.get?_eq_getElem?]
  have hassignMovePos :
      assignStorageRef? config { contract := contract, locals := localsDst } evmMoveElem .storage
        (posRef (.var "move")) (.int (Int.ofNat posWord.toNat)) =
          .ok ({ contract := contract, locals := localsDst }, evmMovePos) := by
    simpa [evmMovePos] using
      dropAssignMovePos_ok evm0 evmMoveElem (locals := localsDst) posWord lenWord
        (by simp [localsDst, localsMove, localsLastIndex, localsLast, localsPos, dropLocals])
        (by
          simp [localsDst, localsMove, Std.HashMap.getElem?_insert,
            Std.HashMap.getElem_insert, Std.HashMap.get?_eq_getElem?])
        (by
          simp [localsDst, localsMove, localsLastIndex, localsLast, localsPos, dropLocals,
            Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert,
            Std.HashMap.get?_eq_getElem?])
  have hpopLenLoad :
      Solm.EVM.storageLoad evmMovePos evmMovePos.executionEnv.codeOwner ⟨2⟩ = popLen := by
    simp [popLen, evmMovePos, evmMoveElem, dropSwapPopLenState, dropAfterMovePosState,
      storageStore_executionEnv]
  have hpopLenPos' : 0 < popLen.toNat := by
    simpa [popLen, evm0, posWord, lenWord] using hpopLenPos
  have hpop :
      popArray? config { contract := contract, locals := localsDst } evmMovePos srcsRef =
        .ok evmPop := by
    simpa [evmPop] using
      dropPopArray_ok evmMovePos localsDst popLen
        (by simp [localsDst, localsMove, localsLastIndex, localsLast, localsPos, dropLocals])
        hpopLenLoad
        hpopLenPos'
  have hdelPos :
      deleteStorage? config { contract := contract, locals := localsDst } evmPop
        (posRef (.var "src")) = .ok evmPos := by
    simpa [evmPos] using
      dropDeletePos_ok evmPop localsDst I
        (by simp [localsDst, localsMove, localsLastIndex, localsLast, localsPos, dropLocals])
        (by
          simp [localsDst, localsMove, localsLastIndex, localsLast, localsPos, dropLocals,
            Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert,
            Std.HashMap.get?_eq_getElem?])
  have hdelAmt :
      deleteStorage? config { contract := contract, locals := localsDst } evmPos
        (amtRef (.var "src")) = .ok evmAmt := by
    simpa [evmAmt] using
      dropDeleteAmt_ok evmPos localsDst I
        (by simp [localsDst, localsMove, localsLastIndex, localsLast, localsPos, dropLocals])
        (by
          simp [localsDst, localsMove, localsLastIndex, localsLast, localsPos, dropLocals,
            Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert,
            Std.HashMap.get?_eq_getElem?])
  have hswapBlock :
      ExecBlock config { contract := contract, locals := localsLast } evm0
        [ .letDecl "lastIndex" (some uint256) (sub256 (.var "last") (.intLit 1)),
          .letDecl "move" (some addr) (.storage (srcElemRef (.var "lastIndex"))),
          .letDecl "dstIndex" (some uint256) (sub256 (.var "pos_") (.intLit 1)),
          .assign .storage (srcElemRef (.var "dstIndex")) (.var "move"),
          .assign .storage (posRef (.var "move")) (.var "pos_") ]
        (.ok { contract := contract, locals := localsDst } evmMovePos) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hlastIndexExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hmoveExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hdstIndexExpr) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (by simpa [localsLastIndex, localsMove, localsDst] using hmoveVar)
        (by simpa [localsLastIndex, localsMove, localsDst] using hassignMoveElem)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (by simpa [localsLastIndex, localsMove, localsDst] using hposVar)
        (by simpa [localsLastIndex, localsMove, localsDst] using hassignMovePos)) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := dropLocals I } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
          .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .letDecl "pos_" (some uint256) (.storage (posRef (.var "src"))),
          .require (.binary .gt (.var "pos_") (.intLit 0)),
          .letDecl "last" (some uint256) (.arrayLength .storage srcsRef),
          .ite
            (.binary .lt (.var "pos_") (.var "last"))
            [ .letDecl "lastIndex" (some uint256) (sub256 (.var "last") (.intLit 1)),
              .letDecl "move" (some addr) (.storage (srcElemRef (.var "lastIndex"))),
              .letDecl "dstIndex" (some uint256) (sub256 (.var "pos_") (.intLit 1)),
              .assign .storage (srcElemRef (.var "dstIndex")) (.var "move"),
              .assign .storage (posRef (.var "move")) (.var "pos_") ]
            [],
          .pop srcsRef,
          .delete (posRef (.var "src")),
          .delete (amtRef (.var "src")) ]
        (.ok { contract := contract, locals := localsDst } evmAmt) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hposExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardPos) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hlenExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.iteTrue hswapExpr hswapBlock) ?_
    refine ExecBlock.consNormal (ExecStmt.pop hpop) ?_
    refine ExecBlock.consNormal (ExecStmt.delete hdelPos) ?_
    exact ExecBlock.consNormal (ExecStmt.delete hdelAmt) ExecBlock.nil
  simpa [ExecTransitionBody, dropTransition, nonpayable, auth, live, evm0, posWord, lenWord,
    lastIndex, dstIndex, localsPos, localsLast, localsLastIndex, localsMove, localsDst,
    evmMoveElem, evmMovePos, evmPop, evmPos, evmAmt] using
    ExecFuncBody.execBlockOK hblock

theorem cureDropSourceBodySwapPopZeroRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : cureSlotWord (cureCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : cureSlotWord ⟨1⟩ σ I = ⟨1⟩)
    (hposNe : cureSlotWord (dropPosSlotFor I) σ I ≠ ⟨0⟩)
    (hlenPos : 0 < (cureSlotWord ⟨2⟩ σ I).toNat)
    (hswap :
      (cureSlotWord (dropPosSlotFor I) σ I).toNat <
        (cureSlotWord ⟨2⟩ σ I).toNat)
    (hpopLenZero :
      dropSwapPopLenState
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (cureSlotWord (dropPosSlotFor I) σ I)
        (cureSlotWord ⟨2⟩ σ I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let posWord := cureSlotWord (dropPosSlotFor I) σ I
    let lenWord := cureSlotWord ⟨2⟩ σ I
    let lastIndex := dropLastIndex lenWord
    let dstIndex := dropDstIndex posWord
    let localsPos : Store := (dropLocals I).insert "pos_" (.int (Int.ofNat posWord.toNat))
    let localsLast : Store := localsPos.insert "last" (.int (Int.ofNat lenWord.toNat))
    let localsLastIndex : Store :=
      localsLast.insert "lastIndex" (.int (Int.ofNat lastIndex.toNat))
    let localsMove : Store :=
      localsLastIndex.insert "move" (.address (dropMoveAddr evm0 lenWord))
    let localsDst : Store :=
      localsMove.insert "dstIndex" (.int (Int.ofNat dstIndex.toNat))
    let evmMoveElem := dropAfterMoveElemState evm0 posWord lenWord
    let evmMovePos := dropAfterMovePosState evm0 evmMoveElem posWord lenWord
    ExecTransitionBody config contract evm0 (dropLocals I) dropTransition.body .reverted := by
  intro evm0 posWord lenWord lastIndex dstIndex localsPos localsLast localsLastIndex
    localsMove localsDst evmMoveElem evmMovePos
  have hposNat : 0 < posWord.toNat := by
    by_contra hnot
    have hz : posWord.toNat = 0 := by omega
    have hzero : posWord = ⟨0⟩ := by
      rw [← u256_ofNat_toNat posWord, hz]
      rfl
    exact hposNe (by simpa [posWord] using hzero)
  have hlenPos' : 0 < lenWord.toNat := by
    simpa [lenWord] using hlenPos
  have hswap' : posWord.toNat < lenWord.toNat := by
    simpa [posWord, lenWord] using hswap
  have hguardAuth := cureAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := dropLocals I) (by simp [dropLocals]) hauth
  have hguardLive := cureLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := dropLocals I) (by simp [dropLocals]) hlive
  have hposLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (dropPosSlotFor I) =
        posWord := by
    simp [evm0, posWord, cureSlotWord, solcSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
  have hlenLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner ⟨2⟩ = lenWord := by
    simp [evm0, lenWord, cureSlotWord, solcSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
  have hposLoadNe :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (dropPosSlotFor I) ≠ ⟨0⟩ := by
    simpa [hposLoad] using hposNe
  have hlastIndexSub : lastIndex = UInt256.sub lenWord ⟨1⟩ := by
    simpa [lastIndex, dropLastIndex] using (dropSubOne_eq_pred lenWord hlenPos).symm
  have hdstIndexSub : dstIndex = UInt256.sub posWord ⟨1⟩ := by
    simpa [dstIndex, dropDstIndex] using (dropSubOne_eq_pred posWord hposNat).symm
  have hlastIdxLt : lastIndex.toNat < lenWord.toNat := by
    dsimp [lastIndex, dropLastIndex]
    rw [ulit_toNat' (lenWord.toNat - 1) (by
      have hlt : lenWord.toNat < UInt256.size := lenWord.val.isLt
      omega)]
    omega
  have hdstIdxLt : dstIndex.toNat < lenWord.toNat := by
    dsimp [dstIndex, dropDstIndex]
    rw [ulit_toNat' (posWord.toNat - 1) (by
      have hlt : posWord.toNat < UInt256.size := posWord.val.isLt
      omega)]
    omega
  have hposExpr :
      evalExpr? config { contract := contract, locals := dropLocals I } evm0
        (.storage (posRef (.var "src"))) =
          .ok (.int (Int.ofNat posWord.toNat)) := by
    simpa [hposLoad] using evalExpr_dropPosStorage evm0 I
  have hguardPos :
      evalExpr? config { contract := contract, locals := localsPos } evm0
        (.binary .gt (.var "pos_") (.intLit 0)) = .ok (.bool true) := by
    simpa [localsPos, hposLoad] using evalExpr_dropPosGtZero_true evm0 I hposLoadNe
  have hlenExpr :
      evalExpr? config { contract := contract, locals := localsPos } evm0
        (.arrayLength .storage srcsRef) =
          .ok (.int (Int.ofNat lenWord.toNat)) := by
    simpa [localsPos, hposLoad, hlenLoad] using evalExpr_dropSrcsLength evm0 I
  have hswapExpr :
      evalExpr? config { contract := contract, locals := localsLast } evm0
        (.binary .lt (.var "pos_") (.var "last")) = .ok (.bool true) := by
    exact evalExpr_dropPosLtLast_true
      (pos := posWord) (last := lenWord)
      (by
        dsimp [localsLast, localsPos]
        rw [Std.HashMap.getElem?_insert]
        simp)
      (by exact store_get_self localsPos "last" (.int (Int.ofNat lenWord.toNat)))
      (by simpa [posWord, lenWord] using hswap)
  have honeToNat : (⟨1⟩ : UInt256).toNat = 1 := by native_decide
  have hlastIndexExpr :
      evalExpr? config { contract := contract, locals := localsLast } evm0
        (sub256 (.var "last") (.intLit 1)) =
          .ok (.int (Int.ofNat lastIndex.toNat)) := by
    exact dropEvalExpr_sub256_ok
      (a := lenWord) (b := ⟨1⟩) (diff := lastIndex)
      (by
        rw [evalExpr?, store_get_self localsPos "last" (.int (Int.ofNat lenWord.toNat))]
        rfl)
      (by
        rw [evalExpr?]
        change pure (Value.int 1) =
          EvalResult.ok (Value.int (Int.ofNat (⟨1⟩ : UInt256).toNat))
        rw [honeToNat]
        rfl)
      hlastIndexSub
      (by simpa using Nat.succ_le_of_lt hlenPos)
  have hmoveExpr :
      evalExpr? config { contract := contract, locals := localsLastIndex } evm0
        (.storage (srcElemRef (.var "lastIndex"))) =
          .ok (.address (dropMoveAddr evm0 lenWord)) := by
    simpa [lastIndex, dropMoveAddr, dropMoveWord] using
      evalExpr_dropSrcElemStorage_lastIndex (evm := evm0) (idx := lastIndex)
        (hlen := hlenLoad)
        (hbase := by simp [localsLastIndex, localsLast, localsPos, dropLocals])
        (hidx := by
          change (localsLast.insert "lastIndex" (.int (Int.ofNat lastIndex.toNat)))["lastIndex"]? =
            some (.int (Int.ofNat lastIndex.toNat))
          exact store_get_self localsLast "lastIndex" (.int (Int.ofNat lastIndex.toNat)))
        (hidxLt := hlastIdxLt)
  have hdstIndexExpr :
      evalExpr? config { contract := contract, locals := localsMove } evm0
        (sub256 (.var "pos_") (.intLit 1)) =
          .ok (.int (Int.ofNat dstIndex.toNat)) := by
    exact dropEvalExpr_sub256_ok
      (a := posWord) (b := ⟨1⟩) (diff := dstIndex)
      (by
        simp [evalExpr?, localsMove, localsLastIndex, localsLast, localsPos, dropLocals,
          EvalResult.ofOption, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert,
          Std.HashMap.get?_eq_getElem?])
      (by
        rw [evalExpr?]
        change pure (Value.int 1) =
          EvalResult.ok (Value.int (Int.ofNat (⟨1⟩ : UInt256).toNat))
        rw [honeToNat]
        rfl)
      hdstIndexSub
      (by simpa using Nat.succ_le_of_lt hposNat)
  have hassignMoveElem :
      assignStorageRef? config { contract := contract, locals := localsDst } evm0 .storage
        (srcElemRef (.var "dstIndex")) (.address (dropMoveAddr evm0 lenWord)) =
          .ok ({ contract := contract, locals := localsDst }, evmMoveElem) := by
    simpa [evmMoveElem, dstIndex] using
      dropAssignMoveElem_ok evm0 (locals := localsDst) posWord lenWord
        (by simp [localsDst, localsMove, localsLastIndex, localsLast, localsPos, dropLocals])
        (by
          change (localsMove.insert "dstIndex" (.int (Int.ofNat dstIndex.toNat)))["dstIndex"]? =
            some (.int (Int.ofNat dstIndex.toNat))
          exact store_get_self localsMove "dstIndex" (.int (Int.ofNat dstIndex.toNat)))
        hlenLoad
        (by simpa [dstIndex] using hdstIdxLt)
  have hmoveVar :
      evalExpr? config { contract := contract, locals := localsDst } evm0 (.var "move") =
        .ok (.address (dropMoveAddr evm0 lenWord)) := by
    simp [evalExpr?, localsDst, localsMove, EvalResult.ofOption,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, Std.HashMap.get?_eq_getElem?]
  have hposVar :
      evalExpr? config { contract := contract, locals := localsDst } evmMoveElem (.var "pos_") =
        .ok (.int (Int.ofNat posWord.toNat)) := by
    simp [evalExpr?, localsDst, localsMove, localsLastIndex, localsLast, localsPos,
      dropLocals, EvalResult.ofOption, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem_insert, Std.HashMap.get?_eq_getElem?]
  have hassignMovePos :
      assignStorageRef? config { contract := contract, locals := localsDst } evmMoveElem .storage
        (posRef (.var "move")) (.int (Int.ofNat posWord.toNat)) =
          .ok ({ contract := contract, locals := localsDst }, evmMovePos) := by
    simpa [evmMovePos] using
      dropAssignMovePos_ok evm0 evmMoveElem (locals := localsDst) posWord lenWord
        (by simp [localsDst, localsMove, localsLastIndex, localsLast, localsPos, dropLocals])
        (by
          simp [localsDst, localsMove, Std.HashMap.getElem?_insert,
            Std.HashMap.getElem_insert, Std.HashMap.get?_eq_getElem?])
        (by
          simp [localsDst, localsMove, localsLastIndex, localsLast, localsPos, dropLocals,
            Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert,
            Std.HashMap.get?_eq_getElem?])
  have hpopLenLoad :
      Solm.EVM.storageLoad evmMovePos evmMovePos.executionEnv.codeOwner ⟨2⟩ = ⟨0⟩ := by
    have hload :
        Solm.EVM.storageLoad evmMovePos evmMovePos.executionEnv.codeOwner ⟨2⟩ =
          dropSwapPopLenState evm0 posWord lenWord := by
      simp [evmMovePos, evmMoveElem, dropSwapPopLenState, dropAfterMovePosState,
        storageStore_executionEnv]
    rw [hload]
    simpa [evm0, posWord, lenWord] using hpopLenZero
  have hpop :
      popArray? config { contract := contract, locals := localsDst } evmMovePos srcsRef =
        .revert := by
    simpa using
      dropPopArray_revert_zero evmMovePos localsDst
        (by simp [localsDst, localsMove, localsLastIndex, localsLast, localsPos, dropLocals])
        hpopLenLoad
  have hswapBlock :
      ExecBlock config { contract := contract, locals := localsLast } evm0
        [ .letDecl "lastIndex" (some uint256) (sub256 (.var "last") (.intLit 1)),
          .letDecl "move" (some addr) (.storage (srcElemRef (.var "lastIndex"))),
          .letDecl "dstIndex" (some uint256) (sub256 (.var "pos_") (.intLit 1)),
          .assign .storage (srcElemRef (.var "dstIndex")) (.var "move"),
          .assign .storage (posRef (.var "move")) (.var "pos_") ]
        (.ok { contract := contract, locals := localsDst } evmMovePos) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hlastIndexExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hmoveExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hdstIndexExpr) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (by simpa [localsLastIndex, localsMove, localsDst] using hmoveVar)
        (by simpa [localsLastIndex, localsMove, localsDst] using hassignMoveElem)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (by simpa [localsLastIndex, localsMove, localsDst] using hposVar)
        (by simpa [localsLastIndex, localsMove, localsDst] using hassignMovePos)) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := dropLocals I } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)),
          .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .letDecl "pos_" (some uint256) (.storage (posRef (.var "src"))),
          .require (.binary .gt (.var "pos_") (.intLit 0)),
          .letDecl "last" (some uint256) (.arrayLength .storage srcsRef),
          .ite
            (.binary .lt (.var "pos_") (.var "last"))
            [ .letDecl "lastIndex" (some uint256) (sub256 (.var "last") (.intLit 1)),
              .letDecl "move" (some addr) (.storage (srcElemRef (.var "lastIndex"))),
              .letDecl "dstIndex" (some uint256) (sub256 (.var "pos_") (.intLit 1)),
              .assign .storage (srcElemRef (.var "dstIndex")) (.var "move"),
              .assign .storage (posRef (.var "move")) (.var "pos_") ]
            [],
          .pop srcsRef,
          .delete (posRef (.var "src")),
          .delete (amtRef (.var "src")) ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hposExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardPos) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hlenExpr) ?_
    refine ExecBlock.consNormal (ExecStmt.iteTrue hswapExpr hswapBlock) ?_
    exact ExecBlock.consRevert (ExecStmt.popRevert hpop)
  simpa [ExecTransitionBody, dropTransition, nonpayable, auth, live, evm0, posWord, lenWord,
    lastIndex, dstIndex, localsPos, localsLast, localsLastIndex, localsMove, localsDst,
    evmMoveElem, evmMovePos] using
    ExecFuncBody.execBlockRevert hblock


end Benchmarks.Dss.Cure
