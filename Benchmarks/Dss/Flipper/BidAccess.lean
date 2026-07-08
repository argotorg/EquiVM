import Benchmarks.Dss.Flipper.BidStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## Generic accessors for `bids[id]` fields -/

private theorem accountAddress_of_word_val (a : AccountAddress) :
    AccountAddress.ofNat (EVM.word a.val).toNat = a := by
  have hword : (EVM.word a.val).toNat = a.val := by
    unfold EVM.word EVM.uintN UInt256.toNat
    change a.val % UInt256.size = a.val
    exact Nat.mod_eq_of_lt (lt_trans a.isLt (by
      norm_num [AccountAddress.size, UInt256.size]))
  rw [hword]
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [Fin.val_ofNat]
  exact Nat.mod_eq_of_lt a.isLt

private theorem word_val_addr_canonical (a : AccountAddress) :
    (EVM.word a.val).toNat < EVM.addressModulus := by
  unfold EVM.word EVM.uintN UInt256.toNat EVM.twoPow
  change (a.val % UInt256.size) < EVM.addressModulus
  have hlt : a.val < EVM.addressModulus := by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using a.isLt
  rw [Nat.mod_eq_of_lt (lt_trans hlt (by norm_num [EVM.addressModulus, EVM.twoPow,
    UInt256.size]))]
  exact hlt

abbrev bidEvaledRefOfWord (id : UInt256) (field : Ident) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (.int (Int.ofNat id.toNat)), .field field] }

abbrev bidSlotOfWord (id : UInt256) (offset : UInt256) : UInt256 :=
  bidBaseOfWord id + offset

abbrev bidBidWord (id : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperSlotWord (bidBaseOfWord id) σ I

abbrev bidLotWord (id : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperSlotWord (bidSlotOfWord id ⟨1⟩) σ I

abbrev bidPackedWord (id : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperSlotWord (bidPackedSlotOfWord id) σ I

abbrev bidGuyWord (id : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperAddressReturnWord (bidPackedSlotOfWord id) σ I

abbrev bidTicWord (id : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperUint48Offset20Word (bidPackedSlotOfWord id) σ I

abbrev bidEndWord (id : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperUint48Offset26Word (bidPackedSlotOfWord id) σ I

abbrev bidUsrWord (id : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperAddressReturnWord (bidSlotOfWord id ⟨3⟩) σ I

abbrev bidGalWord (id : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperAddressReturnWord (bidSlotOfWord id ⟨4⟩) σ I

abbrev bidTabWord (id : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperSlotWord (bidSlotOfWord id ⟨5⟩) σ I

theorem bidBase_eq_bidsBase (id : UInt256) :
    bidsBase (.int (Int.ofNat id.toNat)) = bidBaseOfWord id := by
  simpa [bidBaseOfWord] using bidsBase_intOfNatWord id

theorem evalStorageRef_bidField_of_get_id {evm : EVM.State} {locals : Store}
    {id : UInt256} {field : Ident}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat))) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (bidsF (.var "id") field) = .ok (bidEvaledRefOfWord id field) := by
  rw [evalStorageRef, bidsF]
  simp only [evalStorageRefSteps, evalStorageRefStep, evalExpr?, EvalResult.bind, bind,
    pure, EvalResult.ofOption]
  rw [hid]
  simp [bidEvaledRefOfWord, valueToKey?]

theorem evalExpr_bidBid_of_get_id {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage (bidsF (.var "id") "bid")) =
        .ok (.int (Int.ofNat (bidBidWord id σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint256Int)
    (loc := wordLoc (bidBaseOfWord id))
    (hbase := hbids)
    (her := evalStorageRef_bidField_of_get_id
      (evm := initState cA gh bl σ σ₀ g A I) (locals := locals) (id := id)
      (field := "bid") hid)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract, storageDecls,
        BidStructTy, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        bidEvaledRefOfWord, bidSlotOfWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  exact congrArg EvalResult.ok
    (flipperStorageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I)
      (bidBaseOfWord id))

theorem evalExpr_bidLot_of_get_id {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage (bidsF (.var "id") "lot")) =
        .ok (.int (Int.ofNat (bidLotWord id σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint256Int)
    (loc := wordLoc (bidSlotOfWord id ⟨1⟩))
    (hbase := hbids)
    (her := evalStorageRef_bidField_of_get_id
      (evm := initState cA gh bl σ σ₀ g A I) (locals := locals) (id := id)
      (field := "lot") hid)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract, storageDecls,
        BidStructTy, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        bidEvaledRefOfWord, bidSlotOfWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  exact congrArg EvalResult.ok
    (flipperStorageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I)
      (bidSlotOfWord id ⟨1⟩))

theorem evalExpr_bidLot_of_get_id_evm {evm : EVM.State} {locals : Store}
    {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (bidsF (.var "id") "lot")) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidSlotOfWord id ⟨1⟩)).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint256Int)
    (loc := wordLoc (bidSlotOfWord id ⟨1⟩))
    (hbase := hbids)
    (her := evalStorageRef_bidField_of_get_id (evm := evm) (locals := locals)
      (id := id) (field := "lot") hid)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract, storageDecls,
        BidStructTy, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        bidEvaledRefOfWord, bidSlotOfWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  exact congrArg EvalResult.ok (flipperStorageLocLoad_uint256 evm (bidSlotOfWord id ⟨1⟩))

theorem evalExpr_bidGuy_of_get_id {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat (bidGuyWord id σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .address)
    (loc := addrLoc (bidPackedSlotOfWord id))
    (hbase := hbids)
    (her := evalStorageRef_bidField_of_get_id
      (evm := initState cA gh bl σ σ₀ g A I) (locals := locals) (id := id)
      (field := "guy") hid)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract, storageDecls,
        BidStructTy, addrSt])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        bidEvaledRefOfWord, bidPackedSlotOfWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  exact congrArg EvalResult.ok
    (flipperStorageLocLoad_address_offset0 (initState cA gh bl σ σ₀ g A I)
      (bidPackedSlotOfWord id))

theorem evalExpr_bidGuy_of_get_id_evm {evm : EVM.State} {locals : Store}
    {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (bidsF (.var "id") "guy")) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidPackedSlotOfWord id))
            solcAddrMask).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .address)
    (loc := addrLoc (bidPackedSlotOfWord id))
    (hbase := hbids)
    (her := evalStorageRef_bidField_of_get_id (evm := evm) (locals := locals)
      (id := id) (field := "guy") hid)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract, storageDecls,
        BidStructTy, addrSt])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        bidEvaledRefOfWord, bidPackedSlotOfWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  exact congrArg EvalResult.ok
    (flipperStorageLocLoad_address_offset0 evm (bidPackedSlotOfWord id))

theorem evalExpr_bidTic_of_get_id {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage (bidsF (.var "id") "tic")) =
        .ok (.int (Int.ofNat (bidTicWord id σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint48Int)
    (loc := uint48Loc (bidPackedSlotOfWord id) ⟨20, by decide⟩ (by decide))
    (hbase := hbids)
    (her := evalStorageRef_bidField_of_get_id
      (evm := initState cA gh bl σ σ₀ g A I) (locals := locals) (id := id)
      (field := "tic") hid)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract, storageDecls,
        BidStructTy, uint48St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        bidEvaledRefOfWord, bidPackedSlotOfWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  exact congrArg EvalResult.ok
    (flipperStorageLocLoad_uint48_offset20 (initState cA gh bl σ σ₀ g A I)
      (bidPackedSlotOfWord id))

theorem evalExpr_bidEnd_of_get_id {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage (bidsF (.var "id") "end")) =
        .ok (.int (Int.ofNat (bidEndWord id σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint48Int)
    (loc := uint48Loc (bidPackedSlotOfWord id) ⟨26, by decide⟩ (by decide))
    (hbase := hbids)
    (her := evalStorageRef_bidField_of_get_id
      (evm := initState cA gh bl σ σ₀ g A I) (locals := locals) (id := id)
      (field := "end") hid)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract, storageDecls,
        BidStructTy, uint48St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        bidEvaledRefOfWord, bidPackedSlotOfWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  exact congrArg EvalResult.ok
    (flipperStorageLocLoad_uint48_offset26 (initState cA gh bl σ σ₀ g A I)
      (bidPackedSlotOfWord id))

theorem evalExpr_bidUsr_of_get_id {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage (bidsF (.var "id") "usr")) =
        .ok (.address (AccountAddress.ofNat (bidUsrWord id σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .address)
    (loc := addrLoc (bidSlotOfWord id ⟨3⟩))
    (hbase := hbids)
    (her := evalStorageRef_bidField_of_get_id
      (evm := initState cA gh bl σ σ₀ g A I) (locals := locals) (id := id)
      (field := "usr") hid)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract, storageDecls,
        BidStructTy, addrSt])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        bidEvaledRefOfWord, bidSlotOfWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  exact congrArg EvalResult.ok
    (flipperStorageLocLoad_address_offset0 (initState cA gh bl σ σ₀ g A I)
      (bidSlotOfWord id ⟨3⟩))

theorem evalExpr_bidGal_of_get_id {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage (bidsF (.var "id") "gal")) =
        .ok (.address (AccountAddress.ofNat (bidGalWord id σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .address)
    (loc := addrLoc (bidSlotOfWord id ⟨4⟩))
    (hbase := hbids)
    (her := evalStorageRef_bidField_of_get_id
      (evm := initState cA gh bl σ σ₀ g A I) (locals := locals) (id := id)
      (field := "gal") hid)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract, storageDecls,
        BidStructTy, addrSt])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        bidEvaledRefOfWord, bidSlotOfWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  exact congrArg EvalResult.ok
    (flipperStorageLocLoad_address_offset0 (initState cA gh bl σ σ₀ g A I)
      (bidSlotOfWord id ⟨4⟩))

theorem evalExpr_bidGal_of_get_id_evm {evm : EVM.State} {locals : Store}
    {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (bidsF (.var "id") "gal")) =
        .ok (.address (AccountAddress.ofNat
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidSlotOfWord id ⟨4⟩))
            solcAddrMask).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .address)
    (loc := addrLoc (bidSlotOfWord id ⟨4⟩))
    (hbase := hbids)
    (her := evalStorageRef_bidField_of_get_id (evm := evm) (locals := locals)
      (id := id) (field := "gal") hid)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract, storageDecls,
        BidStructTy, addrSt])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        bidEvaledRefOfWord, bidSlotOfWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  exact congrArg EvalResult.ok
    (flipperStorageLocLoad_address_offset0 evm (bidSlotOfWord id ⟨4⟩))

theorem evalExpr_bidTab_of_get_id {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (.storage (bidsF (.var "id") "tab")) =
        .ok (.int (Int.ofNat (bidTabWord id σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint256Int)
    (loc := wordLoc (bidSlotOfWord id ⟨5⟩))
    (hbase := hbids)
    (her := evalStorageRef_bidField_of_get_id
      (evm := initState cA gh bl σ σ₀ g A I) (locals := locals) (id := id)
      (field := "tab") hid)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract, storageDecls,
        BidStructTy, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        bidEvaledRefOfWord, bidSlotOfWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  exact congrArg EvalResult.ok
    (flipperStorageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I)
      (bidSlotOfWord id ⟨5⟩))

theorem evalExpr_bidTab_of_get_id_evm {evm : EVM.State} {locals : Store}
    {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (bidsF (.var "id") "tab")) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidSlotOfWord id ⟨5⟩)).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint256Int)
    (loc := wordLoc (bidSlotOfWord id ⟨5⟩))
    (hbase := hbids)
    (her := evalStorageRef_bidField_of_get_id (evm := evm) (locals := locals)
      (id := id) (field := "tab") hid)
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract, storageDecls,
        BidStructTy, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        bidEvaledRefOfWord, bidSlotOfWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  exact congrArg EvalResult.ok (flipperStorageLocLoad_uint256 evm (bidSlotOfWord id ⟨5⟩))

theorem assign_bidBidStorage (evm : EVM.State) (id value : UInt256) {locals : Store}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (bidBaseOfWord id) value
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (bidsF (.var "id") "bid") (.int (Int.ofNat value.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := bidEvaledRefOfWord id "bid")
      (loc := wordLoc (bidBaseOfWord id))
      (hbase := hbids)
      (her := evalStorageRef_bidField_of_get_id (evm := evm) (locals := locals)
        (id := id) (field := "bid") hid)
      (hty := by simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract,
        storageDecls, BidStructTy, uint256St])
      (hloc := by
        funext evm
        simp only [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
          bidEvaledRefOfWord, bidsBase_intOfNatWord, bidSlotOfWord])
  simpa [evm'] using flipperStorageLocStore_uint256 evm (bidBaseOfWord id) value

theorem assign_bidGuyStorage (evm : EVM.State) (id : UInt256) {locals : Store}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (bidPackedSlotOfWord id)
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidPackedSlotOfWord id))
        (solcSourceWord evm.executionEnv))
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (bidsF (.var "id") "guy") (.address evm.executionEnv.source) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have hvalue :
      (.address evm.executionEnv.source : Value) =
        .address (AccountAddress.ofNat (EVM.word evm.executionEnv.source.val).toNat) := by
    rw [accountAddress_of_word_val]
  rw [hvalue]
  apply assignStorageRef_storage_scalar_value
      (ty := addrSt)
      (er := bidEvaledRefOfWord id "guy")
      (loc := addrLoc (bidPackedSlotOfWord id))
      (hbase := hbids)
      (her := evalStorageRef_bidField_of_get_id (evm := evm) (locals := locals)
        (id := id) (field := "guy") hid)
      (hty := by simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract,
        storageDecls, BidStructTy, addrSt])
      (hloc := by
        funext evm
        simp only [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
          bidEvaledRefOfWord, bidsBase_intOfNatWord, bidPackedSlotOfWord])
      (hscalar := by trivial)
  simpa [addrLoc, evm', solcSourceWord] using
    storageLocStore_address_offset0 evm (bidPackedSlotOfWord id)
      (EVM.word evm.executionEnv.source.val) (word_val_addr_canonical evm.executionEnv.source)

theorem assign_bidTicStorage (evm : EVM.State) (id value : UInt256) {locals : Store}
    (hvalue : value.toNat < 2 ^ 48)
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat)))
    (hbids : locals.get? "bids" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (bidPackedSlotOfWord id)
      (setUint48Offset20Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidPackedSlotOfWord id))
        value)
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (bidsF (.var "id") "tic") (.int (Int.ofNat value.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint48St)
      (er := bidEvaledRefOfWord id "tic")
      (loc := uint48Loc (bidPackedSlotOfWord id) ⟨20, by decide⟩ (by decide))
      (hbase := hbids)
      (her := evalStorageRef_bidField_of_get_id (evm := evm) (locals := locals)
        (id := id) (field := "tic") hid)
      (hty := by simp [storageTypeAt?, storageTypeStep?, bidEvaledRefOfWord, contract,
        storageDecls, BidStructTy, uint48St])
      (hloc := by
        funext evm
        simp only [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
          bidEvaledRefOfWord, bidsBase_intOfNatWord, bidPackedSlotOfWord])
  simpa [evm'] using flipperStorageLocStore_uint48_offset20 evm (bidPackedSlotOfWord id)
    value hvalue

end Benchmarks.Dss.Flipper
