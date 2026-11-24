import Tests.Pipeline.VyperRegistry.Helpers

variable {fork : Ethereum.Fork}

/-!
# Registry `entries(uint256)`

Dispatcher bucket 6, arm entry pc 1435: the guard and the three field words of
`entries[arg0]` (`keccak(1 ++ arg0)` + 0/1/2), returned raw as `(address, uint256, bool)`.
`storageWF` makes the raw `account` and `active` words the spec's typed views.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperBounded

namespace Tests.Pipeline.VyperRegistry

set_option maxRecDepth 2000000

abbrev entryField (idx : Expr) (f : Ident) : StorageRef :=
  { base := "entries", steps := [.mindex idx, .field f] }

theorem entriesBody_eq : entriesTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .return [.storage (entryField (.var "arg0") "account"), .storage (entryField (.var "arg0") "weight"),
       .storage (entryField (.var "arg0") "active")]] := by rfl

abbrev entriesStore (I : ExecutionEnv) : Store := (∅ : Store).insert "arg0" (uint256Value (argWord I))

theorem entriesDecode_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (entriesTransition.params.map Param.name)
      (transitionSignature entriesTransition).paramTypes I.calldata = some (entriesStore I) := by
  simpa [config, contract, Syntax.contractSyntax, entriesTransition, entriesStore, argWord_eq] using
    decodeMode_uint256_ok "arg0" I.calldata hsz36

theorem entriesDecode_short {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    config.externalABI.decodeCalldata? (entriesTransition.params.map Param.name)
      (transitionSignature entriesTransition).paramTypes I.calldata = none := by
  simpa [config, contract, Syntax.contractSyntax, entriesTransition] using
    decodeMode_uint256_none_short "arg0" I.calldata hsz hshort

/-- The evaluated reference of `entries[id].f` for a `uint256` local `id`. -/
theorem evalEntryRef (L : Store) (evm : EVM.State) (w : UInt256) (f : Ident)
    (hL : L.get? "arg0" = some (uint256Value w)) :
    evalStorageRef config (frame L) evm (entryField (.var "arg0") f) =
      .ok { base := "entries", steps := [.mindex (.int (Int.ofNat w.toNat)), .field f] } := by
  rw [Std.HashMap.get?_eq_getElem?] at hL
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, hL]

/-- The three-word return encoding of `(address, uint256, bool)`. -/
theorem tripleReturnEncoding (a : AccountAddress) (w : UInt256) (b : Bool) :
    encodeReturnValues? [.elem .address, .elem (.int (.uint ⟨256, by decide⟩)), .elem .bool]
      [.address a, uint256Value w, .bool b] =
      some ((UInt256.ofNat a.val).toByteArray ++ (w.toByteArray ++ b.toUInt256.toByteArray)) := by
  have hword : EVM.word w.toNat = w := by show UInt256.ofNat w.toNat = w; exact u256_ofNat_toNat w
  have hltNat : w.toNat < EVM.twoPow 256 := by change w.val.val < EVM.twoPow 256; exact w.val.isLt
  have h1 : encodeABIValue? (.elem .address) (.address a) = some (EVM.Word.toBytesBE (UInt256.ofNat a.val)) := by
    simp [encodeABIValue?, encodeABIWord?]; rfl
  have h2 : encodeABIValue? (.elem (.int (.uint ⟨256, by decide⟩))) (uint256Value w) =
      some (EVM.Word.toBytesBE w) := by
    simp [encodeABIValue?, encodeABIWord?, hword, hltNat, uint256Value]
  have h3 : encodeABIValue? (.elem .bool) (.bool b) = some (EVM.Word.toBytesBE b.toUInt256) := by
    simp [encodeABIValue?, encodeABIWord?]
  rw [toByteArray_eq_toBytesBE, toByteArray_eq_toBytesBE, toByteArray_eq_toBytesBE]
  simp only [encodeReturnValues?, encodeABIValues?, abiTupleHeadSize?, staticABIEncodedSize?,
    isDynamicABIType, encodeABIValuesFrom?, h1, h2, h3, bind, Option.bind, Bool.false_eq_true, if_false,
    List.nil_append, List.append_nil, pure, Option.some.injEq]
  apply ByteArray.ext
  simp [ByteArray.data_append]

/-- Three words written at 64, 96 and 128 over a 64-byte memory, read back as 96 bytes. -/
theorem tripleRead (M : ByteArray) (hM : M.size = 64) (x y z : UInt256) :
    (z.toByteArray.write 0 (y.toByteArray.write 0 (x.toByteArray.write 0 M 64 32) 96 32) 128 32).readWithPadding 64 96 =
      x.toByteArray ++ (y.toByteArray ++ z.toByteArray) := by
  have hM1 : (x.toByteArray.write 0 M 64 32).size = 96 :=
    toByteArray_write32_size_of_ge _ _ 64 64 96 hM (by omega) (lt_usize _ (by decide)) rfl
  have hM2 : (y.toByteArray.write 0 (x.toByteArray.write 0 M 64 32) 96 32).size = 128 :=
    toByteArray_write32_size_of_ge _ _ 96 96 128 hM1 (by omega) (lt_usize _ (by decide)) rfl
  have hM3 : (z.toByteArray.write 0 (y.toByteArray.write 0 (x.toByteArray.write 0 M 64 32) 96 32) 128 32).size = 160 :=
    toByteArray_write32_size_of_ge _ _ 128 128 160 hM2 (by omega) (lt_usize _ (by decide)) rfl
  rw [byteArray_readWithPadding_split _ 64 32 64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by rw [hM3] <;> omega),
    byteArray_readWithPadding_split _ (64 + 32) 32 32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by rw [hM3] <;> omega),
    show (64 : Nat) + 32 = 96 from rfl, show (96 : Nat) + 32 = 128 from rfl,
    toByteArray_write_read_below_of_gap z _ 128 64 (by rw [hM2] <;> omega) (by omega) (by rw [hM2]; exact lt_usize _ (by decide)),
    toByteArray_write_read_below_of_gap y _ 96 64 (by rw [hM1] <;> omega) (by omega) (by rw [hM1]; exact lt_usize _ (by decide)),
    toByteArray_write_read_back_of_gap x M 64 (by rw [hM]; exact lt_usize _ (by decide)),
    toByteArray_write_read_below_of_gap z _ 128 96 (by rw [hM2] <;> omega) (by omega) (by rw [hM2]; exact lt_usize _ (by decide)),
    toByteArray_write_read_back_of_gap y _ 96 (by rw [hM1]; exact lt_usize _ (by decide)),
    toByteArray_write_read_back_of_gap z _ 128 (by rw [hM2]; exact lt_usize _ (by decide))]

/-- The hash scratch memory of `entries[arg0]` over the dispatcher memory of bucket 6. -/
abbrev hashMem6 (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat 1).toByteArray.write 0 ((argWord I).toByteArray.write 0 (registryDispatchMem 6) 32 32) 0 32

theorem hashMem6_size (I : ExecutionEnv) : (hashMem6 I).size = 64 := by
  have h1 : ((argWord I).toByteArray.write 0 (registryDispatchMem 6) 32 32).size = 64 :=
    toByteArray_write32_size_of_ge _ _ 32 32 64 (dispatchMem_size 6 (by decide)) (by omega) (lt_usize _ (by decide)) rfl
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h1]; omega), h1]

/-- `entries(uint256)`: the theorem `Correct.lean` routes selector 8 to. -/
theorem registryEntriesBody {σ σ₀ A I} {g : UInt256} (hwf : storageWF σ I)
    (hcode : I.code = registryBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (registrySelBytes 8)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (registrySelBytes 8) rfl hsel
  obtain ⟨_, _, rd⟩ := registryReachEntriesBody (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  have hd : dispatchMsg contract I.calldata = some entriesTransition :=
    registryDispatch_entries (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel)
      (selIs_exclusive (by native_decide) hsel) (selIs_exclusive (by native_decide) hsel) hsel
  by_cases hshort : I.calldata.size < 36
  · have rd1 := registryBlocks.registry_block_1435_taken (by simp) (guard_short hsize hshort) (by jump_dest) rd
    have rd2 := registryBlocks.registry_block_1661 (by simp) rd1
    exact RDrev.reEquivDecodingFailed hcode rd2 hd (entriesDecode_short hsz hshort)
  have hsz36 : 36 ≤ I.calldata.size := by omega
  by_cases hwv : I.weiValue = ⟨0⟩
  swap
  · have rd1 := registryBlocks.registry_block_1435_taken (by simp) (guard_wv hwv) (by jump_dest) rd
    have rd2 := registryBlocks.registry_block_1661 (by simp) rd1
    exact RDrev.reEquivOfDispatch hcode hd
      (fun _ => by rw [entriesBody_eq]; exact bodyReverts_nonPayable (by simpa [initState] using hwv)) rd2
  have rd1 := registryBlocks.registry_block_1435_fallthrough (by simp) (guard_ok hwv hsz36 hsize) rd
  have rd2 := registryBlocks.registry_block_1445 (by simp) rd1
  have hkec := keccak_entry 6 (by decide) (argWord I)
  simp only [ulit_toNat' 32 (by decide), ulit_toNat' 64 (by decide), ulit_toNat' 96 (by decide),
    ulit_toNat' 128 (by decide), show (⟨0⟩ : UInt256).toNat = 0 from rfl] at rd2
  rw [hkec, slotWord_eq, slotWord_eq, slotWord_eq, tripleRead _ (hashMem6_size I)] at rd2
  have hdec := entriesDecode_ok (I := I) hsz36
  obtain ⟨hacc, hact⟩ := hwf.2 (argWord I)
  have hbase : (entriesStore I).get? "entries" = none := by simp
  have hcv : evalExpr? config (frame (entriesStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simpa [initState] using hwv)
  have h1 : evalExpr? config (frame (entriesStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.storage (entryField (.var "arg0") "account")) =
      .ok (.address (AccountAddress.ofNat (solcSlotWordAt (entrySlot (argWord I)) σ I).toNat)) := by
    rw [evalExpr_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl) (t := .address)
        (er := { base := "entries", steps := [.mindex (.int (Int.ofNat (argWord I).toNat)), .field "account"] })
        (loc := vyperWordLoc (entrySlot (argWord I)) .address) (hbase := hbase)
        (her := evalEntryRef _ _ _ _ (store_get_self _ _ _)) (hty := rfl) (hloc := rfl),
      storageLocLoad_vyperWord, storageLoad_initState_ofUInt256_solcSlotWordAt]
    rfl
  have h2 : evalExpr? config (frame (entriesStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.storage (entryField (.var "arg0") "weight")) =
      .ok (uint256Value (solcSlotWordAt (entrySlot (argWord I) + UInt256.ofNat 1) σ I)) := by
    rw [evalExpr_storage_vyper_uint256_backend (hbackend := rfl) (hcheck := by rfl)
        (er := { base := "entries", steps := [.mindex (.int (Int.ofNat (argWord I).toNat)), .field "weight"] })
        (physicalSlot := entrySlot (argWord I) + UInt256.ofNat 1) (hbase := hbase)
        (her := evalEntryRef _ _ _ _ (store_get_self _ _ _)) (hty := rfl) (hloc := rfl),
      storageLoad_initState_ofUInt256_solcSlotWordAt]
  have h3 : evalExpr? config (frame (entriesStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (.storage (entryField (.var "arg0") "active")) =
      .ok (wordToElem .bool (solcSlotWordAt (entrySlot (argWord I) + UInt256.ofNat 2) σ I)) := by
    rw [evalExpr_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl) (t := .bool)
        (er := { base := "entries", steps := [.mindex (.int (Int.ofNat (argWord I).toNat)), .field "active"] })
        (loc := vyperWordLoc (entrySlot (argWord I) + UInt256.ofNat 2) .bool) (hbase := hbase)
        (her := evalEntryRef _ _ _ _ (store_get_self _ _ _)) (hty := rfl) (hloc := rfl),
      storageLocLoad_vyperWord, storageLoad_initState_ofUInt256_solcSlotWordAt]
  have hbody : ExecTransitionBody fork config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I) (entriesStore I)
      entriesTransition.body
      (.returned (frame (entriesStore I)) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (some [.address (AccountAddress.ofNat (solcSlotWordAt (entrySlot (argWord I)) σ I).toNat),
          uint256Value (solcSlotWordAt (entrySlot (argWord I) + UInt256.ofNat 1) σ I),
          wordToElem .bool (solcSlotWordAt (entrySlot (argWord I) + UInt256.ofNat 2) σ I)])) := by
    rw [entriesBody_eq]
    refine ExecFuncBody.execBlockRet ((ABlock.start.requireStep hcv).run (ExecBlock.consReturn (ExecStmt.return ?_)))
    rw [evalExprs?, h1, evalExprs?, h2, evalExprs?, h3, evalExprs?]
    rfl
  refine rd2.reEquivExecution hcode hd hdec hbody (returnEquiv.returned rfl ?_)
  show encodeReturnValues? [.elem .address, .elem (.int (.uint ⟨256, by decide⟩)), .elem .bool] _ = _
  rcases hact with h | h
  · rw [h]
    show encodeReturnValues? _ [_, _, .bool false] = _
    rw [tripleReturnEncoding, word_roundtrip hacc]
    rfl
  · rw [h]
    show encodeReturnValues? _ [_, _, .bool true] = _
    rw [tripleReturnEncoding, word_roundtrip hacc]
    rfl

end Tests.Pipeline.VyperRegistry
