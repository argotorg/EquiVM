import Examples.OpenZeppelinBench.ERC6909.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace OpenZeppelinBench.ERC6909

/-! ## ABI decode and source-level body for `approve(address,uint256,uint256)` -/

/-- The raw ABI word for `approve`'s `spender` argument. -/
abbrev approveSpenderWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

/-- The raw ABI word for `approve`'s `id` argument. -/
abbrev approveIdWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

/-- The raw ABI word for `approve`'s `amount` argument. -/
abbrev approveAmountWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev approveSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (approveSpenderWord I).toNat)

abbrev approveIdValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (approveIdWord I).toNat)

abbrev approveAmountValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (approveAmountWord I).toNat)

abbrev approveStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "spender" (approveSpenderValue I)).insert "id"
    (approveIdValue I)).insert "amount" (approveAmountValue I)

abbrev approveOwnerWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

def approveSlot (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (.address evm.executionEnv.source)
    (.address (AccountAddress.ofNat (approveSpenderWord I).toNat))
    (.int (Int.ofNat (approveIdWord I).toNat))

def approveSlotI (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (.address I.source)
    (.address (AccountAddress.ofNat (approveSpenderWord I).toNat))
    (.int (Int.ofNat (approveIdWord I).toNat))

def approvePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (approveSlot evm I)
    (approveAmountWord I)

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeScalarWords_addr_uint256_uint256_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [.elem .address, abiUInt256, abiUInt256] bytes 0 =
      some [.address (Ethereum.AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat)] := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_uint256_ok (start := 32) hlen32]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_uint256_ok (start := 64) hlen64]
  rfl

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeScalarWords_addr_uint256_uint256_none_noncanon {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [.elem .address, abiUInt256, abiUInt256] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc)]
  simp only [Option.bind, bind]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeScalarWords_addr_uint256_uint256_none_short {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeScalarWords? [.elem .address, abiUInt256, abiUInt256] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    rw [decodeScalarWord_address_none_short (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    by_cases hcanon : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus
    · rw [decodeScalarWord_address_ok (start := 0) (by simpa using htake0)
        (by simpa using hcanon)]
      simp only [Option.bind, bind]
      by_cases h64 : bytes.length < 64
      · have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        rw [decodeScalarWord_uint256_none_short (start := 32) htake32n]
      · have htake32 : ((bytes.drop 32).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        have htake64n : ¬ ((bytes.drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop]
          omega
        rw [decodeScalarWord_uint256_ok (start := 32) htake32]
        simp only [Option.bind, bind]
        rw [decodeScalarWord_uint256_none_short (start := 64) htake64n]
    · rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using htake0)
        (by simpa using hcanon)]
      simp only [Option.bind, bind]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeCalldata_addr_uint256_uint256_ok {cd : ByteArray} {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd =
      some ((((∅ : Solm.Store).insert x
        (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  have htake36' : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  have htake68' : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_addr_uint256_uint256_ok (bytes := cd.toList.drop 4) htake4
    htake36' htake68' (by rw [hword4]; exact hcanon)]
  change decodeCalldata.insertValues [x, y, z]
      [.address (Ethereum.AccountAddress.ofNat
          (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat)] ∅ =
    some ((((∅ : Solm.Store).insert x
      (.address (Ethereum.AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.int (Int.ofNat (calldataWord cd 36).toNat))).insert z
      (.int (Int.ofNat (calldataWord cd 68).toNat)))
  simp [decodeCalldata.insertValues]
  rw [hword4, hword36, hword68]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeCalldata_addr_uint256_uint256_none_noncanon {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) (hbig : cd.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_addr_uint256_uint256_none_noncanon (bytes := cd.toList.drop 4)
    htake4 (by rw [hword4]; exact hnc)]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeCalldata_addr_uint256_uint256_none_short {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [decodeScalarWords_addr_uint256_uint256_none_short (bytes := cd.toList.drop 4) (by
    rw [List.length_drop, htlen]
    omega)]

-- PROMOTE -> Common.lean / Reasoning.ABI
theorem decodeCalldata_addr_uint256_uint256_none_huge {cd : ByteArray}
    {x y z : Solm.Ident}
    (hbig : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata [x, y, z] [.elem .address, abiUInt256, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [.elem .address, abiUInt256, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

theorem erc6909Decode_approve_ok {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (approveSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = some (approveStore I) := by
  show decodeCalldata ["spender", "id", "amount"] [addr, uint256, uint256] I.calldata =
    some (approveStore I)
  simpa [addr, uint256, abiUInt256, approveStore, approveSpenderValue, approveIdValue,
    approveAmountValue, approveSpenderWord, approveIdWord, approveAmountWord]
    using decodeCalldata_addr_uint256_uint256_ok
      (cd := I.calldata) (x := "spender") (y := "id") (z := "amount")
      hsz100 hbig hcanon

theorem erc6909Decode_approve_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "id", "amount"] [addr, uint256, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    decodeCalldata_addr_uint256_uint256_none_short
      (cd := I.calldata) (x := "spender") (y := "id") (z := "amount") hsz4 hshort

theorem erc6909Decode_approve_none_noncanon {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (approveSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "id", "amount"] [addr, uint256, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, approveSpenderWord] using
    decodeCalldata_addr_uint256_uint256_none_noncanon
      (cd := I.calldata) (x := "spender") (y := "id") (z := "amount") hsz100 hbig hnc

theorem erc6909Decode_approve_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["spender", "id", "amount"] [addr, uint256, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    decodeCalldata_addr_uint256_uint256_none_huge
      (cd := I.calldata) (x := "spender") (y := "id") (z := "amount") hbig

theorem approveOwnerWord_toNat (I : ExecutionEnv) :
    (approveOwnerWord I).toNat = I.source.val := by
  unfold approveOwnerWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem approveOwnerWord_canonical (I : ExecutionEnv) :
    (approveOwnerWord I).toNat < EVM.addressModulus := by
  rw [approveOwnerWord_toNat]
  change I.source.val < AccountAddress.size
  exact I.source.isLt

theorem approveOwner_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (approveOwnerWord I).toNat = I.source := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [approveOwnerWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

theorem approveStore_spender (I : ExecutionEnv) :
    (approveStore I).get? "spender" = some (approveSpenderValue I) := by
  rw [approveStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem approveStore_id (I : ExecutionEnv) :
    (approveStore I).get? "id" = some (approveIdValue I) := by
  rw [approveStore, store_get_ne _ _ (by decide), store_get_self]

theorem approveStore_amount (I : ExecutionEnv) :
    (approveStore I).get? "amount" = some (approveAmountValue I) := by
  rw [approveStore, store_get_self]

theorem approveStore_allowances (I : ExecutionEnv) :
    (approveStore I).get? "_allowances" = none := by
  rw [approveStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_approve_spender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := approveStore I } evm
      (.var "spender") = .ok (approveSpenderValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [approveStore_spender]

theorem evalExpr_approve_id (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := approveStore I } evm
      (.var "id") = .ok (approveIdValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [approveStore_id]

theorem evalExpr_approve_amount (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := approveStore I } evm
      (.var "amount") = .ok (approveAmountValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [approveStore_amount]

theorem evalExpr_approve_sender (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := approveStore I } evm sender =
      .ok (.address evm.executionEnv.source) := by
  simp [sender, evalExpr?, envValue, pure]

theorem evalExpr_approve_zeroAddr (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := approveStore I } evm zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption, pure,
    bind]

def approveEvaledRef (evm : EVM.State) (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "_allowances",
    steps := [.mindex (.address evm.executionEnv.source),
      .mindex (.address (AccountAddress.ofNat (approveSpenderWord I).toNat)),
      .mindex (.int (Int.ofNat (approveIdWord I).toNat))] }

theorem evalStorageRef_approve_allowance (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := approveStore I } evm
      (allowanceRef sender (.var "spender") (.var "id")) =
        EvalResult.ok (approveEvaledRef evm I) := by
  simp [evalStorageRef, evalStorageRefStep, sender, envValue, evalExpr_approve_spender,
    evalExpr_approve_id, approveEvaledRef, approveSpenderValue, approveIdValue,
    valueToKey?, EvalResult.seqList, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?, evalStorageRefSteps, allowanceRef]

theorem approveAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := approveStore I } evm
      .storage (allowanceRef sender (.var "spender") (.var "id")) (approveAmountValue I) =
        .ok ({ contract := contract, locals := approveStore I }, approvePostState evm I) := by
  simp only [allowanceRef]
  apply assignStorageRef_storage_scalar (ty := uint256St) (loc := wordLoc (approveSlot evm I))
      (hbase := approveStore_allowances I)
      (her := evalStorageRef_approve_allowance evm I)
      (hty := by
        simp [storageTypeAt?, approveEvaledRef, contract, storageDecls, uint256St,
          storageTypeStep?])
      (hloc := by
        funext x
        simp [config, storageLayout, approveEvaledRef, approveSlot])
  rw [erc6909StorageLocStore_uint256]
  simp [approvePostState, approveSlot, approveEvaledRef]

theorem evalExpr_approve_sender_ne_zero_true (evm : EVM.State) (hsource : evm.executionEnv.source ≠
    AccountAddress.ofNat 0) :
  evalExpr? config { contract := contract, locals := approveStore evm.executionEnv } evm
      (.binary .ne sender zeroAddr) = .ok (.bool true) := by
  have hbeq :
      (Value.address evm.executionEnv.source == Value.address (AccountAddress.ofNat 0)) =
        false := by
    simp [BEq.beq, hsource]
  simp [evalExpr?, evalExpr_approve_sender, evalExpr_approve_zeroAddr, evalBinaryOp?,
    EvalResult.bind, bind, pure, hbeq]

theorem evalExpr_approve_sender_ne_zero_false (evm : EVM.State) (hsource :
    evm.executionEnv.source = AccountAddress.ofNat 0) :
  evalExpr? config { contract := contract, locals := approveStore evm.executionEnv } evm
      (.binary .ne sender zeroAddr) = .ok (.bool false) := by
  have hbeq :
      (Value.address evm.executionEnv.source == Value.address (AccountAddress.ofNat 0)) =
        true := by
    simp [BEq.beq, hsource]
  simp [evalExpr?, evalExpr_approve_sender, evalExpr_approve_zeroAddr, evalBinaryOp?,
    EvalResult.bind, bind, pure, hbeq]

theorem evalExpr_approve_spender_ne_zero_true (evm : EVM.State) (I : ExecutionEnv)
    (hspender : AccountAddress.ofNat (approveSpenderWord I).toNat ≠ AccountAddress.ofNat 0) :
  evalExpr? config { contract := contract, locals := approveStore I } evm
      (.binary .ne (.var "spender") zeroAddr) = .ok (.bool true) := by
  have hbeq : (approveSpenderValue I == Value.address (AccountAddress.ofNat 0)) = false := by
    simp [approveSpenderValue, BEq.beq, hspender]
  simp [evalExpr?, evalExpr_approve_spender, evalExpr_approve_zeroAddr, evalBinaryOp?,
    EvalResult.bind, bind, pure, hbeq]

theorem evalExpr_approve_spender_ne_zero_false (evm : EVM.State) (I : ExecutionEnv)
    (hspender : AccountAddress.ofNat (approveSpenderWord I).toNat = AccountAddress.ofNat 0) :
  evalExpr? config { contract := contract, locals := approveStore I } evm
      (.binary .ne (.var "spender") zeroAddr) = .ok (.bool false) := by
  have hbeq : (approveSpenderValue I == Value.address (AccountAddress.ofNat 0)) = true := by
    simp [approveSpenderValue, BEq.beq, hspender]
  simp [evalExpr?, evalExpr_approve_spender, evalExpr_approve_zeroAddr, evalBinaryOp?,
    EvalResult.bind, bind, pure, hbeq]

theorem erc6909ApproveBodyReturns (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsource : evm.executionEnv.source ≠ AccountAddress.ofNat 0)
    (hspender :
      AccountAddress.ofNat (approveSpenderWord evm.executionEnv).toNat ≠ AccountAddress.ofNat 0) :
    ExecTransitionBody config contract evm (approveStore evm.executionEnv) approveTransition.body
      (.returned { contract := contract, locals := approveStore evm.executionEnv }
        (approvePostState evm evm.executionEnv) (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_approve_sender_ne_zero_true evm hsource)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_approve_spender_ne_zero_true evm evm.executionEnv hspender)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_approve_amount evm evm.executionEnv)
      (approveAssign evm evm.executionEnv)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by simp [evalExpr?, pure]))

theorem erc6909ApproveBodyReverts_sender (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsource : evm.executionEnv.source = AccountAddress.ofNat 0) :
    ExecTransitionBody config contract evm (approveStore evm.executionEnv) approveTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_approve_sender_ne_zero_false evm hsource))

theorem erc6909ApproveBodyReverts_spender (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsource : evm.executionEnv.source ≠ AccountAddress.ofNat 0)
    (hspender :
      AccountAddress.ofNat (approveSpenderWord evm.executionEnv).toNat = AccountAddress.ofNat 0) :
    ExecTransitionBody config contract evm (approveStore evm.executionEnv) approveTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_approve_sender_ne_zero_true evm hsource)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_approve_spender_ne_zero_false evm evm.executionEnv hspender))

theorem erc6909ApproveSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x42, 0x6a, 0x84, 0x93]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x42, 0x6a, 0x84, 0x93]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc6909Dispatch_approve {cd : ByteArray}
    (hsel : ((⟨#[0x42, 0x6a, 0x84, 0x93]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some approveTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x42, 0x6a, 0x84, 0x93]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split (pre := [allowanceTransition])
    (post := [balanceOfTransition, isOperatorTransition, setOperatorTransition,
      supportsInterfaceTransition, transferTransition, transferFromTransition])
    rfl ?_ (by rw [selectorOf, erc6909ApproveSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl
  rw [selectorOf, erc6909AllowanceSelectorBytes, hcd]
  decide

/-! ## Local scratch-memory facts for the three-level `_allowances` write -/

-- PROMOTE -> Common.lean
theorem erc6909ApproveKeyValueToWord_address_of_canonical (w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    keyValueToWord (.address (AccountAddress.ofNat w.toNat)) = w := by
  apply u256_inj
  unfold keyValueToWord AccountAddress.ofNat
  exact Nat.mod_eq_of_lt (by
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)

theorem approveAccountAddress_ofNat_zero_iff {w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus) :
    AccountAddress.ofNat w.toNat = AccountAddress.ofNat 0 ↔ w = ⟨0⟩ := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    unfold AccountAddress.ofNat at hv
    simp only [Fin.val_ofNat] at hv
    have hwmod : w.toNat % AccountAddress.size = w.toNat := by
      exact Nat.mod_eq_of_lt (by
        simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon)
    rw [hwmod] at hv
    exact uint256_toNat_eq_zero hv
  · intro h
    rw [h]
    rfl

theorem approveSource_zero_iff (I : ExecutionEnv) :
    I.source = AccountAddress.ofNat 0 ↔ approveOwnerWord I = ⟨0⟩ := by
  constructor
  · intro h
    apply u256_inj
    rw [approveOwnerWord_toNat, h]
    rfl
  · intro h
    rw [← approveOwner_ofNat I, h]
    rfl

theorem approveMasked_ne_zero_of_ne_zero {w : UInt256}
    (hcanon : w.toNat < EVM.addressModulus) (hnz : w ≠ ⟨0⟩) :
    UInt256.land solcAddrMask w ≠ ⟨0⟩ := by
  rw [solcAddrMask_clean_left hcanon]
  exact hnz

theorem approveMasked_eq_zero_of_zero {w : UInt256} (hzero : w = ⟨0⟩) :
    UInt256.land solcAddrMask w = ⟨0⟩ := by
  rw [hzero]
  decide

-- PROMOTE -> Common.lean
noncomputable def approveWordAt0Mem (word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 mem 0 32

-- PROMOTE -> Common.lean
noncomputable def approveWordAt32Mem (word : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 mem 32 32

-- PROMOTE -> Common.lean
noncomputable def approveTwoWordHashMem (key slot : UInt256) (mem : ByteArray) : ByteArray :=
  approveWordAt32Mem slot (approveWordAt0Mem key mem)

-- PROMOTE -> Common.lean
theorem approveWordAt0Mem_size {mem : ByteArray} (word : UInt256) (hmem : mem.size = 96) :
    (approveWordAt0Mem word mem).size = 96 := by
  unfold approveWordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

-- PROMOTE -> Common.lean
theorem approveWordAt32Mem_size {mem : ByteArray} (word : UInt256) (hmem : mem.size = 96) :
    (approveWordAt32Mem word mem).size = 96 := by
  unfold approveWordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

-- PROMOTE -> Common.lean
theorem approveTwoWordHashMem_size {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (approveTwoWordHashMem key slot mem).size = 96 := by
  unfold approveTwoWordHashMem
  exact approveWordAt32Mem_size slot (approveWordAt0Mem_size key hmem)

-- PROMOTE -> Common.lean
theorem approveTwoWordHashMem_read0 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (approveTwoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold approveTwoWordHashMem approveWordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [approveWordAt0Mem_size key hmem]; omega) (by omega)]
  unfold approveWordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray key).size ≤ 32
    rw [toByteArray_size])

-- PROMOTE -> Common.lean
theorem approveTwoWordHashMem_read32 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (approveTwoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold approveTwoWordHashMem approveWordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [approveWordAt0Mem_size key hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

-- PROMOTE -> Common.lean
theorem approveTwoWordHashMem_read64 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (approveTwoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold approveTwoWordHashMem approveWordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [approveWordAt0Mem_size key hmem]; omega) (by omega)
      (by rw [approveWordAt0Mem_size key hmem])]
  unfold approveWordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem])]
  exact hread64

-- PROMOTE -> Common.lean
set_option maxHeartbeats 800000 in
theorem approveTwoWordHashMem_read0_64 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 96) :
    (approveTwoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [approveTwoWordHashMem_size key slot hmem]; omega)]
  have hleft :
      (approveTwoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [approveTwoWordHashMem_size key slot hmem]; omega),
      approveTwoWordHashMem_read0 key slot hmem]
  have hright :
      (approveTwoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [approveTwoWordHashMem_size key slot hmem]; omega),
      approveTwoWordHashMem_read32 key slot hmem]
  rw [show (approveTwoWordHashMem key slot mem).extract 0 64 =
      (approveTwoWordHashMem key slot mem).extract 0 32 ++
        (approveTwoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

noncomputable def approveOwnerHashMem (owner : UInt256) : ByteArray :=
  approveTwoWordHashMem owner ⟨2⟩ solcFreePtrMem

noncomputable def approveOwnerSlot (owner : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((approveOwnerHashMem owner).readWithPadding 0 64)))

noncomputable def approveSpenderHashMem (owner spender : UInt256) : ByteArray :=
  approveTwoWordHashMem spender (approveOwnerSlot owner) (approveOwnerHashMem owner)

noncomputable def approveSpenderSlot (owner spender : UInt256) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((approveSpenderHashMem owner spender).readWithPadding 0 64)))

noncomputable def approveIdHashMem (owner spender id : UInt256) : ByteArray :=
  approveTwoWordHashMem id (approveSpenderSlot owner spender)
    (approveSpenderHashMem owner spender)

noncomputable def approveEventMem (owner spender id amount : UInt256) : ByteArray :=
  (UInt256.toByteArray amount).write 0 (approveIdHashMem owner spender id) 128 32

noncomputable def approveReturnMem (owner spender id amount : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0
    (approveEventMem owner spender id amount) 128 32

theorem approveOwnerHashMem_size (owner : UInt256) :
    (approveOwnerHashMem owner).size = 96 := by
  unfold approveOwnerHashMem
  exact approveTwoWordHashMem_size owner ⟨2⟩ solcFreePtrMem_size

theorem approveSpenderHashMem_size (owner spender : UInt256) :
    (approveSpenderHashMem owner spender).size = 96 := by
  unfold approveSpenderHashMem
  exact approveTwoWordHashMem_size spender (approveOwnerSlot owner)
    (approveOwnerHashMem_size owner)

theorem approveIdHashMem_size (owner spender id : UInt256) :
    (approveIdHashMem owner spender id).size = 96 := by
  unfold approveIdHashMem
  exact approveTwoWordHashMem_size id (approveSpenderSlot owner spender)
    (approveSpenderHashMem_size owner spender)

theorem approveOwnerHashMem_read0_64 (owner : UInt256) :
    (approveOwnerHashMem owner).readWithPadding 0 64 =
      UInt256.toByteArray owner ++ UInt256.toByteArray (⟨2⟩ : UInt256) := by
  unfold approveOwnerHashMem
  exact approveTwoWordHashMem_read0_64 owner ⟨2⟩ solcFreePtrMem_size

theorem approveSpenderHashMem_read0_64 (owner spender : UInt256) :
    (approveSpenderHashMem owner spender).readWithPadding 0 64 =
      UInt256.toByteArray spender ++ UInt256.toByteArray (approveOwnerSlot owner) := by
  unfold approveSpenderHashMem
  exact approveTwoWordHashMem_read0_64 spender (approveOwnerSlot owner)
    (approveOwnerHashMem_size owner)

theorem approveIdHashMem_read0_64 (owner spender id : UInt256) :
    (approveIdHashMem owner spender id).readWithPadding 0 64 =
      UInt256.toByteArray id ++ UInt256.toByteArray (approveSpenderSlot owner spender) := by
  unfold approveIdHashMem
  exact approveTwoWordHashMem_read0_64 id (approveSpenderSlot owner spender)
    (approveSpenderHashMem_size owner spender)

theorem approveIdHashMem_read64 (owner spender id : UInt256) :
    (approveIdHashMem owner spender id).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold approveIdHashMem approveSpenderHashMem approveOwnerHashMem
  apply approveTwoWordHashMem_read64
  · exact approveTwoWordHashMem_size spender (approveOwnerSlot owner)
      (approveTwoWordHashMem_size owner ⟨2⟩ solcFreePtrMem_size)
  · apply approveTwoWordHashMem_read64
    · exact approveTwoWordHashMem_size owner ⟨2⟩ solcFreePtrMem_size
    · exact approveTwoWordHashMem_read64 owner ⟨2⟩ solcFreePtrMem_size
        solcFreePtrMem_read64

theorem approveIdHashMem_mload64 (owner spender id : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (approveIdHashMem owner spender id).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((approveIdHashMem owner spender id).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [approveIdHashMem_size]; decide) (by decide)
    (approveIdHashMem_read64 owner spender id)

theorem approveEventMem_size (owner spender id amount : UInt256) :
    (approveEventMem owner spender id amount).size = 160 := by
  unfold approveEventMem
  rw [toByteArray_write_eq _ _ _ (by rw [approveIdHashMem_size]; omega)
      (by rw [approveIdHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, approveIdHashMem_size,
    ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem approveEventMem_read64 (owner spender id amount : UInt256) :
    (approveEventMem owner spender id amount).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold approveEventMem
  rw [toByteArray_write_eq _ _ _ (by rw [approveIdHashMem_size]; omega)
      (by rw [approveIdHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, approveIdHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, approveIdHashMem_size, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [approveIdHashMem_size]),
    ← readWithPadding_eq_extract _ 64 (by rw [approveIdHashMem_size]),
    approveIdHashMem_read64]

theorem approveEventMem_mload64 (owner spender id amount : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (approveEventMem owner spender id amount).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((approveEventMem owner spender id amount).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [approveEventMem_size]; decide) (by decide)
    (approveEventMem_read64 owner spender id amount)

theorem approveReturnMem_size (owner spender id amount : UInt256) :
    (approveReturnMem owner spender id amount).size = 160 := by
  unfold approveReturnMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [approveEventMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, approveEventMem_size, toByteArray_size]
  omega

theorem approveReturnMem_read64 (owner spender id amount : UInt256) :
    (approveReturnMem owner spender id amount).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold approveReturnMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [approveEventMem_size]; omega) (by omega),
    approveEventMem_read64]

theorem approveReturnMem_mload64 (owner spender id amount : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (approveReturnMem owner spender id amount).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((approveReturnMem owner spender id amount).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [approveReturnMem_size]; decide) (by decide)
    (approveReturnMem_read64 owner spender id amount)

theorem approveReturnMem_read128 (owner spender id amount : UInt256) :
    (approveReturnMem owner spender id amount).readWithPadding 128 32 =
      UInt256.toByteArray (⟨1⟩ : UInt256) := by
  unfold approveReturnMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [approveEventMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray (⟨1⟩ : UInt256)).size ≤ 32
    rw [toByteArray_size])

theorem approveOwnerKeccakSlot (I : ExecutionEnv) :
    approveOwnerSlot (approveOwnerWord I) =
      mapSlot (keyValueToWord (.address I.source)) ⟨2⟩ := by
  have hownerKey : keyValueToWord (.address I.source) = approveOwnerWord I := by
    rw [← approveOwner_ofNat I]
    exact erc6909ApproveKeyValueToWord_address_of_canonical _
      (approveOwnerWord_canonical I)
  unfold approveOwnerSlot mapSlot
  rw [approveOwnerHashMem_read0_64, hownerKey]
  exact mappingSlot_single (approveOwnerWord I) ⟨2⟩

theorem approveSpenderKeccakSlot (I : ExecutionEnv)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus) :
    approveSpenderSlot (approveOwnerWord I) (approveSpenderWord I) =
      mapSlot (keyValueToWord
        (.address (AccountAddress.ofNat (approveSpenderWord I).toNat)))
        (mapSlot (keyValueToWord (.address I.source)) ⟨2⟩) := by
  have hownerKey : keyValueToWord (.address I.source) = approveOwnerWord I := by
    rw [← approveOwner_ofNat I]
    exact erc6909ApproveKeyValueToWord_address_of_canonical _
      (approveOwnerWord_canonical I)
  have hspenderKey :
      keyValueToWord (.address (AccountAddress.ofNat (approveSpenderWord I).toNat)) =
        approveSpenderWord I :=
    erc6909ApproveKeyValueToWord_address_of_canonical _ hcanonSpender
  unfold approveSpenderSlot mapSlot
  rw [approveSpenderHashMem_read0_64, approveOwnerKeccakSlot I]
  rw [hownerKey, hspenderKey]
  exact mappingSlot_single (approveSpenderWord I)
    (uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (approveOwnerWord I) ++
      UInt256.toByteArray (⟨2⟩ : UInt256))))

theorem approveFinalKeccakSlot (I : ExecutionEnv)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((approveIdHashMem (approveOwnerWord I) (approveSpenderWord I)
          (approveIdWord I)).readWithPadding 0 64)))
      = approveSlotI I := by
  unfold approveSlotI allowanceSlot mapSlot
  rw [approveIdHashMem_read0_64, approveSpenderKeccakSlot I hcanonSpender]
  have hownerKey : keyValueToWord (.address I.source) = approveOwnerWord I := by
    rw [← approveOwner_ofNat I]
    exact erc6909ApproveKeyValueToWord_address_of_canonical _
      (approveOwnerWord_canonical I)
  have hspenderKey :
      keyValueToWord (.address (AccountAddress.ofNat (approveSpenderWord I).toNat)) =
        approveSpenderWord I :=
    erc6909ApproveKeyValueToWord_address_of_canonical _ hcanonSpender
  rw [hownerKey, hspenderKey]
  rw [show keyValueToWord (.int (Int.ofNat (approveIdWord I).toNat)) =
      approveIdWord I from erc6909WordOfInt_ofNat_toNat (approveIdWord I)]
  exact mappingSlot_single (approveIdWord I)
    (uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (approveSpenderWord I) ++
      UInt256.toByteArray
        (uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (approveOwnerWord I) ++
          UInt256.toByteArray (⟨2⟩ : UInt256)))))))

/-! ## Local high-SWAP reachability helpers -/

-- PROMOTE -> Common.lean / Reasoning.Stepping: generic `SWAP5` xstep.
theorem erc6909Swap5_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f : UInt256} {t : List UInt256}
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

-- PROMOTE -> Common.lean / Reasoning.Stepping: generic `SWAP6` xstep.
theorem erc6909Swap6_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f h : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP6, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: h :: t)
    (hov : t.length + 7 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (h :: b :: c :: d :: e :: f :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP6, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap6 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: h :: t).length - 7 + 7 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem RD.erc6909Swap5 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP5, .none)) (hov : t.length + 6 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (f :: b :: c :: d :: e :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => erc6909Swap5_xstep hc hp hdec hs hov)

theorem RD.erc6909Swap6 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f h : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: h :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP6, .none)) (hov : t.length + 7 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (h :: b :: c :: d :: e :: f :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => erc6909Swap6_xstep hc hp hdec hs hov)

-- PROMOTE -> Common.lean / Reasoning.Stepping: generic `DUP9` xstep.
theorem erc6909Dup9_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f h i j : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP9, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: h :: i :: j :: t)
    (hov : t.length + 10 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (j :: a :: b :: c :: d :: e :: f :: h :: i :: j :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP9, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_dup9 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: h :: i :: j :: t).length - 9 + 10 >
      1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem RD.erc6909Dup9 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f h i j : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: h :: i :: j :: t) mem aw
      rdata acc k C)
    (hdec : decode code pc = some (.DUP9, .none)) (hov : t.length + 10 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (j :: a :: b :: c :: d :: e :: f :: h :: i :: j :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => erc6909Dup9_xstep hc hp hdec hs hov)

/-! ## Local LOG4 reachability helper for the Approval event -/

-- PROMOTE -> Reasoning.Stepping
def erc6909StLog4 (s : State) (a b c d e f : UInt256) (t : List UInt256) : State :=
  {s with
    substate.logSeries := s.substate.logSeries.push
      ⟨s.executionEnv.codeOwner, #[c, d, e, f], s.machineState.memory.readWithPadding a.toNat b.toNat⟩
    machineState.stack := t
    machineState.activeWords :=
      UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable.subNat (memoryExpansionCost s .LOG4)).subNat
        (GasConstants.Glog + GasConstants.Glogdata * b.toNat
            + 4 * GasConstants.Glogtopic)
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1 }

-- PROMOTE -> Reasoning.Stepping
theorem erc6909Log4_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.LOG4, .none)) (hperm : s.executionEnv.perm = true)
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: t)
    (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat
            < memoryExpansionCost s .LOG4
              + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 4 * GasConstants.Glogtopic)
         then .error .OutOfGass else .ok (erc6909StLog4 s a b c d e f t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LOG4, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_log4 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: t).length - 6 + 0 > 1024) := by
    simp only [List.length_cons]
    omega
  have hpermF : (¬ s.executionEnv.perm = true) = False := eq_false (by simp [hperm])
  simp only [collapse_two_stage, if_neg hov', hpermF, if_false, erc6909StLog4]

-- PROMOTE -> Reasoning.Reach
theorem RD.erc6909Log4 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f : UInt256} {t : List UInt256} (mcost : ℕ) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG4, .none)) (hperm : ee.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: d :: e :: f :: t →
        memoryExpansionCost s .LOG4 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + 4 * GasConstants.Glogtopic))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata,
      hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .LOG4 = mcost := hmc s haw hstk
    have hperms : s.executionEnv.perm = true := by
      rw [hee]
      exact hperm
    have st := erc6909Log4_xstep hcode hpc hdec hperms hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost
        + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 4 * GasConstants.Glogtopic))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨erc6909StLog4 s a b c d e f t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          (by have : 1 ≤ GasConstants.Glog := (by decide); omega), by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [erc6909StLog4]
        exact hcode
      · simp only [erc6909StLog4]
        rw [hpc]
      · simp only [erc6909StLog4]
      · simp only [erc6909StLog4, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [erc6909StLog4]
        exact hmem
      · simp only [erc6909StLog4]
        rw [haw, hawout]
      · simp only [erc6909StLog4]
        exact hrdata
      · simp only [erc6909StLog4]
        exact hacc
      · simp only [erc6909StLog4]
        exact hee
      · simp only [erc6909StLog4]
        exact hworld

/-! ## EVM ABI decode traces for the approve body wrapper -/

-- PROMOTE -> Common.lean / Reasoning.Solc: ERC6909's optimizer-on inlined address decoder.
theorem erc6909DecodeAddrOk {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {off ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc6909BenchBytecode ee g s0 ⟨1629⟩ (off :: ret :: R) mem aw rdata acc k C)
    (hcanon : (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)).toNat <
      EVM.addressModulus)
    (hret : (D_J erc6909BenchBytecode 0).contains ret = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD erc6909BenchBytecode ee g s0 ret
      (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: R) mem aw rdata acc k' C' := by
  let word := uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)
  have hclean : UInt256.eq word (UInt256.land word solcAddrMask) = ⟨1⟩ :=
    solcAddrCanon_eq hcanon
  exact ⟨_, _, evm_run h with [
    jumpdest, dup1, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup2, and, dup2, eq, push2 ⟨1651⟩,
    jumpiT (by
      have hclean' :
          UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
            (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
              (UInt256.sub ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩) ⟨1⟩)) = ⟨1⟩ := by
        simpa [word, solcAddrMask, UInt256.sub] using hclean
      rw [hclean']
      decide) (by jump_dest),
    jumpdest, swap2, swap1, pop, jump hret ]⟩

-- PROMOTE -> Common.lean / Reasoning.Solc: revert branch for the same inlined address decoder.
theorem erc6909DecodeAddrRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {off ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD erc6909BenchBytecode ee g s0 ⟨1629⟩ (off :: ret :: R) mem aw rdata acc k C)
    (hnc : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)) solcAddrMask) =
        ⟨0⟩)
    (hov : R.length + 8 ≤ 1024) :
    RDrev erc6909BenchBytecode g s0 := by
  exact evm_run h with [
    jumpdest, dup1, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup2, and, dup2, eq, push2 ⟨1651⟩, jumpiNT (by
      simpa [solcAddrMask, UInt256.sub] using hnc),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909ApproveX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨228⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1742⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨242⟩, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push2 ⟨193⟩, push2 ⟨242⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1742⟩, jump (by jump_dest) ]⟩

theorem erc6909ApproveX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨228⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [approveAmountWord I, approveIdWord I, approveSpenderWord I, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    solcCalldataStaticLenCheckOk (words := 3) (by simpa using hsz100) hszhi hsize
  obtain ⟨k, C, rd1742⟩ := erc6909ApproveX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  have rd1629 := evm_run rd1742 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨1760⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push2 ⟨1769⟩, dup5, push2 ⟨1629⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd1769⟩ := erc6909DecodeAddrOk rd1629 hcanonSpender (by jump_dest)
    (by evm_ov)
  have rd1770 := evm_run rd1769 with [jumpdest]
  have rd1771 := RD.erc6909Swap6 rd1770 (by decide) (by simp)
  have rd1777 := evm_run rd1771 with [push1 ⟨32⟩, dup6, add, calldataload]
  have rd1778 := RD.erc6909Swap6 rd1777 (by decide) (by simp)
  have rd1781 := evm_run rd1778 with [pop, push1 ⟨64⟩, swap1]
  have rd1782 := RD.erc6909Swap5 rd1781 (by decide) (by simp)
  have rd242 := evm_run rd1782 with [
    add, calldataload, swap4, swap3, pop, pop, pop, jump (by jump_dest) ]
  have rd522 := evm_run rd242 with [jumpdest, push2 ⟨522⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [approveSpenderWord, approveIdWord, approveAmountWord, calldataWord] using rd522⟩

theorem erc6909ApproveX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨228⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ :=
    solcCalldataStaticLenCheckShort (words := 3) hsz4 (by simpa using hshort) hsize
      (by norm_num)
  obtain ⟨k, C, rd1742⟩ := erc6909ApproveX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd1742 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨1760⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909ApproveX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨228⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ :=
    solcCalldataStaticLenCheckHuge (words := 3) hbig hsize (by norm_num)
  obtain ⟨k, C, rd1742⟩ := erc6909ApproveX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  exact evm_run rd1742 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨1760⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909ApproveX_noncanon_spender {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (approveSpenderWord I)
      (UInt256.land (approveSpenderWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨228⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    solcCalldataStaticLenCheckOk (words := 3) (by simpa using hsz100) hszhi hsize
  obtain ⟨k, C, rd1742⟩ := erc6909ApproveX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach
  have rd1629 := evm_run rd1742 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨1760⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push2 ⟨1769⟩, dup5, push2 ⟨1629⟩, jump (by jump_dest) ]
  simpa [approveSpenderWord, calldataWord] using erc6909DecodeAddrRevert rd1629 hnc (by evm_ov)

/-! ## EVM trace for the approve body and `_approve` helper -/

def approveApprovalTopic : UInt256 :=
  ⟨0xb3fd5071835887567a0671151121894ddccc2842f1d10bedad13e0d17cace9a7⟩

def approveInvalidApproverSelectorWord : UInt256 :=
  UInt256.shiftLeft ⟨0x198ecd53⟩ ⟨227⟩

def approveInvalidSpenderSelectorWord : UInt256 :=
  UInt256.shiftLeft ⟨0x6f65f465⟩ ⟨224⟩

noncomputable def approveErrorMem (selector arg : UInt256) : ByteArray :=
  (UInt256.toByteArray arg).write 0 (solcReturnMem selector) 132 32

theorem approveErrorMem_size (selector arg : UInt256) :
    (approveErrorMem selector arg).size = 164 := by
  unfold approveErrorMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcReturnMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, solcReturnMem_size, toByteArray_size]
  omega

theorem approveErrorMem_read64 (selector arg : UInt256) :
    (approveErrorMem selector arg).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold approveErrorMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [solcReturnMem_size]; omega) (by omega),
    solcReturnMem_read64]

theorem approveErrorMem_mload64 (selector arg : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (approveErrorMem selector arg).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((approveErrorMem selector arg).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [approveErrorMem_size]; decide) (by decide)
    (approveErrorMem_read64 selector arg)

theorem erc6909ApproveX_toHelper {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨228⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨766⟩
      [approveAmountWord I, approveIdWord I, approveSpenderWord I, approveOwnerWord I,
        ⟨512⟩, ⟨0⟩, approveAmountWord I, approveIdWord I, approveSpenderWord I, ⟨193⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd522⟩ := erc6909ApproveX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonSpender hreach
  exact ⟨_, _, by
    simpa [approveOwnerWord] using evm_run rd522 with [
      jumpdest, push0, push2 ⟨512⟩, caller, dup6, dup6, dup6, push2 ⟨766⟩,
      jump (by jump_dest) ]⟩

theorem erc6909ApproveX_stored {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hsource : I.source ≠ AccountAddress.ofNat 0)
    (hspender : AccountAddress.ofNat (approveSpenderWord I).toNat ≠ AccountAddress.ofNat 0)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨228⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨900⟩
      [⟨32⟩, ⟨64⟩, approveOwnerWord I, approveSpenderWord I, approveAmountWord I,
        approveIdWord I, approveSpenderWord I, approveOwnerWord I, ⟨512⟩, ⟨0⟩,
        approveAmountWord I, approveIdWord I, approveSpenderWord I, ⟨193⟩, sel]
      (approveIdHashMem (approveOwnerWord I) (approveSpenderWord I) (approveIdWord I))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (approveSlotI I) (approveAmountWord I)) k C := by
  obtain ⟨_, _, rd766⟩ := erc6909ApproveX_toHelper (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonSpender hreach
  have hownerWordNZ : approveOwnerWord I ≠ ⟨0⟩ := by
    intro hzero
    exact hsource ((approveSource_zero_iff I).mpr hzero)
  have hspenderWordNZ : approveSpenderWord I ≠ ⟨0⟩ := by
    intro hzero
    exact hspender ((approveAccountAddress_ofNat_zero_iff hcanonSpender).mpr hzero)
  have rd848 := evm_run rd766 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    push2 ⟨807⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean (approveOwnerWord_canonical I)]
      exact hownerWordNZ)
      (by jump_dest),
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and,
    push2 ⟨848⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean hcanonSpender]
      exact hspenderWordNZ)
      (by jump_dest) ]
  have hslot := approveFinalKeccakSlot I hcanonSpender
  have rd876₀ := evm_run rd848 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, dup2, and,
    push0, dup2, dup2,
    raw mstore 0 (approveWordAt0Mem (approveOwnerWord I) solcFreePtrMem)
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean_left (approveOwnerWord_canonical I)]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨2⟩, push1 ⟨32⟩, swap1, dup2,
    raw mstore 0 (approveOwnerHashMem (approveOwnerWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (approveOwnerSlot (approveOwnerWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd877 := RD.erc6909Swap5 rd876₀ (by decide) (by evm_ov)
  have rd878 := RD.erc6909Dup9 rd877 (by decide) (by evm_ov)
  have rd882₀ := evm_run rd878 with [
    and, dup1, dup5,
    raw mstore 0 (approveWordAt0Mem (approveSpenderWord I)
        (approveOwnerHashMem (approveOwnerWord I)))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean hcanonSpender]
        rfl)
      (by decide) (by evm_ov) ]
  have rd883 := RD.erc6909Swap5 rd882₀ (by decide) (by evm_ov)
  have rd899 := evm_run rd883 with [
    dup3,
    raw mstore 0 (approveSpenderHashMem (approveOwnerWord I) (approveSpenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    dup1, dup4,
    raw keccak256 0 (approveSpenderSlot (approveOwnerWord I) (approveSpenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup8, dup5,
    raw mstore 0 (approveWordAt0Mem (approveIdWord I)
        (approveSpenderHashMem (approveOwnerWord I) (approveSpenderWord I)))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    dup3,
    raw mstore 0 (approveIdHashMem (approveOwnerWord I) (approveSpenderWord I)
        (approveIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    swap2, dup3, swap1,
    raw keccak256 0 (approveSlotI I) (UInt256.ofNat 3)
      (by decide) mem_cost hslot (by decide) (by evm_ov),
    dup6, swap1 ]
  have rd899' := rd899
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide,
    solcAddrMask_clean_left (approveOwnerWord_canonical I),
    solcAddrMask_clean hcanonSpender] at rd899'
  simpa using rd899'.sstore hperm (by decide) (by evm_ov)

theorem erc6909ApproveX_revert_owner {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hsource : I.source = AccountAddress.ofNat 0)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨228⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd766⟩ := erc6909ApproveX_toHelper (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonSpender hreach
  have hownerZeroWord : approveOwnerWord I = ⟨0⟩ := (approveSource_zero_iff I).mp hsource
  have rd781 := evm_run rd766 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    push2 ⟨807⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [hownerZeroWord]
      decide) ]
  exact evm_run rd781 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x198ecd53⟩, push1 ⟨227⟩, shl, dup2,
    raw mstore 6 (solcReturnMem approveInvalidApproverSelectorWord)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push0, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (approveErrorMem approveInvalidApproverSelectorWord ⟨0⟩)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (approveErrorMem_mload64 approveInvalidApproverSelectorWord ⟨0⟩)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909ApproveX_revert_spender {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hsource : I.source ≠ AccountAddress.ofNat 0)
    (hspender : AccountAddress.ofNat (approveSpenderWord I).toNat = AccountAddress.ofNat 0)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨228⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd766⟩ := erc6909ApproveX_toHelper (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonSpender hreach
  have hownerWordNZ : approveOwnerWord I ≠ ⟨0⟩ := by
    intro hzero
    exact hsource ((approveSource_zero_iff I).mpr hzero)
  have hspenderZeroWord : approveSpenderWord I = ⟨0⟩ :=
    (approveAccountAddress_ofNat_zero_iff hcanonSpender).mp hspender
  have rd822 := evm_run rd766 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup5, and,
    push2 ⟨807⟩,
    jumpiT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [solcAddrMask_clean (approveOwnerWord_canonical I)]
      exact hownerWordNZ)
      (by jump_dest),
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and,
    push2 ⟨848⟩,
    jumpiNT (by
      rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      rw [hspenderZeroWord]
      decide) ]
  exact evm_run rd822 with [
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    push4 ⟨0x6f65f465⟩, push1 ⟨224⟩, shl, dup2,
    raw mstore 6 (solcReturnMem approveInvalidSpenderSelectorWord)
      (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push0, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (approveErrorMem approveInvalidSpenderSelectorWord ⟨0⟩)
      (UInt256.ofNat 6) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨36⟩, add, push2 ⟨698⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost (approveErrorMem_mload64 approveInvalidSpenderSelectorWord ⟨0⟩)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov) ]

theorem erc6909X_approve {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hperm : I.perm = true)
    (hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus)
    (hsource : I.source ≠ AccountAddress.ofNat 0)
    (hspender : AccountAddress.ofNat (approveSpenderWord I).toNat ≠ AccountAddress.ofNat 0)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨228⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (approveSlotI I) (approveAmountWord I))
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd900⟩ := erc6909ApproveX_stored (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hperm hcanonSpender hsource hspender hreach
  have rd951 := evm_run rd900 with [
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (approveIdHashMem_mload64 (approveOwnerWord I) (approveSpenderWord I)
        (approveIdWord I))
      (by decide) (by evm_ov),
    dup5, dup2,
    raw mstore 6 (approveEventMem (approveOwnerWord I) (approveSpenderWord I)
        (approveIdWord I) (approveAmountWord I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    dup6, swap4, swap3, swap2 ]
  have rd942 := rd951.pushConst approveApprovalTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd951Log := evm_run rd942 with [
    swap2, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (approveEventMem_mload64 (approveOwnerWord I) (approveSpenderWord I)
        (approveIdWord I) (approveAmountWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  have rd952 := RD.erc6909Log4 0 (UInt256.ofNat 5) rd951Log (by decide) hperm
    mem_cost (by decide) (by evm_ov)
  have rd512 := evm_run rd952 with [
    pop, pop, pop, pop, jump (by jump_dest) ]
  have rd193 := evm_run rd512 with [
    jumpdest, pop, push1 ⟨1⟩, swap4, swap3, pop, pop, pop, jump (by jump_dest) ]
  have rd165 := evm_run rd193 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (approveEventMem_mload64 (approveOwnerWord I) (approveSpenderWord I)
        (approveIdWord I) (approveAmountWord I))
      (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 0 (approveReturnMem (approveOwnerWord I) (approveSpenderWord I)
        (approveIdWord I) (approveAmountWord I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by
        rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨165⟩, jump (by jump_dest) ]
  exact evm_run rd165 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (approveReturnMem_mload64 (approveOwnerWord I) (approveSpenderWord I)
        (approveIdWord I) (approveAmountWord I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
            from by decide]
        change (approveReturnMem (approveOwnerWord I) (approveSpenderWord I)
            (approveIdWord I) (approveAmountWord I)).readWithPadding 128 32 =
          UInt256.toByteArray (⟨1⟩ : UInt256)
        exact approveReturnMem_read128 (approveOwnerWord I) (approveSpenderWord I)
          (approveIdWord I) (approveAmountWord I))
      (by evm_ov) ]

theorem erc6909ApproveBodyCore
    {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = erc6909BenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (erc6909SelBytes 3))
    (hreach : ∃ k C, RD erc6909BenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I) ⟨228⟩
      [erc6909SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  have hselApprove : selIs I ⟨#[0x42, 0x6a, 0x84, 0x93]⟩ := by
    simpa [erc6909SelBytes] using hsel
  have hsz4 := erc6909ApproveSelector_size hselApprove
  have hd := erc6909Dispatch_approve (cd := I.calldata) hselApprove
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonSpender : (approveSpenderWord I).toNat < EVM.addressModulus
      · have hdec := erc6909Decode_approve_ok (I := I) hsz100 hbig hcanonSpender
        let evmE := initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I
        let evmS := initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I
        have hσ : EVMStateEquiv evmE evmS := by
          simpa [evmE, evmS] using EVMStateEquiv.initState (g := Sat256.ofUInt256 g)
            hAccounts
        by_cases hsource : I.source = AccountAddress.ofNat 0
        · have hbody :
              ExecTransitionBody config contract evmS (approveStore I)
                approveTransition.body .reverted := by
            simpa [evmS, initState] using erc6909ApproveBodyReverts_sender evmS
              (by simp only [evmS, initState]; exact hwv)
              (by simpa [evmS, initState] using hsource)
          exact (erc6909ApproveX_revert_owner (g := Sat256.ofUInt256 g)
              hsz100 hsize hbig hcanonSpender hsource hreach)
            |>.reEquivExecutionRevert hcode hd hdec hbody
        · by_cases hspender :
            AccountAddress.ofNat (approveSpenderWord I).toNat = AccountAddress.ofNat 0
          · have hbody :
                ExecTransitionBody config contract evmS (approveStore I)
                  approveTransition.body .reverted := by
              simpa [evmS, initState] using erc6909ApproveBodyReverts_spender evmS
                (by simp only [evmS, initState]; exact hwv)
                (by simpa [evmS, initState] using hsource)
                (by simpa [evmS, initState] using hspender)
            exact (erc6909ApproveX_revert_spender (g := Sat256.ofUInt256 g)
                hsz100 hsize hbig hcanonSpender hsource hspender hreach)
              |>.reEquivExecutionRevert hcode hd hdec hbody
          · have hbody :
                ExecTransitionBody config contract evmS (approveStore I)
                  approveTransition.body
                  (.returned { contract := contract, locals := approveStore I }
                    (approvePostState evmS I) (some (.bool true))) := by
              simpa [evmS, initState] using erc6909ApproveBodyReturns evmS
                (by simp only [evmS, initState]; exact hwv)
                (by simpa [evmS, initState] using hsource)
                (by simpa [evmS, initState] using hspender)
            have hσPost : EVMStateEquiv (approvePostState evmE I) (approvePostState evmS I) := by
              unfold approvePostState approveSlot
              rw [hσ.executionEnv]
              exact erc6909EVMStateEquivStorageStoreCodeOwner hσ
                (allowanceSlot (.address evmS.executionEnv.source)
                  (.address (AccountAddress.ofNat (approveSpenderWord I).toNat))
                  (.int (Int.ofNat (approveIdWord I).toNat))) rfl
            exact (erc6909X_approve (g := Sat256.ofUInt256 g)
                hsz100 hsize hbig hperm hcanonSpender hsource hspender hreach)
              |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
                (by simp [evmE, approvePostState, approveSlot, initState,
                  storageStore_createdAccounts])
                (accountMapEquiv.of_eq (by
                  simp [evmE, approvePostState, approveSlot, approveSlotI, initState,
                    storageStore_accountMap]))
                hσPost
                (returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding))
      · have hdec := erc6909Decode_approve_none_noncanon (I := I)
          hsz100 hbig hcanonSpender
        have hnc : UInt256.eq (approveSpenderWord I)
            (UInt256.land (approveSpenderWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanonSpender (solcAddrCanonical_of_clean he))
        exact (erc6909ApproveX_noncanon_spender (g := Sat256.ofUInt256 g)
            hsz100 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := erc6909Decode_approve_none_huge (I := I) hbigge
      exact (erc6909ApproveX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 100 := by omega
    have hdec := erc6909Decode_approve_none_short (I := I) hsz4 hshort
    exact (erc6909ApproveX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end OpenZeppelinBench.ERC6909
