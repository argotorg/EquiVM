import Examples.UniswapV2Pair.Bytecode
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Refinement
import Reasoning.Solc
import Reasoning.SolmBody
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Reasoning.Theory

-- GENERALIZES Reasoning.Solc.fromBytes'_drop1_take20_wordLE_solcAddrMask — same little-endian
-- byte-slice arithmetic, parameterized by byte offset and slice width.
-- LIBRARY CANDIDATE: Reasoning.Solc — packed storage byte-slice-to-mask/division bridge.
set_option maxHeartbeats 1000000 in
theorem fromBytes'_drop_take_wordLE_land_div_mask (w : UInt256) (off size : Nat)
    (hoff : 8 * off < 256) (hsize : 8 * size ≤ 256) :
    fromBytes' (((EVM.Word.toBytesLEWithSizeProof w).1.drop off).take size) =
      (UInt256.land (UInt256.div w (UInt256.ofNat (256 ^ off)))
        (UInt256.ofNat (256 ^ size - 1))).toNat := by
  let bs := (EVM.Word.toBytesLEWithSizeProof w).1
  have hfull : Nat.ofDigits 256 (bs.map (fun b : UInt8 => b.toNat)) = w.toNat := by
    rw [← fromBytes'_eq_ofDigits bs]
    exact fromBytes'_toBytesLEWithSizeProof w
  have hlt : ∀ l ∈ bs.map (fun b : UInt8 => b.toNat), l < 256 := by
    intro l hl
    simp only [List.mem_map] at hl
    rcases hl with ⟨b, _hb, rfl⟩
    exact b.toFin.isLt
  have hdrop := Nat.ofDigits_div_pow_eq_ofDigits_drop (p := 256) off (by decide)
    (bs.map (fun b : UInt8 => b.toNat)) hlt
  have htake := Nat.ofDigits_mod_pow_eq_ofDigits_take (p := 256) size (by decide)
    ((bs.map (fun b : UInt8 => b.toNat)).drop off)
    (fun l hl => hlt l (List.mem_of_mem_drop hl))
  rw [fromBytes'_eq_ofDigits (((EVM.Word.toBytesLEWithSizeProof w).1.drop off).take size)]
  change Nat.ofDigits 256 ((((bs.drop off).take size).map fun b : UInt8 => b.toNat)) = _
  rw [List.map_take, List.map_drop, ← htake, ← hdrop, hfull]
  have hshiftNat : (UInt256.ofNat (256 ^ off)).toNat = 256 ^ off := by
    rw [show 256 ^ off = (2 : Nat) ^ (8 * off) by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
    exact ofNat_pow_toNat hoff
  have hdivNat : (UInt256.div w (UInt256.ofNat (256 ^ off))).toNat =
      w.toNat / 256 ^ off := by
    unfold UInt256.div UInt256.toNat
    simp only
    change w.toNat / (UInt256.ofNat (256 ^ off)).toNat = w.toNat / 256 ^ off
    rw [hshiftNat]
  rw [uland_toNat, hdivNat]
  have hmaskNat : (UInt256.ofNat (256 ^ size - 1)).toNat = 256 ^ size - 1 := by
    have hmaskLt : 256 ^ size - 1 < UInt256.size := by
      have hpow : 256 ^ size ≤ UInt256.size := by
        rw [show 256 ^ size = (2 : Nat) ^ (8 * size) by
          rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
        simpa [UInt256.size] using
          Nat.pow_le_pow_right (by norm_num : 0 < (2 : Nat)) hsize
      have hpos : 0 < 256 ^ size := by positivity
      omega
    exact ulit_toNat' _ hmaskLt
  rw [hmaskNat]
  rw [show 256 ^ size = (2 : Nat) ^ (8 * size) by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
  symm
  exact nat_land_mask_eq_mod (w.toNat / 256 ^ off) (8 * size)

-- LIBRARY CANDIDATE: Reasoning.Storage — transport a storage `findD` disequality across
-- `accountMapEquiv`, dual to `accountMapEquiv_storage_findD`.
theorem accountMapEquiv_storage_findD_ne {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) (addr : AccountAddress) (slot default val : UInt256)
    (h :
      ((σ.find? addr).option default (fun acc => acc.storage.findD slot default)) ≠ val) :
    ((τ.find? addr).option default (fun acc => acc.storage.findD slot default)) ≠ val := by
  intro hbad
  exact h ((accountMapEquiv_storage_findD hστ addr slot default).trans hbad)

-- LIBRARY CANDIDATE: Reasoning.Storage — normalize a code-owner `initState` storage load and
-- transport a disequality across `accountMapEquiv`.
theorem initState_codeOwner_storageLoad_ne_of_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (slot val : UInt256) (hAccounts : accountMapEquiv σ_evm σ_solm)
    (h :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD slot ⟨0⟩)) ≠ val) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner slot ≠ val := by
  have hword := accountMapEquiv_storage_findD_ne hAccounts I.codeOwner slot ⟨0⟩ val h
  simpa [initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage] using hword

-- LIBRARY CANDIDATE: Reasoning.SolmBody — `FunctionDecl` analogue of
-- `internalCallTransitionReturn`, for internal/private Solidity helper calls.
theorem internalCallFunctionReturn {cfg : Config} {caller : Frame} {evm calleeEvm : EVM.State}
    {name retVar : Ident} {args : List Expr} {argVals : List Value}
    {callee : FunctionDecl} {locals : Store} {calleeSolm : Frame} {value : Option Value}
    (hargs : evalExprs? cfg caller evm args = .ok argVals)
    (hlookup : lookupCallable? caller.contract name = some callee.toCallable)
    (hbind : bindParams? callee.params argVals = some locals)
    (hbody : ExecFuncBody cfg { caller with locals := locals } evm callee.body
      (.returned calleeSolm calleeEvm value)) :
    ExecStmt cfg caller evm (.internalCall name args retVar)
      (.ok (resumeAfterInternalCall caller retVar value) calleeEvm) := by
  exact ExecStmt.internalCallReturn (cfg := cfg) (solm := caller) (evm := evm)
    (name := name) (args := args) (retVar := retVar) (argVals := argVals)
    (callee := callee.toCallable) (locals := locals) (calleeSolm := calleeSolm)
    (calleeEvm := calleeEvm) (value := value)
    hargs hlookup (by simpa [FunctionDecl.toCallable] using hbind)
    (by simpa [FunctionDecl.toCallable] using hbody)

-- LIBRARY CANDIDATE: Reasoning.SolmBody — `FunctionDecl` analogue of
-- `internalCallTransitionRevert`, for internal/private Solidity helper calls.
theorem internalCallFunctionRevert {cfg : Config} {caller : Frame} {evm : EVM.State}
    {name retVar : Ident} {args : List Expr} {argVals : List Value}
    {callee : FunctionDecl} {locals : Store}
    (hargs : evalExprs? cfg caller evm args = .ok argVals)
    (hlookup : lookupCallable? caller.contract name = some callee.toCallable)
    (hbind : bindParams? callee.params argVals = some locals)
    (hbody : ExecFuncBody cfg { caller with locals := locals } evm callee.body .reverted) :
    ExecStmt cfg caller evm (.internalCall name args retVar) .reverted := by
  exact ExecStmt.internalCallRevert (cfg := cfg) (solm := caller) (evm := evm)
    (name := name) (args := args) (retVar := retVar) (argVals := argVals)
    (callee := callee.toCallable) (locals := locals)
    hargs hlookup (by simpa [FunctionDecl.toCallable] using hbind)
    (by simpa [FunctionDecl.toCallable] using hbody)

end Reasoning.Theory

namespace UniswapV2Pair

/-! # Shared Uniswap V2 Pair proof helpers -/

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev uniswapSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-! ## Shared caller/address helpers -/

-- LIBRARY CANDIDATE: Reasoning.Solc — canonical EVM `CALLER` word and address round-trip helpers.
abbrev uniswapSourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

theorem uniswapSourceWord_toNat (I : ExecutionEnv) :
    (uniswapSourceWord I).toNat = I.source.val := by
  unfold uniswapSourceWord
  exact ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem uniswapSourceWord_canonical (I : ExecutionEnv) :
    (uniswapSourceWord I).toNat < EVM.addressModulus := by
  rw [uniswapSourceWord_toNat]
  change I.source.val < AccountAddress.size
  exact I.source.isLt

theorem uniswapSource_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (uniswapSourceWord I).toNat = I.source := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [uniswapSourceWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt I.source.isLt

theorem uniswapMaskedAddress_eq_source_of_word_eq {w : UInt256} {I : ExecutionEnv}
    (h : UInt256.land w solcAddrMask = uniswapSourceWord I) :
    AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat = I.source := by
  rw [h, uniswapSource_ofNat]

/-! ## Shared scalar storage and return helpers -/

theorem uniswapStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (addrLoc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  simpa [addrLoc, addressOffset0Loc] using storageLocLoad_address_offset0 evm slot

-- LIBRARY CANDIDATE: Reasoning.Storage — full-slot address storage writes through
-- a `storageLocStore` view.
theorem uniswapStorageLocStore_address_offset0 (evm : EVM.State)
    (slot addr : UInt256) (hcanon : addr.toNat < EVM.addressModulus) :
    storageLocStore evm (addrLoc slot)
        (.address (AccountAddress.ofNat addr.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) addr)) := by
  simpa [addrLoc, addressOffset0Loc] using
    storageLocStore_address_offset0 evm slot addr hcanon

theorem uniswapStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc] using storageLocLoad_uint256 evm slot

-- LIBRARY CANDIDATE: Reasoning.SolmBody — canonical Solm integer value for a `UInt256` word.
abbrev uniswapUint256Value (w : UInt256) : Value :=
  .int (Int.ofNat w.toNat)

-- LIBRARY CANDIDATE: Reasoning.Storage — full-slot uint256 storage writes through
-- a `storageLocStore` view.
theorem uniswapStorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (wordLoc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  simpa [wordLoc, uint256Loc] using storageLocStore_uint256 evm slot val

theorem uniswapStorageLocLoad_bytes32 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (bytes32Loc slot) =
      .fixedBytes ⟨31, by decide⟩
        (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  simpa [bytes32Loc, Reasoning.Theory.bytes32Loc] using storageLocLoad_bytes32 evm slot

/-! ## Shared reentrancy-lock source helpers -/

def uniswapUnlockedState (evm : EVM.State) (val : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨12⟩ val

def uniswapLockEnteredState (evm : EVM.State) : EVM.State :=
  uniswapUnlockedState evm ⟨0⟩

def uniswapLockExitedState (evm : EVM.State) : EVM.State :=
  uniswapUnlockedState evm ⟨1⟩

theorem evalStorageRef_uniswap_unlocked (evm : EVM.State) (locals : Store) :
    evalStorageRef config { contract := contract, locals := locals } evm unlockedRef =
      .ok ({ base := "unlocked", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, unlockedRef, EvalResult.bind, pure, bind]

theorem evalExpr_uniswap_unlocked (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "unlocked" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage unlockedRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint256Int)
    (hbase := by simpa [unlockedRef] using hbase)
    (her := evalStorageRef_uniswap_unlocked evm locals)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)]
  exact congrArg EvalResult.ok (uniswapStorageLocLoad_uint256 evm ⟨12⟩)

theorem evalExpr_uniswap_unlocked_eq_one_true (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "unlocked" = none)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage unlockedRef) (.intLit 1)) = .ok (.bool true) := by
  simp only [evalExpr?, evalExpr_uniswap_unlocked evm locals hbase, EvalResult.bind, bind, pure,
    evalBinaryOp?]
  rw [hunlocked]
  rfl

theorem evalExpr_uniswap_unlocked_eq_one_false (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "unlocked" = none)
    (hlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage unlockedRef) (.intLit 1)) = .ok (.bool false) := by
  have hval :
      (Value.int
          (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩).toNat) ==
        Value.int 1) = false := by
    rw [beq_eq_false_iff_ne]
    intro hvalue
    rw [Value.int.injEq] at hvalue
    apply hlocked
    have hnat : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩).toNat = 1 := by
      exact Int.ofNat.inj hvalue
    calc
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩
          = UInt256.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩).toNat := by
              exact (u256_ofNat_toNat _).symm
      _ = UInt256.ofNat 1 := by rw [hnat]
      _ = ⟨1⟩ := by native_decide
  simp only [evalExpr?, evalExpr_uniswap_unlocked evm locals hbase, EvalResult.bind, bind, pure,
    evalBinaryOp?, hval]

theorem uniswapAssignUnlocked (evm : EVM.State) (locals : Store) (val : UInt256)
    (hbase : locals.get? "unlocked" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm .storage unlockedRef
      (.int (Int.ofNat val.toNat)) =
        .ok ({ contract := contract, locals := locals }, uniswapUnlockedState evm val) := by
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := by simpa [unlockedRef] using hbase)
      (her := evalStorageRef_uniswap_unlocked evm locals)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [uniswapUnlockedState] using uniswapStorageLocStore_uint256 evm ⟨12⟩ val

theorem uniswapAssignUnlockedZero (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "unlocked" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm .storage unlockedRef
      (.int 0) =
        .ok ({ contract := contract, locals := locals }, uniswapLockEnteredState evm) := by
  simpa [uniswapLockEnteredState] using uniswapAssignUnlocked evm locals ⟨0⟩ hbase

theorem uniswapAssignUnlockedOne (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "unlocked" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm .storage unlockedRef
      (.int 1) =
        .ok ({ contract := contract, locals := locals }, uniswapLockExitedState evm) := by
  simpa [uniswapLockExitedState] using uniswapAssignUnlocked evm locals ⟨1⟩ hbase

-- LIBRARY CANDIDATE: Reasoning.SolmBody — generic source-side reentrancy-lock entry prefix,
-- parameterized by guard storage ref, slot, open word, and locked word.
theorem uniswapLockEnterPrefix (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? "unlocked" = none)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩) :
    ExecBlock config { contract := contract, locals := locals } evm lockEnter
      (.ok { contract := contract, locals := locals } (uniswapLockEnteredState evm)) := by
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .require (.binary .eq (.storage unlockedRef) (.intLit 1)),
      .assign .storage unlockedRef (.intLit 0) ]
    (.ok { contract := contract, locals := locals } (uniswapLockEnteredState evm))
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_uniswap_unlocked_eq_one_true evm locals hbase hunlocked)) ?_
  exact ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (uniswapAssignUnlockedZero evm locals hbase))
    ExecBlock.nil

-- LIBRARY CANDIDATE: Reasoning.SolmBody — generic source-side reentrancy-lock entry revert
-- cases, parameterized by guard storage ref, slot, open word, and locked word.
theorem uniswapLockEnterNonpayableRevert (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := locals } evm lockEnter .reverted := by
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .require (.binary .eq (.storage unlockedRef) (.intLit 1)),
      .assign .storage unlockedRef (.intLit 0) ]
    .reverted
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalCallvalueEq_false hwv))

theorem uniswapLockEnterLockedRevert (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? "unlocked" = none)
    (hlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ ≠ ⟨1⟩) :
    ExecBlock config { contract := contract, locals := locals } evm lockEnter .reverted := by
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .require (.binary .eq (.storage unlockedRef) (.intLit 1)),
      .assign .storage unlockedRef (.intLit 0) ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_uniswap_unlocked_eq_one_false evm locals hbase hlocked))

-- LIBRARY CANDIDATE: Reasoning.SolmBody — generic source-side reentrancy-lock exit suffix,
-- parameterized by guard storage ref, slot, and unlocked word.
theorem uniswapLockExitSuffix (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "unlocked" = none) :
    ExecBlock config { contract := contract, locals := locals } evm lockExit
      (.ok { contract := contract, locals := locals } (uniswapLockExitedState evm)) := by
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .assign .storage unlockedRef (.intLit 1) ]
    (.ok { contract := contract, locals := locals } (uniswapLockExitedState evm))
  exact ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (uniswapAssignUnlockedOne evm locals hbase))
    ExecBlock.nil

/-! ## Packed reserve-slot helpers -/

abbrev reserve112Shift : UInt256 := UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩
abbrev reserve112Mask : UInt256 := UInt256.sub reserve112Shift ⟨1⟩
abbrev reserve224Shift : UInt256 := UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩
abbrev reserve32Mask : UInt256 := ⟨4294967295⟩

-- LIBRARY CANDIDATE: Reasoning.Storage — packed unsigned-integer storage loads at byte offsets.
theorem uniswapStorageLocLoad_uint112_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint112Loc0 slot) =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) reserve112Mask).toNat) := by
  unfold storageLocLoad uint112Loc0 wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  change Value.int (Int.ofNat (fromBytes' (((EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1).extract 0 14))) = _
  rw [List.extract_eq_take_drop, List.drop_zero]
  rw [fromBytes'_take_wordLE_land_mask _ 14 (by decide)]
  rw [show UInt256.ofNat (2 ^ (8 * 14) - 1) = reserve112Mask by native_decide]

-- LIBRARY CANDIDATE: Reasoning.Storage — packed unsigned-integer storage loads at byte offsets.
theorem uniswapStorageLocLoad_uint112_offset14 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint112Loc14 slot) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          reserve112Shift) reserve112Mask).toNat) := by
  unfold storageLocLoad uint112Loc14 wordToElem
  change Value.int (Int.ofNat (fromBytes' (((EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1).extract 14 28))) = _
  rw [List.extract_eq_take_drop]
  rw [fromBytes'_drop_take_wordLE_land_div_mask _ 14 14 (by decide) (by decide)]
  rw [show UInt256.ofNat (256 ^ 14) = reserve112Shift by native_decide]
  rw [show UInt256.ofNat (256 ^ 14 - 1) = reserve112Mask by native_decide]

-- LIBRARY CANDIDATE: Reasoning.Storage — packed unsigned-integer storage loads at byte offsets.
theorem uniswapStorageLocLoad_uint32_offset28 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint32Loc28 slot) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          reserve224Shift) reserve32Mask).toNat) := by
  unfold storageLocLoad uint32Loc28 wordToElem
  change Value.int (Int.ofNat (fromBytes' (((EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1).extract 28 32))) = _
  rw [List.extract_eq_take_drop]
  rw [fromBytes'_drop_take_wordLE_land_div_mask _ 28 4 (by decide) (by decide)]
  rw [show UInt256.ofNat (256 ^ 28) = reserve224Shift by native_decide]
  rw [show UInt256.ofNat (256 ^ 4 - 1) = reserve32Mask by native_decide]

abbrev uniswapReserve0Word (evm : EVM.State) : UInt256 :=
  UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩) reserve112Mask

abbrev uniswapReserve1Word (evm : EVM.State) : UInt256 :=
  UInt256.land
    (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩) reserve112Shift)
    reserve112Mask

-- LIBRARY CANDIDATE: Reasoning.SolmBody — packed unsigned-integer storage expression evaluator
-- for a scalar storage reference whose layout uses a byte-offset storage location.
theorem evalExpr_uniswap_storage_uint112_offset0 (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint112Int)))
    (hloc : config.storage.layout er = fun _ => some (uint112Loc0 slot)) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage ref) =
      .ok (.int (Int.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          reserve112Mask).toNat)) := by
  rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
  exact congrArg EvalResult.ok (uniswapStorageLocLoad_uint112_offset0 evm slot)

-- LIBRARY CANDIDATE: Reasoning.SolmBody — packed unsigned-integer storage expression evaluator
-- for a scalar storage reference whose layout uses a nonzero byte-offset storage location.
theorem evalExpr_uniswap_storage_uint112_offset14 (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint112Int)))
    (hloc : config.storage.layout er = fun _ => some (uint112Loc14 slot)) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage ref) =
      .ok (.int (Int.ofNat
        (UInt256.land (UInt256.div
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) reserve112Shift)
          reserve112Mask).toNat)) := by
  rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
  exact congrArg EvalResult.ok (uniswapStorageLocLoad_uint112_offset14 evm slot)

theorem evalExpr_uniswap_reserve0 (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "reserve0" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage reserve0Ref) =
      .ok (.int (Int.ofNat (uniswapReserve0Word evm).toNat)) := by
  exact evalExpr_uniswap_storage_uint112_offset0
    (evm := evm) (locals := locals)
    (ref := reserve0Ref) (er := { base := "reserve0", steps := [] }) (slot := ⟨8⟩)
    (by simpa [reserve0Ref] using hbase)
    (by simp [evalStorageRef, evalStorageRefSteps, reserve0Ref, EvalResult.bind, pure, bind])
    (by rfl) (by rfl)

theorem evalExpr_uniswap_reserve1 (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "reserve1" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage reserve1Ref) =
      .ok (.int (Int.ofNat (uniswapReserve1Word evm).toNat)) := by
  exact evalExpr_uniswap_storage_uint112_offset14
    (evm := evm) (locals := locals)
    (ref := reserve1Ref) (er := { base := "reserve1", steps := [] }) (slot := ⟨8⟩)
    (by simpa [reserve1Ref] using hbase)
    (by simp [evalStorageRef, evalStorageRefSteps, reserve1Ref, EvalResult.bind, pure, bind])
    (by rfl) (by rfl)

theorem evalStorageRef_uniswap_reserve0 (evm : EVM.State) (locals : Store) :
    evalStorageRef config { contract := contract, locals := locals } evm reserve0Ref =
      .ok ({ base := "reserve0", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, reserve0Ref, EvalResult.bind, pure, bind]

theorem evalStorageRef_uniswap_reserve1 (evm : EVM.State) (locals : Store) :
    evalStorageRef config { contract := contract, locals := locals } evm reserve1Ref =
      .ok ({ base := "reserve1", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, reserve1Ref, EvalResult.bind, pure, bind]

theorem evalStorageRef_uniswap_blockTimestampLast (evm : EVM.State) (locals : Store) :
    evalStorageRef config { contract := contract, locals := locals } evm blockTimestampLastRef =
      .ok ({ base := "blockTimestampLast", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, blockTimestampLastRef, EvalResult.bind, pure, bind]

-- LIBRARY CANDIDATE: Reasoning.Storage — packed unsigned-integer storage writes are defined for
-- scalar integer values at byte offsets.
theorem uniswapStorageLocStore_uint112_offset0_int_some
    (evm : EVM.State) (slot : UInt256) (n : Int) :
    ∃ evm', storageLocStore evm (uint112Loc0 slot) (.int n) = some evm' := by
  unfold storageLocStore storageLocWriteWord uint112Loc0
  simp only [valueToWord, bind, Option.bind, pure]
  exact ⟨_, rfl⟩

-- LIBRARY CANDIDATE: Reasoning.Storage — packed unsigned-integer storage writes are defined for
-- scalar integer values at nonzero byte offsets.
theorem uniswapStorageLocStore_uint112_offset14_int_some
    (evm : EVM.State) (slot : UInt256) (n : Int) :
    ∃ evm', storageLocStore evm (uint112Loc14 slot) (.int n) = some evm' := by
  unfold storageLocStore storageLocWriteWord uint112Loc14
  simp only [valueToWord, bind, Option.bind, pure]
  exact ⟨_, rfl⟩

-- LIBRARY CANDIDATE: Reasoning.Storage — packed unsigned-integer storage writes are defined for
-- scalar integer values at nonzero byte offsets.
theorem uniswapStorageLocStore_uint32_offset28_int_some
    (evm : EVM.State) (slot : UInt256) (n : Int) :
    ∃ evm', storageLocStore evm (uint32Loc28 slot) (.int n) = some evm' := by
  unfold storageLocStore storageLocWriteWord uint32Loc28
  simp only [valueToWord, bind, Option.bind, pure]
  exact ⟨_, rfl⟩

theorem uniswapAssignReserve0OfStore (evm evm' : EVM.State) (locals : Store)
    (balance0 : UInt256)
    (hbase : locals.get? "reserve0" = none)
    (hstore :
      storageLocStore evm (uint112Loc0 ⟨8⟩) (uniswapUint256Value balance0) = some evm') :
    assignStorageRef? config { contract := contract, locals := locals } evm .storage reserve0Ref
      (uniswapUint256Value balance0) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  apply assignStorageRef_storage_scalar_value
      (er := ({ base := "reserve0", steps := [] } : EvaledStorageRef))
      (ty := uint112St) (loc := uint112Loc0 ⟨8⟩)
  · simpa [reserve0Ref] using hbase
  · exact evalStorageRef_uniswap_reserve0 evm locals
  · rfl
  · rfl
  · simp
  · exact hstore

theorem uniswapAssignReserve1OfStore (evm evm' : EVM.State) (locals : Store)
    (balance1 : UInt256)
    (hbase : locals.get? "reserve1" = none)
    (hstore :
      storageLocStore evm (uint112Loc14 ⟨8⟩) (uniswapUint256Value balance1) = some evm') :
    assignStorageRef? config { contract := contract, locals := locals } evm .storage reserve1Ref
      (uniswapUint256Value balance1) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  apply assignStorageRef_storage_scalar_value
      (er := ({ base := "reserve1", steps := [] } : EvaledStorageRef))
      (ty := uint112St) (loc := uint112Loc14 ⟨8⟩)
  · simpa [reserve1Ref] using hbase
  · exact evalStorageRef_uniswap_reserve1 evm locals
  · rfl
  · rfl
  · simp
  · exact hstore

theorem uniswapAssignBlockTimestampLastOfStore (evm evm' : EVM.State) (locals : Store)
    (value : Value)
    (hbase : locals.get? "blockTimestampLast" = none)
    (hscalar : match value with | .struct _ _ | .array _ => False | _ => True)
    (hstore : storageLocStore evm (uint32Loc28 ⟨8⟩) value = some evm') :
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      blockTimestampLastRef value = .ok ({ contract := contract, locals := locals }, evm') := by
  apply assignStorageRef_storage_scalar_value
      (er := ({ base := "blockTimestampLast", steps := [] } : EvaledStorageRef))
      (ty := uint32St) (loc := uint32Loc28 ⟨8⟩)
  · simpa [blockTimestampLastRef] using hbase
  · exact evalStorageRef_uniswap_blockTimestampLast evm locals
  · rfl
  · rfl
  · exact hscalar
  · exact hstore

def uniswapSlotWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)

abbrev uniswapAddressReturnWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (uniswapSlotWord slot σ I) solcAddrMask

abbrev uniswapAddressAtSlot (evm : EVM.State) (slot : UInt256) : AccountAddress :=
  AccountAddress.ofNat
    (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) solcAddrMask).toNat

-- LIBRARY CANDIDATE: Reasoning.SolmBody — generic scalar address-storage expression evaluator,
-- parameterized by config, contract, storage ref, and concrete address storage location.
theorem evalExpr_uniswap_storage_address (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot)) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage ref) =
      .ok (.address (uniswapAddressAtSlot evm slot)) := by
  rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
  exact congrArg EvalResult.ok (uniswapStorageLocLoad_address_offset0 evm slot)

theorem evalExpr_uniswap_this (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } evm this =
      .ok (.address evm.executionEnv.codeOwner) := by
  simp [this, evalExpr?, envValue, pure]

theorem evalExprs_uniswap_this_single (evm : EVM.State) (locals : Store) :
    evalExprs? config { contract := contract, locals := locals } evm [this] =
      .ok [.address evm.executionEnv.codeOwner] := by
  simp [evalExprs?, evalExpr_uniswap_this, EvalResult.bind, bind, pure]

-- LIBRARY CANDIDATE: Reasoning.SolmBody — source-side low-level call followed by
-- `require(okVar)`, parameterized by receiver, ETH value, calldata expression, and locals.
abbrev uniswapLowLevelCallRequireStore (locals : Store) (okVar dataVar : Ident)
    (success : Bool) (out : ByteArray) : Store :=
  (locals.insert okVar (.bool success)).insert dataVar (.bytes out)

theorem uniswapLowLevelCallRequireStore_ok (locals : Store) (okVar dataVar : Ident)
    (success : Bool) (out : ByteArray) (hne : (dataVar == okVar) = false) :
    (uniswapLowLevelCallRequireStore locals okVar dataVar success out).get? okVar =
      some (.bool success) := by
  rw [uniswapLowLevelCallRequireStore, store_get_ne _ _ hne, store_get_self]

theorem evalExpr_uniswapLowLevelCallRequire_ok {cfg : Config} {C : ContractDecl}
    (evm : EVM.State) (locals : Store) (okVar dataVar : Ident)
    (success : Bool) (out : ByteArray) (hne : (dataVar == okVar) = false) :
    evalExpr? cfg
      { contract := C, locals := uniswapLowLevelCallRequireStore locals okVar dataVar success out }
      evm (.var okVar) = .ok (.bool success) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [uniswapLowLevelCallRequireStore_ok _ _ _ _ _ hne]

theorem uniswapLowLevelCallRequireSuccess {cfg : Config} {C : ContractDecl}
    (evm evm' : EVM.State) (locals : Store)
    {receiver eth cdata : Expr} {okVar dataVar : Ident}
    {target : AccountAddress} {sendVal : Int} {calldata out : ByteArray}
    (hreceiver : evalExpr? cfg { contract := C, locals := locals } evm receiver =
      .ok (.address target))
    (heth : evalExpr? cfg { contract := C, locals := locals } evm eth = .ok (.int sendVal))
    (hdata : evalExpr? cfg { contract := C, locals := locals } evm cdata = .ok (.bytes calldata))
    (hcall : callViaEVM evm (EVM.address target) sendVal calldata (true, evm', out))
    (hne : (dataVar == okVar) = false) :
    ExecBlock cfg { contract := C, locals := locals } evm
      [ .lowLevelCall receiver eth cdata okVar dataVar,
        .require (.var okVar) ]
      (.ok
        { contract := C, locals := uniswapLowLevelCallRequireStore locals okVar dataVar true out }
        evm') := by
  refine ExecBlock.consNormal
    (solm' :=
      { contract := C, locals := uniswapLowLevelCallRequireStore locals okVar dataVar true out })
    (evm' := evm') ?_ ?_
  · simpa [uniswapLowLevelCallRequireStore] using
      ExecStmt.lowLevelCallSuccess hreceiver heth hdata hcall
  · exact ExecBlock.consNormal
      (ExecStmt.requireTrue
        (evalExpr_uniswapLowLevelCallRequire_ok evm' locals okVar dataVar true out hne))
      ExecBlock.nil

theorem uniswapLowLevelCallRequireFailure {cfg : Config} {C : ContractDecl}
    (evm evm' : EVM.State) (locals : Store)
    {receiver eth cdata : Expr} {okVar dataVar : Ident}
    {target : AccountAddress} {sendVal : Int} {calldata out : ByteArray}
    (hreceiver : evalExpr? cfg { contract := C, locals := locals } evm receiver =
      .ok (.address target))
    (heth : evalExpr? cfg { contract := C, locals := locals } evm eth = .ok (.int sendVal))
    (hdata : evalExpr? cfg { contract := C, locals := locals } evm cdata = .ok (.bytes calldata))
    (hcall : callViaEVM evm (EVM.address target) sendVal calldata (false, evm', out))
    (hne : (dataVar == okVar) = false) :
    ExecBlock cfg { contract := C, locals := locals } evm
      [ .lowLevelCall receiver eth cdata okVar dataVar,
        .require (.var okVar) ]
      .reverted := by
  refine ExecBlock.consNormal
    (solm' :=
      { contract := C, locals := uniswapLowLevelCallRequireStore locals okVar dataVar false out })
    (evm' := evm') ?_ ?_
  · simpa [uniswapLowLevelCallRequireStore] using
      ExecStmt.lowLevelCallFailure hreceiver heth hdata hcall
  · exact ExecBlock.consRevert
      (ExecStmt.requireFalse
        (evalExpr_uniswapLowLevelCallRequire_ok evm' locals okVar dataVar false out hne))

-- LIBRARY CANDIDATE: Reasoning.SolmBody — source-side successful typed external call from a
-- storage address receiver with zero value and `address(this)` as its single argument.
theorem uniswapExternalBalanceOfThisSuccess (evm evm' : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256} {retVar : Ident}
    {out : ByteArray} {value : Value}
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm slot))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm', out))
    (hdec : config.externalABI.decode? "balanceOf" out = some value) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .externalCall (.storage ref) "balanceOf" (.intLit 0) [this] retVar ]
      (.ok { contract := contract, locals := locals.insert retVar value } evm') := by
  exact ExecBlock.consNormal
    (ExecStmt.externalCallSuccess
      (evalExpr_uniswap_storage_address evm locals hbase her hty hloc)
      (by simp [evalExpr?, pure])
      (evalExprs_uniswap_this_single evm locals)
      hcall hdec)
    ExecBlock.nil

-- LIBRARY CANDIDATE: Reasoning.SolmBody — source-side failed typed external call from a storage
-- address receiver with zero value and `address(this)` as its single argument.
theorem uniswapExternalBalanceOfThisFailure (evm evm' : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256} {retVar : Ident}
    {out : ByteArray}
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm slot))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (false, evm', out)) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .externalCall (.storage ref) "balanceOf" (.intLit 0) [this] retVar ] .reverted := by
  exact ExecBlock.consRevert
    (ExecStmt.externalCallFailure
      (evalExpr_uniswap_storage_address evm locals hbase her hty hloc)
      (by simp [evalExpr?, pure])
      (evalExprs_uniswap_this_single evm locals)
      hcall)

-- LIBRARY CANDIDATE: Reasoning.SolmBody — source-side ABI-decode revert after a successful typed
-- external call from a storage address receiver with `address(this)` as its single argument.
theorem uniswapExternalBalanceOfThisDecodeRevert (evm evm' : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256} {retVar : Ident}
    {out : ByteArray}
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm slot))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm', out))
    (hdec : config.externalABI.decode? "balanceOf" out = none) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .externalCall (.storage ref) "balanceOf" (.intLit 0) [this] retVar ] .reverted := by
  exact ExecBlock.consRevert
    (ExecStmt.externalCallReturnDecodeRevert
      (evalExpr_uniswap_storage_address evm locals hbase her hty hloc)
      (by simp [evalExpr?, pure])
      (evalExprs_uniswap_this_single evm locals)
      hcall hdec)

abbrev uniswapBalanceOfStore (locals : Store) (balance0 balance1 : Value) : Store :=
  (locals.insert "balance0" balance0).insert "balance1" balance1

abbrev uniswapBalanceOfFrame (locals : Store) (balance0 balance1 : Value) : Frame :=
  { contract := contract, locals := uniswapBalanceOfStore locals balance0 balance1 }

theorem uniswapBalanceOfStore_balance0 (locals : Store) (balance0 balance1 : Value) :
    (uniswapBalanceOfStore locals balance0 balance1).get? "balance0" = some balance0 := by
  rw [uniswapBalanceOfStore, store_get_ne _ _ (by decide), store_get_self]

theorem uniswapBalanceOfStore_balance1 (locals : Store) (balance0 balance1 : Value) :
    (uniswapBalanceOfStore locals balance0 balance1).get? "balance1" = some balance1 := by
  rw [uniswapBalanceOfStore, store_get_self]

theorem uniswapTokenBalanceOfThisCallsPrefix (evm evm0 evm1 : EVM.State) (locals : Store)
    {out0 out1 : ByteArray} {balance0 balance1 : Value}
    (hbase0 : locals.get? "token0" = none)
    (hbase1 : (locals.insert "balance0" balance0).get? "token1" = none)
    (hcall0 : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨6⟩))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some balance1) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
        .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ]
      (.ok (uniswapBalanceOfFrame locals balance0 balance1) evm1) := by
  have htoken0 :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0" ]
        (.ok { contract := contract, locals := locals.insert "balance0" balance0 } evm0) := by
    exact uniswapExternalBalanceOfThisSuccess
      (evm := evm) (evm' := evm0) (locals := locals)
      (ref := token0Ref) (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (retVar := "balance0")
      (by simpa [token0Ref] using hbase0)
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl) hcall0 hdec0
  have htoken1 :
      ExecBlock config { contract := contract, locals := locals.insert "balance0" balance0 } evm0
        [ .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ]
        (.ok (uniswapBalanceOfFrame locals balance0 balance1) evm1) := by
    exact uniswapExternalBalanceOfThisSuccess
      (evm := evm0) (evm' := evm1) (locals := locals.insert "balance0" balance0)
      (ref := token1Ref) (er := { base := "token1", steps := [] }) (slot := ⟨7⟩)
      (retVar := "balance1")
      (by simpa [token1Ref] using hbase1)
      (by simp [evalStorageRef, evalStorageRefSteps, token1Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl) hcall1 hdec1
  exact Reasoning.Refinement.execBlock_append htoken0 htoken1

theorem uniswapTokenBalanceOfThisFirstCallFailure (evm evm0 : EVM.State) (locals : Store)
    {out0 : ByteArray}
    (hbase0 : locals.get? "token0" = none)
    (hcall0 : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨6⟩))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (false, evm0, out0)) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
        .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ]
      .reverted := by
  have hfirst :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0" ]
        .reverted := by
    exact uniswapExternalBalanceOfThisFailure
      (evm := evm) (evm' := evm0) (locals := locals)
      (ref := token0Ref) (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (retVar := "balance0")
      (by simpa [token0Ref] using hbase0)
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl) hcall0
  exact Reasoning.Refinement.execBlock_append_term (s2 :=
      [ .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ])
    hfirst (by intro f e h; cases h)

theorem uniswapTokenBalanceOfThisFirstCallDecodeRevert (evm evm0 : EVM.State) (locals : Store)
    {out0 : ByteArray}
    (hbase0 : locals.get? "token0" = none)
    (hcall0 : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨6⟩))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = none) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
        .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ]
      .reverted := by
  have hfirst :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0" ]
        .reverted := by
    exact uniswapExternalBalanceOfThisDecodeRevert
      (evm := evm) (evm' := evm0) (locals := locals)
      (ref := token0Ref) (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (retVar := "balance0")
      (by simpa [token0Ref] using hbase0)
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl) hcall0 hdec0
  exact Reasoning.Refinement.execBlock_append_term (s2 :=
      [ .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ])
    hfirst (by intro f e h; cases h)

theorem uniswapTokenBalanceOfThisSecondCallFailure (evm evm0 evm1 : EVM.State)
    (locals : Store) {out0 out1 : ByteArray} {balance0 : Value}
    (hbase0 : locals.get? "token0" = none)
    (hbase1 : (locals.insert "balance0" balance0).get? "token1" = none)
    (hcall0 : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨6⟩))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (false, evm1, out1)) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
        .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ]
      .reverted := by
  have htoken0 :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0" ]
        (.ok { contract := contract, locals := locals.insert "balance0" balance0 } evm0) := by
    exact uniswapExternalBalanceOfThisSuccess
      (evm := evm) (evm' := evm0) (locals := locals)
      (ref := token0Ref) (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (retVar := "balance0")
      (by simpa [token0Ref] using hbase0)
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl) hcall0 hdec0
  have htoken1 :
      ExecBlock config { contract := contract, locals := locals.insert "balance0" balance0 } evm0
        [ .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ]
        .reverted := by
    exact uniswapExternalBalanceOfThisFailure
      (evm := evm0) (evm' := evm1) (locals := locals.insert "balance0" balance0)
      (ref := token1Ref) (er := { base := "token1", steps := [] }) (slot := ⟨7⟩)
      (retVar := "balance1")
      (by simpa [token1Ref] using hbase1)
      (by simp [evalStorageRef, evalStorageRefSteps, token1Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl) hcall1
  exact Reasoning.Refinement.execBlock_append htoken0 htoken1

theorem uniswapTokenBalanceOfThisSecondCallDecodeRevert (evm evm0 evm1 : EVM.State)
    (locals : Store) {out0 out1 : ByteArray} {balance0 : Value}
    (hbase0 : locals.get? "token0" = none)
    (hbase1 : (locals.insert "balance0" balance0).get? "token1" = none)
    (hcall0 : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨6⟩))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = none) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0",
        .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ]
      .reverted := by
  have htoken0 :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .externalCall (.storage token0Ref) "balanceOf" (.intLit 0) [this] "balance0" ]
        (.ok { contract := contract, locals := locals.insert "balance0" balance0 } evm0) := by
    exact uniswapExternalBalanceOfThisSuccess
      (evm := evm) (evm' := evm0) (locals := locals)
      (ref := token0Ref) (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (retVar := "balance0")
      (by simpa [token0Ref] using hbase0)
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl) hcall0 hdec0
  have htoken1 :
      ExecBlock config { contract := contract, locals := locals.insert "balance0" balance0 } evm0
        [ .externalCall (.storage token1Ref) "balanceOf" (.intLit 0) [this] "balance1" ]
        .reverted := by
    exact uniswapExternalBalanceOfThisDecodeRevert
      (evm := evm0) (evm' := evm1) (locals := locals.insert "balance0" balance0)
      (ref := token1Ref) (er := { base := "token1", steps := [] }) (slot := ⟨7⟩)
      (retVar := "balance1")
      (by simpa [token1Ref] using hbase1)
      (by simp [evalStorageRef, evalStorageRefSteps, token1Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl) hcall1 hdec1
  exact Reasoning.Refinement.execBlock_append htoken0 htoken1

-- LIBRARY CANDIDATE: Reasoning.SolmBody — source-side successful high-level external call after
-- Solidity's `EXTCODESIZE(receiver) > 0` guard, parameterized by receiver and call metadata.
theorem uniswapCheckedExternalBalanceOfThisSuccess (evm evm' : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256} {retVar : Ident}
    {out : ByteArray} {value : Value}
    (hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage ref)) (.intLit 0)) = .ok (.bool true))
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm slot))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm', out))
    (hdec : config.externalABI.decode? "balanceOf" out = some value) :
    ExecBlock config { contract := contract, locals := locals } evm
      (balanceOfThisStmts (.storage ref) retVar)
      (.ok { contract := contract, locals := locals.insert retVar value } evm') := by
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .require (.binary .gt (.extCodeSize (.storage ref)) (.intLit 0)),
      .externalCall (.storage ref) "balanceOf" (.intLit 0) [this] retVar ]
    (.ok { contract := contract, locals := locals.insert retVar value } evm')
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  exact uniswapExternalBalanceOfThisSuccess evm evm' locals
    (ref := ref) (er := er) (slot := slot) (retVar := retVar)
    hbase her hty hloc hcall hdec

-- LIBRARY CANDIDATE: Reasoning.SolmBody — source-side failed high-level external call after
-- Solidity's `EXTCODESIZE(receiver) > 0` guard, parameterized by receiver and call metadata.
theorem uniswapCheckedExternalBalanceOfThisFailure (evm evm' : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256} {retVar : Ident}
    {out : ByteArray}
    (hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage ref)) (.intLit 0)) = .ok (.bool true))
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm slot))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (false, evm', out)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (balanceOfThisStmts (.storage ref) retVar) .reverted := by
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .require (.binary .gt (.extCodeSize (.storage ref)) (.intLit 0)),
      .externalCall (.storage ref) "balanceOf" (.intLit 0) [this] retVar ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  exact uniswapExternalBalanceOfThisFailure evm evm' locals
    (ref := ref) (er := er) (slot := slot) (retVar := retVar)
    hbase her hty hloc hcall

-- LIBRARY CANDIDATE: Reasoning.SolmBody — source-side ABI-decode revert after a successful
-- high-level external call protected by Solidity's `EXTCODESIZE(receiver) > 0` guard.
theorem uniswapCheckedExternalBalanceOfThisDecodeRevert
    (evm evm' : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256} {retVar : Ident}
    {out : ByteArray}
    (hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage ref)) (.intLit 0)) = .ok (.bool true))
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm slot))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm', out))
    (hdec : config.externalABI.decode? "balanceOf" out = none) :
    ExecBlock config { contract := contract, locals := locals } evm
      (balanceOfThisStmts (.storage ref) retVar) .reverted := by
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .require (.binary .gt (.extCodeSize (.storage ref)) (.intLit 0)),
      .externalCall (.storage ref) "balanceOf" (.intLit 0) [this] retVar ]
    .reverted
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  exact uniswapExternalBalanceOfThisDecodeRevert evm evm' locals
    (ref := ref) (er := er) (slot := slot) (retVar := retVar)
    hbase her hty hloc hcall hdec

-- LIBRARY CANDIDATE: Reasoning.SolmBody — source-side high-level external call reverts before
-- the call when Solidity's `EXTCODESIZE(receiver) > 0` guard is false.
theorem uniswapCheckedExternalBalanceOfThisNoCode (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {retVar : Ident}
    (hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage ref)) (.intLit 0)) = .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (balanceOfThisStmts (.storage ref) retVar) .reverted := by
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .require (.binary .gt (.extCodeSize (.storage ref)) (.intLit 0)),
      .externalCall (.storage ref) "balanceOf" (.intLit 0) [this] retVar ]
    .reverted
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)

theorem uniswapCheckedTokenBalanceOfThisCallsPrefix
    (evm evm0 evm1 : EVM.State) (locals : Store)
    {out0 out1 : ByteArray} {balance0 balance1 : Value}
    (hguard0 :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config { contract := contract, locals := locals.insert "balance0" balance0 } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hbase0 : locals.get? "token0" = none)
    (hbase1 : (locals.insert "balance0" balance0).get? "token1" = none)
    (hcall0 : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨6⟩))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some balance1) :
    ExecBlock config { contract := contract, locals := locals } evm
      (pairBalanceOfThisStmts "balance0" "balance1")
      (.ok (uniswapBalanceOfFrame locals balance0 balance1) evm1) := by
  have htoken0 :
      ExecBlock config { contract := contract, locals := locals } evm
        (token0BalanceOfThisStmts "balance0")
        (.ok { contract := contract, locals := locals.insert "balance0" balance0 } evm0) := by
    exact uniswapCheckedExternalBalanceOfThisSuccess
      (evm := evm) (evm' := evm0) (locals := locals)
      (ref := token0Ref) (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (retVar := "balance0")
      hguard0 (by simpa [token0Ref] using hbase0)
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl) hcall0 hdec0
  have htoken1 :
      ExecBlock config { contract := contract, locals := locals.insert "balance0" balance0 } evm0
        (token1BalanceOfThisStmts "balance1")
        (.ok (uniswapBalanceOfFrame locals balance0 balance1) evm1) := by
    exact uniswapCheckedExternalBalanceOfThisSuccess
      (evm := evm0) (evm' := evm1) (locals := locals.insert "balance0" balance0)
      (ref := token1Ref) (er := { base := "token1", steps := [] }) (slot := ⟨7⟩)
      (retVar := "balance1")
      hguard1 (by simpa [token1Ref] using hbase1)
      (by simp [evalStorageRef, evalStorageRefSteps, token1Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl) hcall1 hdec1
  simpa [pairBalanceOfThisStmts, token0BalanceOfThisStmts, token1BalanceOfThisStmts]
    using Reasoning.Refinement.execBlock_append htoken0 htoken1

theorem uniswapCheckedTokenBalanceOfThisFirstCallNoCode
    (evm : EVM.State) (locals : Store)
    (hguard0 :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (pairBalanceOfThisStmts "balance0" "balance1") .reverted := by
  have hfirst :
      ExecBlock config { contract := contract, locals := locals } evm
        (token0BalanceOfThisStmts "balance0") .reverted := by
    exact uniswapCheckedExternalBalanceOfThisNoCode
      (evm := evm) (locals := locals) (ref := token0Ref) (retVar := "balance0") hguard0
  simpa [pairBalanceOfThisStmts, token0BalanceOfThisStmts, token1BalanceOfThisStmts]
    using Reasoning.Refinement.execBlock_append_term
      (s2 := token1BalanceOfThisStmts "balance1") hfirst (by intro f e h; cases h)

theorem uniswapCheckedTokenBalanceOfThisFirstCallFailure
    (evm evm0 : EVM.State) (locals : Store) {out0 : ByteArray}
    (hguard0 :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hbase0 : locals.get? "token0" = none)
    (hcall0 : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨6⟩))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (false, evm0, out0)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (pairBalanceOfThisStmts "balance0" "balance1") .reverted := by
  have hfirst :
      ExecBlock config { contract := contract, locals := locals } evm
        (token0BalanceOfThisStmts "balance0") .reverted := by
    exact uniswapCheckedExternalBalanceOfThisFailure
      (evm := evm) (evm' := evm0) (locals := locals)
      (ref := token0Ref) (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (retVar := "balance0")
      hguard0 (by simpa [token0Ref] using hbase0)
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl) hcall0
  simpa [pairBalanceOfThisStmts, token0BalanceOfThisStmts, token1BalanceOfThisStmts]
    using Reasoning.Refinement.execBlock_append_term
      (s2 := token1BalanceOfThisStmts "balance1") hfirst (by intro f e h; cases h)

theorem uniswapCheckedTokenBalanceOfThisFirstCallDecodeRevert
    (evm evm0 : EVM.State) (locals : Store) {out0 : ByteArray}
    (hguard0 :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hbase0 : locals.get? "token0" = none)
    (hcall0 : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨6⟩))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = none) :
    ExecBlock config { contract := contract, locals := locals } evm
      (pairBalanceOfThisStmts "balance0" "balance1") .reverted := by
  have hfirst :
      ExecBlock config { contract := contract, locals := locals } evm
        (token0BalanceOfThisStmts "balance0") .reverted := by
    exact uniswapCheckedExternalBalanceOfThisDecodeRevert
      (evm := evm) (evm' := evm0) (locals := locals)
      (ref := token0Ref) (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (retVar := "balance0")
      hguard0 (by simpa [token0Ref] using hbase0)
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl) hcall0 hdec0
  simpa [pairBalanceOfThisStmts, token0BalanceOfThisStmts, token1BalanceOfThisStmts]
    using Reasoning.Refinement.execBlock_append_term
      (s2 := token1BalanceOfThisStmts "balance1") hfirst (by intro f e h; cases h)

theorem uniswapCheckedTokenBalanceOfThisSecondCallNoCode
    (evm evm0 : EVM.State) (locals : Store) {out0 : ByteArray} {balance0 : Value}
    (hguard0 :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config { contract := contract, locals := locals.insert "balance0" balance0 } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool false))
    (hbase0 : locals.get? "token0" = none)
    (hcall0 : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨6⟩))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0) :
    ExecBlock config { contract := contract, locals := locals } evm
      (pairBalanceOfThisStmts "balance0" "balance1") .reverted := by
  have htoken0 :
      ExecBlock config { contract := contract, locals := locals } evm
        (token0BalanceOfThisStmts "balance0")
        (.ok { contract := contract, locals := locals.insert "balance0" balance0 } evm0) := by
    exact uniswapCheckedExternalBalanceOfThisSuccess
      (evm := evm) (evm' := evm0) (locals := locals)
      (ref := token0Ref) (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (retVar := "balance0")
      hguard0 (by simpa [token0Ref] using hbase0)
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl) hcall0 hdec0
  have htoken1 :
      ExecBlock config { contract := contract, locals := locals.insert "balance0" balance0 } evm0
        (token1BalanceOfThisStmts "balance1") .reverted := by
    exact uniswapCheckedExternalBalanceOfThisNoCode
      (evm := evm0) (locals := locals.insert "balance0" balance0)
      (ref := token1Ref) (retVar := "balance1") hguard1
  simpa [pairBalanceOfThisStmts, token0BalanceOfThisStmts, token1BalanceOfThisStmts]
    using Reasoning.Refinement.execBlock_append htoken0 htoken1

theorem uniswapCheckedTokenBalanceOfThisSecondCallFailure
    (evm evm0 evm1 : EVM.State) (locals : Store)
    {out0 out1 : ByteArray} {balance0 : Value}
    (hguard0 :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config { contract := contract, locals := locals.insert "balance0" balance0 } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hbase0 : locals.get? "token0" = none)
    (hbase1 : (locals.insert "balance0" balance0).get? "token1" = none)
    (hcall0 : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨6⟩))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (false, evm1, out1)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (pairBalanceOfThisStmts "balance0" "balance1") .reverted := by
  have htoken0 :
      ExecBlock config { contract := contract, locals := locals } evm
        (token0BalanceOfThisStmts "balance0")
        (.ok { contract := contract, locals := locals.insert "balance0" balance0 } evm0) := by
    exact uniswapCheckedExternalBalanceOfThisSuccess
      (evm := evm) (evm' := evm0) (locals := locals)
      (ref := token0Ref) (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (retVar := "balance0")
      hguard0 (by simpa [token0Ref] using hbase0)
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl) hcall0 hdec0
  have htoken1 :
      ExecBlock config { contract := contract, locals := locals.insert "balance0" balance0 } evm0
        (token1BalanceOfThisStmts "balance1") .reverted := by
    exact uniswapCheckedExternalBalanceOfThisFailure
      (evm := evm0) (evm' := evm1) (locals := locals.insert "balance0" balance0)
      (ref := token1Ref) (er := { base := "token1", steps := [] }) (slot := ⟨7⟩)
      (retVar := "balance1")
      hguard1 (by simpa [token1Ref] using hbase1)
      (by simp [evalStorageRef, evalStorageRefSteps, token1Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl) hcall1
  simpa [pairBalanceOfThisStmts, token0BalanceOfThisStmts, token1BalanceOfThisStmts]
    using Reasoning.Refinement.execBlock_append htoken0 htoken1

theorem uniswapCheckedTokenBalanceOfThisSecondCallDecodeRevert
    (evm evm0 evm1 : EVM.State) (locals : Store)
    {out0 out1 : ByteArray} {balance0 : Value}
    (hguard0 :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config { contract := contract, locals := locals.insert "balance0" balance0 } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hbase0 : locals.get? "token0" = none)
    (hbase1 : (locals.insert "balance0" balance0).get? "token1" = none)
    (hcall0 : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm ⟨6⟩))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm0, out0))
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some balance0)
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1))
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = none) :
    ExecBlock config { contract := contract, locals := locals } evm
      (pairBalanceOfThisStmts "balance0" "balance1") .reverted := by
  have htoken0 :
      ExecBlock config { contract := contract, locals := locals } evm
        (token0BalanceOfThisStmts "balance0")
        (.ok { contract := contract, locals := locals.insert "balance0" balance0 } evm0) := by
    exact uniswapCheckedExternalBalanceOfThisSuccess
      (evm := evm) (evm' := evm0) (locals := locals)
      (ref := token0Ref) (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (retVar := "balance0")
      hguard0 (by simpa [token0Ref] using hbase0)
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl) hcall0 hdec0
  have htoken1 :
      ExecBlock config { contract := contract, locals := locals.insert "balance0" balance0 } evm0
        (token1BalanceOfThisStmts "balance1") .reverted := by
    exact uniswapCheckedExternalBalanceOfThisDecodeRevert
      (evm := evm0) (evm' := evm1) (locals := locals.insert "balance0" balance0)
      (ref := token1Ref) (er := { base := "token1", steps := [] }) (slot := ⟨7⟩)
      (retVar := "balance1")
      hguard1 (by simpa [token1Ref] using hbase1)
      (by simp [evalStorageRef, evalStorageRefSteps, token1Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl) hcall1 hdec1
  simpa [pairBalanceOfThisStmts, token0BalanceOfThisStmts, token1BalanceOfThisStmts]
    using Reasoning.Refinement.execBlock_append htoken0 htoken1

-- LIBRARY CANDIDATE: Reasoning.SolmBody — generic nonpayable scalar address-storage getter body,
-- parameterized by config, contract, storage ref, and concrete storage location.
theorem uniswapAddressGetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return (.storage ref) ])
      (.returned { contract := contract, locals := locals } evm
        (some (.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (uniswapStorageLocLoad_address_offset0 evm slot))

-- LIBRARY CANDIDATE: Reasoning.SolmBody — generic nonpayable scalar uint256 storage getter body,
-- parameterized by config, contract, storage ref, and concrete storage location.
theorem uniswapUint256GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)))
    (hloc : config.storage.layout er = fun _ => some (wordLoc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return (.storage ref) ])
      (.returned { contract := contract, locals := locals } evm
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (uniswapStorageLocLoad_uint256 evm slot))

-- LIBRARY CANDIDATE: Reasoning.SolmBody — generic nonpayable scalar bytes32 storage getter body,
-- parameterized by config, contract, storage ref, and concrete storage location.
theorem uniswapBytes32GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.bytes bytes32Width)))
    (hloc : config.storage.layout er = fun _ => some (bytes32Loc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return (.storage ref) ])
      (.returned { contract := contract, locals := locals } evm
        (some (.fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot))))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (uniswapStorageLocLoad_bytes32 evm slot))

-- LIBRARY CANDIDATE: Reasoning.SolmBody — generic nonpayable integer-literal return body.
theorem uniswapIntLiteralBodyReturns (evm : EVM.State) (locals : Store) (n : Int)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return (.intLit n) ])
      (.returned { contract := contract, locals := locals } evm (some (.int n))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by simp [evalExpr?, pure])

-- LIBRARY CANDIDATE: Reasoning.SolmBody — generic nonpayable fixed-bytes-literal return body.
theorem uniswapFixedBytesLiteralBodyReturns (evm : EVM.State) (locals : Store)
    (n : Fin 32) (bytes : List UInt8) (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals
      (nonpayable ++ [ .return (.fixedBytesLit n bytes) ])
      (.returned { contract := contract, locals := locals } evm (some (.fixedBytes n bytes))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by simp [evalExpr?, pure])

-- LIBRARY CANDIDATE: Reasoning.ABI — generic uint8 scalar return encoding.
theorem uniswapUint8ReturnEncoding (v : UInt256) (h8 : v.toNat < EVM.twoPow 8) :
    encodeReturnValue? (.elem (.int (.uint ⟨8, by decide⟩)))
        (.int (Int.ofNat v.toNat)) =
      some (UInt256.toByteArray v) := by
  have hword : EVM.word v.toNat = v := by
    show UInt256.ofNat v.toNat = v
    exact u256_ofNat_toNat v
  refine scalarReturnEncoding (t := (.int (.uint ⟨8, by decide⟩))) (w := v) rfl ?_ ?_
  · simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
    decide
  · simp [encodeABIValue?, encodeABIWord?, hword, h8]

/-! ## Shared lock-revert memory -/

def uniswapLockRevertSelector : UInt256 :=
  UInt256.shiftLeft (⟨4594637⟩ : UInt256) ⟨229⟩

def uniswapLockRevertStringWord : UInt256 :=
  UInt256.shiftLeft (⟨7267690950230416977285330377544234619217⟩ : UInt256) ⟨122⟩

def uniswapLockRevertMem0 : ByteArray :=
  solcReturnMem uniswapLockRevertSelector

def uniswapLockRevertMem1 : ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 uniswapLockRevertMem0 132 32

def uniswapLockRevertMem2 : ByteArray :=
  (UInt256.toByteArray (⟨17⟩ : UInt256)).write 0 uniswapLockRevertMem1 164 32

def uniswapLockRevertMem3 : ByteArray :=
  (UInt256.toByteArray uniswapLockRevertStringWord).write 0 uniswapLockRevertMem2 196 32

-- LIBRARY CANDIDATE: Reasoning.Memory - generic solc `Error(string)` memory-builder fact,
-- parameterized by selector, string length, packed string word, and active-word bound.
theorem uniswapLockRevertMem3_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ uniswapLockRevertMem3.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
         (uniswapLockRevertMem3.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  native_decide

abbrev uniswapRetEnd : UInt256 := (⟨128⟩ : UInt256) + ⟨32⟩

theorem uniswapSubRet32_toNat :
    (UInt256.sub uniswapRetEnd ⟨128⟩).toNat = 32 := by
  decide

-- LIBRARY CANDIDATE: Reasoning.Solc — unsigned `LT` variant of the common solc
-- static-argument length check (`calldatasize - 4 < 32`).
theorem uniswapDecodeLenCheckOk_4_32_lt {sz : ℕ}
    (hsz36 : 36 ≤ sz) (hsize : sz < UInt256.size) :
    UInt256.lt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨32⟩ = ⟨0⟩ := by
  apply ult_zero
  have h4 : (⟨4⟩ : UInt256).toNat = 4 := by decide
  rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    usub_ofNat_word_toNat (by rw [h4]; omega) hsize]
  omega

-- LIBRARY CANDIDATE: Reasoning.Solc — unsigned `LT` variant of the common solc
-- static-argument length check (`calldatasize - 4 < 64`).
theorem uniswapDecodeLenCheckOk_4_64_lt {sz : ℕ}
    (hsz68 : 68 ≤ sz) (hsize : sz < UInt256.size) :
    UInt256.lt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨64⟩ = ⟨0⟩ := by
  apply ult_zero
  have h4 : (⟨4⟩ : UInt256).toNat = 4 := by decide
  rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
    usub_ofNat_word_toNat (by rw [h4]; omega) hsize]
  omega

-- LIBRARY CANDIDATE: Reasoning.Solc — unsigned `LT` variant of the common solc
-- static-argument length check (`calldatasize - 4 < 96`).
theorem uniswapDecodeLenCheckOk_4_96_lt {sz : ℕ}
    (hsz100 : 100 ≤ sz) (hsize : sz < UInt256.size) :
    UInt256.lt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨96⟩ = ⟨0⟩ := by
  apply ult_zero
  have h4 : (⟨4⟩ : UInt256).toNat = 4 := by decide
  rw [show (⟨96⟩ : UInt256).toNat = 96 from by decide,
    usub_ofNat_word_toNat (by rw [h4]; omega) hsize]
  omega

end UniswapV2Pair

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

/-! ## Shared getter routines -/

/-- Bytecode shape for Uniswap's generated full-slot address getter routines.

The routine loads `slot`, masks the low 160 bits, duplicates the dynamic return address, and jumps
back to the caller.  It appears at pc 2917 (`token0`), pc 5443 (`factory`), and pc 5458 (`token1`).
-/
@[reducible] def uniswapAddressSlotGetterWf (pc slot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p8 := p6 + UInt256.ofNat 2
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  decode UniswapV2Pair.uniswapV2PairBytecode pc = some (.JUMPDEST, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p3 = some (.SLOAD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p4 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p6 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p8 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p10 = some (.SHL, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p11 = some (.SUB, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p12 = some (.AND, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p13 = some (.DUP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p14 = some (.JUMP, .none)

/-- Discharge a Uniswap address-slot getter bytecode-shape proof at a concrete PC/slot. -/
macro "uniswap_address_slot_getter_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapAddressSlotGetterWf
    repeat' first | apply And.intro | native_decide)

/-- Bytecode shape for an external getter thunk that jumps to an internal getter routine. -/
@[reducible] def uniswapGetterEntryWf (pc returnPc routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p7 := p4 + UInt256.ofNat 3
  decode UniswapV2Pair.uniswapV2PairBytecode pc = some (.JUMPDEST, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p1 =
      some (.Push .PUSH2, some (returnPc, 2))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p4 =
      some (.Push .PUSH2, some (routine, 2))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p7 = some (.JUMP, .none)

/-- Bytecode shape for the external thunk that jumps to an address-slot getter routine. -/
@[reducible] def uniswapAddressGetterEntryWf (pc routine : UInt256) : Prop :=
  uniswapGetterEntryWf pc ⟨825⟩ routine

/-- Bytecode shape for the external thunk that jumps to a word-slot getter routine. -/
@[reducible] def uniswapWordGetterEntryWf (pc routine : UInt256) : Prop :=
  uniswapGetterEntryWf pc ⟨861⟩ routine

/-- Discharge a Uniswap getter external-thunk bytecode-shape proof. -/
macro "uniswap_getter_entry_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapGetterEntryWf
    repeat' first | apply And.intro | native_decide)

/-- Discharge a Uniswap address getter external-thunk bytecode-shape proof. -/
macro "uniswap_address_getter_entry_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapAddressGetterEntryWf Reasoning.Reach.uniswapGetterEntryWf
    repeat' first | apply And.intro | native_decide)

/-- Discharge a Uniswap word getter external-thunk bytecode-shape proof. -/
macro "uniswap_word_getter_entry_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapWordGetterEntryWf Reasoning.Reach.uniswapGetterEntryWf
    repeat' first | apply And.intro | native_decide)

/-- Bytecode shape for Uniswap's generated full-slot word getter routines. -/
@[reducible] def uniswapWordSlotGetterWf (pc slot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  decode UniswapV2Pair.uniswapV2PairBytecode pc = some (.JUMPDEST, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p3 = some (.SLOAD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p4 = some (.DUP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p5 = some (.JUMP, .none)

/-- Discharge a Uniswap full-slot word getter bytecode-shape proof at a concrete PC/slot. -/
macro "uniswap_word_slot_getter_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapWordSlotGetterWf
    repeat' first | apply And.intro | native_decide)

/-! ## Constant getter routines -/

/-- Bytecode shape for Uniswap's generated constant getter routines.

The routine pushes a literal of width `width`, duplicates the dynamic return address, and jumps
back to the caller.  It appears for `PERMIT_TYPEHASH`, `decimals`, and `MINIMUM_LIQUIDITY`.
-/
@[reducible] def uniswapConstGetterWf
    (pc val : UInt256) (width : Nat) (op : Operation.POp) : Prop :=
  let p1 := pc + ⟨1⟩
  let pNext := p1 + UInt256.ofNat width.succ
  decode UniswapV2Pair.uniswapV2PairBytecode pc = some (.JUMPDEST, .none)
  ∧ op ≠ .PUSH0
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p1 = some (.Push op, some (val, width))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode pNext = some (.DUP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode (pNext + ⟨1⟩) = some (.JUMP, .none)

/-- Discharge a Uniswap constant getter bytecode-shape proof at a concrete PC/value/width. -/
macro "uniswap_const_getter_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapConstGetterWf
    repeat' first | apply And.intro | native_decide)

-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc external getter thunk,
-- parameterized by bytecode, thunk PC, return-wrapper PC, and getter-routine PC.
theorem RD.uniswapGetterThunk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {entry returnPc routine : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : uniswapGetterEntryWf entry returnPc routine)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true) :
    ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) routine (returnPc :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  rcases hentry with ⟨hd0, hd1, hd4, hd7⟩
  have rd1 := rdEntry.jumpdest hd0 (by simp only [List.length_singleton]; omega)
  have rd4 := rd1.push2 returnPc hd1 (by simp only [List.length_singleton]; omega)
  have rd7 := rd4.push2 routine hd4
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdRoutine := rd7.jump hd7 hroutine
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, rdRoutine⟩

/-! ## Shared lock-entry prefix -/

/-- Bytecode shape for Uniswap's optimizer-emitted reentrancy-lock success prefix.

The prefix checks storage slot 12 for `1`, jumps over the revert block, then stores `0` in slot 12.
It appears at the front of `skim`, `sync`, and the larger liquidity/swap routines.
-/
@[reducible] def uniswapLockEnterOkWf (pc okPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p10 := p7 + UInt256.ofNat 3
  let pOk1 := okPc + ⟨1⟩
  let pOk3 := pOk1 + UInt256.ofNat 2
  let pOk5 := pOk3 + UInt256.ofNat 2
  decode UniswapV2Pair.uniswapV2PairBytecode pc = some (.JUMPDEST, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p1 =
      some (.Push .PUSH1, some (⟨12⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p3 = some (.SLOAD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p4 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p6 = some (.EQ, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p7 =
      some (.Push .PUSH2, some (okPc, 2))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p10 = some (.JUMPI, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode okPc = some (.JUMPDEST, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode pOk1 =
      some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode pOk3 =
      some (.Push .PUSH1, some (⟨12⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode pOk5 = some (.SSTORE, .none)

/-- Discharge a Uniswap lock-entry success bytecode-shape proof. -/
macro "uniswap_lock_enter_ok_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapLockEnterOkWf
    repeat' first | apply And.intro | native_decide)

-- LIBRARY CANDIDATE: Reasoning.Reach - generic solc reentrancy-lock success prefix,
-- parameterized by bytecode, guard slot, unlocked word, locked word, entry PC, and success PC.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapLockEnterOk {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc okPc : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 pc R mem aw rdata (cA, σ) k C)
    (hwf : uniswapLockEnterOkWf pc okPc)
    (hperm : ee.perm = true)
    (hunlocked :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (hok : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains okPc = true)
    (hov : R.length + 2 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 (okPc + UInt256.ofNat 6) R
      mem aw rdata (cA, sstoreAccountMap ee.codeOwner σ ⟨12⟩ ⟨0⟩) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd6, hd7, hd10, hdOk, hdOk1, hdOk3, hdOk5⟩
  have rd1 := h.jumpdest hd0 (by omega)
  have rd3 := rd1.push1 ⟨12⟩ hd1 (by omega)
  obtain ⟨_, _, rd4₀⟩ := rd3.sload hd3 (by omega)
  have rd4 := rd4₀
  rw [hunlocked] at rd4
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by simp only [List.length_cons]; omega)
  have rd7₀ := rd6.eq hd6 (by omega)
  have rd7 := rd7₀
  rw [uInt256_eq_self] at rd7
  have rd10 := rd7.push2 okPc hd7 (by simp only [List.length_cons]; omega)
  have rdOk := rd10.jumpiT hd10 one_ne_zero_uint hok (by omega)
  have rdOk1 := rdOk.jumpdest hdOk (by omega)
  have rdOk3 := rdOk1.push1 ⟨0⟩ hdOk1 (by omega)
  have rdOk5 := rdOk3.push1 ⟨12⟩ hdOk3 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdAfter⟩ := rdOk5.sstore hperm hdOk5 (by omega)
  have hpcOut :
      okPc + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ =
        okPc + UInt256.ofNat 6 := by
    rw [u256_add_assoc okPc ⟨1⟩ (UInt256.ofNat 2)]
    rw [u256_add_assoc okPc (⟨1⟩ + UInt256.ofNat 2) (UInt256.ofNat 2)]
    rw [u256_add_assoc okPc (⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2) ⟨1⟩]
    congr 1
  exact ⟨_, _, by simpa [hpcOut] using rdAfter⟩

/-- Bytecode shape for the locked branch of Uniswap's reentrancy guard.

When storage slot 12 is not `1`, the guard falls through to the inlined `Error("UniswapV2:
LOCKED")` revert builder.
-/
@[reducible] def uniswapLockEnterLockedWf (pc okPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p10 := p7 + UInt256.ofNat 3
  let r0 := p10 + ⟨1⟩
  let r2 := r0 + UInt256.ofNat 2
  let r3 := r2 + ⟨1⟩
  let r4 := r3 + ⟨1⟩
  let r8 := r4 + UInt256.ofNat 4
  let r10 := r8 + UInt256.ofNat 2
  let r11 := r10 + ⟨1⟩
  let r12 := r11 + ⟨1⟩
  let r13 := r12 + ⟨1⟩
  let r15 := r13 + UInt256.ofNat 2
  let r17 := r15 + UInt256.ofNat 2
  let r18 := r17 + ⟨1⟩
  let r19 := r18 + ⟨1⟩
  let r20 := r19 + ⟨1⟩
  let r22 := r20 + UInt256.ofNat 2
  let r24 := r22 + UInt256.ofNat 2
  let r25 := r24 + ⟨1⟩
  let r26 := r25 + ⟨1⟩
  let r27 := r26 + ⟨1⟩
  let r45 := r27 + UInt256.ofNat 18
  let r47 := r45 + UInt256.ofNat 2
  let r48 := r47 + ⟨1⟩
  let r50 := r48 + UInt256.ofNat 2
  let r51 := r50 + ⟨1⟩
  let r52 := r51 + ⟨1⟩
  let r53 := r52 + ⟨1⟩
  let r54 := r53 + ⟨1⟩
  let r55 := r54 + ⟨1⟩
  let r56 := r55 + ⟨1⟩
  let r57 := r56 + ⟨1⟩
  let r58 := r57 + ⟨1⟩
  let r59 := r58 + ⟨1⟩
  let r61 := r59 + UInt256.ofNat 2
  let r62 := r61 + ⟨1⟩
  let r63 := r62 + ⟨1⟩
  decode UniswapV2Pair.uniswapV2PairBytecode pc = some (.JUMPDEST, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p1 =
      some (.Push .PUSH1, some (⟨12⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p3 = some (.SLOAD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p4 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p6 = some (.EQ, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p7 =
      some (.Push .PUSH2, some (okPc, 2))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p10 = some (.JUMPI, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r0 =
      some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r2 = some (.DUP1, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r3 = some (.MLOAD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r4 =
      some (.Push .PUSH3, some (⟨4594637⟩, 3))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r8 =
      some (.Push .PUSH1, some (⟨229⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r10 = some (.SHL, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r11 = some (.DUP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r12 = some (.MSTORE, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r13 =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r15 =
      some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r17 = some (.DUP3, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r18 = some (.ADD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r19 = some (.MSTORE, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r20 =
      some (.Push .PUSH1, some (⟨17⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r22 =
      some (.Push .PUSH1, some (⟨36⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r24 = some (.DUP3, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r25 = some (.ADD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r26 = some (.MSTORE, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r27 =
      some (.Push .PUSH17,
        some (⟨7267690950230416977285330377544234619217⟩, 17))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r45 =
      some (.Push .PUSH1, some (⟨122⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r47 = some (.SHL, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r48 =
      some (.Push .PUSH1, some (⟨68⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r50 = some (.DUP3, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r51 = some (.ADD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r52 = some (.MSTORE, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r53 = some (.SWAP1, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r54 = some (.MLOAD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r55 = some (.SWAP1, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r56 = some (.DUP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r57 = some (.SWAP1, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r58 = some (.SUB, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r59 =
      some (.Push .PUSH1, some (⟨100⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r61 = some (.ADD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r62 = some (.SWAP1, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode r63 = some (.REVERT, .none)

/-- Discharge a Uniswap lock-entry locked-branch bytecode-shape proof. -/
macro "uniswap_lock_enter_locked_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapLockEnterLockedWf
    repeat' first | apply And.intro | native_decide)

-- LIBRARY CANDIDATE: Reasoning.Reach - generic solc reentrancy-lock locked revert prefix,
-- parameterized by bytecode, guard slot, unlocked word, revert string payload, entry PC, and
-- success PC.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapLockEnterLocked {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc okPc : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 pc R
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : uniswapLockEnterLockedWf pc okPc)
    (hlocked :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hov : R.length + 6 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd6, hd7, hd10, hr0, hr2, hr3, hr4, hr8, hr10, hr11,
      hr12, hr13, hr15, hr17, hr18, hr19, hr20, hr22, hr24, hr25, hr26, hr27,
      hr45, hr47, hr48, hr50, hr51, hr52, hr53, hr54, hr55, hr56, hr57, hr58,
      hr59, hr61, hr62, hr63⟩
  set lockedWord :=
    (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩))
    with hlockedWord
  have hlockedWord_ne : lockedWord ≠ ⟨1⟩ := by
    exact hlocked
  have heqZero : UInt256.eq (⟨1⟩ : UInt256) lockedWord = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hlockedWord_ne hbad.symm)
  have rd1 := h.jumpdest hd0 (by omega)
  have rd3 := rd1.push1 ⟨12⟩ hd1 (by omega)
  obtain ⟨_, _, rd4₀⟩ := rd3.sload hd3 (by omega)
  have rd4 := rd4₀
  rw [← hlockedWord] at rd4
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by simp only [List.length_cons]; omega)
  have rd7₀ := rd6.eq hd6 (by omega)
  have rd7 := rd7₀
  rw [heqZero] at rd7
  have rd10 := rd7.push2 okPc hd7 (by simp only [List.length_cons]; omega)
  have rdRevert := rd10.jumpiNT hd10 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by omega)
  have rdR4 := evm_run rdRevert with [
    raw push1 ⟨64⟩ hr0 (by evm_ov),
    raw dup1 hr2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hr3
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)]
  have rdR8 := rdR4.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) hr4 (by evm_ov)
  have rdR27 := evm_run rdR8 with [
    raw push1 ⟨229⟩ hr8 (by evm_ov),
    raw shl hr10 (by evm_ov),
    raw dup2 hr11 (by evm_ov),
    raw mstore 6 UniswapV2Pair.uniswapLockRevertMem0 (UInt256.ofNat 5) hr12
      mem_cost (by native_decide) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hr13 (by evm_ov),
    raw push1 ⟨4⟩ hr15 (by evm_ov),
    raw dup3 hr17 (by evm_ov),
    raw add hr18 (by evm_ov),
    raw mstore 3 UniswapV2Pair.uniswapLockRevertMem1 (UInt256.ofNat 6) hr19
      mem_cost (by native_decide) (by decide) (by evm_ov),
    raw push1 ⟨17⟩ hr20 (by evm_ov),
    raw push1 ⟨36⟩ hr22 (by evm_ov),
    raw dup3 hr24 (by evm_ov),
    raw add hr25 (by evm_ov),
    raw mstore 3 UniswapV2Pair.uniswapLockRevertMem2 (UInt256.ofNat 7) hr26
      mem_cost (by native_decide) (by decide) (by evm_ov)]
  have rdR45 := rdR27.pushConst
    (⟨7267690950230416977285330377544234619217⟩ : UInt256)
    (width := 17) (op := .PUSH17) (by decide) hr27 (by evm_ov)
  exact evm_run rdR45 with [
    raw push1 ⟨122⟩ hr45 (by evm_ov),
    raw shl hr47 (by evm_ov),
    raw push1 ⟨68⟩ hr48 (by evm_ov),
    raw dup3 hr50 (by evm_ov),
    raw add hr51 (by evm_ov),
    raw mstore 3 UniswapV2Pair.uniswapLockRevertMem3 (UInt256.ofNat 8) hr52
      mem_cost (by native_decide) (by decide) (by evm_ov),
    raw swap1 hr53 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hr54
      mem_cost UniswapV2Pair.uniswapLockRevertMem3_mload64 (by decide) (by evm_ov),
    raw swap1 hr55 (by evm_ov),
    raw dup2 hr56 (by evm_ov),
    raw swap1 hr57 (by evm_ov),
    raw sub hr58 (by evm_ov),
    raw push1 ⟨100⟩ hr59 (by evm_ov),
    raw add hr61 (by evm_ov),
    raw swap1 hr62 (by evm_ov),
    raw rev 0 hr63 mem_cost (by evm_ov)]

-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc full-slot address getter routine,
-- parameterized by bytecode, entry PC, storage slot, and the same shape predicate.
theorem RD.uniswapAddressSlotGetter {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc slot ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 pc (ret :: R) mem aw rdata
        (cA, σ) k C)
    (hwf : uniswapAddressSlotGetterWf pc slot)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (UInt256.land solcAddrMask
        (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) ::
        ret :: R) mem aw rdata (cA, σ) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 slot hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd2 (by simp only [List.length_cons]; omega)
  have rd6 := rd4.push1 ⟨1⟩ hd3 (by simp only [List.length_cons]; omega)
  have rd8 := rd6.push1 ⟨1⟩ hd4 (by simp only [List.length_cons]; omega)
  have rd10 := rd8.push1 ⟨160⟩ hd5 (by simp only [List.length_cons]; omega)
  have rd11 := rd10.shl hd6 (by simp only [List.length_cons]; omega)
  have rd12 := rd11.sub hd7 (by simp only [List.length_cons]; omega)
  have rd13 := rd12.and hd8 (by simp only [List.length_cons]; omega)
  have rd14 := rd13.dup2 hd9 (by omega)
  have rdRet := rd14.jump hd10 hret (by simp only [List.length_cons]; omega)
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  exact ⟨_, _, by simpa [hmask] using rdRet⟩

-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc full-slot uint256 getter routine,
-- parameterized by bytecode, entry PC, storage slot, and the same shape predicate.
theorem RD.uniswapWordSlotGetter {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc slot ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 pc (ret :: R) mem aw rdata
        (cA, σ) k C)
    (hwf : uniswapWordSlotGetterWf pc slot)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      ((σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) ::
        ret :: R) mem aw rdata (cA, σ) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd3, hd4⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 slot hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd2 (by simp only [List.length_cons]; omega)
  have rd5 := rd4.dup2 hd3 (by omega)
  have rdRet := rd5.jump hd4 hret (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rdRet⟩

-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc constant getter routine, parameterized by
-- bytecode, entry PC, pushed value, push width/opcode, and the same shape predicate.
theorem RD.uniswapConstGetter {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc val ret : UInt256} {width : Nat} {op : Operation.POp} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 pc (ret :: R) mem aw rdata
        (cA, σ) k C)
    (hwf : uniswapConstGetterWf pc val width op)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret (val :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  rcases hwf with ⟨hd0, hop, hd1, hdNext, hdJump⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rdNext := rd1.pushConst val (width := width) (op := op) hop hd1
    (by simp only [List.length_cons]; omega)
  have rdDup := rdNext.dup2 hdNext (by omega)
  have rdRet := rdDup.jump hdJump hret (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rdRet⟩

-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc one-word address return wrapper,
-- parameterized by bytecode, entry PC, and return-tail bytecode shape.
/-- Uniswap's address-return wrapper at pc 825. -/
theorem RD.uniswapReturnAddress825 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨825⟩ (val :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 9 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0 acc
      (UInt256.toByteArray (UInt256.land val solcAddrMask)) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap3, and, dup3,
    raw mstore 6 (solcReturnMem (UInt256.land val solcAddrMask)) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rfl)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (solcReturnMem_mload64 (UInt256.land val solcAddrMask))
      (by decide) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨32⟩, add, swap1,
    raw ret 0 (UInt256.toByteArray (UInt256.land val solcAddrMask)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        simpa using solcReturnMem_read128 (UInt256.land val solcAddrMask))
      (by evm_ov) ]

-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc one-word uint256 return wrapper,
-- parameterized by bytecode, entry PC, and return-tail bytecode shape.
/-- Uniswap's uint256-return wrapper at pc 861. -/
theorem RD.uniswapReturnWord861 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨861⟩ (val :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 5 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0 acc (UInt256.toByteArray val) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    swap2, dup3,
    raw mstore 6 (solcReturnMem val) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (solcReturnMem_mload64 val)
      (by decide) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨32⟩, add, swap1,
    raw ret 0 (UInt256.toByteArray val) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        simpa using solcReturnMem_read128 val)
      (by evm_ov) ]

-- GENERALIZES Reasoning.Reach/RD.uniswapReturnWord861 — same solc one-word return wrapper,
-- but parameterized over the incoming scratch memory and the post-MSTORE return memory.
-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc one-word return wrapper from arbitrary memory.
theorem RD.uniswapReturnWord861FromMem {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256} {mem memout rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨861⟩ (val :: ret :: R)
        mem (UInt256.ofNat 3) rdata acc k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout : (UInt256.toByteArray val).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 : memout.readWithPadding 128 32 = UInt256.toByteArray val)
    (hov : R.length + 5 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0 acc (UInt256.toByteArray val) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      hmload64
      (by decide) (by evm_ov),
    swap2, dup3,
    raw mstore 6 memout (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      hmemoutLoad64
      (by decide) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨32⟩, add, swap1,
    raw ret 0 (UInt256.toByteArray val) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov) ]

-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc one-word uint8 return wrapper,
-- parameterized by bytecode, entry PC, and return-tail bytecode shape.
/-- Uniswap's uint8-return wrapper for `decimals()` at pc 949. -/
theorem RD.uniswapReturnUint8_949 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨949⟩ (val :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 9 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0 acc
      (UInt256.toByteArray (UInt256.land val ⟨255⟩)) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    push1 ⟨255⟩, swap1, swap3, and, dup3,
    raw mstore 6 (solcReturnMem (UInt256.land val ⟨255⟩)) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (solcReturnMem_mload64 (UInt256.land val ⟨255⟩))
      (by decide) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨32⟩, add, swap1,
    raw ret 0 (UInt256.toByteArray (UInt256.land val ⟨255⟩)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        simpa using solcReturnMem_read128 (UInt256.land val ⟨255⟩))
      (by evm_ov) ]

-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc external thunk for a storage address getter,
-- parameterized by bytecode, thunk PC, getter-routine PC, return-wrapper PC, and storage slot.
theorem RD.uniswapAddressGetterExternal {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {entry routine slot : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : uniswapAddressGetterEntryWf entry routine)
    (hgetter : uniswapAddressSlotGetterWf routine slot)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hret825 : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ⟨825⟩ = true) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UniswapV2Pair.uniswapAddressReturnWord slot σ I)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.uniswapGetterThunk (returnPc := ⟨825⟩)
    hreach hentry hroutine
  obtain ⟨_, _, rd825⟩ := RD.uniswapAddressSlotGetter (slot := slot) (R := [sel]) rdRoutine
    hgetter hret825 (by simp only [List.length_singleton]; omega)
  have hret := RD.uniswapReturnAddress825
    (val := UInt256.land solcAddrMask (UniswapV2Pair.uniswapSlotWord slot σ I))
    (ret := ⟨825⟩) (R := [sel]) rd825
    (by simp only [List.length_singleton]; omega)
  have hclean :
      UInt256.land
          (UInt256.land solcAddrMask (UniswapV2Pair.uniswapSlotWord slot σ I)) solcAddrMask =
        UniswapV2Pair.uniswapAddressReturnWord slot σ I := by
    rw [u256_land_comm solcAddrMask (UniswapV2Pair.uniswapSlotWord slot σ I)]
    exact solcAddrMask_clean
      (solcAddrMask_result_canonical (UniswapV2Pair.uniswapSlotWord slot σ I))
  simpa [hclean] using hret

-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc external thunk for a storage uint256 getter,
-- parameterized by bytecode, thunk PC, getter-routine PC, return-wrapper PC, and storage slot.
theorem RD.uniswapWordGetterExternal {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {entry routine slot : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : uniswapWordGetterEntryWf entry routine)
    (hgetter : uniswapWordSlotGetterWf routine slot)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hret861 : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ⟨861⟩ = true) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UniswapV2Pair.uniswapSlotWord slot σ I)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.uniswapGetterThunk (returnPc := ⟨861⟩)
    hreach hentry hroutine
  obtain ⟨_, _, rd861⟩ := RD.uniswapWordSlotGetter (slot := slot) (R := [sel]) rdRoutine
    hgetter hret861 (by simp only [List.length_singleton]; omega)
  exact RD.uniswapReturnWord861
    (val := UniswapV2Pair.uniswapSlotWord slot σ I) (ret := ⟨861⟩) (R := [sel]) rd861
    (by simp only [List.length_singleton]; omega)

-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc external thunk for a word-returning constant
-- getter, parameterized by bytecode, thunk PC, getter-routine PC, return-wrapper PC, and literal.
theorem RD.uniswapWordConstGetterExternal {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {entry routine val : UInt256} {width : Nat} {op : Operation.POp}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : uniswapWordGetterEntryWf entry routine)
    (hgetter : uniswapConstGetterWf routine val width op)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hret861 : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ⟨861⟩ = true) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray val) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.uniswapGetterThunk (returnPc := ⟨861⟩)
    hreach hentry hroutine
  obtain ⟨_, _, rd861⟩ := RD.uniswapConstGetter (val := val) (width := width) (op := op)
    (R := [sel]) rdRoutine hgetter hret861 (by simp only [List.length_singleton]; omega)
  exact RD.uniswapReturnWord861 (val := val) (ret := ⟨861⟩) (R := [sel]) rd861
    (by simp only [List.length_singleton]; omega)

-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc external thunk for a uint8-returning constant
-- getter, parameterized by bytecode, thunk PC, getter-routine PC, return-wrapper PC, and literal.
theorem RD.uniswapUint8ConstGetterExternal {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {entry routine val : UInt256} {width : Nat} {op : Operation.POp}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : uniswapGetterEntryWf entry ⟨949⟩ routine)
    (hgetter : uniswapConstGetterWf routine val width op)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hret949 : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ⟨949⟩ = true) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land val ⟨255⟩)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.uniswapGetterThunk (returnPc := ⟨949⟩)
    hreach hentry hroutine
  obtain ⟨_, _, rd949⟩ := RD.uniswapConstGetter (val := val) (width := width) (op := op)
    (R := [sel]) rdRoutine hgetter hret949 (by simp only [List.length_singleton]; omega)
  exact RD.uniswapReturnUint8_949 (val := val) (ret := ⟨949⟩) (R := [sel]) rd949
    (by simp only [List.length_singleton]; omega)

end Reasoning.Reach

namespace UniswapV2Pair

open Reasoning.Refinement

theorem uniswapAddressGetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot : UInt256}
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldata (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : Reasoning.Reach.uniswapAddressGetterEntryWf entry routine)
    (hgetter : Reasoning.Reach.uniswapAddressSlotGetterWf routine slot)
    (hroutine : (D_J uniswapV2PairBytecode 0).contains routine = true)
    (hreturn : transition.returnType = some addr)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.address (AccountAddress.ofNat
            (uniswapAddressReturnWord slot σ_solm I).toNat))))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : uniswapSlotWord slot σ_evm I = uniswapSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some (Value.address (AccountAddress.ofNat (uniswapAddressReturnWord slot σ_solm I).toNat)) =
        some (Value.address (AccountAddress.ofNat (uniswapAddressReturnWord slot σ_evm I).toNat)) := by
    have hslot : uniswapSlotWord slot σ_solm I = uniswapSlotWord slot σ_evm I := hword.symm
    simp [uniswapAddressReturnWord, hslot]
  have henc :
      returnEquiv (UInt256.toByteArray (uniswapAddressReturnWord slot σ_evm I))
        (some (.address (AccountAddress.ofNat (uniswapAddressReturnWord slot σ_evm I).toNat)))
        transition.returnType := by
    rw [hreturn]
    simpa [uniswapAddressReturnWord] using
      (returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (uniswapSlotWord slot σ_evm I)))
  exact (RD.uniswapAddressGetterExternal (g := Sat256.ofUInt256 g)
      (entry := entry) (routine := routine) (slot := slot) hreach hentry hgetter hroutine
      (by jump_dest)).reEquivExecutionTransport
    hcode hdispatch hdecode hbody hval hAccounts henc

theorem uniswapUint256GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot : UInt256}
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldata (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : Reasoning.Reach.uniswapWordGetterEntryWf entry routine)
    (hgetter : Reasoning.Reach.uniswapWordSlotGetterWf routine slot)
    (hroutine : (D_J uniswapV2PairBytecode 0).contains routine = true)
    (hreturn : transition.returnType = some uint256)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int (Int.ofNat (uniswapSlotWord slot σ_solm I).toNat))))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : uniswapSlotWord slot σ_evm I = uniswapSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some (Value.int (Int.ofNat (uniswapSlotWord slot σ_solm I).toNat)) =
        some (Value.int (Int.ofNat (uniswapSlotWord slot σ_evm I).toNat)) := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (uniswapSlotWord slot σ_evm I))
        (some (.int (Int.ofNat (uniswapSlotWord slot σ_evm I).toNat)))
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (uniswapSlotWord slot σ_evm I))
  exact (RD.uniswapWordGetterExternal (g := Sat256.ofUInt256 g)
      (entry := entry) (routine := routine) (slot := slot) hreach hentry hgetter hroutine
      (by jump_dest)).reEquivExecutionTransport
    hcode hdispatch hdecode hbody hval hAccounts henc

theorem uniswapBytes32GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot : UInt256}
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldata (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : Reasoning.Reach.uniswapWordGetterEntryWf entry routine)
    (hgetter : Reasoning.Reach.uniswapWordSlotGetterWf routine slot)
    (hroutine : (D_J uniswapV2PairBytecode 0).contains routine = true)
    (hreturn : transition.returnType = some bytes32)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.fixedBytes ⟨31, by decide⟩
            (EVM.Word.toBytesBE (uniswapSlotWord slot σ_solm I)))))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : uniswapSlotWord slot σ_evm I = uniswapSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some (Value.fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (uniswapSlotWord slot σ_solm I))) =
        some (Value.fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (uniswapSlotWord slot σ_evm I))) := by
    rw [← hword]
  have henc :
      returnEquiv (UInt256.toByteArray (uniswapSlotWord slot σ_evm I))
        (some (.fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (uniswapSlotWord slot σ_evm I))))
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [bytes32] using bytes32ReturnEncoding (uniswapSlotWord slot σ_evm I))
  exact (RD.uniswapWordGetterExternal (g := Sat256.ofUInt256 g)
      (entry := entry) (routine := routine) (slot := slot) hreach hentry hgetter hroutine
      (by jump_dest)).reEquivExecutionTransport
    hcode hdispatch hdecode hbody hval hAccounts henc

end UniswapV2Pair
