import Examples.UniswapV2Pair.Bytecode
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Refinement
import Reasoning.Solc
import Reasoning.SolmBody
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! # Shared Uniswap V2 Pair proof helpers -/

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev uniswapSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-! ## Shared caller/address helpers -/

abbrev uniswapSourceWord (I : ExecutionEnv) : UInt256 :=
  solcSourceWord I

theorem uniswapSourceWord_toNat (I : ExecutionEnv) :
    (uniswapSourceWord I).toNat = I.source.val := by
  exact solcSourceWord_toNat I

theorem uniswapSourceWord_canonical (I : ExecutionEnv) :
    (uniswapSourceWord I).toNat < EVM.addressModulus := by
  exact solcSourceWord_canonical I

theorem uniswapSource_ofNat (I : ExecutionEnv) :
    AccountAddress.ofNat (uniswapSourceWord I).toNat = I.source := by
  exact solcSource_ofNat I

theorem uniswapMaskedAddress_eq_source_of_word_eq {w : UInt256} {I : ExecutionEnv}
    (h : UInt256.land w solcAddrMask = uniswapSourceWord I) :
    AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat = I.source := by
  exact solcMaskedAddress_eq_source_of_word_eq h

/-! ## Shared scalar storage and return helpers -/

theorem uniswapStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (addrLoc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  simpa [addrLoc, addressOffset0Loc] using storageLocLoad_address_offset0 evm slot

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

abbrev uniswapUint256Value (w : UInt256) : Value :=
  uint256Value w

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
  exact nonpayableRequireAssignStorageBlock hwv
    (evalExpr_uniswap_unlocked_eq_one_true evm locals hbase hunlocked)
    (by simp [evalExpr?, pure])
    (uniswapAssignUnlockedZero evm locals hbase)

theorem uniswapLockEnterNonpayableRevert (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := locals } evm lockEnter .reverted := by
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .require (.binary .eq (.storage unlockedRef) (.intLit 1)),
      .assign .storage unlockedRef (.intLit 0) ]
    .reverted
  exact blockReverts_nonPayable hwv

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
  exact nonpayableSecondRequireReverts hwv
    (evalExpr_uniswap_unlocked_eq_one_false evm locals hbase hlocked)

theorem uniswapLockExitSuffix (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "unlocked" = none) :
    ExecBlock config { contract := contract, locals := locals } evm lockExit
      (.ok { contract := contract, locals := locals } (uniswapLockExitedState evm)) := by
  change ExecBlock config { contract := contract, locals := locals } evm
    [ .assign .storage unlockedRef (.intLit 1) ]
    (.ok { contract := contract, locals := locals } (uniswapLockExitedState evm))
  exact assignStorageBlock (by simp [evalExpr?, pure])
    (uniswapAssignUnlockedOne evm locals hbase)

/-! ## Packed reserve-slot helpers -/

abbrev reserve112Shift : UInt256 := UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩
abbrev reserve112Mask : UInt256 := UInt256.sub reserve112Shift ⟨1⟩
abbrev reserve224Shift : UInt256 := UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨224⟩
abbrev reserve32Mask : UInt256 := ⟨4294967295⟩

theorem uniswapStorageLocLoad_uint112_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint112Loc0 slot) =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) reserve112Mask).toNat) := by
  rw [← show UInt256.ofNat (2 ^ (8 * 14) - 1) = reserve112Mask by native_decide]
  simpa [uint112Loc0, uint112Int] using
    storageLocLoad_uint_offset0 evm slot (14 : Fin 33) ⟨112, by decide⟩ (by decide)

theorem uniswapStorageLocLoad_uint112_offset14 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint112Loc14 slot) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          reserve112Shift) reserve112Mask).toNat) := by
  rw [← show UInt256.ofNat (256 ^ 14) = reserve112Shift by native_decide]
  rw [← show UInt256.ofNat (256 ^ 14 - 1) = reserve112Mask by native_decide]
  simpa [uint112Loc14, uint112Int] using
    storageLocLoad_uint_offset evm slot (14 : Fin 32) (14 : Fin 33) ⟨112, by decide⟩
      (by decide) (by decide)

theorem uniswapStorageLocLoad_uint32_offset28 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint32Loc28 slot) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          reserve224Shift) reserve32Mask).toNat) := by
  rw [← show UInt256.ofNat (256 ^ 28) = reserve224Shift by native_decide]
  rw [← show UInt256.ofNat (256 ^ 4 - 1) = reserve32Mask by native_decide]
  simpa [uint32Loc28, uint32Int] using
    storageLocLoad_uint_offset evm slot (28 : Fin 32) (4 : Fin 33) ⟨32, by decide⟩
      (by decide) (by decide)

abbrev uniswapReserve0Word (evm : EVM.State) : UInt256 :=
  UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩) reserve112Mask

abbrev uniswapReserve1Word (evm : EVM.State) : UInt256 :=
  UInt256.land
    (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩) reserve112Shift)
    reserve112Mask

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
  exact evalExpr_storage_scalar_value hbase her hty hloc
    (uniswapStorageLocLoad_uint112_offset0 evm slot)

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
  exact evalExpr_storage_scalar_value hbase her hty hloc
    (uniswapStorageLocLoad_uint112_offset14 evm slot)

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

theorem uniswapStorageLocStore_uint112_offset0_int_some
    (evm : EVM.State) (slot : UInt256) (n : Int) :
    ∃ evm', storageLocStore evm (uint112Loc0 slot) (.int n) = some evm' := by
  exact storageLocStore_int_some evm (uint112Loc0 slot) n

theorem uniswapStorageLocStore_uint112_offset14_int_some
    (evm : EVM.State) (slot : UInt256) (n : Int) :
    ∃ evm', storageLocStore evm (uint112Loc14 slot) (.int n) = some evm' := by
  exact storageLocStore_int_some evm (uint112Loc14 slot) n

theorem uniswapStorageLocStore_uint32_offset28_int_some
    (evm : EVM.State) (slot : UInt256) (n : Int) :
    ∃ evm', storageLocStore evm (uint32Loc28 slot) (.int n) = some evm' := by
  exact storageLocStore_int_some evm (uint32Loc28 slot) n

def setUint112Offset0Word (old val : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land reserve112Mask val)
    (UInt256.land (UInt256.lnot reserve112Mask) old)

def setUint112Offset14Word (old val : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.mul reserve112Shift (UInt256.land reserve112Mask val))
    (UInt256.land (UInt256.lnot (UInt256.shiftLeft reserve112Mask ⟨112⟩)) old)

def setUint32Offset28Word (old val : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.mul (UInt256.land val reserve32Mask) reserve224Shift)
    (UInt256.land (UInt256.sub reserve224Shift ⟨1⟩) old)

theorem uniswapUint112Masked_lt (w : UInt256) :
    (UInt256.land w reserve112Mask).toNat < 2 ^ 112 := by
  rw [u256_land_toNat]
  have hmask : reserve112Mask.toNat = 2 ^ 112 - 1 := by native_decide
  rw [hmask]
  have hle : Nat.land w.toNat (2 ^ 112 - 1) ≤ 2 ^ 112 - 1 :=
    nat_land_le_right _ _
  have hltSize : Nat.land w.toNat (2 ^ 112 - 1) < UInt256.size := by
    exact lt_of_le_of_lt hle (by norm_num [UInt256.size])
  rw [Nat.mod_eq_of_lt hltSize]
  exact lt_of_le_of_lt hle (by norm_num)

theorem uniswapUint32Masked_lt (w : UInt256) :
    (UInt256.land w reserve32Mask).toNat < 2 ^ 32 := by
  rw [u256_land_toNat]
  have hmask : reserve32Mask.toNat = 2 ^ 32 - 1 := by native_decide
  rw [hmask]
  have hle : Nat.land w.toNat (2 ^ 32 - 1) ≤ 2 ^ 32 - 1 :=
    nat_land_le_right _ _
  have hltSize : Nat.land w.toNat (2 ^ 32 - 1) < UInt256.size := by
    exact lt_of_le_of_lt hle (by norm_num [UInt256.size])
  rw [Nat.mod_eq_of_lt hltSize]
  exact lt_of_le_of_lt hle (by norm_num)

theorem uniswapUint112Masked_toNat (w : UInt256) :
    (UInt256.land w reserve112Mask).toNat = w.toNat % 2 ^ 112 := by
  rw [u256_land_toNat]
  have hmask : reserve112Mask.toNat = 2 ^ 112 - 1 := by native_decide
  rw [hmask]
  rw [nat_land_mask_eq_mod]
  exact Nat.mod_eq_of_lt (by
    exact lt_trans (Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 112))
      (by norm_num [UInt256.size]))

-- LIBRARY CANDIDATE: generalizes a packed storage field clear for a middle byte range.
set_option maxHeartbeats 1000000 in
theorem natLandClearMiddle112_224 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n ((2 ^ 112 - 1) + (2 ^ 32 - 1) * 2 ^ 224) =
      n % 2 ^ 112 + (n / 2 ^ 224) * 2 ^ 224 := by
  have hlowLt : n % 2 ^ 112 < 2 ^ 224 := by
    exact lt_trans (Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 112)) (by norm_num)
  have hmaskLowLt : 2 ^ 112 - 1 < 2 ^ 224 := by norm_num
  have hmaskEq :
      Nat.lor (2 ^ 112 - 1) ((2 ^ 32 - 1) * 2 ^ 224) =
        (2 ^ 112 - 1) + (2 ^ 32 - 1) * 2 ^ 224 := by
    rw [nat_lor_shift_add (2 ^ 112 - 1) (2 ^ 32 - 1) 224 hmaskLowLt]
  have hrhsEq :
      Nat.lor (n % 2 ^ 112) ((n / 2 ^ 224) * 2 ^ 224) =
        n % 2 ^ 112 + (n / 2 ^ 224) * 2 ^ 224 := by
    rw [nat_lor_shift_add (n % 2 ^ 112) (n / 2 ^ 224) 224 hlowLt]
  rw [← hmaskEq, ← hrhsEq]
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& ((2 ^ 112 - 1) ||| ((2 ^ 32 - 1) * 2 ^ 224))).testBit i =
    ((n % 2 ^ 112) ||| (n / 2 ^ 224 * 2 ^ 224)).testBit i
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_or]
  rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  rw [show (2 ^ 32 - 1) * 2 ^ 224 = (2 ^ 32 - 1) <<< 224 by
    rw [Nat.shiftLeft_eq]]
  rw [show n / 2 ^ 224 * 2 ^ 224 = (n / 2 ^ 224) <<< 224 by
    rw [Nat.shiftLeft_eq]]
  rw [nat_testBit_shiftLeft, nat_testBit_shiftLeft]
  by_cases hi112 : i < 112
  · have hi224 : i < 224 := by omega
    simp [hi112, hi224]
  · by_cases hi224 : i < 224
    · simp [hi112, hi224]
    · have h224le : 224 ≤ i := Nat.le_of_not_gt hi224
      rw [Nat.testBit_two_pow_sub_one]
      by_cases hi256 : i < 256
      · have hsub32 : i - 224 < 32 := by omega
        rw [show decide (i - 224 < 32) = true by simp [hsub32]]
        rw [nat_div_pow_testBit n 224 i h224le]
        simp [hi112, hi224]
      · have hsub32 : ¬ (i - 224 < 32) := by omega
        rw [show decide (i - 224 < 32) = false by simp [hsub32]]
        have hnfalse : n.testBit i = false := by
          have hpow : n < 2 ^ i :=
            lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega))
          exact Nat.testBit_lt_two_pow hpow
        rw [nat_div_pow_testBit n 224 i h224le, hnfalse]
        simp [hi112, hi224]

theorem uint112Offset14MiddleClear_toNat (old : UInt256) :
    (UInt256.land (UInt256.lnot (UInt256.shiftLeft reserve112Mask ⟨112⟩)) old).toNat =
      (UInt256.land old reserve112Mask).toNat + (old.toNat / 2 ^ 224) * 2 ^ 224 := by
  rw [u256_land_toNat]
  have hmask :
      (UInt256.lnot (UInt256.shiftLeft reserve112Mask ⟨112⟩)).toNat =
        (2 ^ 112 - 1) + (2 ^ 32 - 1) * 2 ^ 224 := by
    native_decide
  rw [hmask, nat_land_comm]
  rw [natLandClearMiddle112_224 old.toNat old.val.isLt]
  have hlt :
      old.toNat % 2 ^ 112 + old.toNat / 2 ^ 224 * 2 ^ 224 < UInt256.size := by
    have hlow : old.toNat % 2 ^ 112 < 2 ^ 112 := Nat.mod_lt _ (by positivity)
    have hq : old.toNat / 2 ^ 224 < 2 ^ 32 := by
      apply Nat.div_lt_of_lt_mul
      rw [show 2 ^ 224 * 2 ^ 32 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
      exact old.val.isLt
    have hlowle : old.toNat % 2 ^ 112 ≤ 2 ^ 112 - 1 := by omega
    have hqle : old.toNat / 2 ^ 224 ≤ 2 ^ 32 - 1 := Nat.le_pred_of_lt hq
    have hqterm : old.toNat / 2 ^ 224 * 2 ^ 224 ≤ (2 ^ 32 - 1) * 2 ^ 224 :=
      Nat.mul_le_mul_right _ hqle
    have hmax : (2 ^ 112 - 1) + (2 ^ 32 - 1) * 2 ^ 224 < UInt256.size := by
      norm_num [UInt256.size, Nat.pow_add]
    omega
  rw [Nat.mod_eq_of_lt hlt, uniswapUint112Masked_toNat]

-- LIBRARY CANDIDATE: disjoint `lor` recomposition for low/middle/high packed fields.
theorem natLorLowMiddleHigh112_224 (low mid high : Nat)
    (hlow : low < 2 ^ 112) (hmid : mid < 2 ^ 112) :
    Nat.lor (mid * 2 ^ 112) (low + high * 2 ^ 224) =
      low + mid * 2 ^ 112 + high * 2 ^ 224 := by
  have hlow224 : low < 2 ^ 224 := lt_trans hlow (by norm_num)
  have hlowHigh : Nat.lor low (high * 2 ^ 224) = low + high * 2 ^ 224 := by
    exact nat_lor_shift_add low high 224 hlow224
  rw [← hlowHigh]
  rw [nat_lor_comm (mid * 2 ^ 112) (Nat.lor low (high * 2 ^ 224))]
  rw [show Nat.lor (Nat.lor low (high * 2 ^ 224)) (mid * 2 ^ 112) =
      Nat.lor low (Nat.lor (high * 2 ^ 224) (mid * 2 ^ 112)) from
    Nat.lor_assoc low (high * 2 ^ 224) (mid * 2 ^ 112)]
  rw [nat_lor_comm (high * 2 ^ 224) (mid * 2 ^ 112)]
  have hmidShift : mid * 2 ^ 112 < 2 ^ 224 := by
    calc
      mid * 2 ^ 112 < 2 ^ 112 * 2 ^ 112 :=
        Nat.mul_lt_mul_of_pos_right hmid (by positivity)
      _ = 2 ^ 224 := by rw [← Nat.pow_add]
  rw [nat_lor_shift_add (mid * 2 ^ 112) high 224 hmidShift]
  rw [show mid * 2 ^ 112 + high * 2 ^ 224 =
      (mid + high * 2 ^ 112) * 2 ^ 112 by ring]
  rw [nat_lor_shift_add low (mid + high * 2 ^ 112) 112 hlow]
  ring

theorem setUint112Offset0Word_toNat (old val : UInt256) :
    (setUint112Offset0Word old val).toNat =
      (UInt256.land reserve112Mask val).toNat + (old.toNat / 2 ^ 112) * 2 ^ 112 := by
  unfold setUint112Offset0Word
  rw [u256_lor_toNat]
  have hhigh :
      (UInt256.land (UInt256.lnot reserve112Mask) old).toNat =
        (old.toNat / 2 ^ 112) * 2 ^ 112 := by
    rw [u256_land_toNat]
    have hlnot : (UInt256.lnot reserve112Mask).toNat = 2 ^ 256 - 2 ^ 112 := by
      native_decide
    rw [hlnot, nat_land_comm]
    rw [natLandClearLow old.toNat 112 (by norm_num) old.val.isLt]
    have hlt : old.toNat / 2 ^ 112 * 2 ^ 112 < UInt256.size :=
      lt_of_le_of_lt (Nat.div_mul_le_self _ _) old.val.isLt
    rw [Nat.mod_eq_of_lt hlt]
  rw [hhigh]
  rw [nat_lor_shift_add]
  · have hlt :
        (UInt256.land reserve112Mask val).toNat +
            old.toNat / 2 ^ 112 * 2 ^ 112 < UInt256.size := by
      have hlow : (UInt256.land reserve112Mask val).toNat < 2 ^ 112 := by
        simpa [u256_land_comm reserve112Mask val] using uniswapUint112Masked_lt val
      have hq : old.toNat / 2 ^ 112 < 2 ^ 144 := by
        apply Nat.div_lt_of_lt_mul
        rw [show 2 ^ 112 * 2 ^ 144 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
        exact old.val.isLt
      have hlowle : (UInt256.land reserve112Mask val).toNat ≤ 2 ^ 112 - 1 := by
        omega
      have hqle : old.toNat / 2 ^ 112 ≤ 2 ^ 144 - 1 := Nat.le_pred_of_lt hq
      have hqterm :
          old.toNat / 2 ^ 112 * 2 ^ 112 ≤ (2 ^ 144 - 1) * 2 ^ 112 :=
        Nat.mul_le_mul_right _ hqle
      have hmax : (2 ^ 112 - 1) + (2 ^ 144 - 1) * 2 ^ 112 < UInt256.size := by
        norm_num [UInt256.size, Nat.pow_add]
      omega
    rw [Nat.mod_eq_of_lt hlt]
  · simpa [u256_land_comm reserve112Mask val] using uniswapUint112Masked_lt val

set_option maxHeartbeats 1000000 in
theorem setUint112Offset14Word_toNat (old val : UInt256) :
    (setUint112Offset14Word old val).toNat =
      (UInt256.land old reserve112Mask).toNat +
        (UInt256.land reserve112Mask val).toNat * 2 ^ 112 +
      (old.toNat / 2 ^ 224) * 2 ^ 224 := by
  unfold setUint112Offset14Word
  rw [u256_lor_toNat, u256_mul_toNat, uint112Offset14MiddleClear_toNat]
  have hshift : reserve112Shift.toNat = 2 ^ 112 := by native_decide
  rw [hshift]
  have hmidLt : (UInt256.land reserve112Mask val).toNat < 2 ^ 112 := by
    simpa [u256_land_comm reserve112Mask val] using uniswapUint112Masked_lt val
  have hmulLt : 2 ^ 112 * (UInt256.land reserve112Mask val).toNat < UInt256.size := by
    calc
      2 ^ 112 * (UInt256.land reserve112Mask val).toNat < 2 ^ 112 * 2 ^ 112 :=
        Nat.mul_lt_mul_of_pos_left hmidLt (by positivity)
      _ < UInt256.size := by norm_num [UInt256.size, Nat.pow_add]
  rw [Nat.mod_eq_of_lt hmulLt]
  rw [show 2 ^ 112 * (UInt256.land reserve112Mask val).toNat =
      (UInt256.land reserve112Mask val).toNat * 2 ^ 112 by ring]
  rw [natLorLowMiddleHigh112_224]
  · have hlt :
        (UInt256.land old reserve112Mask).toNat +
            (UInt256.land reserve112Mask val).toNat * 2 ^ 112 +
          old.toNat / 2 ^ 224 * 2 ^ 224 < UInt256.size := by
      have hlow := uniswapUint112Masked_lt old
      have hq : old.toNat / 2 ^ 224 < 2 ^ 32 := by
        apply Nat.div_lt_of_lt_mul
        rw [show 2 ^ 224 * 2 ^ 32 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
        exact old.val.isLt
      have hlowle : (UInt256.land old reserve112Mask).toNat ≤ 2 ^ 112 - 1 := by
        omega
      have hmidle : (UInt256.land reserve112Mask val).toNat ≤ 2 ^ 112 - 1 := by
        omega
      have hqle : old.toNat / 2 ^ 224 ≤ 2 ^ 32 - 1 := Nat.le_pred_of_lt hq
      have hmidterm :
          (UInt256.land reserve112Mask val).toNat * 2 ^ 112 ≤ (2 ^ 112 - 1) * 2 ^ 112 :=
        Nat.mul_le_mul_right _ hmidle
      have hqterm :
          old.toNat / 2 ^ 224 * 2 ^ 224 ≤ (2 ^ 32 - 1) * 2 ^ 224 :=
        Nat.mul_le_mul_right _ hqle
      have hmax :
          (2 ^ 112 - 1) + (2 ^ 112 - 1) * 2 ^ 112 +
            (2 ^ 32 - 1) * 2 ^ 224 < UInt256.size := by
        norm_num [UInt256.size, Nat.pow_add]
      omega
    rw [Nat.mod_eq_of_lt hlt]
  · exact uniswapUint112Masked_lt old
  · exact hmidLt

theorem setUint32Offset28Word_toNat (old val : UInt256) :
    (setUint32Offset28Word old val).toNat =
      old.toNat % 2 ^ 224 + (UInt256.land val reserve32Mask).toNat * 2 ^ 224 := by
  unfold setUint32Offset28Word
  rw [u256_lor_toNat, u256_mul_toNat]
  have hshift : reserve224Shift.toNat = 2 ^ 224 := by native_decide
  rw [hshift]
  have hlow :
      (UInt256.land (UInt256.sub reserve224Shift ⟨1⟩) old).toNat =
        old.toNat % 2 ^ 224 := by
    rw [u256_land_toNat]
    have hmask : (UInt256.sub reserve224Shift ⟨1⟩).toNat = 2 ^ 224 - 1 := by
      native_decide
    rw [hmask, nat_land_comm, nat_land_mask_eq_mod]
    exact Nat.mod_eq_of_lt (by
      exact lt_trans (Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 224))
        (by norm_num [UInt256.size]))
  rw [hlow]
  have hmulLt : (UInt256.land val reserve32Mask).toNat * 2 ^ 224 < UInt256.size := by
    calc
      (UInt256.land val reserve32Mask).toNat * 2 ^ 224 < 2 ^ 32 * 2 ^ 224 :=
        Nat.mul_lt_mul_of_pos_right (uniswapUint32Masked_lt val) (by positivity)
      _ = UInt256.size := by norm_num [UInt256.size, Nat.pow_add]
  rw [Nat.mod_eq_of_lt hmulLt]
  rw [nat_lor_comm]
  rw [nat_lor_shift_add]
  · have hlt :
        old.toNat % 2 ^ 224 + (UInt256.land val reserve32Mask).toNat * 2 ^ 224 <
          UInt256.size := by
      have hlowLt : old.toNat % 2 ^ 224 < 2 ^ 224 := Nat.mod_lt _ (by positivity)
      have hval := uniswapUint32Masked_lt val
      have hlowle : old.toNat % 2 ^ 224 ≤ 2 ^ 224 - 1 := by omega
      have hvalle : (UInt256.land val reserve32Mask).toNat ≤ 2 ^ 32 - 1 := by omega
      have hvterm :
          (UInt256.land val reserve32Mask).toNat * 2 ^ 224 ≤ (2 ^ 32 - 1) * 2 ^ 224 :=
        Nat.mul_le_mul_right _ hvalle
      have hmax : (2 ^ 224 - 1) + (2 ^ 32 - 1) * 2 ^ 224 < UInt256.size := by
        norm_num [UInt256.size, Nat.pow_add]
      omega
    rw [Nat.mod_eq_of_lt hlt]
  · exact Nat.mod_lt _ (by positivity : 0 < (2 : Nat) ^ 224)

theorem uniswapStorageLocStore_uint112_offset0 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (uint112Loc0 slot) (uniswapUint256Value val) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint112Offset0Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val)) := by
  unfold storageLocStore storageLocWriteWord uint112Loc0 uniswapUint256Value uint256Value
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  have hvlen := (EVM.Word.toBytesLEWithSizeProof val).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (14 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (14 : Fin 33).val) _) =
      (setUint112Offset0Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (14 : Fin 33).val = 14 from rfl,
    List.take_zero, List.nil_append]
  rw [fromBytes'_append, fromBytes'_take_wordLE_land_mask val 14 (by decide),
    fromBytes'_drop_wordLE]
  have hlen14 : ((EVM.Word.toBytesLEWithSizeProof val).1.take 14).length = 14 := by
    rw [List.length_take, hvlen]
    norm_num
  rw [hlen14]
  rw [show 2 ^ (8 * 14) = 2 ^ 112 by norm_num]
  rw [show 256 ^ 14 = 2 ^ 112 by norm_num]
  rw [setUint112Offset0Word_toNat]
  rw [show UInt256.ofNat (2 ^ 112 - 1) = reserve112Mask by native_decide]
  rw [u256_land_comm val reserve112Mask]
  ring_nf

theorem uniswapStorageLocStore_uint112_offset14 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (uint112Loc14 slot) (uniswapUint256Value val) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint112Offset14Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val)) := by
  unfold storageLocStore storageLocWriteWord uint112Loc14 uniswapUint256Value uint256Value
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof val).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (14 : Fin 32).val _ ++ List.take (14 : Fin 33).val _
        ++ List.drop ((14 : Fin 32).val + (14 : Fin 33).val) _) =
      (setUint112Offset14Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val).toNat
  rw [show (14 : Fin 32).val = 14 from rfl, show (14 : Fin 33).val = 14 from rfl,
    show (14 : Nat) + 14 = 28 by norm_num]
  rw [List.append_assoc]
  rw [fromBytes'_append
    (List.take 14 (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1)
    (List.take 14 (EVM.Word.toBytesLEWithSizeProof val).1 ++
      List.drop 28 (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1)]
  rw [fromBytes'_append
    (List.take 14 (EVM.Word.toBytesLEWithSizeProof val).1)
    (List.drop 28 (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1)]
  rw [fromBytes'_take_wordLE_land_mask _ 14 (by decide),
    fromBytes'_take_wordLE_land_mask val 14 (by decide),
    fromBytes'_drop_wordLE]
  have hlenOld14 : ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 14).length = 14 := by
    rw [List.length_take, hslen]
    norm_num
  have hlenVal14 : ((EVM.Word.toBytesLEWithSizeProof val).1.take 14).length = 14 := by
    rw [List.length_take, hvlen]
    norm_num
  rw [hlenOld14, hlenVal14]
  rw [show 2 ^ (8 * 14) = 2 ^ 112 by norm_num]
  rw [show 256 ^ 28 = 2 ^ 224 by norm_num]
  rw [setUint112Offset14Word_toNat]
  rw [show UInt256.ofNat (2 ^ 112 - 1) = reserve112Mask by native_decide]
  rw [u256_land_comm val reserve112Mask]
  ring_nf

theorem uniswapStorageLocStore_uint32_offset28 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (uint32Loc28 slot) (uniswapUint256Value val) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setUint32Offset28Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val)) := by
  unfold storageLocStore storageLocWriteWord uint32Loc28 uniswapUint256Value uint256Value
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof val).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (28 : Fin 32).val _ ++ List.take (4 : Fin 33).val _
        ++ List.drop ((28 : Fin 32).val + (4 : Fin 33).val) _) =
      (setUint32Offset28Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) val).toNat
  rw [show (28 : Fin 32).val = 28 from rfl, show (4 : Fin 33).val = 4 from rfl,
    show (28 : Nat) + 4 = 32 by norm_num]
  rw [List.append_assoc]
  rw [fromBytes'_append
    (List.take 28 (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1)
    (List.take 4 (EVM.Word.toBytesLEWithSizeProof val).1 ++
      List.drop 32 (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1)]
  rw [fromBytes'_append
    (List.take 4 (EVM.Word.toBytesLEWithSizeProof val).1)
    (List.drop 32 (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1)]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE_land_mask val 4 (by decide),
    fromBytes'_drop_wordLE]
  have hlenOld28 : ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 28).length = 28 := by
    rw [List.length_take, hslen]
    norm_num
  have hlenVal4 : ((EVM.Word.toBytesLEWithSizeProof val).1.take 4).length = 4 := by
    rw [List.length_take, hvlen]
    norm_num
  rw [hlenOld28, hlenVal4]
  rw [show 256 ^ 28 = 2 ^ 224 by norm_num]
  rw [show 2 ^ (8 * 28) = 2 ^ 224 by norm_num]
  rw [show 2 ^ (8 * 4) = 2 ^ 32 by norm_num]
  rw [show 256 ^ 32 = 2 ^ 256 by norm_num]
  rw [show (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat / 2 ^ 256 = 0 by
    exact Nat.div_eq_of_lt (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).val.isLt]
  rw [setUint32Offset28Word_toNat]
  rw [show UInt256.ofNat (2 ^ 32 - 1) = reserve32Mask by native_decide]
  ring_nf

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
  · cases value <;> simp at hscalar ⊢
    simp [storageLocStore, valueToWord] at hstore
  · exact hstore

def uniswapSlotWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)

abbrev uniswapAddressReturnWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (uniswapSlotWord slot σ I) solcAddrMask

abbrev uniswapAddressAtSlot (evm : EVM.State) (slot : UInt256) : AccountAddress :=
  AccountAddress.ofNat
    (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) solcAddrMask).toNat

theorem evalExpr_uniswap_storage_address (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot)) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage ref) =
      .ok (.address (uniswapAddressAtSlot evm slot)) := by
  exact evalExpr_storage_scalar_value hbase her hty hloc
    (uniswapStorageLocLoad_address_offset0 evm slot)

theorem evalExpr_uniswap_this (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } evm this =
      .ok (.address evm.executionEnv.codeOwner) := by
  simp [this, evalExpr?, envValue, pure]

theorem evalExprs_uniswap_this_single (evm : EVM.State) (locals : Store) :
    evalExprs? config { contract := contract, locals := locals } evm [this] =
      .ok [.address evm.executionEnv.codeOwner] := by
  simp [evalExprs?, evalExpr_uniswap_this, EvalResult.bind, bind, pure]

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
  simpa [uniswapLowLevelCallRequireStore] using
    lowLevelCallSuccessThenRequireTrue
      (cfg := cfg) (C := C) (evm := evm) (evm' := evm') (locals := locals)
      (receiver := receiver) (eth := eth) (cdata := cdata) (requireCond := .var okVar)
      (okVar := okVar) (dataVar := dataVar)
      hreceiver heth hdata hcall
      (evalExpr_uniswapLowLevelCallRequire_ok evm' locals okVar dataVar true out hne)

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
  simpa [uniswapLowLevelCallRequireStore] using
    lowLevelCallFailureThenRequireFalse
      (cfg := cfg) (C := C) (evm := evm) (evm' := evm') (locals := locals)
      (receiver := receiver) (eth := eth) (cdata := cdata) (requireCond := .var okVar)
      (okVar := okVar) (dataVar := dataVar)
      hreceiver heth hdata hcall
      (evalExpr_uniswapLowLevelCallRequire_ok evm' locals okVar dataVar false out hne)

theorem uniswapExternalBalanceOfThisSuccess (evm evm' : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256} {retVar : Ident}
    {out : ByteArray} {value : Value}
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm slot))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm', out) false)
    (hdec : config.externalABI.decode? "balanceOf" out = some [value]) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .externalCall (.storage ref) "balanceOf" (.intLit 0) [this] retVar (perm := false) ]
      (.ok { contract := contract, locals := locals.insert retVar value } evm') := by
  exact externalCallSuccess
    (receiver := .storage ref) (name := "balanceOf") (sendVal := 0) (args := [this])
    (target := uniswapAddressAtSlot evm slot)
    (evalExpr_uniswap_storage_address evm locals hbase her hty hloc)
    (evalExprs_uniswap_this_single evm locals)
    hcall hdec

theorem uniswapExternalBalanceOfThisFailure (evm evm' : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256} {retVar : Ident}
    {out : ByteArray}
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm slot))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (false, evm', out) false) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .externalCall (.storage ref) "balanceOf" (.intLit 0) [this] retVar (perm := false) ] .reverted := by
  exact externalCallFailure
    (receiver := .storage ref) (name := "balanceOf") (sendVal := 0) (args := [this])
    (target := uniswapAddressAtSlot evm slot)
    (evalExpr_uniswap_storage_address evm locals hbase her hty hloc)
    (evalExprs_uniswap_this_single evm locals)
    hcall

theorem uniswapExternalBalanceOfThisDecodeRevert (evm evm' : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256} {retVar : Ident}
    {out : ByteArray}
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot))
    (hcall : typedCallViaEVM config evm (EVM.address (uniswapAddressAtSlot evm slot))
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm', out) false)
    (hdec : config.externalABI.decode? "balanceOf" out = none) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .externalCall (.storage ref) "balanceOf" (.intLit 0) [this] retVar (perm := false) ] .reverted := by
  exact externalCallDecodeRevert
    (receiver := .storage ref) (name := "balanceOf") (sendVal := 0) (args := [this])
    (target := uniswapAddressAtSlot evm slot)
    (evalExpr_uniswap_storage_address evm locals hbase her hty hloc)
    (evalExprs_uniswap_this_single evm locals)
    hcall hdec

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
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm', out) false)
    (hdec : config.externalABI.decode? "balanceOf" out = some [value]) :
    ExecBlock config { contract := contract, locals := locals } evm
      (balanceOfThisStmts (.storage ref) retVar)
      (.ok { contract := contract, locals := locals.insert retVar value } evm') := by
  simpa [balanceOfThisStmts] using
    checkedExternalCallSuccess
      (receiver := .storage ref) (name := "balanceOf") (sendVal := 0) (args := [this])
      (target := uniswapAddressAtSlot evm slot)
      hguard
      (evalExpr_uniswap_storage_address evm locals hbase her hty hloc)
      (evalExprs_uniswap_this_single evm locals)
      hcall hdec

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
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (false, evm', out) false) :
    ExecBlock config { contract := contract, locals := locals } evm
      (balanceOfThisStmts (.storage ref) retVar) .reverted := by
  simpa [balanceOfThisStmts] using
    checkedExternalCallFailure
      (receiver := .storage ref) (name := "balanceOf") (sendVal := 0) (args := [this])
      (target := uniswapAddressAtSlot evm slot)
      hguard
      (evalExpr_uniswap_storage_address evm locals hbase her hty hloc)
      (evalExprs_uniswap_this_single evm locals)
      hcall

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
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm', out) false)
    (hdec : config.externalABI.decode? "balanceOf" out = none) :
    ExecBlock config { contract := contract, locals := locals } evm
      (balanceOfThisStmts (.storage ref) retVar) .reverted := by
  simpa [balanceOfThisStmts] using
    checkedExternalCallDecodeRevert
      (receiver := .storage ref) (name := "balanceOf") (sendVal := 0) (args := [this])
      (target := uniswapAddressAtSlot evm slot)
      hguard
      (evalExpr_uniswap_storage_address evm locals hbase her hty hloc)
      (evalExprs_uniswap_this_single evm locals)
      hcall hdec

theorem uniswapCheckedExternalBalanceOfThisNoCode (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {retVar : Ident}
    (hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage ref)) (.intLit 0)) = .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals } evm
      (balanceOfThisStmts (.storage ref) retVar) .reverted := by
  simpa [balanceOfThisStmts] using
    checkedExternalCallNoCode
      (receiver := .storage ref) (name := "balanceOf") (sendVal := 0) (args := [this])
      (retVar := retVar)
      hguard

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
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some [balance0])
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" out1 = some [balance1]) :
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
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (false, evm0, out0) false) :
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
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm0, out0) false)
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
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some [balance0]) :
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
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some [balance0])
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (false, evm1, out1) false) :
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
      "balanceOf" 0 [.address evm.executionEnv.codeOwner] (true, evm0, out0) false)
    (hdec0 : config.externalABI.decode? "balanceOf" out0 = some [balance0])
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
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

theorem uniswapAddressGetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (uniswapStorageLocLoad_address_offset0 evm slot))

theorem uniswapUint256GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)))
    (hloc : config.storage.layout er = fun _ => some (wordLoc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (uniswapStorageLocLoad_uint256 evm slot))

theorem uniswapBytes32GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.bytes bytes32Width)))
    (hloc : config.storage.layout er = fun _ => some (bytes32Loc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (uniswapStorageLocLoad_bytes32 evm slot))

theorem uniswapIntLiteralBodyReturns (evm : EVM.State) (locals : Store) (n : Int)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.intLit n)] ])
      (.returned { contract := contract, locals := locals } evm (some [(.int n)])) := by
  simpa [nonpayable] using
    nonpayableIntLiteralBodyReturns (cfg := config) (contract := contract) evm locals n h

theorem uniswapFixedBytesLiteralBodyReturns (evm : EVM.State) (locals : Store)
    (n : Fin 32) (bytes : List UInt8) (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm locals
      (nonpayable ++ [ .return [(.fixedBytesLit n bytes)] ])
      (.returned { contract := contract, locals := locals } evm (some [(.fixedBytes n bytes)])) := by
  simpa [nonpayable] using
    nonpayableFixedBytesLiteralBodyReturns (cfg := config) (contract := contract)
      evm locals n bytes h

/-! ## Shared lock-revert payload -/

def uniswapLockRevertStringWord : UInt256 :=
  UInt256.shiftLeft (⟨7267690950230416977285330377544234619217⟩ : UInt256) ⟨122⟩

abbrev uniswapRetEnd : UInt256 := (⟨128⟩ : UInt256) + ⟨32⟩

theorem uniswapSubRet32_toNat :
    (UInt256.sub uniswapRetEnd ⟨128⟩).toNat = 32 := by
  decide

theorem uniswapDecodeLenCheckOk_4_32_lt {sz : ℕ}
    (hsz36 : 36 ≤ sz) (hsize : sz < UInt256.size) :
    UInt256.lt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨32⟩ = ⟨0⟩ := by
  exact solcDecodeLenCheckOkUnsigned
    (head := (⟨4⟩ : UInt256)) (need := (⟨32⟩ : UInt256)) (by simpa using hsz36) hsize

theorem uniswapDecodeLenCheckOk_4_64_lt {sz : ℕ}
    (hsz68 : 68 ≤ sz) (hsize : sz < UInt256.size) :
    UInt256.lt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨64⟩ = ⟨0⟩ := by
  exact solcDecodeLenCheckOkUnsigned
    (head := (⟨4⟩ : UInt256)) (need := (⟨64⟩ : UInt256)) (by simpa using hsz68) hsize

theorem uniswapDecodeLenCheckOk_4_96_lt {sz : ℕ}
    (hsz100 : 100 ≤ sz) (hsize : sz < UInt256.size) :
    UInt256.lt (UInt256.sub (UInt256.ofNat sz) ⟨4⟩) ⟨96⟩ = ⟨0⟩ := by
  exact solcDecodeLenCheckOkUnsigned
    (head := (⟨4⟩ : UInt256)) (need := (⟨96⟩ : UInt256)) (by simpa using hsz100) hsize

end UniswapV2Pair

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

/-! ## Shared getter routines -/

/-- Bytecode shape for Uniswap's generated full-slot address getter routines.

The routine loads `slot`, masks the low 160 bits, duplicates the dynamic return address, and jumps
back to the caller.  It appears at pc 2917 (`token0`), pc 5443 (`factory`), and pc 5458 (`token1`).
-/
@[reducible] def uniswapAddressSlotGetterWf (pc slot : UInt256) : Prop :=
  solcAddressSlotGetterWf UniswapV2Pair.uniswapV2PairBytecode pc slot

/-- Discharge a Uniswap address-slot getter bytecode-shape proof at a concrete PC/slot. -/
macro "uniswap_address_slot_getter_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapAddressSlotGetterWf
    repeat' first | apply And.intro | native_decide)

/-- Bytecode shape for an external getter thunk that jumps to an internal getter routine. -/
@[reducible] def uniswapGetterEntryWf (pc returnPc routine : UInt256) : Prop :=
  solcGetterEntryWf UniswapV2Pair.uniswapV2PairBytecode pc returnPc routine

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
  solcWordSlotGetterWf UniswapV2Pair.uniswapV2PairBytecode pc slot

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
  solcConstGetterWf UniswapV2Pair.uniswapV2PairBytecode pc val width op

/-- Discharge a Uniswap constant getter bytecode-shape proof at a concrete PC/value/width. -/
macro "uniswap_const_getter_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapConstGetterWf
    repeat' first | apply And.intro | native_decide)

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
  exact RD.solcGetterThunk hreach hentry hroutine

/-! ## Shared lock-entry prefix -/

/-- Bytecode shape for Uniswap's optimizer-emitted reentrancy-lock success prefix.

The prefix checks storage slot 12 for `1`, jumps over the revert block, then stores `0` in slot 12.
It appears at the front of `skim`, `sync`, and the larger liquidity/swap routines.
-/
@[reducible] def uniswapLockEnterOkWf (pc okPc : UInt256) : Prop :=
  solcLockEnterOkWf UniswapV2Pair.uniswapV2PairBytecode pc okPc ⟨12⟩ ⟨1⟩ ⟨0⟩

/-- Discharge a Uniswap lock-entry success bytecode-shape proof. -/
macro "uniswap_lock_enter_ok_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapLockEnterOkWf Reasoning.Reach.solcLockEnterOkWf
    repeat' first | apply And.intro | native_decide)

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
  exact RD.solcLockEnterOk h hwf hperm (by simpa [solcSlotWord] using hunlocked) hok hov

macro "uniswap_lock_enter_guard_wf" : term =>
  `(by
    unfold solcLockEnterGuardWf
    repeat' first | apply And.intro | native_decide)

macro "uniswap_lock_revert_tail_wf" : term =>
  `(by
    unfold solcErrorStringRevertTailWf solcLockEnterRevertPc
    repeat' first | apply And.intro | native_decide)

/-- Bytecode shape for the lock guard after a routine-specific prelude.

`mint` and `burn` enter at a `JUMPDEST` followed by a small stack setup before the standard
storage-slot-12 lock check.  This predicate starts at the `PUSH1 12` guard instruction.
-/
@[reducible] def uniswapLockEnterBodyGuardWf (pc okPc : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p9 := p6 + UInt256.ofNat 3
  decode UniswapV2Pair.uniswapV2PairBytecode pc =
      some (.Push .PUSH1, some (⟨12⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p2 = some (.SLOAD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p3 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p5 = some (.EQ, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p6 =
      some (.Push .PUSH2, some (okPc, 2))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p9 = some (.JUMPI, .none)

@[reducible] def uniswapLockEnterBodyRevertPc (pc : UInt256) : UInt256 :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p9 := p6 + UInt256.ofNat 3
  p9 + ⟨1⟩

macro "uniswap_lock_enter_body_guard_wf" : term =>
  `(by
    unfold uniswapLockEnterBodyGuardWf
    repeat' first | apply And.intro | native_decide)

macro "uniswap_lock_body_revert_tail_wf" : term =>
  `(by
    unfold solcErrorStringRevertTailWf uniswapLockEnterBodyRevertPc
    repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapLockEnterBodyLocked {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {pc okPc : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 pc R
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hguard : uniswapLockEnterBodyGuardWf pc okPc)
    (htail :
      solcErrorStringRevertTailWf UniswapV2Pair.uniswapV2PairBytecode
        (uniswapLockEnterBodyRevertPc pc) ⟨17⟩
        (⟨7267690950230416977285330377544234619217⟩ : UInt256) ⟨122⟩
        .PUSH17 17)
    (hlocked :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
      ⟨1⟩)
    (hov : R.length + 5 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  rcases hguard with ⟨hd0, hd2, hd3, hd5, hd6, hd9⟩
  set lockedWord := solcSlotWord σ ee ⟨12⟩ with hlockedWord
  have hlockedWord_ne : lockedWord ≠ ⟨1⟩ := by
    simpa [solcSlotWord, hlockedWord] using hlocked
  have heqZero : UInt256.eq ⟨1⟩ lockedWord = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hlockedWord_ne hbad.symm)
  have rd2 := h.push1 ⟨12⟩ hd0 (by omega)
  obtain ⟨_, _, rd3₀⟩ := rd2.sload hd2 (by omega)
  have rd3 := rd3₀
  have hraw :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        lockedWord := by
    simpa [solcSlotWord] using hlockedWord.symm
  rw [hraw] at rd3
  have rd5 := rd3.push1 ⟨1⟩ hd3 (by simp only [List.length_cons]; omega)
  have rd6₀ := rd5.eq hd5 (by omega)
  have rd6 := rd6₀
  rw [heqZero] at rd6
  have rd9 := rd6.push2 okPc hd6 (by simp only [List.length_cons]; omega)
  have rdRevert₀ := rd9.jumpiNT hd9 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by omega)
  have rdRevert := by
    simpa [uniswapLockEnterBodyRevertPc] using rdRevert₀
  exact RD.solcErrorStringRevertTail rdRevert htail (by decide) (by rfl)
    solcFreePtrMem_size solcFreePtrMem_read64 (by omega)

/-- Bytecode shape for a lock guard body plus the success-side `SSTORE`. -/
@[reducible] def uniswapLockEnterBodyOkWf (pc okPc : UInt256) : Prop :=
  let pOk1 := okPc + ⟨1⟩
  let pOk3 := pOk1 + UInt256.ofNat 2
  let pOk5 := pOk3 + UInt256.ofNat 2
  let pOk6 := pOk5 + ⟨1⟩
  let pOk7 := pOk6 + ⟨1⟩
  uniswapLockEnterBodyGuardWf pc okPc
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode okPc = some (.JUMPDEST, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode pOk1 =
      some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode pOk3 =
      some (.Push .PUSH1, some (⟨12⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode pOk5 = some (.DUP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode pOk6 = some (.SWAP1, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode pOk7 = some (.SSTORE, .none)

macro "uniswap_lock_enter_body_ok_wf" : term =>
  `(by
    unfold uniswapLockEnterBodyOkWf uniswapLockEnterBodyGuardWf
    repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapLockEnterBodyOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {pc okPc : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 pc R
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : uniswapLockEnterBodyOkWf pc okPc)
    (hperm : ee.perm = true)
    (hunlocked :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) =
        ⟨1⟩)
    (hok : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains okPc = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 (okPc + UInt256.ofNat 8)
      (⟨0⟩ :: R) solcFreePtrMem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨12⟩ ⟨0⟩) k' C' := by
  rcases hwf with ⟨hguard, hdOk, hdOk1, hdOk3, hdOk5, hdOk6, hdOk7⟩
  rcases hguard with ⟨hd0, hd2, hd3, hd5, hd6, hd9⟩
  have rd2 := h.push1 ⟨12⟩ hd0 (by omega)
  obtain ⟨_, _, rd3₀⟩ := rd2.sload hd2 (by omega)
  have rd3 := rd3₀
  rw [hunlocked] at rd3
  have rd5 := rd3.push1 ⟨1⟩ hd3 (by simp only [List.length_cons]; omega)
  have rd6₀ := rd5.eq hd5 (by omega)
  have rd6 := rd6₀
  rw [uInt256_eq_self] at rd6
  have rd9 := rd6.push2 okPc hd6 (by simp only [List.length_cons]; omega)
  have rdOk := rd9.jumpiT hd9 one_ne_zero_uint hok (by omega)
  have rdOk1 := rdOk.jumpdest hdOk (by omega)
  have rdOk3 := rdOk1.push1 ⟨0⟩ hdOk1 (by omega)
  have rdOk5 := rdOk3.push1 ⟨12⟩ hdOk3 (by simp only [List.length_cons]; omega)
  have rdOk6 := rdOk5.dup2 hdOk5 (by omega)
  have rdOk7 := rdOk6.swap1 hdOk6 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdAfter⟩ := rdOk7.sstore hperm hdOk7
    (by simp only [List.length_cons]; omega)
  have hpcOut :
      okPc + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        okPc + UInt256.ofNat 8 := by
    rw [u256_add_assoc okPc ⟨1⟩ (UInt256.ofNat 2)]
    rw [u256_add_assoc okPc (⟨1⟩ + UInt256.ofNat 2) (UInt256.ofNat 2)]
    rw [u256_add_assoc okPc (⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2) ⟨1⟩]
    rw [u256_add_assoc okPc (⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩) ⟨1⟩]
    rw [u256_add_assoc okPc
      (⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) ⟨1⟩]
    congr 1
  exact ⟨_, _, by simpa [hpcOut] using rdAfter⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapLockEnterLocked {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc okPc : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 pc R
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hguard :
      solcLockEnterGuardWf UniswapV2Pair.uniswapV2PairBytecode pc okPc ⟨12⟩ ⟨1⟩)
    (htail :
      solcErrorStringRevertTailWf UniswapV2Pair.uniswapV2PairBytecode
        (solcLockEnterRevertPc pc) ⟨17⟩
        (⟨7267690950230416977285330377544234619217⟩ : UInt256) ⟨122⟩
        .PUSH17 17)
    (hlocked :
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
      ⟨1⟩)
    (hov : R.length + 6 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  exact RD.solcLockEnterLockedStringRevert
    (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := pc) (okPc := okPc)
    (slot := ⟨12⟩) (unlocked := ⟨1⟩) (len := ⟨17⟩)
    (rawWord := (⟨7267690950230416977285330377544234619217⟩ : UInt256))
    (shift := ⟨122⟩) (word := UniswapV2Pair.uniswapLockRevertStringWord)
    (op := .PUSH17) (width := 17) (R := R) h
    hguard htail
    (by decide)
    (by simpa [solcSlotWord] using hlocked)
    (by rfl)
    hov

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
  exact RD.solcAddressSlotGetter h hwf hret hov

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
  exact RD.solcWordSlotGetter h hwf hret hov

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
  exact RD.solcConstGetter h hwf hret hov

/-- Uniswap's address-return wrapper at pc 825. -/
theorem RD.uniswapReturnAddress825 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨825⟩ (val :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 9 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0 acc
      (UInt256.toByteArray (UInt256.land val solcAddrMask)) := by
  exact RD.solcReturnAddressFromMem h
    (by
      unfold solcReturnAddressFromMemWf
      repeat' first | apply And.intro | native_decide)
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (UInt256.land val solcAddrMask))
    (solcReturnMem_read128 (UInt256.land val solcAddrMask))
    hov

/-- Uniswap's uint256-return wrapper at pc 861. -/
theorem RD.uniswapReturnWord861 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨861⟩ (val :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 5 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0 acc (UInt256.toByteArray val) := by
  exact RD.solcReturnWordFromMem h
    (by
      unfold solcReturnWordFromMemWf
      repeat' first | apply And.intro | native_decide)
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 val)
    (solcReturnMem_read128 val)
    hov

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
  exact RD.solcReturnWordFromMem h
    (by
      unfold solcReturnWordFromMemWf
      repeat' first | apply And.intro | native_decide)
    hmload64
    hmemout
    hmemoutLoad64
    hread128
    hov

/-- Uniswap's uint8-return wrapper for `decimals()` at pc 949. -/
theorem RD.uniswapReturnUint8_949 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨949⟩ (val :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 9 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0 acc
      (UInt256.toByteArray (UInt256.land val ⟨255⟩)) := by
  exact RD.solcReturnUint8FromMem h
    (by
      unfold solcReturnUint8FromMemWf
      repeat' first | apply And.intro | native_decide)
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (UInt256.land val ⟨255⟩))
    (solcReturnMem_read128 (UInt256.land val ⟨255⟩))
    hov

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
  simpa [UniswapV2Pair.uniswapAddressReturnWord, UniswapV2Pair.uniswapSlotWord, solcSlotWord]
    using RD.solcAddressGetterExternal (returnPc := ⟨825⟩)
      hreach hentry hgetter hroutine hret825
      (by
        unfold solcReturnAddressFromMemWf
        repeat' first | apply And.intro | native_decide)

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
  simpa [UniswapV2Pair.uniswapSlotWord, solcSlotWord]
    using RD.solcWordGetterExternal (returnPc := ⟨861⟩)
      hreach hentry hgetter hroutine hret861
      (by
        unfold solcReturnWordFromMemWf
        repeat' first | apply And.intro | native_decide)

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
  exact RD.solcWordConstGetterExternal (returnPc := ⟨861⟩)
    hreach hentry hgetter hroutine hret861
    (by
      unfold solcReturnWordFromMemWf
      repeat' first | apply And.intro | native_decide)

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
  exact RD.solcUint8ConstGetterExternal (returnPc := ⟨949⟩)
    hreach hentry hgetter hroutine hret949
    (by
      unfold solcReturnUint8FromMemWf
      repeat' first | apply And.intro | native_decide)

end Reasoning.Reach

namespace UniswapV2Pair

open Reasoning.Refinement

theorem uniswapAddressGetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot : UInt256}
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : Reasoning.Reach.uniswapAddressGetterEntryWf entry routine)
    (hgetter : Reasoning.Reach.uniswapAddressSlotGetterWf routine slot)
    (hroutine : (D_J uniswapV2PairBytecode 0).contains routine = true)
    (hreturn : transition.returnType = [addr])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (uniswapAddressReturnWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : uniswapSlotWord slot σ_evm I = uniswapSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.address (AccountAddress.ofNat (uniswapAddressReturnWord slot σ_solm I).toNat)] =
        some [Value.address (AccountAddress.ofNat (uniswapAddressReturnWord slot σ_evm I).toNat)] := by
    have hslot : uniswapSlotWord slot σ_solm I = uniswapSlotWord slot σ_evm I := hword.symm
    simp [uniswapAddressReturnWord, hslot]
  have henc :
      returnEquiv (UInt256.toByteArray (uniswapAddressReturnWord slot σ_evm I))
        (some [(.address (AccountAddress.ofNat (uniswapAddressReturnWord slot σ_evm I).toNat))])
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
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : Reasoning.Reach.uniswapWordGetterEntryWf entry routine)
    (hgetter : Reasoning.Reach.uniswapWordSlotGetterWf routine slot)
    (hroutine : (D_J uniswapV2PairBytecode 0).contains routine = true)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (uniswapSlotWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : uniswapSlotWord slot σ_evm I = uniswapSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (uniswapSlotWord slot σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (uniswapSlotWord slot σ_evm I).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (uniswapSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (uniswapSlotWord slot σ_evm I).toNat))])
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
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : Reasoning.Reach.uniswapWordGetterEntryWf entry routine)
    (hgetter : Reasoning.Reach.uniswapWordSlotGetterWf routine slot)
    (hroutine : (D_J uniswapV2PairBytecode 0).contains routine = true)
    (hreturn : transition.returnType = [bytes32])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.fixedBytes ⟨31, by decide⟩
            (EVM.Word.toBytesBE (uniswapSlotWord slot σ_solm I)))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : uniswapSlotWord slot σ_evm I = uniswapSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (uniswapSlotWord slot σ_solm I))] =
        some [Value.fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (uniswapSlotWord slot σ_evm I))] := by
    rw [← hword]
  have henc :
      returnEquiv (UInt256.toByteArray (uniswapSlotWord slot σ_evm I))
        (some [(.fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (uniswapSlotWord slot σ_evm I)))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [bytes32] using bytes32ReturnEncoding (uniswapSlotWord slot σ_evm I))
  exact (RD.uniswapWordGetterExternal (g := Sat256.ofUInt256 g)
      (entry := entry) (routine := routine) (slot := slot) hreach hentry hgetter hroutine
      (by jump_dest)).reEquivExecutionTransport
    hcode hdispatch hdecode hbody hval hAccounts henc

end UniswapV2Pair
