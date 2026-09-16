import Examples.UniswapV2Pair.Bytecode
import Reasoning.ABI
import Reasoning.Dispatch
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
  rw [testBit_shiftLeft, testBit_shiftLeft]
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
        rw [divPow_testBit n 224 i h224le]
        simp [hi112, hi224]
      · have hsub32 : ¬ (i - 224 < 32) := by omega
        rw [show decide (i - 224 < 32) = false by simp [hsub32]]
        have hnfalse : n.testBit i = false := by
          have hpow : n < 2 ^ i :=
            lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega))
          exact Nat.testBit_lt_two_pow hpow
        rw [divPow_testBit n 224 i h224le, hnfalse]
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
    using execBlock_append htoken0 htoken1

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
    using execBlock_append_term
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
    using execBlock_append_term
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
    using execBlock_append_term
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
    using execBlock_append htoken0 htoken1

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
    using execBlock_append htoken0 htoken1

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
    using execBlock_append htoken0 htoken1

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
