import Benchmarks.Dss.Flipper.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flipper

/-! ## External-call target helpers -/

abbrev flipperVatTargetWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperAddressReturnWord ⟨2⟩ σ I

abbrev flipperCatTargetWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperAddressReturnWord ⟨7⟩ σ I

abbrev flipperVatAddress (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (flipperVatTargetWord σ I).toNat

abbrev flipperCatAddress (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (flipperCatTargetWord σ I).toNat

theorem flipperVatAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    flipperVatAddress σ I = AccountAddress.ofUInt256 (flipperVatTargetWord σ I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]

theorem flipperCatAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    flipperCatAddress σ I = AccountAddress.ofUInt256 (flipperCatTargetWord σ I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]

theorem flipperEvmAddress_accountAddress (a : AccountAddress) :
    EVM.address a.val = a := by
  apply Fin.ext
  show a.val % EVM.addressModulus = a.val
  rw [show EVM.addressModulus = AccountAddress.size from by decide]
  exact Nat.mod_eq_of_lt a.isLt

theorem flipperVatEvmAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    EVM.address (flipperVatAddress σ I) =
      AccountAddress.ofUInt256 (flipperVatTargetWord σ I) := by
  rw [flipperVatAddress_eq_target]
  exact flipperEvmAddress_accountAddress _

theorem flipperCatEvmAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    EVM.address (flipperCatAddress σ I) =
      AccountAddress.ofUInt256 (flipperCatTargetWord σ I) := by
  rw [flipperCatAddress_eq_target]
  exact flipperEvmAddress_accountAddress _

theorem flipper_extCodeSizeWord_zero_lookup_code_zero {σ : AccountMap} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : Reasoning.Theory.extCodeSizeWord σ target = ⟨0⟩) :
    (UInt256.ofNat
      ((σ.get? addr).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  subst addr
  unfold Reasoning.Theory.extCodeSizeWord at hzero
  cases hacc : σ.get? (AccountAddress.ofUInt256 target) with
  | none =>
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, hacc] using hword

theorem flipper_extCodeSizeWord_pos_lookup_code_pos {σ : AccountMap} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩) :
    0 <
      (UInt256.ofNat
        ((σ.get? addr).option 0 (fun acc => acc.code.size))).toNat := by
  by_contra hnot
  have hnat :
      (UInt256.ofNat
        ((σ.get? addr).option 0 (fun acc => acc.code.size))).toNat = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hwordZero :
      UInt256.ofNat ((σ.get? addr).option 0 (fun acc => acc.code.size)) = ⟨0⟩ :=
    uint256_toNat_eq_zero hnat
  have hword :
      UInt256.ofNat ((σ.get? addr).option 0 (fun acc => acc.code.size)) =
        Reasoning.Theory.extCodeSizeWord σ target := by
    subst addr
    cases hacc : σ.get? (AccountAddress.ofUInt256 target) <;>
      simp [-Std.ExtTreeMap.get?_eq_getElem?, Reasoning.Theory.extCodeSizeWord,
        hacc, Option.option] <;>
      native_decide
  exact hne (by rw [← hword, hwordZero])

theorem flipperVatCode_zero_of_codeSize_zero {σ σ₀ A I} {g : UInt256}
    (hzero :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  simpa [initState, State.lookupAccount] using
    flipper_extCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := flipperVatTargetWord σ I) (addr := flipperVatAddress σ I)
      (flipperVatAddress_eq_target σ I) hzero

theorem flipperCatCode_zero_of_codeSize_zero {σ σ₀ A I} {g : UInt256}
    (hzero :
      Reasoning.Theory.extCodeSizeWord σ (flipperCatTargetWord σ I) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (flipperCatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  simpa [initState, State.lookupAccount] using
    flipper_extCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := flipperCatTargetWord σ I) (addr := flipperCatAddress σ I)
      (flipperCatAddress_eq_target σ I) hzero

theorem flipperVatCode_pos_of_codeSize_ne_zero {σ σ₀ A I} {g : UInt256}
    (hne :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩) :
    0 <
      (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat := by
  simpa [initState, State.lookupAccount] using
    flipper_extCodeSizeWord_pos_lookup_code_pos
      (σ := σ) (target := flipperVatTargetWord σ I) (addr := flipperVatAddress σ I)
      (flipperVatAddress_eq_target σ I) hne

theorem flipperCatCode_pos_of_codeSize_ne_zero {σ σ₀ A I} {g : UInt256}
    (hne :
      Reasoning.Theory.extCodeSizeWord σ (flipperCatTargetWord σ I) ≠ ⟨0⟩) :
    0 <
      (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (flipperCatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat := by
  simpa [initState, State.lookupAccount] using
    flipper_extCodeSizeWord_pos_lookup_code_pos
      (σ := σ) (target := flipperCatTargetWord σ I) (addr := flipperCatAddress σ I)
      (flipperCatAddress_eq_target σ I) hne

theorem evalExpr_flipperStorageVatOfLocals {evm : EVM.State} {locals : Store}
    (hvat : locals.get? "vat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (flipperVatAddress evm.accountMap evm.executionEnv)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := vatRef) (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨2⟩)
    (value := .address (flipperVatAddress evm.accountMap evm.executionEnv))
    hvat
    (by simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [vatRef, storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by
      simpa [flipperVatAddress, flipperVatTargetWord, flipperAddressReturnWord,
        flipperSlotWord] using flipperStorageLocLoad_address_offset0 evm ⟨2⟩)

theorem evalExpr_flipperStorageCatOfLocals {evm : EVM.State} {locals : Store}
    (hcat : locals.get? "cat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage catRef) =
      .ok (.address (flipperCatAddress evm.accountMap evm.executionEnv)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := catRef) (er := ({ base := "cat", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨7⟩)
    (value := .address (flipperCatAddress evm.accountMap evm.executionEnv))
    hcat
    (by simp [catRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [catRef, storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by
      simpa [flipperCatAddress, flipperCatTargetWord, flipperAddressReturnWord,
        flipperSlotWord] using flipperStorageLocLoad_address_offset0 evm ⟨7⟩)

theorem evalExpr_flipperVatCodeGuard_false_ofLocals {evm : EVM.State} {locals : Store}
    (hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (flipperVatAddress evm.accountMap evm.executionEnv)))
    (hnoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (flipperVatAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hvat, evalBinaryOp?, EVM.Word.ofNat, hnoCode]

theorem evalExpr_flipperVatCodeGuard_true_ofLocals {evm : EVM.State} {locals : Store}
    (hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (flipperVatAddress evm.accountMap evm.executionEnv)))
    (hcode :
      0 <
        (UInt256.ofNat
          ((evm.lookupAccount (flipperVatAddress evm.accountMap evm.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hvat, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExpr_flipperCatCodeGuard_false_ofLocals {evm : EVM.State} {locals : Store}
    (hcat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage catRef) =
        .ok (.address (flipperCatAddress evm.accountMap evm.executionEnv)))
    (hnoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (flipperCatAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hcat, evalBinaryOp?, EVM.Word.ofNat, hnoCode]

theorem evalExpr_flipperCatCodeGuard_true_ofLocals {evm : EVM.State} {locals : Store}
    (hcat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage catRef) =
        .ok (.address (flipperCatAddress evm.accountMap evm.executionEnv)))
    (hcode :
      0 <
        (UInt256.ofNat
          ((evm.lookupAccount (flipperCatAddress evm.accountMap evm.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hcat, evalBinaryOp?, EVM.Word.ofNat, hcode]

end Benchmarks.Dss.Flipper
