import Benchmarks.Dss.Flipper.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

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

theorem flipperVatTargetWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    flipperVatTargetWord σ I = flipperVatTargetWord τ I := by
  have hslot : flipperSlotWord ⟨2⟩ σ I = flipperSlotWord ⟨2⟩ τ I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  simp [flipperVatTargetWord, flipperAddressReturnWord, hslot]

theorem flipperCatTargetWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    flipperCatTargetWord σ I = flipperCatTargetWord τ I := by
  have hslot : flipperSlotWord ⟨7⟩ σ I = flipperSlotWord ⟨7⟩ τ I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨7⟩ ⟨0⟩
  simp [flipperCatTargetWord, flipperAddressReturnWord, hslot]

theorem flipperVatAddress_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    flipperVatAddress σ I = flipperVatAddress τ I := by
  apply Fin.ext
  simp [flipperVatAddress, flipperVatTargetWord_accountMapEquiv hAccounts]

theorem flipperCatAddress_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    flipperCatAddress σ I = flipperCatAddress τ I := by
  apply Fin.ext
  simp [flipperCatAddress, flipperCatTargetWord_accountMapEquiv hAccounts]

theorem flipperVatCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (flipperVatTargetWord σ I) = ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (flipperVatTargetWord τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (flipperVatTargetWord σ I)
  have htarget : flipperVatTargetWord σ I = flipperVatTargetWord τ I :=
    flipperVatTargetWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem flipperCatCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (flipperCatTargetWord σ I) = ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (flipperCatTargetWord τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (flipperCatTargetWord σ I)
  have htarget : flipperCatTargetWord σ I = flipperCatTargetWord τ I :=
    flipperCatTargetWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem flipperVatCodeSize_ne_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (flipperVatTargetWord τ I) ≠ ⟨0⟩ := by
  intro hzero
  exact hne (flipperVatCodeSize_zero_accountMapEquiv hAccounts.symm hzero)

theorem flipperCatCodeSize_ne_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (flipperCatTargetWord σ I) ≠ ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (flipperCatTargetWord τ I) ≠ ⟨0⟩ := by
  intro hzero
  exact hne (flipperCatCodeSize_zero_accountMapEquiv hAccounts.symm hzero)

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

theorem flipperVatEvmAddress_eq_target_of_accountMapEquiv {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    EVM.address (flipperVatAddress σ_solm I) =
      AccountAddress.ofUInt256 (flipperVatTargetWord σ_evm I) := by
  have haddr :
      flipperVatAddress σ_solm I =
        AccountAddress.ofUInt256 (flipperVatTargetWord σ_evm I) := by
    calc
      flipperVatAddress σ_solm I = flipperVatAddress σ_evm I :=
        (flipperVatAddress_accountMapEquiv hAccounts).symm
      _ = AccountAddress.ofUInt256 (flipperVatTargetWord σ_evm I) :=
        flipperVatAddress_eq_target σ_evm I
  rw [haddr]
  exact flipperEvmAddress_accountAddress _

theorem flipperCatEvmAddress_eq_target_of_accountMapEquiv {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    EVM.address (flipperCatAddress σ_solm I) =
      AccountAddress.ofUInt256 (flipperCatTargetWord σ_evm I) := by
  have haddr :
      flipperCatAddress σ_solm I =
        AccountAddress.ofUInt256 (flipperCatTargetWord σ_evm I) := by
    calc
      flipperCatAddress σ_solm I = flipperCatAddress σ_evm I :=
        (flipperCatAddress_accountMapEquiv hAccounts).symm
      _ = AccountAddress.ofUInt256 (flipperCatTargetWord σ_evm I) :=
        flipperCatAddress_eq_target σ_evm I
  rw [haddr]
  exact flipperEvmAddress_accountAddress _

theorem flipper_uniswapExtCodeSizeWord_zero_lookup_code_zero {σ : AccountMap} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : Reasoning.Theory.uniswapExtCodeSizeWord σ target = ⟨0⟩) :
    (UInt256.ofNat
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  subst addr
  unfold Reasoning.Theory.uniswapExtCodeSizeWord at hzero
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      simpa [hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [hacc] using hword

theorem flipper_uniswapExtCodeSizeWord_pos_lookup_code_pos {σ : AccountMap} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : Reasoning.Theory.uniswapExtCodeSizeWord σ target ≠ ⟨0⟩) :
    0 <
      (UInt256.ofNat
        ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat := by
  by_contra hnot
  have hnat :
      (UInt256.ofNat
        ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hwordZero :
      UInt256.ofNat ((σ.find? addr).option 0 (fun acc => acc.code.size)) = ⟨0⟩ :=
    uint256_toNat_eq_zero hnat
  have hword :
      UInt256.ofNat ((σ.find? addr).option 0 (fun acc => acc.code.size)) =
        Reasoning.Theory.uniswapExtCodeSizeWord σ target := by
    subst addr
    cases hacc : σ.find? (AccountAddress.ofUInt256 target) <;>
      simp [Reasoning.Theory.uniswapExtCodeSizeWord, hacc, Option.option] <;>
      native_decide
  exact hne (by rw [← hword, hwordZero])

theorem flipperVatCode_zero_of_codeSize_zero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (flipperVatTargetWord σ I) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  simpa [initState, State.lookupAccount] using
    flipper_uniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := flipperVatTargetWord σ I) (addr := flipperVatAddress σ I)
      (flipperVatAddress_eq_target σ I) hzero

theorem flipperCatCode_zero_of_codeSize_zero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (flipperCatTargetWord σ I) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (flipperCatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  simpa [initState, State.lookupAccount] using
    flipper_uniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := flipperCatTargetWord σ I) (addr := flipperCatAddress σ I)
      (flipperCatAddress_eq_target σ I) hzero

theorem flipperVatCode_pos_of_codeSize_ne_zero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩) :
    0 <
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat := by
  by_contra hnot
  have hnat :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hwordZero :
      UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size)) = ⟨0⟩ :=
    uint256_toNat_eq_zero hnat
  have hword :
      UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size)) =
        Reasoning.Theory.uniswapExtCodeSizeWord σ (flipperVatTargetWord σ I) := by
    cases hacc : σ.find? (AccountAddress.ofUInt256 (flipperVatTargetWord σ I)) <;>
      simp [initState, State.lookupAccount, Reasoning.Theory.uniswapExtCodeSizeWord,
        flipperVatAddress_eq_target σ I, hacc, Option.option] <;>
      native_decide
  exact hne (by rw [← hword, hwordZero])

theorem flipperCatCode_pos_of_codeSize_ne_zero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (flipperCatTargetWord σ I) ≠ ⟨0⟩) :
    0 <
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (flipperCatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat := by
  by_contra hnot
  have hnat :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (flipperCatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hwordZero :
      UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (flipperCatAddress σ I)).option 0 (fun acc => acc.code.size)) = ⟨0⟩ :=
    uint256_toNat_eq_zero hnat
  have hword :
      UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (flipperCatAddress σ I)).option 0 (fun acc => acc.code.size)) =
        Reasoning.Theory.uniswapExtCodeSizeWord σ (flipperCatTargetWord σ I) := by
    cases hacc : σ.find? (AccountAddress.ofUInt256 (flipperCatTargetWord σ I)) <;>
      simp [initState, State.lookupAccount, Reasoning.Theory.uniswapExtCodeSizeWord,
        flipperCatAddress_eq_target σ I, hacc, Option.option] <;>
      native_decide
  exact hne (by rw [← hword, hwordZero])

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
