import Reasoning.ExternalCall
import Reasoning.WordArithmetic
import Reasoning.MemoryArithmetic

/-!
# EVM state, storage, and source evaluation facts

Reusable account and storage projections, external-code and precompile facts,
and elementary source-language evaluation lemmas.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace Reasoning.Theory

theorem copiedSelector {mem out} (hm : 96 ≤ mem.size)
    (hl : 4 ≤ out.size) :
    UInt256.shiftRight (loadedWord (out.write 0 mem 0 4) ⟨0⟩) ⟨224⟩ =
      UInt256.shiftRight (calldataWord out 0) ⟨224⟩ := by
  have hsz : 96 ≤ (out.write 0 mem 0 4).size := by
    rw [copyWindow_size out mem 0 0 4 (by decide) hl (by omega)]
    omega
  rw [loadedWord_zero (by omega)]
  apply u256_inj
  rw [selector_toNat _ (by omega), selector_toNat out hl]
  have hx := copyWindow_extract out mem 0 0 4 0 4 (by decide) hl (by omega) (by decide)
  have ht := congrArg (fun b : ByteArray ↦ b.data.toList) hx
  simpa only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    List.drop_zero] using congrArg fromBytesBigEndian ht

/-- Code size at an address transports across `EVMStateEquiv` (`Eq` preserves code). -/
theorem codeW_eq_of_equiv {a b : EVM.State} (addr : AccountAddress) (h : EVMStateEquiv a b) :
    UInt256.ofNat ((a.lookupAccount addr).option 0 (fun acc => acc.code.size)) =
      UInt256.ofNat ((b.lookupAccount addr).option 0 (fun acc => acc.code.size)) := by
  simpa only [State.lookupAccount, h.accountMap]

/-- `extCodeSizeWord` reads only an account's `.code` (as `ofNat · .code.size`), so it is a
    function of `(σ.getD a default).code` — the projection `accountCodeStateEq` preserves. -/
theorem extCodeSizeWord_eq_ofNat_getD (σ : AccountMap) (target : UInt256) :
    Reasoning.Theory.extCodeSizeWord σ target
      = UInt256.ofNat (σ.getD (AccountAddress.ofUInt256 target) default).code.size := by
  unfold Reasoning.Theory.extCodeSizeWord
  cases h : σ.get? (AccountAddress.ofUInt256 target) with
  | none =>
      have hdefault : (default : Account).code.size = 0 := by
        decide
      simp [Std.ExtTreeMap.getD_eq_getD_getElem?,
        ← Std.ExtTreeMap.get?_eq_getElem?, Option.option, hdefault, h]
      rfl
  | some acc =>
      simp [Std.ExtTreeMap.getD_eq_getD_getElem?,
        ← Std.ExtTreeMap.get?_eq_getElem?, Option.option, h]

/-- Code preservation transfers to `extCodeSizeWord`: static calls leave every account's
    `EXTCODESIZE` word unchanged. -/
theorem extCodeSizeWord_eq_of_accountCodeStateEq {σ σ' : AccountMap} (target : UInt256)
    (h : accountCodeStateEq σ σ') :
    Reasoning.Theory.extCodeSizeWord σ' target
      = Reasoning.Theory.extCodeSizeWord σ target := by
  rw [extCodeSizeWord_eq_ofNat_getD, extCodeSizeWord_eq_ofNat_getD,
    (h (AccountAddress.ofUInt256 target)).symm]

theorem extCodeSizeWord_eq (σ : AccountMap) (target : UInt256) :
    extCodeSizeWord σ target =
      UInt256.ofNat ((σ.get? (AccountAddress.ofUInt256 target)).option 0
        (fun acc => acc.code.size)) := by
  unfold extCodeSizeWord
  cases σ.get? (AccountAddress.ofUInt256 target) <;> rfl

theorem storageStore_executionEnv' (evm : EVM.State)
    (addr : AccountAddress) (slot value : UInt256) :
    (Solm.EVM.storageStore evm addr slot value).executionEnv = evm.executionEnv := by
  unfold Solm.EVM.storageStore
  cases State.lookupAccount evm addr <;> rfl

theorem slotWord_eq_of_accounts_eq
    {σ : AccountMap} (evm : EVM.State) (I : ExecutionEnv) (slot : UInt256)
    (henv : evm.executionEnv = I)
    (hAccounts : σ = evm.accountMap) :
  solcSlotWord σ I slot =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot := by
  simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    solcSlotWord, henv, hAccounts]

theorem storageStore_present (evm : EVM.State)
    (addr : AccountAddress) (slot val : UInt256) {acc : Account}
    (hacc : evm.accountMap.get? addr = some acc) :
    ∃ acc', (Solm.EVM.storageStore evm addr slot val).accountMap.get? addr = some acc' := by
  unfold Solm.EVM.storageStore State.lookupAccount
  rw [hacc]
  simp [Option.option, State.setAccount, Std.ExtTreeMap.getElem?_insert_self]

theorem keyValueToWord_int_ofNat_of_lt {n : Nat} (hn : n < UInt256.size) :
    keyValueToWord (.int (Int.ofNat n)) = UInt256.ofNat n := by
  have hto : (UInt256.ofNat n).toNat = n := ulit_toNat' n hn
  simpa [hto] using keyValueToWord_uint256 (UInt256.ofNat n)

theorem evalBinaryOpGtInt (x y : Int) :
    evalBinaryOp? .gt (.int x) (.int y) = .ok (.bool (x > y)) := by
  rfl

theorem evalBinaryOpNeAddress (a b : AccountAddress) :
    evalBinaryOp? .ne (.address a) (.address b) =
      .ok (.bool (!(Value.address a == Value.address b))) := by
  rfl

theorem storageLocStore_uint256_pred (evm : EVM.State) (slot len : UInt256)
    (hpos : 0 < len.toNat) :
    storageLocStore evm (uint256Loc slot) (.int (Int.ofNat len.toNat - 1)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.ofNat (len.toNat - 1))) := by
  unfold storageLocStore storageLocWriteWord uint256Loc
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

theorem storageLocStore_uint256_succ (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (uint256Loc slot) (.int (Int.ofNat val.toNat + 1)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot (val + ⟨1⟩)) := by
  unfold storageLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, bidWordOfInt_succ, bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (val + ⟨1⟩)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = (val + ⟨1⟩).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

theorem xi_error_of_X_sat_local {σ σ₀ A I}
    {g : Sat256} {e : ExecutionException}
    (h : X (g.toNat + 1) (D_J I.code 0)
            (initState σ σ₀ g A I) = .error e) :
    Ξ σ σ₀ g.toUInt256 A I = .error e :=
  Xi_error_of_X (g := g.toUInt256) (by
    simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using h)

theorem evalExpr_binary_nonshort {cfg solm evm op lhs rhs}
    (hand : op ≠ BinaryOp.and) (hor : op ≠ BinaryOp.or) :
    evalExpr? cfg solm evm (.binary op lhs rhs) =
      (do
        let lhsValue <- evalExpr? cfg solm evm lhs
        let rhsValue <- evalExpr? cfg solm evm rhs
        evalBinaryOp? op lhsValue rhsValue) := by
  cases op <;> simp [evalExpr?] at hand hor ⊢

theorem storageLocStore_uint256_ofNat (evm : EVM.State) (slot : UInt256) (n : Nat) :
    storageLocStore evm (uint256Loc slot) (.int (Int.ofNat n)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (EVM.word (Int.ofNat n).toNat)) := by
  unfold storageLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, bind, Option.bind, pure]
  rw [wordOfInt_nonneg]
  · have hslen := (EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
    have hvlen := (EVM.Word.toBytesLEWithSizeProof (EVM.word (Int.ofNat n).toNat)).2
    congr 2
    apply u256_inj
    show fromBytes'
        (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
          ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) =
        (EVM.word (Int.ofNat n).toNat).toNat
    rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
      List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
      List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]
  · simp

theorem toExecute_ecrecover_precompile (σ : AccountMap) :
    toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) =
      ToExecute.Precompiled (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) := by
  unfold toExecute
  have hmem : AccountAddress.ofUInt256 (⟨1⟩ : UInt256) ∈ π := by
    unfold π
    decide
  rw [if_pos hmem]

theorem ecrecover_output_size (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) :
    let r := Ξ_ECREC σ g A I
    r.2.2.2.size = 0 ∨ r.2.2.2.size = 32 := by
  unfold Ξ_ECREC
  dsimp
  split
  · left
    rfl
  · split
    · left
      rfl
    · split
      · right
        rw [ByteArray.size_append]
        rw [ByteArray_zeroes_size]
        rw [ByteArray.size_extract]
        rw [keccak_size]
        decide
      · left
        rfl

theorem staticcallTheta_ecrecover_output_size
    {blobVersionedHashes blocks σ σ₀ A_in r s g p v v' d e H w σ' g' A' z o}
    (hΘ : (σ', g', A', z, o) =
      Θ σ σ₀ A_in r s
        (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          g p v v' d e H blobVersionedHashes blocks w) :
    o.size = 0 ∨ o.size = 32 := by
  have hpre : toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) =
      ToExecute.Precompiled (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) := by
    exact toExecute_ecrecover_precompile σ
  have hone : (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) = 1 := by
    decide
  have hout := congrArg (fun x => x.2.2.2.2.size) hΘ
  have hout' :
      o.size =
        (Θ σ σ₀ A_in r s
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          g p v v' d e H blobVersionedHashes blocks w).2.2.2.2.size := by
    simpa using hout
  rw [hout']
  unfold Θ
  rw [hpre, hone]
  dsimp
  exact ecrecover_output_size _ g A_in _

theorem code_zero_of_codeSize_zero {evm : EVM.State} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : Reasoning.Theory.extCodeSizeWord evm.accountMap target = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount addr).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  simpa [State.lookupAccount] using
    extCodeSizeWord_zero_lookup_code_zero
      (σ := evm.accountMap) haddr hzero

theorem code_pos_of_codeSize_ne_zero {evm : EVM.State} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : Reasoning.Theory.extCodeSizeWord evm.accountMap target ≠ ⟨0⟩) :
    0 <
      (UInt256.ofNat
        ((evm.lookupAccount addr).option 0 (fun acc => acc.code.size))).toNat := by
  by_contra hnot
  have hnat :
      (UInt256.ofNat
        ((evm.lookupAccount addr).option 0 (fun acc => acc.code.size))).toNat = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hwordZero :
      UInt256.ofNat ((evm.lookupAccount addr).option 0 (fun acc => acc.code.size)) = ⟨0⟩ :=
    uint256_toNat_eq_zero hnat
  have hword :
      UInt256.ofNat ((evm.lookupAccount addr).option 0 (fun acc => acc.code.size)) =
        Reasoning.Theory.extCodeSizeWord evm.accountMap target := by
    subst addr
    cases hacc : evm.accountMap.get? (AccountAddress.ofUInt256 target) <;>
      simp [-Std.ExtTreeMap.get?_eq_getElem?, State.lookupAccount,
        Reasoning.Theory.extCodeSizeWord, hacc,
        Option.option] <;>
      decide
  exact hne (by rw [← hword, hwordZero])

theorem code_zero_of_state_codeSize_zero {evm : EVM.State} {targetWord : UInt256}
    (hzero :
      Reasoning.Theory.extCodeSizeWord evm.accountMap targetWord = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat targetWord]
  unfold Reasoning.Theory.extCodeSizeWord at hzero
  cases hacc : evm.accountMap.get? (AccountAddress.ofUInt256 targetWord) with
  | none =>
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, State.lookupAccount, hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by decide)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, State.lookupAccount, hacc] using hword

theorem code_pos_of_state_codeSize_ne {evm : EVM.State} {targetWord : UInt256}
    (hne :
      Reasoning.Theory.extCodeSizeWord evm.accountMap targetWord ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (AccountAddress.ofNat targetWord.toNat)).option 0
        (fun acc => acc.code.size))).toNat := by
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat targetWord]
  unfold Reasoning.Theory.extCodeSizeWord at hne
  cases hacc : evm.accountMap.get? (AccountAddress.ofUInt256 targetWord) with
  | none =>
      exfalso
      exact hne (by simp [-Std.ExtTreeMap.get?_eq_getElem?, hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [-Std.ExtTreeMap.get?_eq_getElem?, hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, State.lookupAccount,
        hacc] using Nat.pos_of_ne_zero htoNatNe

theorem addressValueTransport (a : AccountAddress) :
    some [Value.address (AccountAddress.ofNat a.toNat)] =
      some [Value.address (AccountAddress.ofNat
        (UInt256.land (EVM.Word.ofNat a.toNat) solcAddrMask).toNat)] := by
  have hword : (EVM.Word.ofNat a.toNat).toNat = a.toNat := by
    unfold EVM.Word.ofNat UInt256.ofNat UInt256.toNat
    exact Nat.mod_eq_of_lt
      (lt_of_lt_of_le a.isLt (show AccountAddress.size ≤ UInt256.size from by decide))
  have hcanon : (EVM.Word.ofNat a.toNat).toNat < EVM.addressModulus := by
    rw [hword]
    change a.toNat < EVM.twoPow 160
    simp [EVM.twoPow, AccountAddress.size]
  rw [solcAddrMask_clean hcanon, hword]

theorem addressWordCode_zero_of_state {evm : EVM.State} (target : UInt256)
    (hzero : Reasoning.Theory.extCodeSizeWord evm.accountMap target = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (AccountAddress.ofNat target.toNat)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  simpa [State.lookupAccount] using
    extCodeSizeWord_zero_lookup_code_zero
      (σ := evm.accountMap) (target := target)
      (addr := AccountAddress.ofNat target.toNat)
      (accountAddress_ofUInt256_eq_ofNat_toNat target).symm hzero

theorem addressWordCode_pos_of_state {evm : EVM.State} (target : UInt256)
    (hne : Reasoning.Theory.extCodeSizeWord evm.accountMap target ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (AccountAddress.ofNat target.toNat)).option 0
        (fun acc => acc.code.size))).toNat := by
  simpa [State.lookupAccount] using
    extCodeSizeWord_ne_zero_lookup_code_pos
      (σ := evm.accountMap) (target := target)
      (addr := AccountAddress.ofNat target.toNat)
      (accountAddress_ofUInt256_eq_ofNat_toNat target).symm hne

theorem storageStore_σ0 (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).σ₀ = evm.σ₀ := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.get? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage]

theorem storageStore_substate' (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).substate = evm.substate := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.get? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage]

theorem sstoreAccountMap_get?_owner_some_of_some
    (σ : AccountMap) (a : AccountAddress) (slot val : UInt256) {acc : Account}
    (hacc : σ.get? a = some acc) :
    ∃ acc', (sstoreAccountMap a σ slot val).get? a = some acc' := by
  unfold sstoreAccountMap
  rw [hacc]
  simp only [Option.option, Std.ExtTreeMap.get?_eq_getElem?,
    Std.ExtTreeMap.getElem?_insert_self]
  exact ⟨if val == (default : UInt256) then { acc with storage := acc.storage.erase slot }
    else { acc with storage := acc.storage.insert slot val }, rfl⟩

theorem sstoreAccountMap_storage_getD_self_zero_present
    (σ : AccountMap) (a : AccountAddress) (slot val : UInt256) {acc : Account}
    (hacc : σ.get? a = some acc) :
    (((sstoreAccountMap a σ slot val).get? a).option (⟨0⟩ : UInt256)
        (fun acc => acc.storage.getD slot ⟨0⟩)) = val := by
  unfold sstoreAccountMap
  rw [hacc]
  simp only [Option.option, Std.ExtTreeMap.get?_eq_getElem?,
    Std.ExtTreeMap.getElem?_insert_self]
  by_cases hzero : (val == (default : UInt256)) = true
  · have hval : val = (⟨0⟩ : UInt256) := by
      simpa using eq_of_beq hzero
    subst val
    simp [hzero]
  · have hfalse : (val == (default : UInt256)) = false := by
      cases h : (val == (default : UInt256)) <;> simp [h] at hzero ⊢
    simp [hfalse]

theorem keyValueToWord_uint256_natCast (w : UInt256) :
    keyValueToWord (.int ((w.toNat : Nat) : Int)) = w := by
  simpa using keyValueToWord_uint256 w

theorem evmState_ext {s t : EVM.State}
    (hAccountMap : s.accountMap = t.accountMap)
    (hSigma0 : s.σ₀ = t.σ₀)
    (hGas : s.totalGasUsedInBlock = t.totalGasUsedInBlock)
    (hReceipts : s.transactionReceipts = t.transactionReceipts)
    (hSubstate : s.substate = t.substate)
    (hEnv : s.executionEnv = t.executionEnv)
    (hMachine : s.machineState = t.machineState) : s = t := by
  cases s
  cases t
  simp_all

theorem storageStore_totalGasUsedInBlock
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).totalGasUsedInBlock =
      evm.totalGasUsedInBlock := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.get? addr <;> simp [Option.option, State.setAccount]

theorem storageStore_transactionReceipts
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).transactionReceipts = evm.transactionReceipts := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.get? addr <;> simp [Option.option, State.setAccount]

theorem storageStore_machineState
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).machineState = evm.machineState := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.get? addr <;> simp [Option.option, State.setAccount]



theorem depth_ne_1024_of_lt {d : Fin 1025} (h : d.val < 1024) : d ≠ 1024 := by
  intro hd
  have hdval : d.val = (1024 : Fin 1025).val := congrArg Fin.val hd
  have h1024 : (1024 : Fin 1025).val = 1024 := by decide
  omega

theorem initStateDepth_ne_1024_of_lt {σ σ₀ A I g}
    (h : I.depth.val < 1024) :
    (initState σ σ₀ g A I).executionEnv.depth ≠ 1024 := by
  simpa [initState] using depth_ne_1024_of_lt h

/-- Bridge the Solm `storageLoad` at `I.codeOwner` to the EVM-side `solcSlotWord`. -/
theorem storageLoad_eq_solcSlotWord (evm : EVM.State) (I : ExecutionEnv) (slot : UInt256) :
    Solm.EVM.storageLoad evm I.codeOwner slot = solcSlotWord evm.accountMap I slot := by
  simp [solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Ethereum.Account.lookupStorage]

theorem solcSlotWordAt_sstore_ne (σ : AccountMap) (I : ExecutionEnv)
    (readSlot writeSlot val : UInt256) (hne : readSlot ≠ writeSlot) :
    solcSlotWordAt readSlot (sstoreAccountMap I.codeOwner σ writeSlot val) I =
      solcSlotWordAt readSlot σ I := by
  exact sstoreAccountMap_storage_getD_ne σ I.codeOwner readSlot writeSlot val hne

theorem solcSlotWord_sstore_ne' (σ : AccountMap) (I : ExecutionEnv)
    (readSlot writeSlot val : UInt256) (hne : readSlot ≠ writeSlot) :
    solcSlotWord (sstoreAccountMap I.codeOwner σ writeSlot val) I readSlot =
      solcSlotWord σ I readSlot := by
  simpa [solcSlotWordAt] using solcSlotWordAt_sstore_ne σ I readSlot writeSlot val hne

/-- General append/split for the forward zeroing fold: running `fuel + tail` clears is running
    `tail` more clears from the advanced cursor after the first `fuel`. -/
theorem clearDataWordsForwardFrom_append_gen (owner : AccountAddress) (base : UInt256) :
    ∀ (fuel : Nat) (τ : AccountMap) (idx : UInt256) (tail : Nat),
      clearDataWordsForwardFrom owner τ base idx (fuel + tail) =
        clearDataWordsForwardFrom owner
          (clearDataWordsForwardFrom owner τ base idx fuel) base
          (UInt256.ofNat fuel + idx) tail
  | 0, τ, idx, tail => by
      simp only [Nat.zero_add, clearDataWordsForwardFrom]
      rw [show (UInt256.ofNat 0 + idx) = idx from by
        apply u256_inj; rw [uadd_toNat]
        simp only [show (UInt256.ofNat 0).toNat = 0 from rfl, Nat.zero_add]
        exact Nat.mod_eq_of_lt idx.val.isLt]
  | fuel + 1, τ, idx, tail => by
      have key : fuel + 1 + tail = (fuel + tail) + 1 := by omega
      rw [key, clearDataWordsForwardFrom,
        clearDataWordsForwardFrom_append_gen owner base fuel
          (sstoreAccountMap owner τ (base + idx) ⟨0⟩) ((⟨1⟩ : UInt256) + idx) tail]
      conv_rhs => rw [clearDataWordsForwardFrom]
      rw [show UInt256.ofNat (fuel + 1) + idx = UInt256.ofNat fuel + ((⟨1⟩ : UInt256) + idx) from by
        rw [← u256_one_add_ofNat, u256_add_comm (⟨1⟩ : UInt256) (UInt256.ofNat fuel), uadd_assoc]]

/-- Peel the final store off a `⟨0⟩`-based clear run: `n+1` clears equal `n` clears followed by a
    single `sstore` of `⟨0⟩` at `base + n`. -/
theorem clearDataWordsForwardFrom_append (owner : AccountAddress) (τ : AccountMap)
    (base : UInt256) (n : Nat) :
    clearDataWordsForwardFrom owner τ base ⟨0⟩ (n + 1) =
      sstoreAccountMap owner (clearDataWordsForwardFrom owner τ base ⟨0⟩ n)
        (base + UInt256.ofNat n) ⟨0⟩ := by
  rw [clearDataWordsForwardFrom_append_gen owner base n τ ⟨0⟩ 1]
  rw [show (UInt256.ofNat n + (⟨0⟩ : UInt256)) = UInt256.ofNat n from by
    apply u256_inj; rw [uadd_toNat]
    simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.add_zero]
    exact Nat.mod_eq_of_lt (UInt256.ofNat n).val.isLt]
  rw [clearDataWordsForwardFrom, clearDataWordsForwardFrom]

theorem shortL1_size (v : UInt256) : (writeWord solcFreePtrMem 64 v).size = 96 := by
  rw [writeWord_size solcFreePtrMem 64 v
    (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num)),
    solcFreePtrMem_size]; omega

theorem shortL2_size (v w : UInt256) :
    (writeWord (writeWord solcFreePtrMem 64 v) 128 w).size = 160 := by
  rw [writeWord_size _ 128 w (by rw [shortL1_size]; exact lt_usize _ (by norm_num)),
    shortL1_size]; omega

/-- `storageLoad` at `evm`'s own code owner reads `solcSlotWord` over `evm.accountMap`. -/
theorem storageLoad_eq_solcSlotWord_of_codeOwner_eq (evm : EVM.State) (I : ExecutionEnv)
    (slot : UInt256)
    (hco : evm.executionEnv.codeOwner = I.codeOwner) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot =
      solcSlotWord evm.accountMap I slot := by
  rw [hco]
  simp [solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Ethereum.Account.lookupStorage]

/-- `storageStore` leaves `executionEnv` untouched. -/
theorem storageStore_executionEnv_eq (evm : EVM.State) (a : AccountAddress) (s v : UInt256) :
    (Solm.EVM.storageStore evm a s v).executionEnv = evm.executionEnv := by
  exact Reasoning.Theory.storageStore_executionEnv evm a s v

theorem storageLoad_storageStore_self_nonzero (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) {acc : Account} (hacc : evm.lookupAccount a = some acc)
    (_hval : (val == default) = false) :
    Solm.EVM.storageLoad (Solm.EVM.storageStore evm a slot val) a slot = val :=
  storageLoad_storageStore_same_present evm a (by simpa [State.lookupAccount] using hacc) slot val

/-- The offset bound check `iszero(gt(0x20, 2^64-1))` is taken (offset `0x20 ≤ 2^64-1`). -/
theorem decoderValidOff :
    (UInt256.isZero (UInt256.gt (UInt256.ofNat 32)
      (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨0x40⟩) ⟨1⟩))) ≠ ⟨0⟩ := by
  rw [ugt_zero (by rw [u64mask_toNat, ulit_toNat' _ (by decide : (32:ℕ) < UInt256.size)]; omega)]
  decide

theorem storageLocLoad_bool_offset0' (evm : EVM.State) (slot : UInt256)
    {hbound : (⟨0⟩ : UInt256).toNat + (⟨1⟩ : UInt256).toNat ≤ 32} :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 1, hbound := hbound, type := .bool }
      = wordToElem .bool
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩) := by
  simpa [boolOffset0Loc] using storageLocLoad_bool_offset0 evm slot

theorem storageLocLoad_bool_offset0_false' (evm : EVM.State) (slot : UInt256)
    {hbound : (⟨0⟩ : UInt256).toNat + (⟨1⟩ : UInt256).toNat ≤ 32}
    (hzero : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ =
      ⟨0⟩) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 1, hbound := hbound, type := .bool } =
      .bool false := by
  simpa [boolOffset0Loc] using storageLocLoad_bool_offset0_false evm slot hzero

theorem storageLocLoad_bool_offset0_true' (evm : EVM.State) (slot : UInt256)
    {hbound : (⟨0⟩ : UInt256).toNat + (⟨1⟩ : UInt256).toNat ≤ 32}
    (hnz : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩ ≠
      ⟨0⟩) :
    storageLocLoad evm
        { slot := slot, offset := 0, size := 1, hbound := hbound, type := .bool } =
      .bool true := by
  simpa [boolOffset0Loc] using storageLocLoad_bool_offset0_true evm slot hnz

theorem storageLocStore_bool_true_offset0' (evm : EVM.State) (slot : UInt256)
    {hbound : (⟨0⟩ : UInt256).toNat + (⟨1⟩ : UInt256).toNat ≤ 32} :
    storageLocStore evm
        { slot := slot, offset := 0, size := 1, hbound := hbound, type := .bool }
        (.bool true) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (UInt256.lor
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.lnot ⟨255⟩)) ⟨1⟩)) := by
  simpa [boolOffset0Loc] using storageLocStore_bool_true_offset0 evm slot

@[simp] theorem storageStore_executionEnv'' (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).executionEnv = evm.executionEnv := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.get? a <;> rfl

theorem evalBinaryOp_lt_int_ok (x y : Int) :
    evalBinaryOp? .lt (.int x) (.int y) = .ok (.bool (x < y)) := by
  rfl

theorem evalBinaryOp_add_int_ok (x y : Int) :
    evalBinaryOp? .add (.int x) (.int y) = .ok (.int (x + y)) := by
  rfl

theorem getElem?_insert_ne (locals : Store) {k a : Ident} (value : Value)
    (h : (k == a) = false) :
    (locals.insert k value)[a]? = locals[a]? := by
  simp [Std.HashMap.getElem?_insert, h]

theorem getElem?_insert_self (locals : Store) (k : Ident) (value : Value) :
    (locals.insert k value)[k]? = some value := by
  simp

theorem timestamp_add_duration_word_eq_left (evm : EVM.State) (biddingTime : Int)
    (h0 : 0 ≤ biddingTime)
    (hlt : biddingTime < Int.ofNat (EVM.twoPow 256))
    (hno : ¬ UInt256.size ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat +
        (EVM.word biddingTime.toNat).toNat) :
    EVM.word ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat + biddingTime.toNat) =
      UInt256.ofNat evm.executionEnv.header.timestamp + EVM.word biddingTime.toNat :=
  constructorCheckedAddIntWordBaseFirst_eq
    (UInt256.ofNat evm.executionEnv.header.timestamp) biddingTime h0 hlt hno

theorem normalizeRawBoolWord_false_of_u256 {word : Nat}
    (hword : (UInt256.ofNat word).toNat = word) (hzero : UInt256.ofNat word = ⟨0⟩) :
    normalizeRawBoolWord? (rawBoolWordValue word) = .ok (.bool false) := by
  have hword0 : word = 0 := by
    have h := congrArg UInt256.toNat hzero
    simpa [hword] using h
  subst word
  rfl

theorem normalizeRawBoolWord_true_of_u256 {word : Nat}
    (hword : (UInt256.ofNat word).toNat = word) (hone : UInt256.ofNat word = ⟨1⟩) :
    normalizeRawBoolWord? (rawBoolWordValue word) = .ok (.bool true) := by
  have hword1 : word = 1 := by
    have h := congrArg UInt256.toNat hone
    simpa [hword] using h
  subst word
  rfl

theorem normalizeRawBoolWord_revert_of_u256 {word : Nat}
    (hword : (UInt256.ofNat word).toNat = word)
    (hzero : UInt256.ofNat word ≠ ⟨0⟩) (hone : UInt256.ofNat word ≠ ⟨1⟩) :
    normalizeRawBoolWord? (rawBoolWordValue word) = .revert := by
  have hword0 : word ≠ 0 := by
    intro h0
    apply hzero
    subst word
    rfl
  have hword1 : word ≠ 1 := by
    intro h1
    apply hone
    subst word
    rfl
  simp [normalizeRawBoolWord?, rawBoolWordValue, hword0, hword1]

theorem evalBinaryOp_eq_int_ok (x y : Int) :
    evalBinaryOp? .eq (.int x) (.int y) =
      .ok (.bool (Value.int x == Value.int y)) := by
  rfl

theorem start_bound_of_slt_one {I : ExecutionEnv} {off : UInt256}
    (hcalldataSign : I.calldata.size < 2 ^ 255)
    (hoff : off.toNat ≤ solcMaxU64)
    (hstart : UInt256.slt (((⟨4⟩ : UInt256) + off) + ⟨31⟩)
      (UInt256.ofNat I.calldata.size) = ⟨1⟩) :
    4 + off.toNat + 31 < I.calldata.size := by
  by_contra hnot
  have hleft :
      (((⟨4⟩ : UInt256) + off) + ⟨31⟩).toNat = 4 + off.toNat + 31 :=
    add4_word_add31_toNat off hoff
  have hhi : (((⟨4⟩ : UInt256) + off) + ⟨31⟩).toNat < 2 ^ 255 := by
    rw [hleft]
    rw [show solcMaxU64 = 18446744073709551615 by rfl] at hoff
    omega
  have hzero :
      UInt256.slt (((⟨4⟩ : UInt256) + off) + ⟨31⟩)
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    apply slt_lit_zero hcalldataSign
    · rw [hleft]
      omega
    · exact hhi
  rw [hstart] at hzero
  have hnat := congrArg UInt256.toNat hzero
  change (1 : Nat) = 0 at hnat
  omega

theorem array_end_bound_of_ugt_zero {I : ExecutionEnv} {off len : UInt256}
    (hoff : off.toNat ≤ solcMaxU64)
    (hlen : len.toNat ≤ solcMaxU64)
    (hend : UInt256.gt (((((⟨4⟩ : UInt256) + off) +
          UInt256.shiftLeft len ⟨5⟩) + ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) :
    4 + off.toNat + 32 + 32 * len.toNat ≤ I.calldata.size := by
  have h32lenSmall : 32 * len.toNat < UInt256.size := by
    rw [show solcMaxU64 = 18446744073709551615 by rfl] at hlen
    norm_num [UInt256.size]
    omega
  have hleft :
      (((((⟨4⟩ : UInt256) + off) + UInt256.shiftLeft len ⟨5⟩) + ⟨32⟩)).toNat =
        4 + off.toNat + 32 * len.toNat + 32 := by
    rw [← u256_ofNat_toNat off, ← u256_ofNat_toNat len,
      shiftLeft5_ofNat_eq h32lenSmall]
    have h4off32len :
        ((UInt256.ofNat 4 + UInt256.ofNat off.toNat) +
            UInt256.ofNat (32 * len.toNat)).toNat =
          4 + off.toNat + 32 * len.toNat := by
      apply uadd3_ofNat_toNat
      · norm_num [UInt256.size]
      · exact off.val.isLt
      · exact h32lenSmall
      · rw [show solcMaxU64 = 18446744073709551615 by rfl] at hoff
        norm_num [UInt256.size]
        omega
      · rw [show solcMaxU64 = 18446744073709551615 by rfl] at hoff hlen
        norm_num [UInt256.size]
        omega
    rw [uadd_toNat]
    change
      (((UInt256.ofNat 4 + UInt256.ofNat off.toNat) +
            UInt256.ofNat (32 * len.toNat)).toNat + (UInt256.ofNat 32).toNat) %
          UInt256.size =
        4 + (UInt256.ofNat off.toNat).toNat +
          32 * (UInt256.ofNat len.toNat).toNat + 32
    rw [h4off32len, ulit_toNat' 32 (by norm_num [UInt256.size]),
      ulit_toNat' off.toNat off.val.isLt, ulit_toNat' len.toNat len.val.isLt]
    apply Nat.mod_eq_of_lt
    rw [show solcMaxU64 = 18446744073709551615 by rfl] at hoff hlen
    norm_num [UInt256.size]
    omega
  by_contra hnot
  have hgt : UInt256.gt
      (((((⟨4⟩ : UInt256) + off) + UInt256.shiftLeft len ⟨5⟩) + ⟨32⟩))
      (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    apply ugt_one
    rw [hleft, ulit_toNat' I.calldata.size hsize]
    omega
  rw [hend] at hgt
  have hnat := congrArg UInt256.toNat hgt
  change (0 : Nat) = 1 at hnat
  omega

theorem sourceWord_canonical (I : ExecutionEnv) :
    (UInt256.ofNat I.source.val).toNat < EVM.addressModulus := by
  rw [ulit_toNat' _ (lt_of_lt_of_le I.source.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))]
  simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using I.source.isLt

theorem withdrawAccountMapEquiv_balance {σ τ : AccountMap}
    (hστ : σ = τ) (addr : AccountAddress) :
    (σ.get? addr |>.elim ⟨0⟩ (·.balance)) =
      (τ.get? addr |>.elim ⟨0⟩ (·.balance)) := by
  rw [hστ]

theorem store_get_empty (k : Ident) : (∅ : Solm.Store).get? k = none := by simp

theorem wordToElem_bool_scalar (word : UInt256) :
    match wordToElem .bool word with
    | .struct _ _ => False
    | .array _ => False
    | .bytes _ => False
    | _ => True := by
  change
    match
        (if (word.val == 0) = true then
          Value.bool false
        else
          Value.bool true) with
    | .struct _ _ => False
    | .array _ => False
    | .bytes _ => False
    | _ => True
  by_cases h : (word.val == 0) = true <;> simp [h]

theorem evalBinaryOp_ne_int_ok (x y : Int) :
    evalBinaryOp? .ne (.int x) (.int y) =
      .ok (.bool (!(Value.int x == Value.int y))) := by
  rfl

theorem timestamp_add_duration_word_eq (evm : EVM.State) (biddingTime : Int)
    (h0 : 0 ≤ biddingTime)
    (hlt : biddingTime < Int.ofNat (EVM.twoPow 256))
    (hno : ¬ UInt256.size ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat +
        (EVM.word biddingTime.toNat).toNat) :
    EVM.word ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat + biddingTime.toNat) =
      EVM.word biddingTime.toNat + UInt256.ofNat evm.executionEnv.header.timestamp :=
  constructorCheckedAddIntWord_eq
    (UInt256.ofNat evm.executionEnv.header.timestamp) biddingTime h0 hlt hno

theorem sstoreZero_clearDataWordsForwardFrom_comm
    (owner : AccountAddress) (σ : AccountMap) (base idx slot : UInt256) :
    ∀ fuel,
      sstoreAccountMap owner
          (clearDataWordsForwardFrom owner σ base idx fuel) slot ⟨0⟩ =
        clearDataWordsForwardFrom owner
          (sstoreAccountMap owner σ slot ⟨0⟩) base idx fuel
  | 0 => rfl
  | n + 1 => by
      simp [clearDataWordsForwardFrom]
      have ih := sstoreZero_clearDataWordsForwardFrom_comm
        owner (sstoreAccountMap owner σ (base + idx) ⟨0⟩)
        base ((⟨1⟩ : UInt256) + idx) slot n
      have hcomm₀ :
          sstoreAccountMap owner
              (sstoreAccountMap owner σ (base + idx) ⟨0⟩) slot ⟨0⟩ =
            sstoreAccountMap owner
              (sstoreAccountMap owner σ slot ⟨0⟩) (base + idx) ⟨0⟩ := by
        by_cases hne : slot ≠ base + idx
        · exact (sstoreAccountMap_comm σ owner slot ⟨0⟩ (base + idx) ⟨0⟩ hne).symm
        · have heq : slot = base + idx := by exact Classical.not_not.mp hne
          subst slot
          rfl
      have hcomm := congrArg
        (fun accounts => clearDataWordsForwardFrom owner accounts base
          ((⟨1⟩ : UInt256) + idx) n) hcomm₀
      exact Eq.trans ih hcomm

theorem sstoreZero_clearDataWordsForwardFrom_absorb_first
    {owner : AccountAddress} {τ : AccountMap} {base idx : UInt256} (fuel : Nat) :
    sstoreAccountMap owner
        (clearDataWordsForwardFrom owner τ base idx (fuel + 1)) (base + idx) ⟨0⟩ =
      clearDataWordsForwardFrom owner τ base idx (fuel + 1) := by
  simp [clearDataWordsForwardFrom]
  have hcomm := sstoreZero_clearDataWordsForwardFrom_comm
    owner (sstoreAccountMap owner τ (base + idx) ⟨0⟩)
    base ((⟨1⟩ : UInt256) + idx) (base + idx) fuel
  have hself := sstoreAccountMap_self_update
    τ owner (base + idx) (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)
  have htailSelf := congrArg
    (fun accounts => clearDataWordsForwardFrom owner accounts base
      ((⟨1⟩ : UInt256) + idx) fuel) hself
  exact Eq.trans hcomm (Eq.symm htailSelf)

theorem clearDataWordsForwardFrom_double_prefix
    {owner : AccountAddress} {τ : AccountMap} {base idx : UInt256} :
    ∀ oldFuel newFuel : Nat, oldFuel ≤ newFuel →
      clearDataWordsForwardFrom owner
          (clearDataWordsForwardFrom owner τ base idx oldFuel) base idx newFuel =
        clearDataWordsForwardFrom owner τ base idx newFuel
  | 0, newFuel, _hle => by
      simp [clearDataWordsForwardFrom]
  | oldFuel + 1, 0, hle => by
      omega
  | oldFuel + 1, newFuel + 1, hle => by
      simp [clearDataWordsForwardFrom]
      have hcomm := sstoreZero_clearDataWordsForwardFrom_comm
        owner (sstoreAccountMap owner τ (base + idx) ⟨0⟩)
        base ((⟨1⟩ : UInt256) + idx) (base + idx) oldFuel
      have hself := sstoreAccountMap_self_update
        τ owner (base + idx) (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)
      have htailSelf := congrArg
        (fun accounts => clearDataWordsForwardFrom owner accounts base
          ((⟨1⟩ : UInt256) + idx) oldFuel) hself
      have hbase := Eq.trans hcomm (Eq.symm htailSelf)
      have hcong := congrArg
        (fun accounts => clearDataWordsForwardFrom owner accounts base
          ((⟨1⟩ : UInt256) + idx) newFuel) hbase
      have htail := clearDataWordsForwardFrom_double_prefix
        (owner := owner) (τ := sstoreAccountMap owner τ (base + idx) ⟨0⟩)
        (base := base) (idx := ((⟨1⟩ : UInt256) + idx))
        oldFuel newFuel (by omega)
      exact Eq.trans hcong htail

theorem codeOwnerWord_clean (I : ExecutionEnv) :
    UInt256.land (UInt256.ofNat I.codeOwner.val) solcAddrMask = UInt256.ofNat I.codeOwner.val := by
  have hsmall : I.codeOwner.val < 2 ^ 160 := I.codeOwner.isLt
  have hsize : I.codeOwner.val < UInt256.size :=
    lt_trans hsmall (by decide : 2 ^ 160 < UInt256.size)
  apply u256_inj
  rw [u256_land_toNat, UInt256.toNat_ofNat_of_lt hsize,
    show solcAddrMask.toNat = 2 ^ 160 - 1 from by decide,
    land_mask160 I.codeOwner.val hsmall, Nat.mod_eq_of_lt hsize]

theorem addressValue_masked (w : UInt256) :
    (.address (AccountAddress.ofNat w.toNat) : Value) =
      .address (AccountAddress.ofNat (UInt256.land solcAddrMask w).toNat) := by
  exact solcAddressValue_masked w

theorem cast_addressAsUint256 (w : UInt256) :
    castValue? (.address (AccountAddress.ofNat w.toNat)) packedUInt256StorageType =
      some (.int (Int.ofNat (UInt256.land solcAddrMask w).toNat)) := by
  have haddr : (AccountAddress.ofNat w.toNat).toNat =
      (UInt256.land solcAddrMask w).toNat := permitAddress_toNat_mask w
  have hlt : (AccountAddress.ofNat w.toNat).toNat < EVM.twoPow 256 := by
    exact lt_of_lt_of_le (AccountAddress.ofNat w.toNat).isLt (by decide)
  simp only [castValue?, packedUInt256StorageType, abiUInt256Int]
  rw [if_pos hlt]
  rw [haddr]

theorem valueInt_beq_false_of_ne {x y : Int} (h : x ≠ y) :
    (Value.int x == Value.int y) = false := by
  rw [beq_eq_false_iff_ne]
  intro hv
  cases hv
  exact h rfl

theorem storageLocStore_word_int_some
    (evm : EVM.State) (slot : UInt256) (n : Int) :
    ∃ evm', storageLocStore evm (uint256Loc slot) (.int n) = some evm' := by
  unfold storageLocStore storageLocWriteWord uint256Loc
  simp only [valueToWord, bind, Option.bind, pure]
  exact ⟨_, rfl⟩

/-- `solcSlotWordAt` transports across `EVMStateEquiv` (same codeOwner storage view). -/
theorem solcSlotWordAt_eq_of_equiv {a b : EVM.State} (h : EVMStateEquiv a b) (s : UInt256) :
    solcSlotWordAt s a.accountMap a.executionEnv = solcSlotWordAt s b.accountMap b.executionEnv :=
      by
  rw [h.executionEnv, h.accountMap]

/-- Lift a return trace whose final account map may differ from the initial map to `Ξ`. -/
theorem RDretXiResultAccountMap {σ σ₀ A I} {g : Sat256} {code o : ByteArray}
    {acc : AccountMap} (hcode : I.code = code)
    (h : RDret code g (initState σ σ₀ g A I) acc o) :
    Ξ σ σ₀ g.toUInt256 A I = .error .OutOfGass ∨
      ∃ (g' : UInt256) (A' : Substate),
        Ξ σ σ₀ g.toUInt256 A I = .ok (.success (acc, g', A') o) := by
  rcases h with hOOG | ⟨s, hX, hacc⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hOOG
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hOOG))
  · have hxi := Xi_success_of_X (g := g.toUInt256) (by
      rw [← hcode] at hX
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    rw [hacc] at hxi
    exact Or.inr ⟨_, _, hxi⟩

/-- On `evm0`, a code-owner storage read at `slot` is the layout word `solcSlotWordAt slot σ I`. -/
theorem storageLoad_initState_ofUInt256_solcSlotWordAt {σ σ₀ A I} {g : UInt256} (slot : UInt256) :
    Solm.EVM.storageLoad (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner slot =
      solcSlotWordAt slot σ I := by
  have hco : (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
      I.codeOwner := rfl
  rw [hco, codeOwnerStorageWord_initState]
  rfl

theorem storageLoad_after_initState_store
    {σ σ₀ A I} {g : Sat256} (writeSlot readSlot val : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore (initState σ σ₀ g A I) I.codeOwner writeSlot val)
        I.codeOwner readSlot =
      solcSlotWordAt readSlot (sstoreAccountMap I.codeOwner σ writeSlot val) I := by
  simp [Solm.EVM.storageLoad, solcSlotWordAt, solcSlotWord, initState,
    storageStore_accountMap, State.lookupAccount,
    Account.lookupStorage]

theorem storageLoad_after_initState_store₂
    {σ σ₀ A I} {g : Sat256}
    (slot₁ slot₂ readSlot val₁ val₂ : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore (initState σ σ₀ g A I)
            I.codeOwner slot₁ val₁)
          I.codeOwner slot₂ val₂)
        I.codeOwner readSlot =
      solcSlotWordAt readSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ slot₁ val₁) slot₂ val₂) I := by
  simp [Solm.EVM.storageLoad, solcSlotWordAt, solcSlotWord, initState,
    storageStore_accountMap, State.lookupAccount, Account.lookupStorage]

theorem storageLoad_after_initState_store₃
    {σ σ₀ A I} {g : Sat256}
    (slot₁ slot₂ slot₃ readSlot val₁ val₂ val₃ : UInt256) :
    Solm.EVM.storageLoad
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore (initState σ σ₀ g A I)
              I.codeOwner slot₁ val₁)
            I.codeOwner slot₂ val₂)
          I.codeOwner slot₃ val₃)
        I.codeOwner readSlot =
      solcSlotWordAt readSlot
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ slot₁ val₁) slot₂ val₂)
          slot₃ val₃) I := by
  simp [Solm.EVM.storageLoad, solcSlotWordAt, solcSlotWord, initState,
    storageStore_accountMap, State.lookupAccount, Account.lookupStorage]

theorem storageLoad_codeOwner_eq_solcSlotWordAt (evm : EVM.State) (I : ExecutionEnv)
    (slot : UInt256) (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot =
      solcSlotWordAt slot evm.accountMap I := by
  simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, solcSlotWordAt,
    solcSlotWord, howner]

/-- The storage word at an arbitrary slot, as read from `initState σ`. -/
theorem storageLoad_initState_solcSlotWord {σ σ₀ A I} {g : Sat256} (slot : UInt256) :
    EVM.storageLoad (initState σ σ₀ g A I)
        (initState σ σ₀ g A I).executionEnv.codeOwner slot =
      solcSlotWord σ I slot := by
  simp [EVM.storageLoad, State.lookupAccount, initState, solcSlotWord, solcSlotWord,
    Account.lookupStorage]

theorem RDretXiResultAccountMapReordered {σ σ' σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {code o : ByteArray}
    (hcode : I.code = code)
    (h : RDret code g (initState σ σ₀ g A I) σ' o) :
    Ξ σ σ₀ g.toUInt256 A I = .error .OutOfGass
    ∨ ∃ (g' : UInt256) (A' : Substate),
        Ξ σ σ₀ g.toUInt256 A I =
          .ok (.success (σ', g', A') o) := by
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hσ : s.accountMap = σ' := hacc
    have hxi := Xi_success_of_X (g := g.toUInt256) (by
      rw [← hcode] at hX
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    rw [hσ] at hxi
    exact Or.inr ⟨_, _, hxi⟩

theorem assignStorageRef_storage_bool_word {cfg : Config} {solm : Frame}
    {evm evm' : EVM.State} {slot : StorageRef} {er : EvaledStorageRef}
    {ty : StorageType} {loc : StorageLoc} {word : UInt256}
    (hbase : solm.locals.get? slot.base = none)
    (her : evalStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.storage er = some ty)
    (hloc : cfg.storage.layout er = fun _ => some loc)
    (hstore : storageLocStore evm loc (wordToElem .bool word) = some evm') :
    assignStorageRef? cfg solm evm .storage slot (wordToElem .bool word) =
      .ok (solm, evm') := by
  exact assignStorageRef_storage_scalar_value hbase her hty hloc
    (wordToElem_bool_scalar word) hstore

end Reasoning.Theory
