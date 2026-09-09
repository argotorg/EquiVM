import Benchmarks.WETH9.TransferFromDefs

/-!
# WETH9 `transferFrom` source-level (Solm) body

The `transferFromTransition.body` executed on `tfStore I`, in the three success branches
(`src == caller`; `src ≠ caller ∧ allowance == uint(-1)`; `src ≠ caller ∧ allowance ≠ uint(-1)`)
and the two require reverts.  Each success lemma exposes the post-state accountMap as the same
`wtfPostMap` tower the EVM produces, so the refinement bridge is a pure `accountMapEquiv` argument.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.WETH9

/-- The source allowance word `allowance[src][msg.sender]` read from `σ`. -/
abbrev tfAllowWord (I : ExecutionEnv) (σ : AccountMap) : UInt256 :=
  solcSlotWord σ I (wtfAllowSlot I (tfSrcMasked I))

/-- The source `balanceOf[src]` word read from `σ`. -/
abbrev tfBalSrcWord (I : ExecutionEnv) (σ : AccountMap) : UInt256 :=
  solcSlotWord σ I (wtfBalSlot (tfSrcMasked I))

/-! ## Infrastructure: store lookups, wrapping arithmetic, reads, assigns, post-state maps -/

/-- Wrapping `sub` on store, valid even on underflow (solc 0.5 `unchecked`). -/
theorem tf_wordOfInt_sub (a b : UInt256) :
    EVM.wordOfInt (Int.ofNat a.toNat - Int.ofNat b.toNat) = UInt256.sub a b := by
  by_cases h : b.toNat ≤ a.toNat
  · exact wordOfInt_sub_words h
  · have h' : a.toNat < b.toNat := Nat.lt_of_not_le h
    have hsub : Int.ofNat (b.toNat - a.toNat) = Int.ofNat b.toNat - Int.ofNat a.toNat :=
      Int.ofNat_sub (le_of_lt h')
    have hcast : (Int.ofNat a.toNat - Int.ofNat b.toNat) = -(Int.ofNat (b.toNat - a.toNat)) := by
      rw [hsub]; ring
    have hd : b.toNat - a.toNat ≠ 0 := Nat.sub_ne_zero_of_lt h'
    have hb : b.toNat < UInt256.size := b.val.isLt
    have hwm : EVM.wordModulus = UInt256.size := rfl
    have hlt' : b.toNat - a.toNat < EVM.wordModulus := by rw [hwm]; omega
    have hneg : Int.ofNat a.toNat - Int.ofNat b.toNat < 0 := by
      have hlt : Int.ofNat a.toNat < Int.ofNat b.toNat := Int.ofNat_lt.mpr h'
      linarith
    apply u256_inj
    rw [usub_toNat_underflow h', EVM.wordOfInt, if_pos hneg, hcast]
    simp only [Int.natAbs_neg, Int.natAbs_ofNat', Nat.mod_eq_of_lt hlt', if_neg hd]
    show (EVM.uintN 256 (EVM.wordModulus - (b.toNat - a.toNat))).val
      = UInt256.size + a.toNat - b.toNat
    show (EVM.wordModulus - (b.toNat - a.toNat)) % EVM.twoPow 256
      = UInt256.size + a.toNat - b.toNat
    rw [hwm, show EVM.twoPow 256 = UInt256.size from rfl, Nat.mod_eq_of_lt (by omega)]
    omega

/-! ### Store lookups -/

theorem tfStore_get_balanceOf (I : ExecutionEnv) : (tfStore I).get? "balanceOf" = none := by
  unfold tfStore
  rw [store_get_ne _ _ (by decide +native), store_get_ne _ _ (by decide +native),
    store_get_ne _ _ (by decide +native)]
  simp

theorem tfStore_get_allowance (I : ExecutionEnv) : (tfStore I).get? "allowance" = none := by
  unfold tfStore
  rw [store_get_ne _ _ (by decide +native), store_get_ne _ _ (by decide +native),
    store_get_ne _ _ (by decide +native)]
  simp

theorem tfStore_get_src (I : ExecutionEnv) : (tfStore I).get? "src" = some (tfSrcVal I) := by
  unfold tfStore
  rw [store_get_ne _ _ (by decide +native), store_get_ne _ _ (by decide +native)]
  simp

theorem tfStore_get_wad (I : ExecutionEnv) : (tfStore I).get? "wad" = some (tfWadVal I) := by
  unfold tfStore; simp

theorem tfStore_index_src (I : ExecutionEnv) : (tfStore I)["src"] = tfSrcVal I := by
  unfold tfStore; simp [Std.HashMap.getElem_insert]

theorem tfStore_index_dst (I : ExecutionEnv) : (tfStore I)["dst"] = tfDstVal I := by
  unfold tfStore; simp [Std.HashMap.getElem_insert]

/-! ### `storageLoad`/`storageStore` bridges and post-state intermediate maps -/

/-- `storageLoad` at `evm`'s own code owner reads `solcSlotWord` over `evm.accountMap`. -/
theorem tf_load_slot (evm : EVM.State) (I : ExecutionEnv) (slot : UInt256)
    (hco : evm.executionEnv.codeOwner = I.codeOwner) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot =
      solcSlotWord evm.accountMap I slot := by
  rw [hco]
  simp [solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Ethereum.Account.lookupStorage]

/-- `storageStore` leaves `executionEnv` untouched. -/
theorem tf_execEnv (evm : EVM.State) (a : AccountAddress) (s v : UInt256) :
    (Solm.EVM.storageStore evm a s v).executionEnv = evm.executionEnv := by
  simp [Solm.EVM.storageStore, State.lookupAccount, State.setAccount]
  cases evm.accountMap.find? a <;> rfl

/-- Intermediate map after `allowance[src][caller] -= wad`. -/
def tfAllowSt (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (wtfAllowSlot I (tfSrcMasked I))
    (UInt256.sub (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (wtfAllowSlot I (tfSrcMasked I))) (tfWadWord I))

/-- Intermediate map after `balanceOf[src] -= wad`. -/
def tfSrcSt (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (wtfBalSlot (tfSrcMasked I))
    (UInt256.sub (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (wtfBalSlot (tfSrcMasked I))) (tfWadWord I))

/-- Intermediate map after `balanceOf[dst] += wad`. -/
def tfDstSt (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (wtfBalSlot (tfDstMasked I))
    (UInt256.add (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (wtfBalSlot (tfDstMasked I))) (tfWadWord I))

theorem tfAllowSt_co (evm : EVM.State) (I : ExecutionEnv) :
    (tfAllowSt evm I).executionEnv.codeOwner = evm.executionEnv.codeOwner := by
  unfold tfAllowSt; rw [tf_execEnv]

theorem tfSrcSt_co (evm : EVM.State) (I : ExecutionEnv) :
    (tfSrcSt evm I).executionEnv.codeOwner = evm.executionEnv.codeOwner := by
  unfold tfSrcSt; rw [tf_execEnv]

theorem tfAllowSt_accountMap (evm : EVM.State) (I : ExecutionEnv)
    (hco : evm.executionEnv.codeOwner = I.codeOwner) :
    (tfAllowSt evm I).accountMap = sstoreAccountMap I.codeOwner evm.accountMap
      (wtfAllowSlot I (tfSrcMasked I))
      (UInt256.sub (solcSlotWord evm.accountMap I (wtfAllowSlot I (tfSrcMasked I)))
        (tfWadWord I)) := by
  unfold tfAllowSt
  rw [storageStore_accountMap, tf_load_slot evm I _ hco, hco]

theorem tfSrcSt_accountMap (evm : EVM.State) (I : ExecutionEnv)
    (hco : evm.executionEnv.codeOwner = I.codeOwner) :
    (tfSrcSt evm I).accountMap = wtfSrcDebitedMap I evm.accountMap (tfSrcMasked I) (tfWadWord I) := by
  unfold tfSrcSt wtfSrcDebitedMap
  rw [storageStore_accountMap, tf_load_slot evm I _ hco, hco]

theorem tfDstSt_accountMap (evm : EVM.State) (I : ExecutionEnv)
    (hco : evm.executionEnv.codeOwner = I.codeOwner) :
    (tfDstSt evm I).accountMap = sstoreAccountMap I.codeOwner evm.accountMap
      (wtfBalSlot (tfDstMasked I))
      (UInt256.add (tfWadWord I) (solcSlotWord evm.accountMap I (wtfBalSlot (tfDstMasked I)))) := by
  unfold tfDstSt
  rw [storageStore_accountMap, tf_load_slot evm I _ hco, hco]
  exact congrArg (sstoreAccountMap I.codeOwner evm.accountMap (wtfBalSlot (tfDstMasked I)))
    (u256_add_comm _ _)

theorem tfAllowSt_created (evm : EVM.State) (I : ExecutionEnv) :
    (tfAllowSt evm I).createdAccounts = evm.createdAccounts := by
  unfold tfAllowSt; rw [storageStore_createdAccounts]

theorem tfSrcSt_created (evm : EVM.State) (I : ExecutionEnv) :
    (tfSrcSt evm I).createdAccounts = evm.createdAccounts := by
  unfold tfSrcSt; rw [storageStore_createdAccounts]

theorem tfDstSt_created (evm : EVM.State) (I : ExecutionEnv) :
    (tfDstSt evm I).createdAccounts = evm.createdAccounts := by
  unfold tfDstSt; rw [storageStore_createdAccounts]

/-- Skip-case post-state accountMap: `balanceOf[src] -= wad; balanceOf[dst] += wad`. -/
theorem tfSkip_accountMap {cA gh bl σ σ₀ A I} {g : Sat256} :
    (tfDstSt (tfSrcSt (initState cA gh bl σ σ₀ g A I) I) I).accountMap =
      wtfPostMap I σ (tfSrcMasked I) (tfDstMasked I) (tfWadWord I) := by
  have hco0 : (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner = I.codeOwner := rfl
  have hcoS : (tfSrcSt (initState cA gh bl σ σ₀ g A I) I).executionEnv.codeOwner = I.codeOwner := by
    rw [tfSrcSt_co, hco0]
  rw [tfDstSt_accountMap _ I hcoS, tfSrcSt_accountMap _ I hco0]
  rfl

theorem tfSkip_created {cA gh bl σ σ₀ A I} {g : Sat256} :
    (tfDstSt (tfSrcSt (initState cA gh bl σ σ₀ g A I) I) I).createdAccounts =
      (initState cA gh bl σ σ₀ g A I).createdAccounts := by
  rw [tfDstSt_created, tfSrcSt_created]

/-- Spend-case post-state accountMap: allowance debit then `balanceOf` src/dst. -/
theorem tfSpend_accountMap {cA gh bl σ σ₀ A I} {g : Sat256} :
    (tfDstSt (tfSrcSt (tfAllowSt (initState cA gh bl σ σ₀ g A I) I) I) I).accountMap =
      wtfPostMap I (tfAllowDebitMap I σ) (tfSrcMasked I) (tfDstMasked I) (tfWadWord I) := by
  have hco0 : (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner = I.codeOwner := rfl
  have hcoA : (tfAllowSt (initState cA gh bl σ σ₀ g A I) I).executionEnv.codeOwner = I.codeOwner := by
    rw [tfAllowSt_co, hco0]
  have hcoS :
      (tfSrcSt (tfAllowSt (initState cA gh bl σ σ₀ g A I) I) I).executionEnv.codeOwner =
        I.codeOwner := by rw [tfSrcSt_co, hcoA]
  have hMA :
      (tfAllowSt (initState cA gh bl σ σ₀ g A I) I).accountMap = tfAllowDebitMap I σ := by
    rw [tfAllowSt_accountMap _ I hco0]; rfl
  rw [tfDstSt_accountMap _ I hcoS, tfSrcSt_accountMap _ I hcoA, hMA]
  rfl

theorem tfSpend_created {cA gh bl σ σ₀ A I} {g : Sat256} :
    (tfDstSt (tfSrcSt (tfAllowSt (initState cA gh bl σ σ₀ g A I) I) I) I).createdAccounts =
      (initState cA gh bl σ σ₀ g A I).createdAccounts := by
  rw [tfDstSt_created, tfSrcSt_created, tfAllowSt_created]

/-! ### Source-level reads -/

theorem tfEvalSrc (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tfStore I } evm (.var "src") =
      .ok (tfSrcVal I) := by
  simp only [evalExpr?, EvalResult.ofOption]; rw [tfStore_get_src]

theorem tfEvalWad (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tfStore I } evm (.var "wad") =
      .ok (tfWadVal I) := by
  simp only [evalExpr?, EvalResult.ofOption]; rw [tfStore_get_wad]

theorem tfEvalSrcBal (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tfStore I } evm
      (.storage (balanceOfRef (.var "src"))) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wtfBalSlot (tfSrcMasked I))).toNat)) := by
  refine evalExpr_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := tfStore I }) (slot := balanceOfRef (.var "src"))
    (er := { base := "balanceOf",
             steps := [.mindex (.address (AccountAddress.ofNat (tfSrcWord I).toNat))] })
    (t := .int uint256Int)
    (loc := wordLoc (balanceOfSlot (.address (AccountAddress.ofNat (tfSrcWord I).toNat))))
    (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (wtfBalSlot (tfSrcMasked I))).toNat))
    (hbase := tfStore_get_balanceOf I) ?_ ?_ (by rfl) ?_
  · simp [evalStorageRef, evalStorageRefStep, balanceOfRef, tfSrcVal, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, tfStore_index_src]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · rw [show wordLoc (balanceOfSlot (.address (AccountAddress.ofNat (tfSrcWord I).toNat)))
        = uint256Loc (balanceOfSlot (.address (AccountAddress.ofNat (tfSrcWord I).toNat))) from rfl,
      storageLocLoad_uint256, tfBalSrcSlot_eq]

theorem tfEvalDstBal (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tfStore I } evm
      (.storage (balanceOfRef (.var "dst"))) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wtfBalSlot (tfDstMasked I))).toNat)) := by
  refine evalExpr_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := tfStore I }) (slot := balanceOfRef (.var "dst"))
    (er := { base := "balanceOf",
             steps := [.mindex (.address (AccountAddress.ofNat (tfDstWord I).toNat))] })
    (t := .int uint256Int)
    (loc := wordLoc (balanceOfSlot (.address (AccountAddress.ofNat (tfDstWord I).toNat))))
    (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (wtfBalSlot (tfDstMasked I))).toNat))
    (hbase := tfStore_get_balanceOf I) ?_ ?_ (by rfl) ?_
  · simp [evalStorageRef, evalStorageRefStep, balanceOfRef, tfDstVal, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, tfStore_index_dst]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · rw [show wordLoc (balanceOfSlot (.address (AccountAddress.ofNat (tfDstWord I).toNat)))
        = uint256Loc (balanceOfSlot (.address (AccountAddress.ofNat (tfDstWord I).toNat))) from rfl,
      storageLocLoad_uint256, tfBalDstSlot_eq]

theorem tfEvalAllow (evm : EVM.State) (I : ExecutionEnv) (hsrc : evm.executionEnv = I) :
    evalExpr? config { contract := contract, locals := tfStore I } evm
      (.storage (allowanceRef (.var "src") sender)) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wtfAllowSlot I (tfSrcMasked I))).toNat)) := by
  refine evalExpr_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := tfStore I })
    (slot := allowanceRef (.var "src") sender)
    (er := { base := "allowance",
             steps := [.mindex (.address (AccountAddress.ofNat (tfSrcWord I).toNat)),
                       .mindex (.address I.source)] })
    (t := .int uint256Int)
    (loc := wordLoc (allowanceSlot (.address (AccountAddress.ofNat (tfSrcWord I).toNat))
      (.address I.source)))
    (value := .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (wtfAllowSlot I (tfSrcMasked I))).toNat))
    (hbase := tfStore_get_allowance I) ?_ ?_ (by rfl) ?_
  · simp [evalStorageRef, evalStorageRefStep, allowanceRef, sender, envValue, hsrc, tfSrcVal,
      valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, tfStore_index_src]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · rw [show wordLoc (allowanceSlot (.address (AccountAddress.ofNat (tfSrcWord I).toNat))
          (.address I.source))
        = uint256Loc (allowanceSlot (.address (AccountAddress.ofNat (tfSrcWord I).toNat))
          (.address I.source)) from rfl,
      storageLocLoad_uint256, tfAllowSlot_eq]

/-! ### Require / condition evaluations -/

theorem tfEvalSrcBalGe_true (evm : EVM.State) (I : ExecutionEnv)
    (henough : (tfWadWord I).toNat ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (wtfBalSlot (tfSrcMasked I))).toNat) :
    evalExpr? config { contract := contract, locals := tfStore I } evm
      (.binary .ge (.storage (balanceOfRef (.var "src"))) (.var "wad")) = .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [tfEvalSrcBal, tfEvalWad]
  simp [EvalResult.bind, bind, evalBinaryOp?]
  omega

theorem tfEvalSrcBalGe_false (evm : EVM.State) (I : ExecutionEnv)
    (hlt : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (wtfBalSlot (tfSrcMasked I))).toNat < (tfWadWord I).toNat) :
    evalExpr? config { contract := contract, locals := tfStore I } evm
      (.binary .ge (.storage (balanceOfRef (.var "src"))) (.var "wad")) = .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [tfEvalSrcBal, tfEvalWad]
  simp [EvalResult.bind, bind, evalBinaryOp?]
  omega

theorem tfEvalSrcNeSender_true (evm : EVM.State) (I : ExecutionEnv)
    (hne : AccountAddress.ofNat (tfSrcWord I).toNat ≠ evm.executionEnv.source) :
    evalExpr? config { contract := contract, locals := tfStore I } evm
      (.binary .ne (.var "src") sender) = .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [tfEvalSrc]
  simp [EvalResult.bind, bind, evalExpr?, evalBinaryOp?, sender, envValue, tfSrcVal, hne]

theorem tfEvalSrcNeSender_false (evm : EVM.State) (I : ExecutionEnv)
    (heq : AccountAddress.ofNat (tfSrcWord I).toNat = evm.executionEnv.source) :
    evalExpr? config { contract := contract, locals := tfStore I } evm
      (.binary .ne (.var "src") sender) = .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [tfEvalSrc]
  simp [EvalResult.bind, bind, evalExpr?, evalBinaryOp?, sender, envValue, tfSrcVal, heq]

theorem tfEvalAllowNeMax_true (evm : EVM.State) (I : ExecutionEnv) (hsrc : evm.executionEnv = I)
    (hnotMax : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (wtfAllowSlot I (tfSrcMasked I))).toNat ≠ UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := tfStore I } evm
      (.binary .ne (.storage (allowanceRef (.var "src") sender)) (.intLit maxUint256)) =
      .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [tfEvalAllow evm I hsrc]
  rw [show evalExpr? config { contract := contract, locals := tfStore I } evm (.intLit maxUint256)
      = .ok (.int maxUint256) by simp only [evalExpr?, pure]]
  simp [EvalResult.bind, bind, evalBinaryOp?, maxUint256]
  intro h
  apply hnotMax
  apply Int.ofNat.inj
  have hmaxInt : Int.ofNat (UInt256.size - 1) =
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 : Int) := by
    norm_num [UInt256.size]
  rw [hmaxInt]; exact h

theorem tfEvalAllowNeMax_false (evm : EVM.State) (I : ExecutionEnv) (hsrc : evm.executionEnv = I)
    (hmax : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (wtfAllowSlot I (tfSrcMasked I))).toNat = UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := tfStore I } evm
      (.binary .ne (.storage (allowanceRef (.var "src") sender)) (.intLit maxUint256)) =
      .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [tfEvalAllow evm I hsrc]
  rw [show evalExpr? config { contract := contract, locals := tfStore I } evm (.intLit maxUint256)
      = .ok (.int maxUint256) by simp only [evalExpr?, pure]]
  simp [EvalResult.bind, bind, evalBinaryOp?, maxUint256, UInt256.size, hmax]

theorem tfEvalCond_skipSender (evm : EVM.State) (I : ExecutionEnv)
    (heq : AccountAddress.ofNat (tfSrcWord I).toNat = evm.executionEnv.source) :
    evalExpr? config { contract := contract, locals := tfStore I } evm
      (.binary .and (.binary .ne (.var "src") sender)
        (.binary .ne (.storage (allowanceRef (.var "src") sender)) (.intLit maxUint256))) =
      .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [tfEvalSrcNeSender_false evm I heq]
  simp only [EvalResult.bind, bind, pure]

theorem tfEvalCond_skipMax (evm : EVM.State) (I : ExecutionEnv) (hsrc : evm.executionEnv = I)
    (hne : AccountAddress.ofNat (tfSrcWord I).toNat ≠ evm.executionEnv.source)
    (hmax : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (wtfAllowSlot I (tfSrcMasked I))).toNat = UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := tfStore I } evm
      (.binary .and (.binary .ne (.var "src") sender)
        (.binary .ne (.storage (allowanceRef (.var "src") sender)) (.intLit maxUint256))) =
      .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [tfEvalSrcNeSender_true evm I hne]
  simp only [EvalResult.bind, bind]
  rw [tfEvalAllowNeMax_false evm I hsrc hmax]
  rfl

theorem tfEvalCond_spend (evm : EVM.State) (I : ExecutionEnv) (hsrc : evm.executionEnv = I)
    (hne : AccountAddress.ofNat (tfSrcWord I).toNat ≠ evm.executionEnv.source)
    (hnotMax : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (wtfAllowSlot I (tfSrcMasked I))).toNat ≠ UInt256.size - 1) :
    evalExpr? config { contract := contract, locals := tfStore I } evm
      (.binary .and (.binary .ne (.var "src") sender)
        (.binary .ne (.storage (allowanceRef (.var "src") sender)) (.intLit maxUint256))) =
      .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [tfEvalSrcNeSender_true evm I hne]
  simp only [EvalResult.bind, bind]
  rw [tfEvalAllowNeMax_true evm I hsrc hnotMax]
  rfl

theorem tfEvalAllowGeWad_true (evm : EVM.State) (I : ExecutionEnv) (hsrc : evm.executionEnv = I)
    (hle : (tfWadWord I).toNat ≤ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (wtfAllowSlot I (tfSrcMasked I))).toNat) :
    evalExpr? config { contract := contract, locals := tfStore I } evm
      (.binary .ge (.storage (allowanceRef (.var "src") sender)) (.var "wad")) =
      .ok (.bool true) := by
  conv_lhs => unfold evalExpr?
  rw [tfEvalAllow evm I hsrc, tfEvalWad]
  simp [EvalResult.bind, bind, evalBinaryOp?]
  omega

theorem tfEvalAllowGeWad_false (evm : EVM.State) (I : ExecutionEnv) (hsrc : evm.executionEnv = I)
    (hlt : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (wtfAllowSlot I (tfSrcMasked I))).toNat < (tfWadWord I).toNat) :
    evalExpr? config { contract := contract, locals := tfStore I } evm
      (.binary .ge (.storage (allowanceRef (.var "src") sender)) (.var "wad")) =
      .ok (.bool false) := by
  conv_lhs => unfold evalExpr?
  rw [tfEvalAllow evm I hsrc, tfEvalWad]
  simp [EvalResult.bind, bind, evalBinaryOp?]
  omega

/-! ### Unchecked arithmetic RHS reads and storage assigns -/

theorem tfEvalSrcSubRaw (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tfStore I } evm
      (.binary .sub (.storage (balanceOfRef (.var "src"))) (.var "wad")) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wtfBalSlot (tfSrcMasked I))).toNat - Int.ofNat (tfWadWord I).toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [tfEvalSrcBal, tfEvalWad]
  simp [EvalResult.bind, bind, evalBinaryOp?]

theorem tfEvalDstAddRaw (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tfStore I } evm
      (.binary .add (.storage (balanceOfRef (.var "dst"))) (.var "wad")) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wtfBalSlot (tfDstMasked I))).toNat + Int.ofNat (tfWadWord I).toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [tfEvalDstBal, tfEvalWad]
  simp [EvalResult.bind, bind, evalBinaryOp?]

theorem tfEvalAllowSubRaw (evm : EVM.State) (I : ExecutionEnv) (hsrc : evm.executionEnv = I) :
    evalExpr? config { contract := contract, locals := tfStore I } evm
      (.binary .sub (.storage (allowanceRef (.var "src") sender)) (.var "wad")) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wtfAllowSlot I (tfSrcMasked I))).toNat - Int.ofNat (tfWadWord I).toNat)) := by
  conv_lhs => unfold evalExpr?
  rw [tfEvalAllow evm I hsrc, tfEvalWad]
  simp [EvalResult.bind, bind, evalBinaryOp?]

theorem tfAssignSrc (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := tfStore I } evm
      .storage (balanceOfRef (.var "src"))
      (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wtfBalSlot (tfSrcMasked I))).toNat - Int.ofNat (tfWadWord I).toNat)) =
      .ok ({ contract := contract, locals := tfStore I }, tfSrcSt evm I) := by
  refine assignStorageRef_storage_scalar_value
    (er := { base := "balanceOf",
             steps := [.mindex (.address (AccountAddress.ofNat (tfSrcWord I).toNat))] })
    (ty := uint256St)
    (loc := wordLoc (balanceOfSlot (.address (AccountAddress.ofNat (tfSrcWord I).toNat))))
    (hbase := tfStore_get_balanceOf I) ?_ ?_ (by rfl) (by trivial) ?_
  · simp [evalStorageRef, evalStorageRefStep, balanceOfRef, tfSrcVal, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, tfStore_index_src]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · unfold tfSrcSt
    rw [show wordLoc (balanceOfSlot (.address (AccountAddress.ofNat (tfSrcWord I).toNat)))
        = uint256Loc (balanceOfSlot (.address (AccountAddress.ofNat (tfSrcWord I).toNat))) from rfl,
      storageLocStore_uint256_int, tfBalSrcSlot_eq, tf_wordOfInt_sub]

theorem tfAssignDst (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := tfStore I } evm
      .storage (balanceOfRef (.var "dst"))
      (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wtfBalSlot (tfDstMasked I))).toNat + Int.ofNat (tfWadWord I).toNat)) =
      .ok ({ contract := contract, locals := tfStore I }, tfDstSt evm I) := by
  refine assignStorageRef_storage_scalar_value
    (er := { base := "balanceOf",
             steps := [.mindex (.address (AccountAddress.ofNat (tfDstWord I).toNat))] })
    (ty := uint256St)
    (loc := wordLoc (balanceOfSlot (.address (AccountAddress.ofNat (tfDstWord I).toNat))))
    (hbase := tfStore_get_balanceOf I) ?_ ?_ (by rfl) (by trivial) ?_
  · simp [evalStorageRef, evalStorageRefStep, balanceOfRef, tfDstVal, valueToKey?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, tfStore_index_dst]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · unfold tfDstSt
    rw [show wordLoc (balanceOfSlot (.address (AccountAddress.ofNat (tfDstWord I).toNat)))
        = uint256Loc (balanceOfSlot (.address (AccountAddress.ofNat (tfDstWord I).toNat))) from rfl,
      storageLocStore_uint256_int, tfBalDstSlot_eq, wordOfInt_add_words]

theorem tfAssignAllow (evm : EVM.State) (I : ExecutionEnv) (hsrc : evm.executionEnv = I) :
    assignStorageRef? config { contract := contract, locals := tfStore I } evm
      .storage (allowanceRef (.var "src") sender)
      (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wtfAllowSlot I (tfSrcMasked I))).toNat - Int.ofNat (tfWadWord I).toNat)) =
      .ok ({ contract := contract, locals := tfStore I }, tfAllowSt evm I) := by
  refine assignStorageRef_storage_scalar_value
    (er := { base := "allowance",
             steps := [.mindex (.address (AccountAddress.ofNat (tfSrcWord I).toNat)),
                       .mindex (.address I.source)] })
    (ty := uint256St)
    (loc := wordLoc (allowanceSlot (.address (AccountAddress.ofNat (tfSrcWord I).toNat))
      (.address I.source)))
    (hbase := tfStore_get_allowance I) ?_ ?_ (by rfl) (by trivial) ?_
  · simp [evalStorageRef, evalStorageRefStep, allowanceRef, sender, envValue, hsrc, tfSrcVal,
      valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, tfStore_index_src]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
  · unfold tfAllowSt
    rw [show wordLoc (allowanceSlot (.address (AccountAddress.ofNat (tfSrcWord I).toNat))
          (.address I.source))
        = uint256Loc (allowanceSlot (.address (AccountAddress.ofNat (tfSrcWord I).toNat))
          (.address I.source)) from rfl,
      storageLocStore_uint256_int, tfAllowSlot_eq, tf_wordOfInt_sub]

/-- Body, case `src == msg.sender`: the `&&` short-circuits, no allowance spend. -/
theorem weth9TFSolmSkipSender {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsrcCaller : AccountAddress.ofNat (tfSrcWord I).toNat = I.source)
    (henough : (tfWadWord I).toNat ≤ (tfBalSrcWord I σ).toNat) :
    ∃ evmPost cs, ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tfStore I)
      transferFromTransition.body (.returned cs evmPost (some [.bool true]))
      ∧ evmPost.accountMap = wtfPostMap I σ (tfSrcMasked I) (tfDstMasked I) (tfWadWord I)
      ∧ evmPost.createdAccounts = (initState cA gh bl σ σ₀ g A I).createdAccounts := by
  have hsrc : (initState cA gh bl σ σ₀ g A I).executionEnv = I := rfl
  have hco : (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner = I.codeOwner := rfl
  have hwv' : (initState cA gh bl σ σ₀ g A I).executionEnv.weiValue = ⟨0⟩ := by rw [hsrc]; exact hwv
  have hsrcSource : (initState cA gh bl σ σ₀ g A I).executionEnv.source = I.source := by rw [hsrc]
  have hloadSrc : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner (wtfBalSlot (tfSrcMasked I))
      = tfBalSrcWord I σ := by rw [tf_load_slot _ I _ hco]; rfl
  have hbody : ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tfStore I)
      transferFromTransition.body
      (.returned { contract := contract, locals := tfStore I }
        (tfDstSt (tfSrcSt (initState cA gh bl σ σ₀ g A I) I) I) (some [.bool true])) := by
    refine ExecFuncBody.execBlockRet ?_
    simp only [transferFromTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv')) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (tfEvalSrcBalGe_true (initState cA gh bl σ σ₀ g A I) I (by rw [hloadSrc]; exact henough)))
      ?_
    refine ExecBlock.consNormal
      (ExecStmt.iteFalse
        (result := .ok { contract := contract, locals := tfStore I }
          (initState cA gh bl σ σ₀ g A I))
        (tfEvalCond_skipSender (initState cA gh bl σ σ₀ g A I) I
          (by rw [hsrcSource]; exact hsrcCaller))
        ExecBlock.nil) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (tfEvalSrcSubRaw _ I) (tfAssignSrc _ I)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (tfEvalDstAddRaw _ I) (tfAssignDst _ I)) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by simp [evalExpr?, pure])))
  exact ⟨_, _, hbody, tfSkip_accountMap, tfSkip_created⟩

/-- Body, case `src ≠ msg.sender ∧ allowance == uint(-1)`: no allowance spend. -/
theorem weth9TFSolmSkipMax {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsrcNe : AccountAddress.ofNat (tfSrcWord I).toNat ≠ I.source)
    (hmax : (tfAllowWord I σ).toNat = UInt256.size - 1)
    (henough : (tfWadWord I).toNat ≤ (tfBalSrcWord I σ).toNat) :
    ∃ evmPost cs, ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tfStore I)
      transferFromTransition.body (.returned cs evmPost (some [.bool true]))
      ∧ evmPost.accountMap = wtfPostMap I σ (tfSrcMasked I) (tfDstMasked I) (tfWadWord I)
      ∧ evmPost.createdAccounts = (initState cA gh bl σ σ₀ g A I).createdAccounts := by
  have hsrc : (initState cA gh bl σ σ₀ g A I).executionEnv = I := rfl
  have hco : (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner = I.codeOwner := rfl
  have hwv' : (initState cA gh bl σ σ₀ g A I).executionEnv.weiValue = ⟨0⟩ := by rw [hsrc]; exact hwv
  have hsrcSource : (initState cA gh bl σ σ₀ g A I).executionEnv.source = I.source := by rw [hsrc]
  have hloadSrc : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner (wtfBalSlot (tfSrcMasked I))
      = tfBalSrcWord I σ := by rw [tf_load_slot _ I _ hco]; rfl
  have hloadAllow : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner (wtfAllowSlot I (tfSrcMasked I))
      = tfAllowWord I σ := by rw [tf_load_slot _ I _ hco]; rfl
  have hbody : ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tfStore I)
      transferFromTransition.body
      (.returned { contract := contract, locals := tfStore I }
        (tfDstSt (tfSrcSt (initState cA gh bl σ σ₀ g A I) I) I) (some [.bool true])) := by
    refine ExecFuncBody.execBlockRet ?_
    simp only [transferFromTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv')) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (tfEvalSrcBalGe_true (initState cA gh bl σ σ₀ g A I) I (by rw [hloadSrc]; exact henough)))
      ?_
    refine ExecBlock.consNormal
      (ExecStmt.iteFalse
        (result := .ok { contract := contract, locals := tfStore I }
          (initState cA gh bl σ σ₀ g A I))
        (tfEvalCond_skipMax (initState cA gh bl σ σ₀ g A I) I hsrc
          (by rw [hsrcSource]; exact hsrcNe) (by rw [hloadAllow]; exact hmax))
        ExecBlock.nil) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (tfEvalSrcSubRaw _ I) (tfAssignSrc _ I)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (tfEvalDstAddRaw _ I) (tfAssignDst _ I)) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by simp [evalExpr?, pure])))
  exact ⟨_, _, hbody, tfSkip_accountMap, tfSkip_created⟩

/-- Body, case `src ≠ msg.sender ∧ allowance ≠ uint(-1) ∧ allowance ≥ wad`: spend the allowance. -/
theorem weth9TFSolmSpend {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsrcNe : AccountAddress.ofNat (tfSrcWord I).toNat ≠ I.source)
    (hnotMax : (tfAllowWord I σ).toNat ≠ UInt256.size - 1)
    (hallowEnough : (tfWadWord I).toNat ≤ (tfAllowWord I σ).toNat)
    (henough : (tfWadWord I).toNat ≤ (tfBalSrcWord I σ).toNat) :
    ∃ evmPost cs, ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tfStore I)
      transferFromTransition.body (.returned cs evmPost (some [.bool true]))
      ∧ evmPost.accountMap
          = wtfPostMap I (tfAllowDebitMap I σ) (tfSrcMasked I) (tfDstMasked I) (tfWadWord I)
      ∧ evmPost.createdAccounts = (initState cA gh bl σ σ₀ g A I).createdAccounts := by
  have hsrc : (initState cA gh bl σ σ₀ g A I).executionEnv = I := rfl
  have hco : (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner = I.codeOwner := rfl
  have hwv' : (initState cA gh bl σ σ₀ g A I).executionEnv.weiValue = ⟨0⟩ := by rw [hsrc]; exact hwv
  have hsrcSource : (initState cA gh bl σ σ₀ g A I).executionEnv.source = I.source := by rw [hsrc]
  have hloadSrc : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner (wtfBalSlot (tfSrcMasked I))
      = tfBalSrcWord I σ := by rw [tf_load_slot _ I _ hco]; rfl
  have hloadAllow : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner (wtfAllowSlot I (tfSrcMasked I))
      = tfAllowWord I σ := by rw [tf_load_slot _ I _ hco]; rfl
  have hbody : ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tfStore I)
      transferFromTransition.body
      (.returned { contract := contract, locals := tfStore I }
        (tfDstSt (tfSrcSt (tfAllowSt (initState cA gh bl σ σ₀ g A I) I) I) I) (some [.bool true])) := by
    refine ExecFuncBody.execBlockRet ?_
    simp only [transferFromTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv')) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue
        (tfEvalSrcBalGe_true (initState cA gh bl σ σ₀ g A I) I (by rw [hloadSrc]; exact henough)))
      ?_
    refine ExecBlock.consNormal
      (ExecStmt.iteTrue
        (result := .ok { contract := contract, locals := tfStore I }
          (tfAllowSt (initState cA gh bl σ σ₀ g A I) I))
        (tfEvalCond_spend (initState cA gh bl σ σ₀ g A I) I hsrc
          (by rw [hsrcSource]; exact hsrcNe) (by rw [hloadAllow]; exact hnotMax))
        ?_) ?_
    · refine ExecBlock.consNormal
        (ExecStmt.requireTrue
          (tfEvalAllowGeWad_true (initState cA gh bl σ σ₀ g A I) I hsrc
            (by rw [hloadAllow]; exact hallowEnough))) ?_
      refine ExecBlock.consNormal
        (ExecStmt.assign (tfEvalAllowSubRaw (initState cA gh bl σ σ₀ g A I) I hsrc)
          (tfAssignAllow (initState cA gh bl σ σ₀ g A I) I hsrc)) ?_
      exact ExecBlock.nil
    · refine ExecBlock.consNormal
        (ExecStmt.assign (tfEvalSrcSubRaw _ I) (tfAssignSrc _ I)) ?_
      refine ExecBlock.consNormal
        (ExecStmt.assign (tfEvalDstAddRaw _ I) (tfAssignDst _ I)) ?_
      exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by simp [evalExpr?, pure])))
  exact ⟨_, _, hbody, tfSpend_accountMap, tfSpend_created⟩

/-- Body, revert case `balanceOf[src] < wad`. -/
theorem weth9TFSolmRevBal {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlt : (tfBalSrcWord I σ).toNat < (tfWadWord I).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tfStore I)
      transferFromTransition.body .reverted := by
  have hsrc : (initState cA gh bl σ σ₀ g A I).executionEnv = I := rfl
  have hco : (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner = I.codeOwner := rfl
  have hwv' : (initState cA gh bl σ σ₀ g A I).executionEnv.weiValue = ⟨0⟩ := by rw [hsrc]; exact hwv
  have hloadSrc : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner (wtfBalSlot (tfSrcMasked I))
      = tfBalSrcWord I σ := by rw [tf_load_slot _ I _ hco]; rfl
  refine ExecFuncBody.execBlockRevert ?_
  simp only [transferFromTransition, nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv')) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (tfEvalSrcBalGe_false (initState cA gh bl σ σ₀ g A I) I (by rw [hloadSrc]; exact hlt)))

/-- Body, revert case `src ≠ msg.sender ∧ allowance ≠ uint(-1) ∧ allowance < wad`. -/
theorem weth9TFSolmRevAllow {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsrcNe : AccountAddress.ofNat (tfSrcWord I).toNat ≠ I.source)
    (hnotMax : (tfAllowWord I σ).toNat ≠ UInt256.size - 1)
    (henough : (tfWadWord I).toNat ≤ (tfBalSrcWord I σ).toNat)
    (hallowLt : (tfAllowWord I σ).toNat < (tfWadWord I).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tfStore I)
      transferFromTransition.body .reverted := by
  have hsrc : (initState cA gh bl σ σ₀ g A I).executionEnv = I := rfl
  have hco : (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner = I.codeOwner := rfl
  have hwv' : (initState cA gh bl σ σ₀ g A I).executionEnv.weiValue = ⟨0⟩ := by rw [hsrc]; exact hwv
  have hsrcSource : (initState cA gh bl σ σ₀ g A I).executionEnv.source = I.source := by rw [hsrc]
  have hloadSrc : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner (wtfBalSlot (tfSrcMasked I))
      = tfBalSrcWord I σ := by rw [tf_load_slot _ I _ hco]; rfl
  have hloadAllow : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner (wtfAllowSlot I (tfSrcMasked I))
      = tfAllowWord I σ := by rw [tf_load_slot _ I _ hco]; rfl
  refine ExecFuncBody.execBlockRevert ?_
  simp only [transferFromTransition, nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv')) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (tfEvalSrcBalGe_true (initState cA gh bl σ σ₀ g A I) I (by rw [hloadSrc]; exact henough)))
    ?_
  exact ExecBlock.consRevert
    (ExecStmt.iteTrue (result := .reverted)
      (tfEvalCond_spend (initState cA gh bl σ σ₀ g A I) I hsrc
        (by rw [hsrcSource]; exact hsrcNe) (by rw [hloadAllow]; exact hnotMax))
      (ExecBlock.consRevert
        (ExecStmt.requireFalse
          (tfEvalAllowGeWad_false (initState cA gh bl σ σ₀ g A I) I hsrc
            (by rw [hloadAllow]; exact hallowLt)))))

end Benchmarks.WETH9
