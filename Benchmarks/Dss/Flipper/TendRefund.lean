import Benchmarks.Dss.Flipper.TendSameCaller

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## Caller-changing refund branch for `tend(uint256,uint256,uint256)` -/

abbrev tendAfterRefundMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (bidPackedSlotOfWord (tendId I))
    (setAddressOffset0Word
      (flipperSlotWord (bidPackedSlotOfWord (tendId I)) σ I)
      (solcSourceWord I))

abbrev tendRefundMoveArgValsOf (evm : EVM.State) (I : ExecutionEnv) : List Value :=
  [.address evm.executionEnv.source,
    .address
      (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (bidPackedSlotOfWord (tendId I)))
          solcAddrMask).toNat),
    .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidBaseOfWord (tendId I))).toNat)]

abbrev tendLocalsAfterRefund (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (tendLocalsBidOneBegBid σ I).insert "_refundRet" (collapseReturns [])

abbrev tendLocalsAfterRefundPay (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (tendLocalsAfterRefund σ I).insert "_payRet" (collapseReturns [])

abbrev tendLocalsAfterRefundWithTicFrom (σpre σtic : AccountMap) (I : ExecutionEnv) : Store :=
  (tendLocalsAfterRefundPay σpre I).insert "tic_"
    (.int (Int.ofNat (tendTicNewWord σtic I).toNat))

theorem tend_storageStore_sigma0 (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).σ₀ = evm.σ₀ := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount, Account.updateStorage]

theorem tend_storageStore_totalGasUsedInBlock (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).totalGasUsedInBlock =
      evm.totalGasUsedInBlock := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount, Account.updateStorage]

theorem tend_storageStore_transactionReceipts (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).transactionReceipts =
      evm.transactionReceipts := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount, Account.updateStorage]

theorem tend_storageStore_machineState (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).machineState = evm.machineState := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount, Account.updateStorage]

theorem tend_storageStore_blocks (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).blocks = evm.blocks := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount, Account.updateStorage]

theorem tend_storageStore_genesisBlockHeader (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).genesisBlockHeader =
      evm.genesisBlockHeader := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount, Account.updateStorage]

theorem evalExpr_tendCallerNeGuy_true {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcaller : solcSourceWord I ≠ bidGuyWord (tendId I) σ I) :
    evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) =
        .ok (.bool true) := by
  have hsender :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ g A I) sender = .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, initState]
    rfl
  have hguy := evalExpr_bidGuy_of_get_id (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (locals := tendLocalsBidOneBegBid σ I) (id := tendId I)
    (tendLocalsBidOneBegBid_get_id σ I) (tendLocalsBidOneBegBid_get_bids σ I)
  have haddr : I.source ≠ AccountAddress.ofNat (bidGuyWord (tendId I) σ I).toNat := by
    intro hbad
    have hmask := keyValueToWord_address_ofNat_mask (bidGuyWord (tendId I) σ I)
    rw [← hbad] at hmask
    have hsourceKey :
        keyValueToWord (.address I.source) = solcSourceWord I := by
      simp [keyValueToWord_address, solcSourceWord]
    rw [hsourceKey] at hmask
    have hclean :
        UInt256.land solcAddrMask (bidGuyWord (tendId I) σ I) =
          bidGuyWord (tendId I) σ I := by
      simpa [bidGuyWord, flipperAddressReturnWord, u256_land_comm] using
        (solcAddrMask_clean
          (solcAddrMask_result_canonical
            (flipperSlotWord (bidPackedSlotOfWord (tendId I)) σ I)))
    exact hcaller (by simpa [hclean] using hmask)
  simp [evalExpr?, EvalResult.bind, bind, hsender, hguy, evalBinaryOp?, haddr]

theorem evalExprs_tendRefundMoveArgs_ofLocals {evm : EVM.State} {locals : Store}
    {I : ExecutionEnv}
    (hid : locals.get? "id" = some (.int (Int.ofNat (tendId I).toNat)))
    (hbids : locals.get? "bids" = none) :
    evalExprs? config { contract := contract, locals := locals } evm
      [sender, .storage (bidsF (.var "id") "guy"),
        .storage (bidsF (.var "id") "bid")] =
        .ok (tendRefundMoveArgValsOf evm I) := by
  have hguy := evalExpr_bidGuy_of_get_id_evm (evm := evm)
    (locals := locals) (id := tendId I) hid hbids
  have hbid := evalExpr_bidBid_of_get_id_evm (evm := evm)
    (locals := locals) (id := tendId I) hid hbids
  simp only [evalExprs?, evalExpr?, envValue, sender, hguy, hbid, tendRefundMoveArgValsOf,
    EvalResult.bind, bind, pure]

theorem tendLocalsAfterRefund_get_id (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsAfterRefund σ I).get? "id" =
      some (.int (Int.ofNat (tendId I).toNat)) := by
  rw [tendLocalsAfterRefund, store_get_ne _ _ (by decide)]
  exact tendLocalsBidOneBegBid_get_id σ I

theorem tendLocalsAfterRefund_get_bid (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsAfterRefund σ I).get? "bid" =
      some (.int (Int.ofNat (tendBid I).toNat)) := by
  rw [tendLocalsAfterRefund, store_get_ne _ _ (by decide)]
  exact tendLocalsBidOneBegBid_get_bid σ I

theorem tendLocalsAfterRefund_get_bids (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsAfterRefund σ I).get? "bids" = none := by
  rw [tendLocalsAfterRefund, store_get_ne _ _ (by decide)]
  exact tendLocalsBidOneBegBid_get_bids σ I

theorem tendLocalsAfterRefund_get_vat (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsAfterRefund σ I).get? "vat" = none := by
  rw [tendLocalsAfterRefund, store_get_ne _ _ (by decide)]
  exact tendLocalsBidOneBegBid_get_vat σ I

theorem tendLocalsAfterRefund_get_ttl (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsAfterRefund σ I).get? "ttl" = none := by
  rw [tendLocalsAfterRefund, store_get_ne _ _ (by decide)]
  exact tendLocalsBidOneBegBid_get_ttl σ I

theorem tendLocalsAfterRefundPay_get_id (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsAfterRefundPay σ I).get? "id" =
      some (.int (Int.ofNat (tendId I).toNat)) := by
  rw [tendLocalsAfterRefundPay, store_get_ne _ _ (by decide)]
  exact tendLocalsAfterRefund_get_id σ I

theorem tendLocalsAfterRefundPay_get_bid (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsAfterRefundPay σ I).get? "bid" =
      some (.int (Int.ofNat (tendBid I).toNat)) := by
  rw [tendLocalsAfterRefundPay, store_get_ne _ _ (by decide)]
  exact tendLocalsAfterRefund_get_bid σ I

theorem tendLocalsAfterRefundPay_get_bids (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsAfterRefundPay σ I).get? "bids" = none := by
  rw [tendLocalsAfterRefundPay, store_get_ne _ _ (by decide)]
  exact tendLocalsAfterRefund_get_bids σ I

theorem tendLocalsAfterRefundPay_get_vat (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsAfterRefundPay σ I).get? "vat" = none := by
  rw [tendLocalsAfterRefundPay, store_get_ne _ _ (by decide)]
  exact tendLocalsAfterRefund_get_vat σ I

theorem tendLocalsAfterRefundPay_get_ttl (σ : AccountMap) (I : ExecutionEnv) :
    (tendLocalsAfterRefundPay σ I).get? "ttl" = none := by
  rw [tendLocalsAfterRefundPay, store_get_ne _ _ (by decide)]
  exact tendLocalsAfterRefund_get_ttl σ I

theorem tendLocalsAfterRefundWithTicFrom_get_id (σpre σtic : AccountMap)
    (I : ExecutionEnv) :
    (tendLocalsAfterRefundWithTicFrom σpre σtic I).get? "id" =
      some (.int (Int.ofNat (tendId I).toNat)) := by
  rw [tendLocalsAfterRefundWithTicFrom, store_get_ne _ _ (by decide)]
  exact tendLocalsAfterRefundPay_get_id σpre I

theorem tendLocalsAfterRefundWithTicFrom_get_bids (σpre σtic : AccountMap)
    (I : ExecutionEnv) :
    (tendLocalsAfterRefundWithTicFrom σpre σtic I).get? "bids" = none := by
  rw [tendLocalsAfterRefundWithTicFrom, store_get_ne _ _ (by decide)]
  exact tendLocalsAfterRefundPay_get_bids σpre I

theorem tendLocalsAfterRefundWithTicFrom_get_ttl (σpre σtic : AccountMap)
    (I : ExecutionEnv) :
    (tendLocalsAfterRefundWithTicFrom σpre σtic I).get? "ttl" = none := by
  rw [tendLocalsAfterRefundWithTicFrom, store_get_ne _ _ (by decide)]
  exact tendLocalsAfterRefundPay_get_ttl σpre I

theorem tendLocalsAfterRefundWithTicFrom_get_tic (σpre σtic : AccountMap)
    (I : ExecutionEnv) :
    (tendLocalsAfterRefundWithTicFrom σpre σtic I).get? "tic_" =
      some (.int (Int.ofNat (tendTicNewWord σtic I).toNat)) := by
  rw [tendLocalsAfterRefundWithTicFrom, store_get_self]

theorem evalExpr_tendAfterRefundTicNewGeNow_true_from {evm : EVM.State}
    {σpre σtic : AccountMap} {I : ExecutionEnv}
    (hts : evm.executionEnv.header.timestamp = I.header.timestamp)
    (hfit : (tendNow48 I).toNat + (tendTtlWord σtic I).toNat < 2 ^ 48) :
    evalExpr? config
      { contract := contract, locals := tendLocalsAfterRefundWithTicFrom σpre σtic I }
      evm (.binary .ge (.var "tic_") now48) = .ok (.bool true) := by
  have htic := evalExpr_varUInt256
    (evm := evm) (locals := tendLocalsAfterRefundWithTicFrom σpre σtic I)
    (name := "tic_") (value := tendTicNewWord σtic I)
    (tendLocalsAfterRefundWithTicFrom_get_tic σpre σtic I)
  have hnow := evalExpr_tendNow48
    (evm := evm) (locals := tendLocalsAfterRefundWithTicFrom σpre σtic I) (I := I) hts
  have hle : (tendNow48 I).toNat ≤ (tendTicNewWord σtic I).toNat :=
    tendTicNewWord_ge_now48_noOverflow hfit
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [htic, hnow]
  simp [evalBinaryOp?, hle]
  all_goals decide

theorem evalExpr_tendAfterRefundTicVarWithTicFrom {evm : EVM.State}
    {σpre σtic : AccountMap} {I : ExecutionEnv} :
    evalExpr? config
      { contract := contract, locals := tendLocalsAfterRefundWithTicFrom σpre σtic I }
      evm (.var "tic_") = .ok (.int (Int.ofNat (tendTicNewWord σtic I).toNat)) := by
  exact evalExpr_varUInt256 (evm := evm)
    (locals := tendLocalsAfterRefundWithTicFrom σpre σtic I)
    (name := "tic_") (value := tendTicNewWord σtic I)
    (tendLocalsAfterRefundWithTicFrom_get_tic σpre σtic I)

theorem flipperTendSourceBlockAfterRefundSuccessTail {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmRefund : EVM.State} {outRefund : ByteArray}
    {r : ExecResult}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (hfitBid : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size)
    (hinc :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .ge (.var "bidOne") (.var "begBid"))
          (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
          .ok (.bool true))
    (hcaller : solcSourceWord I ≠ bidGuyWord (tendId I) σ I)
    (hvatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallRefund :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (tendRefundMoveArgValsOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I)
        (true, evmRefund, outRefund) true)
    (htail :
      let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (tendId I))
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
            (bidPackedSlotOfWord (tendId I)))
          (solcSourceWord evmRefund.executionEnv))
      ExecBlock config { contract := contract, locals := tendLocalsAfterRefund σ I } evmGuy
        tendAfterIncreasePayTailStmts r) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
      (bidPackedSlotOfWord (tendId I))
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
          (bidPackedSlotOfWord (tendId I)))
        (solcSourceWord evmRefund.executionEnv))
    ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body r := by
  intro locals evm0 evmGuy
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_tendGuyNeZero_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hguy
  have hmulBid :
      evalExpr? config { contract := contract, locals := locals } evm0
        (mul256 (.var "bid") (.intLit ONE)) =
          .ok (.int (Int.ofNat (tendBidOneWord I).toNat)) := by
    dsimp [locals, evm0]
    exact evalExpr_tendBidOneMul_ok (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBid
  have hreqBid :
      evalExpr? config { contract := contract, locals := tendLocalsBidOne I } evm0
        (.binary .or
          (.binary .eq (.intLit ONE) (.intLit 0))
          (.binary .eq (.binary .div (.var "bidOne") (.intLit ONE)) (.var "bid"))) =
          .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_tendBidOneRequire_ok (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBid
  have hmulBeg :
      evalExpr? config { contract := contract, locals := tendLocalsBidOne I } evm0
        (mul256 (.storage begRef) (.storage (bidsF (.var "id") "bid"))) =
          .ok (.int (Int.ofNat (tendBegBidWord σ I).toNat)) := by
    dsimp [evm0]
    exact evalExpr_tendBegBidMul_ok (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBeg
  have hreqBeg :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.binary .or
          (.binary .eq (.storage (bidsF (.var "id") "bid")) (.intLit 0))
          (.binary .eq (.binary .div (.var "begBid")
            (.storage (bidsF (.var "id") "bid"))) (.storage begRef))) =
          .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_tendBegBidRequire_ok (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBeg
  have hcallerTrue :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) =
          .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_tendCallerNeGuy_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hcaller
  have hvat :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.storage vatRef) = .ok (.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (tendLocalsBidOneBegBid_get_vat σ I)
  have hguardRefund :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    apply evalExpr_flipperVatCodeGuard_true_ofLocals hvat
    simpa [evm0, initState] using hvatCode
  have hargsRefund :
      evalExprs? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        [sender, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "bid")] =
          .ok (tendRefundMoveArgValsOf evm0 I) := by
    exact evalExprs_tendRefundMoveArgs_ofLocals
      (tendLocalsBidOneBegBid_get_id σ I) (tendLocalsBidOneBegBid_get_bids σ I)
  have hcallRefund' :
      typedCallViaEVM config evm0
        (EVM.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) "move" 0
        (tendRefundMoveArgValsOf evm0 I) (true, evmRefund, outRefund) true := by
    simpa [evm0, initState] using hcallRefund
  have hdecRefund : config.externalABI.decode? "move" outRefund = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hrefundBlock :
      ExecBlock config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_refundRet")
        (.ok { contract := contract, locals := tendLocalsAfterRefund σ I } evmRefund) := by
    simpa [checkedExternalCallStmts, tendLocalsAfterRefund] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evm0)
        (evm' := evmRefund) (locals := tendLocalsBidOneBegBid σ I)
        (receiver := .storage vatRef) (retVar := "_refundRet") (name := "move")
        (target := flipperVatAddress evm0.accountMap evm0.executionEnv) (sendVal := 0)
        (args := [sender, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "bid")])
        (argVals := tendRefundMoveArgValsOf evm0 I) (out := outRefund) (perm := true)
        (value := []) hguardRefund hvat hargsRefund hcallRefund' hdecRefund
  have hsender :
      evalExpr? config { contract := contract, locals := tendLocalsAfterRefund σ I }
        evmRefund sender = .ok (.address evmRefund.executionEnv.source) := by
    simp [sender, evalExpr?, envValue]
    rfl
  have hassignGuy :
      assignStorageRef? config { contract := contract, locals := tendLocalsAfterRefund σ I }
        evmRefund .storage (bidsF (.var "id") "guy")
        (.address evmRefund.executionEnv.source) =
          .ok ({ contract := contract, locals := tendLocalsAfterRefund σ I }, evmGuy) := by
    simpa [evmGuy] using
      assign_bidGuyStorage evmRefund (tendId I)
        (tendLocalsAfterRefund_get_id σ I) (tendLocalsAfterRefund_get_bids σ I)
  have hassignBlock :
      ExecBlock config { contract := contract, locals := tendLocalsAfterRefund σ I }
        evmRefund [ .assign .storage (bidsF (.var "id") "guy") sender ]
        (.ok { contract := contract, locals := tendLocalsAfterRefund σ I } evmGuy) := by
    exact ExecBlock.consNormal (ExecStmt.assign hsender hassignGuy) ExecBlock.nil
  have hthen :
      ExecBlock config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_refundRet" ++
        [ .assign .storage (bidsF (.var "id") "guy") sender ])
        (.ok { contract := contract, locals := tendLocalsAfterRefund σ I } evmGuy) := by
    exact execBlock_append hrefundBlock hassignBlock
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hticGuard)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hendGuard)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hlotGuard)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using htabGuard)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hbidGuard)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hmulBid) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqBid) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hmulBeg) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreqBeg) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hinc) ?_
  refine ExecBlock.consNormal (ExecStmt.iteTrue hcallerTrue hthen) ?_
  simpa [tendAfterIncreasePayTailStmts] using htail

theorem flipperTendSourceBodyRefundBranchRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (hfitBid : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size)
    (hinc :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .ge (.var "bidOne") (.var "begBid"))
          (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
          .ok (.bool true))
    (hcaller : solcSourceWord I ≠ bidGuyWord (tendId I) σ I)
    (hbranch :
      ExecBlock config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_refundRet" ++
        [ .assign .storage (bidsF (.var "id") "guy") sender ])
        .reverted) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
  intro locals evm0
  have hguyGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .ne (.storage (bidsF (.var "id") "guy")) zeroAddr) =
          .ok (.bool true) := by
    simpa [locals, evm0] using
      evalExpr_tendGuyNeZero_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hguy
  have hmulBid :
      evalExpr? config { contract := contract, locals := locals } evm0
        (mul256 (.var "bid") (.intLit ONE)) =
          .ok (.int (Int.ofNat (tendBidOneWord I).toNat)) := by
    dsimp [locals, evm0]
    exact evalExpr_tendBidOneMul_ok (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBid
  have hreqBid :
      evalExpr? config { contract := contract, locals := tendLocalsBidOne I } evm0
        (.binary .or
          (.binary .eq (.intLit ONE) (.intLit 0))
          (.binary .eq (.binary .div (.var "bidOne") (.intLit ONE)) (.var "bid"))) =
          .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_tendBidOneRequire_ok (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBid
  have hmulBeg :
      evalExpr? config { contract := contract, locals := tendLocalsBidOne I } evm0
        (mul256 (.storage begRef) (.storage (bidsF (.var "id") "bid"))) =
          .ok (.int (Int.ofNat (tendBegBidWord σ I).toNat)) := by
    dsimp [evm0]
    exact evalExpr_tendBegBidMul_ok (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBeg
  have hreqBeg :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.binary .or
          (.binary .eq (.storage (bidsF (.var "id") "bid")) (.intLit 0))
          (.binary .eq (.binary .div (.var "begBid")
            (.storage (bidsF (.var "id") "bid"))) (.storage begRef))) =
          .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_tendBegBidRequire_ok (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hfitBeg
  have hcallerTrue :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.binary .ne sender (.storage (bidsF (.var "id") "guy"))) =
          .ok (.bool true) := by
    simpa [evm0] using
      evalExpr_tendCallerNeGuy_true (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) hcaller
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguyGuard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hticGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hendGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hlotGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using htabGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue (by simpa [locals, evm0] using hbidGuard)) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hmulBid) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqBid) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl hmulBeg) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqBeg) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hinc) ?_
    exact ExecBlock.consRevert (ExecStmt.iteTrue hcallerTrue hbranch)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperTendSourceBodyRefundNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (hfitBid : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size)
    (hinc :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .ge (.var "bidOne") (.var "begBid"))
          (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
          .ok (.bool true))
    (hcaller : solcSourceWord I ≠ bidGuyWord (tendId I) σ I)
    (hvatNoCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
  intro locals evm0
  have hvat :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.storage vatRef) = .ok (.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (tendLocalsBidOneBegBid_get_vat σ I)
  have hguardRefund :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) := by
    apply evalExpr_flipperVatCodeGuard_false_ofLocals hvat
    simpa [evm0, initState] using hvatNoCode
  have hrefundBlock :
      ExecBlock config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_refundRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallNoCode (cfg := config) (C := contract) (evm := evm0)
        (locals := tendLocalsBidOneBegBid σ I) (receiver := .storage vatRef)
        (retVar := "_refundRet") (name := "move") (sendVal := 0)
        (args := [sender, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "bid")])
        hguardRefund
  have hbranch :
      ExecBlock config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_refundRet" ++
        [ .assign .storage (bidsF (.var "id") "guy") sender ])
        .reverted := by
    exact execBlock_append_term (s2 := [ .assign .storage (bidsF (.var "id") "guy") sender ])
      hrefundBlock (by intro f' e' h; cases h)
  simpa [locals, evm0] using
    (flipperTendSourceBodyRefundBranchRevert (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hguy hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid hfitBeg hinc
      hcaller hbranch)

theorem flipperTendSourceBodyRefundCallFailure {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmRefund : EVM.State} {outRefund : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (hfitBid : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size)
    (hinc :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .ge (.var "bidOne") (.var "begBid"))
          (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
          .ok (.bool true))
    (hcaller : solcSourceWord I ≠ bidGuyWord (tendId I) σ I)
    (hvatCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallRefund :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (tendRefundMoveArgValsOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I)
        (false, evmRefund, outRefund) true) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
  intro locals evm0
  have hvat :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.storage vatRef) = .ok (.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (tendLocalsBidOneBegBid_get_vat σ I)
  have hguardRefund :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    apply evalExpr_flipperVatCodeGuard_true_ofLocals hvat
    simpa [evm0, initState] using hvatCode
  have hargsRefund :
      evalExprs? config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        [sender, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "bid")] =
          .ok (tendRefundMoveArgValsOf evm0 I) := by
    exact evalExprs_tendRefundMoveArgs_ofLocals
      (tendLocalsBidOneBegBid_get_id σ I) (tendLocalsBidOneBegBid_get_bids σ I)
  have hcallRefund' :
      typedCallViaEVM config evm0
        (EVM.address (flipperVatAddress evm0.accountMap evm0.executionEnv)) "move" 0
        (tendRefundMoveArgValsOf evm0 I) (false, evmRefund, outRefund) true := by
    simpa [evm0, initState] using hcallRefund
  have hrefundBlock :
      ExecBlock config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_refundRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure (cfg := config) (C := contract) (evm := evm0)
        (evm' := evmRefund) (locals := tendLocalsBidOneBegBid σ I)
        (receiver := .storage vatRef) (retVar := "_refundRet") (name := "move")
        (target := flipperVatAddress evm0.accountMap evm0.executionEnv) (sendVal := 0)
        (args := [sender, .storage (bidsF (.var "id") "guy"),
          .storage (bidsF (.var "id") "bid")])
        (argVals := tendRefundMoveArgValsOf evm0 I) (out := outRefund) (perm := true)
        hguardRefund hvat hargsRefund hcallRefund'
  have hbranch :
      ExecBlock config { contract := contract, locals := tendLocalsBidOneBegBid σ I } evm0
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "guy"),
            .storage (bidsF (.var "id") "bid")] "_refundRet" ++
        [ .assign .storage (bidsF (.var "id") "guy") sender ])
        .reverted := by
    exact execBlock_append_term (s2 := [ .assign .storage (bidsF (.var "id") "guy") sender ])
      hrefundBlock (by intro f' e' h; cases h)
  simpa [locals, evm0] using
    (flipperTendSourceBodyRefundBranchRevert (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hwv hguy hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid hfitBeg hinc
      hcaller hbranch)

theorem flipperTendSourceBodyPayNoCodeAfterRefund {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmRefund : EVM.State} {outRefund : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (hfitBid : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size)
    (hinc :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .ge (.var "bidOne") (.var "begBid"))
          (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
          .ok (.bool true))
    (hcaller : solcSourceWord I ≠ bidGuyWord (tendId I) σ I)
    (hrefundCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallRefund :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (tendRefundMoveArgValsOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I)
        (true, evmRefund, outRefund) true)
    (hpayNoCode :
      let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (tendId I))
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
            (bidPackedSlotOfWord (tendId I)))
          (solcSourceWord evmRefund.executionEnv))
      (UInt256.ofNat
        ((evmGuy.lookupAccount
          (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)).option
          0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
  intro locals evm0
  let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
    (bidPackedSlotOfWord (tendId I))
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (tendId I)))
      (solcSourceWord evmRefund.executionEnv))
  have hvat :
      evalExpr? config { contract := contract, locals := tendLocalsAfterRefund σ I }
        evmGuy (.storage vatRef) =
          .ok (.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (tendLocalsAfterRefund_get_vat σ I)
  have hguardPay :
      evalExpr? config { contract := contract, locals := tendLocalsAfterRefund σ I }
        evmGuy (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) := by
    exact evalExpr_flipperVatCodeGuard_false_ofLocals hvat (by simpa [evmGuy] using hpayNoCode)
  have hpayBlock :
      ExecBlock config { contract := contract, locals := tendLocalsAfterRefund σ I } evmGuy
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "gal"),
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallNoCode (cfg := config) (C := contract) (evm := evmGuy)
        (locals := tendLocalsAfterRefund σ I) (receiver := .storage vatRef)
        (retVar := "_payRet") (name := "move") (sendVal := 0)
        (args := [sender, .storage (bidsF (.var "id") "gal"),
          wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))])
        hguardPay
  have htail :
      ExecBlock config { contract := contract, locals := tendLocalsAfterRefund σ I } evmGuy
        tendAfterIncreasePayTailStmts .reverted := by
    exact execBlock_append_term
      (s2 := [ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
        checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
        [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
      hpayBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body
        .reverted := by
    simpa [locals, evm0, evmGuy] using
      (flipperTendSourceBlockAfterRefundSuccessTail (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmRefund := evmRefund) (outRefund := outRefund) hwv hguy hticGuard hendGuard
        hlotGuard htabGuard hbidGuard hfitBid hfitBeg hinc hcaller hrefundCode
        hcallRefund htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperTendSourceBodyPayCallFailureAfterRefund {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmRefund evmPay : EVM.State} {outRefund outPay : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (hfitBid : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size)
    (hinc :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .ge (.var "bidOne") (.var "begBid"))
          (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
          .ok (.bool true))
    (hcaller : solcSourceWord I ≠ bidGuyWord (tendId I) σ I)
    (hrefundCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallRefund :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (tendRefundMoveArgValsOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I)
        (true, evmRefund, outRefund) true)
    (hpayCode :
      let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (tendId I))
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
            (bidPackedSlotOfWord (tendId I)))
          (solcSourceWord evmRefund.executionEnv))
      0 <
        (UInt256.ofNat
          ((evmGuy.lookupAccount
            (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallPay :
      let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (tendId I))
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
            (bidPackedSlotOfWord (tendId I)))
          (solcSourceWord evmRefund.executionEnv))
      typedCallViaEVM config evmGuy
        (EVM.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) "move" 0
        (tendPayMoveArgValsOf evmGuy I) (false, evmPay, outPay) true) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
  intro locals evm0
  let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
    (bidPackedSlotOfWord (tendId I))
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (tendId I)))
      (solcSourceWord evmRefund.executionEnv))
  have hvat :
      evalExpr? config { contract := contract, locals := tendLocalsAfterRefund σ I }
        evmGuy (.storage vatRef) =
          .ok (.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (tendLocalsAfterRefund_get_vat σ I)
  have hguardPay :
      evalExpr? config { contract := contract, locals := tendLocalsAfterRefund σ I }
        evmGuy (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_flipperVatCodeGuard_true_ofLocals hvat (by simpa [evmGuy] using hpayCode)
  have hargsPay :
      evalExprs? config { contract := contract, locals := tendLocalsAfterRefund σ I } evmGuy
        [sender, .storage (bidsF (.var "id") "gal"),
          wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))] =
          .ok (tendPayMoveArgValsOf evmGuy I) := by
    exact evalExprs_tendPayMoveArgs_ofLocals
      (tendLocalsAfterRefund_get_id σ I)
      (tendLocalsAfterRefund_get_bid σ I)
      (tendLocalsAfterRefund_get_bids σ I)
  have hcallPay' :
      typedCallViaEVM config evmGuy
        (EVM.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) "move" 0
        (tendPayMoveArgValsOf evmGuy I) (false, evmPay, outPay) true := by
    simpa [evmGuy] using hcallPay
  have hpayBlock :
      ExecBlock config { contract := contract, locals := tendLocalsAfterRefund σ I } evmGuy
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "gal"),
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet")
        .reverted := by
    simpa [checkedExternalCallStmts] using
      checkedExternalCallFailure (cfg := config) (C := contract) (evm := evmGuy)
        (evm' := evmPay) (locals := tendLocalsAfterRefund σ I)
        (receiver := .storage vatRef) (retVar := "_payRet") (name := "move")
        (target := flipperVatAddress evmGuy.accountMap evmGuy.executionEnv) (sendVal := 0)
        (args := [sender, .storage (bidsF (.var "id") "gal"),
          wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))])
        (argVals := tendPayMoveArgValsOf evmGuy I) (out := outPay) (perm := true)
        hguardPay hvat hargsPay hcallPay'
  have htail :
      ExecBlock config { contract := contract, locals := tendLocalsAfterRefund σ I } evmGuy
        tendAfterIncreasePayTailStmts .reverted := by
    exact execBlock_append_term
      (s2 := [ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
        checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
        [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
      hpayBlock (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body
        .reverted := by
    simpa [locals, evm0, evmGuy] using
      (flipperTendSourceBlockAfterRefundSuccessTail (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmRefund := evmRefund) (outRefund := outRefund) hwv hguy hticGuard hendGuard
        hlotGuard htabGuard hbidGuard hfitBid hfitBeg hinc hcaller hrefundCode
        hcallRefund htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperTendSourceBodySuccessAfterRefund {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmRefund evmPay : EVM.State} {outRefund outPay : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (hfitBid : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size)
    (hinc :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .ge (.var "bidOne") (.var "begBid"))
          (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
          .ok (.bool true))
    (hcaller : solcSourceWord I ≠ bidGuyWord (tendId I) σ I)
    (hrefundCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallRefund :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (tendRefundMoveArgValsOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I)
        (true, evmRefund, outRefund) true)
    (hpayCode :
      let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (tendId I))
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
            (bidPackedSlotOfWord (tendId I)))
          (solcSourceWord evmRefund.executionEnv))
      0 <
        (UInt256.ofNat
          ((evmGuy.lookupAccount
            (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallPay :
      let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (tendId I))
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
            (bidPackedSlotOfWord (tendId I)))
          (solcSourceWord evmRefund.executionEnv))
      typedCallViaEVM config evmGuy
        (EVM.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) "move" 0
        (tendPayMoveArgValsOf evmGuy I) (true, evmPay, outPay) true)
    (hpayTs : evmPay.executionEnv.header.timestamp = I.header.timestamp)
    (hpayOwner : evmPay.executionEnv.codeOwner = I.codeOwner)
    (hfitTic :
      (tendNow48 I).toNat +
          (tendTtlWord
            (Solm.EVM.storageStore evmPay evmPay.executionEnv.codeOwner
              (bidBaseOfWord (tendId I)) (tendBid I)).accountMap I).toNat <
        2 ^ 48) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evmBid := Solm.EVM.storageStore evmPay evmPay.executionEnv.codeOwner
      (bidBaseOfWord (tendId I)) (tendBid I)
    let evmTic := Solm.EVM.storageStore evmBid evmBid.executionEnv.codeOwner
      (bidPackedSlotOfWord (tendId I))
      (setUint48Offset20Word
        (Solm.EVM.storageLoad evmBid evmBid.executionEnv.codeOwner
          (bidPackedSlotOfWord (tendId I)))
        (tendTicNewWord evmBid.accountMap I))
    ExecTransitionBody config contract evm0 locals tendTransition.body
      (.returned
        { contract := contract, locals := tendLocalsAfterRefundWithTicFrom σ evmBid.accountMap I }
        evmTic none) := by
  intro locals evm0 evmBid evmTic
  let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
    (bidPackedSlotOfWord (tendId I))
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (tendId I)))
      (solcSourceWord evmRefund.executionEnv))
  have hvat :
      evalExpr? config { contract := contract, locals := tendLocalsAfterRefund σ I }
        evmGuy (.storage vatRef) =
          .ok (.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (tendLocalsAfterRefund_get_vat σ I)
  have hguardPay :
      evalExpr? config { contract := contract, locals := tendLocalsAfterRefund σ I }
        evmGuy (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_flipperVatCodeGuard_true_ofLocals hvat (by simpa [evmGuy] using hpayCode)
  have hargsPay :
      evalExprs? config { contract := contract, locals := tendLocalsAfterRefund σ I } evmGuy
        [sender, .storage (bidsF (.var "id") "gal"),
          wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))] =
          .ok (tendPayMoveArgValsOf evmGuy I) := by
    exact evalExprs_tendPayMoveArgs_ofLocals
      (tendLocalsAfterRefund_get_id σ I)
      (tendLocalsAfterRefund_get_bid σ I)
      (tendLocalsAfterRefund_get_bids σ I)
  have hcallPay' :
      typedCallViaEVM config evmGuy
        (EVM.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) "move" 0
        (tendPayMoveArgValsOf evmGuy I) (true, evmPay, outPay) true := by
    simpa [evmGuy] using hcallPay
  have hdecPay : config.externalABI.decode? "move" outPay = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hpayBlock :
      ExecBlock config { contract := contract, locals := tendLocalsAfterRefund σ I } evmGuy
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "gal"),
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet")
        (.ok { contract := contract, locals := tendLocalsAfterRefundPay σ I } evmPay) := by
    simpa [checkedExternalCallStmts, tendLocalsAfterRefundPay] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evmGuy)
        (evm' := evmPay) (locals := tendLocalsAfterRefund σ I)
        (receiver := .storage vatRef) (retVar := "_payRet") (name := "move")
        (target := flipperVatAddress evmGuy.accountMap evmGuy.executionEnv) (sendVal := 0)
        (args := [sender, .storage (bidsF (.var "id") "gal"),
          wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))])
        (argVals := tendPayMoveArgValsOf evmGuy I) (out := outPay) (perm := true)
        (value := []) hguardPay hvat hargsPay hcallPay' hdecPay
  have hbidVar :
      evalExpr? config { contract := contract, locals := tendLocalsAfterRefundPay σ I }
        evmPay (.var "bid") = .ok (.int (Int.ofNat (tendBid I).toNat)) := by
    exact evalExpr_varUInt256 (evm := evmPay) (locals := tendLocalsAfterRefundPay σ I)
      (name := "bid") (value := tendBid I) (tendLocalsAfterRefundPay_get_bid σ I)
  have hassignBid :
      assignStorageRef? config { contract := contract, locals := tendLocalsAfterRefundPay σ I }
        evmPay .storage (bidsF (.var "id") "bid")
        (.int (Int.ofNat (tendBid I).toNat)) =
          .ok ({ contract := contract, locals := tendLocalsAfterRefundPay σ I }, evmBid) := by
    simpa [evmBid] using
      assign_bidBidStorage evmPay (tendId I) (tendBid I)
        (tendLocalsAfterRefundPay_get_id σ I) (tendLocalsAfterRefundPay_get_bids σ I)
  have hletTic :
      evalExpr? config { contract := contract, locals := tendLocalsAfterRefundPay σ I }
        evmBid (wrap48 (.binary .add now48 (.storage ttlRef))) =
          .ok (.int (Int.ofNat (tendTicNewWord evmBid.accountMap I).toNat)) := by
    exact evalExpr_tendTicNew (evm := evmBid) (locals := tendLocalsAfterRefundPay σ I)
      (I := I) (tendLocalsAfterRefundPay_get_ttl σ I)
      (by simpa [evmBid, storageStore_executionEnv] using hpayTs)
      (by simpa [evmBid, storageStore_executionEnv] using hpayOwner)
  have hgeTic :
      evalExpr? config
        { contract := contract, locals := tendLocalsAfterRefundWithTicFrom σ evmBid.accountMap I }
        evmBid (.binary .ge (.var "tic_") now48) = .ok (.bool true) := by
    exact evalExpr_tendAfterRefundTicNewGeNow_true_from (evm := evmBid)
      (σpre := σ) (σtic := evmBid.accountMap) (I := I)
      (by simpa [evmBid, storageStore_executionEnv] using hpayTs)
      (by simpa [evmBid] using hfitTic)
  have hticVar :
      evalExpr? config
        { contract := contract, locals := tendLocalsAfterRefundWithTicFrom σ evmBid.accountMap I }
        evmBid (.var "tic_") =
          .ok (.int (Int.ofNat (tendTicNewWord evmBid.accountMap I).toNat)) := by
    exact evalExpr_tendAfterRefundTicVarWithTicFrom (evm := evmBid)
      (σpre := σ) (σtic := evmBid.accountMap) (I := I)
  let solmTic : Frame :=
    { contract := contract, locals := tendLocalsAfterRefundWithTicFrom σ evmBid.accountMap I }
  have hassignTic :
      assignStorageRef? config
          { contract := contract, locals := tendLocalsAfterRefundWithTicFrom σ evmBid.accountMap I }
          evmBid .storage (bidsF (.var "id") "tic")
          (.int (Int.ofNat (tendTicNewWord evmBid.accountMap I).toNat)) =
        .ok (solmTic, evmTic) := by
    simpa [evmTic, solmTic] using
      assign_bidTicStorage evmBid (tendId I) (tendTicNewWord evmBid.accountMap I)
        (tendTicNewWord_bound evmBid.accountMap I)
        (tendLocalsAfterRefundWithTicFrom_get_id σ evmBid.accountMap I)
        (tendLocalsAfterRefundWithTicFrom_get_bids σ evmBid.accountMap I)
  have hpost :
      ExecBlock config { contract := contract, locals := tendLocalsAfterRefundPay σ I }
        evmPay
        ([ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
          checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
        (.ok
          { contract := contract, locals := tendLocalsAfterRefundWithTicFrom σ evmBid.accountMap I }
          evmTic) := by
    refine ExecBlock.consNormal (ExecStmt.assign hbidVar hassignBid) ?_
    simp only [checkedAdd48Into, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.letDecl hletTic) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hgeTic) ?_
    exact ExecBlock.consNormal (ExecStmt.assign hticVar hassignTic) ExecBlock.nil
  have htail :
      ExecBlock config { contract := contract, locals := tendLocalsAfterRefund σ I } evmGuy
        tendAfterIncreasePayTailStmts
        (.ok
          { contract := contract, locals := tendLocalsAfterRefundWithTicFrom σ evmBid.accountMap I }
          evmTic) := by
    have hjoined :
        ExecBlock config { contract := contract, locals := tendLocalsAfterRefund σ I } evmGuy
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [sender, .storage (bidsF (.var "id") "gal"),
              wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
            "_payRet" ++
          ([ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
            checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
            [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ]))
          (.ok
            { contract := contract,
              locals := tendLocalsAfterRefundWithTicFrom σ evmBid.accountMap I }
            evmTic) := by
      exact execBlock_append hpayBlock hpost
    simpa [tendAfterIncreasePayTailStmts, List.append_assoc] using hjoined
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body
        (.ok
          { contract := contract, locals := tendLocalsAfterRefundWithTicFrom σ evmBid.accountMap I }
          evmTic) := by
    simpa [locals, evm0, evmGuy] using
      (flipperTendSourceBlockAfterRefundSuccessTail (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmRefund := evmRefund) (outRefund := outRefund) hwv hguy hticGuard hendGuard
        hlotGuard htabGuard hbidGuard hfitBid hfitBeg hinc hcaller hrefundCode
        hcallRefund htail)
  simpa [ExecTransitionBody, locals, evm0, evmBid, evmTic] using
    ExecFuncBody.execBlockOK hblock

theorem flipperTendSourceBodyAdd48OverflowAfterRefund {cA gh bl σ σ₀ A I}
    {g : UInt256} {evmRefund evmPay : EVM.State} {outRefund outPay : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hguy : bidGuyWord (tendId I) σ I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (hfitBid : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg :
      (tendBegWord σ I).toNat * (bidBidWord (tendId I) σ I).toNat < UInt256.size)
    (hinc :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .ge (.var "bidOne") (.var "begBid"))
          (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
          .ok (.bool true))
    (hcaller : solcSourceWord I ≠ bidGuyWord (tendId I) σ I)
    (hrefundCode :
      0 <
        (UInt256.ofNat
          (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
            (flipperVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallRefund :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (tendRefundMoveArgValsOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) I)
        (true, evmRefund, outRefund) true)
    (hpayCode :
      let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (tendId I))
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
            (bidPackedSlotOfWord (tendId I)))
          (solcSourceWord evmRefund.executionEnv))
      0 <
        (UInt256.ofNat
          ((evmGuy.lookupAccount
            (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)).option
            0 (fun acc => acc.code.size))).toNat)
    (hcallPay :
      let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (tendId I))
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
            (bidPackedSlotOfWord (tendId I)))
          (solcSourceWord evmRefund.executionEnv))
      typedCallViaEVM config evmGuy
        (EVM.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) "move" 0
        (tendPayMoveArgValsOf evmGuy I) (true, evmPay, outPay) true)
    (hpayTs : evmPay.executionEnv.header.timestamp = I.header.timestamp)
    (hpayOwner : evmPay.executionEnv.codeOwner = I.codeOwner)
    (hoverTic :
      2 ^ 48 ≤
        (tendNow48 I).toNat +
          (tendTtlWord
            (Solm.EVM.storageStore evmPay evmPay.executionEnv.codeOwner
              (bidBaseOfWord (tendId I)) (tendBid I)).accountMap I).toNat) :
    let locals := tendLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals tendTransition.body .reverted := by
  intro locals evm0
  let evmGuy := Solm.EVM.storageStore evmRefund evmRefund.executionEnv.codeOwner
    (bidPackedSlotOfWord (tendId I))
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evmRefund evmRefund.executionEnv.codeOwner
        (bidPackedSlotOfWord (tendId I)))
      (solcSourceWord evmRefund.executionEnv))
  let evmBid := Solm.EVM.storageStore evmPay evmPay.executionEnv.codeOwner
    (bidBaseOfWord (tendId I)) (tendBid I)
  have hvat :
      evalExpr? config { contract := contract, locals := tendLocalsAfterRefund σ I }
        evmGuy (.storage vatRef) =
          .ok (.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) := by
    exact evalExpr_flipperStorageVatOfLocals (tendLocalsAfterRefund_get_vat σ I)
  have hguardPay :
      evalExpr? config { contract := contract, locals := tendLocalsAfterRefund σ I }
        evmGuy (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) := by
    exact evalExpr_flipperVatCodeGuard_true_ofLocals hvat (by simpa [evmGuy] using hpayCode)
  have hargsPay :
      evalExprs? config { contract := contract, locals := tendLocalsAfterRefund σ I } evmGuy
        [sender, .storage (bidsF (.var "id") "gal"),
          wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))] =
          .ok (tendPayMoveArgValsOf evmGuy I) := by
    exact evalExprs_tendPayMoveArgs_ofLocals
      (tendLocalsAfterRefund_get_id σ I)
      (tendLocalsAfterRefund_get_bid σ I)
      (tendLocalsAfterRefund_get_bids σ I)
  have hcallPay' :
      typedCallViaEVM config evmGuy
        (EVM.address (flipperVatAddress evmGuy.accountMap evmGuy.executionEnv)) "move" 0
        (tendPayMoveArgValsOf evmGuy I) (true, evmPay, outPay) true := by
    simpa [evmGuy] using hcallPay
  have hdecPay : config.externalABI.decode? "move" outPay = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hpayBlock :
      ExecBlock config { contract := contract, locals := tendLocalsAfterRefund σ I } evmGuy
        (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
          [sender, .storage (bidsF (.var "id") "gal"),
            wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
          "_payRet")
        (.ok { contract := contract, locals := tendLocalsAfterRefundPay σ I } evmPay) := by
    simpa [checkedExternalCallStmts, tendLocalsAfterRefundPay] using
      checkedExternalCallSuccess (cfg := config) (C := contract) (evm := evmGuy)
        (evm' := evmPay) (locals := tendLocalsAfterRefund σ I)
        (receiver := .storage vatRef) (retVar := "_payRet") (name := "move")
        (target := flipperVatAddress evmGuy.accountMap evmGuy.executionEnv) (sendVal := 0)
        (args := [sender, .storage (bidsF (.var "id") "gal"),
          wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))])
        (argVals := tendPayMoveArgValsOf evmGuy I) (out := outPay) (perm := true)
        (value := []) hguardPay hvat hargsPay hcallPay' hdecPay
  have hbidVar :
      evalExpr? config { contract := contract, locals := tendLocalsAfterRefundPay σ I }
        evmPay (.var "bid") = .ok (.int (Int.ofNat (tendBid I).toNat)) := by
    exact evalExpr_varUInt256 (evm := evmPay) (locals := tendLocalsAfterRefundPay σ I)
      (name := "bid") (value := tendBid I) (tendLocalsAfterRefundPay_get_bid σ I)
  have hassignBid :
      assignStorageRef? config { contract := contract, locals := tendLocalsAfterRefundPay σ I }
        evmPay .storage (bidsF (.var "id") "bid")
        (.int (Int.ofNat (tendBid I).toNat)) =
          .ok ({ contract := contract, locals := tendLocalsAfterRefundPay σ I }, evmBid) := by
    simpa [evmBid] using
      assign_bidBidStorage evmPay (tendId I) (tendBid I)
        (tendLocalsAfterRefundPay_get_id σ I) (tendLocalsAfterRefundPay_get_bids σ I)
  have hletTic :
      evalExpr? config { contract := contract, locals := tendLocalsAfterRefundPay σ I }
        evmBid (wrap48 (.binary .add now48 (.storage ttlRef))) =
          .ok (.int (Int.ofNat (tendTicNewWord evmBid.accountMap I).toNat)) := by
    exact evalExpr_tendTicNew (evm := evmBid) (locals := tendLocalsAfterRefundPay σ I)
      (I := I) (tendLocalsAfterRefundPay_get_ttl σ I)
      (by simpa [evmBid, storageStore_executionEnv] using hpayTs)
      (by simpa [evmBid, storageStore_executionEnv] using hpayOwner)
  have hgeTicFalse :
      evalExpr? config
        { contract := contract, locals := tendLocalsAfterRefundWithTicFrom σ evmBid.accountMap I }
        evmBid (.binary .ge (.var "tic_") now48) = .ok (.bool false) := by
    have htic := evalExpr_tendAfterRefundTicVarWithTicFrom (evm := evmBid)
      (σpre := σ) (σtic := evmBid.accountMap) (I := I)
    have hnow := evalExpr_tendNow48
      (evm := evmBid)
      (locals := tendLocalsAfterRefundWithTicFrom σ evmBid.accountMap I) (I := I)
      (by simpa [evmBid, storageStore_executionEnv] using hpayTs)
    have hlt : (tendTicNewWord evmBid.accountMap I).toNat < (tendNow48 I).toNat :=
      tendTicNewWord_lt_now48_overflow (by simpa [evmBid] using hoverTic)
    exact evalExpr_ge_uint256_false htic hnow hlt
  have hpost :
      ExecBlock config { contract := contract, locals := tendLocalsAfterRefundPay σ I }
        evmPay
        ([ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
          checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
          [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ])
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.assign hbidVar hassignBid) ?_
    simp only [checkedAdd48Into, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.letDecl hletTic) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hgeTicFalse)
  have htail :
      ExecBlock config { contract := contract, locals := tendLocalsAfterRefund σ I } evmGuy
        tendAfterIncreasePayTailStmts .reverted := by
    have hjoined :
        ExecBlock config { contract := contract, locals := tendLocalsAfterRefund σ I } evmGuy
          (checkedExternalCallStmts (.storage vatRef) "move" (.intLit 0)
            [sender, .storage (bidsF (.var "id") "gal"),
              wrap256 (.binary .sub (.var "bid") (.storage (bidsF (.var "id") "bid")))]
            "_payRet" ++
          ([ .assign .storage (bidsF (.var "id") "bid") (.var "bid") ] ++
            checkedAdd48Into "tic_" now48 (.storage ttlRef) ++
            [ .assign .storage (bidsF (.var "id") "tic") (.var "tic_") ]))
          .reverted := by
      exact execBlock_append hpayBlock hpost
    simpa [tendAfterIncreasePayTailStmts, List.append_assoc] using hjoined
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 tendTransition.body
        .reverted := by
    simpa [locals, evm0, evmGuy] using
      (flipperTendSourceBlockAfterRefundSuccessTail (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmRefund := evmRefund) (outRefund := outRefund) hwv hguy hticGuard hendGuard
        hlotGuard htabGuard hbidGuard hfitBid hfitBeg hinc hcaller hrefundCode
        hcallRefund htail)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperTendX_takeRefundBranch {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (_hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcaller : solcSourceWord I ≠ bidGuyWord (tendId I) σ I)
    (h : RD flipperBytecode I g s0 ⟨3486⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3520⟩
      [tendBid I, tendLot I, tendId I, ret, sel]
      (twoWordHashMem (tendId I) ⟨1⟩ mem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let memHash := twoWordHashMem (tendId I) ⟨1⟩ mem
  let rawPacked := flipperSlotWord (bidPackedSlotOfWord (tendId I)) σ I
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have rd3504 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tendId I) mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 memHash (UInt256.ofNat 3)
      (by native_decide) mem_cost (by
        dsimp [memHash, twoWordHashMem, wordAt32Mem, wordAt0Mem]
        rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (tendId I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by simpa [memHash, bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (tendId I) hmemSize)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k3505, C3505, rd3505raw⟩ := rd3504.sload (by native_decide) (by evm_ov)
  have rd3505 : RD flipperBytecode I g s0 ⟨3505⟩
      [rawPacked, tendBid I, tendLot I, tendId I, ret, sel]
      memHash (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3505 C3505 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (tendId I) = bidPackedSlotOfWord (tendId I) := by
      simpa [bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [rawPacked, flipperSlotWord, hslotAdd] using rd3505raw
  have rd3516raw := evm_run rd3505 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  obtain ⟨k3516, C3516, rd3516⟩ : ∃ k' C',
      RD flipperBytecode I g s0 ⟨3516⟩
        [UInt256.eq (solcSourceWord I) (bidGuyWord (tendId I) σ I), tendBid I,
          tendLot I, tendId I, ret, sel]
        memHash (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by
      simpa [rawPacked, bidGuyWord, flipperAddressReturnWord, hmask160, u256_land_comm]
        using rd3516raw⟩
  have heq : UInt256.eq (solcSourceWord I) (bidGuyWord (tendId I) σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne hcaller
  rw [heq] at rd3516
  exact ⟨_, _, evm_run rd3516 with [
    raw push2 ⟨3686⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)]⟩

theorem flipperTendX_refundCalldataReady {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD flipperBytecode I g s0 ⟨3520⟩
      [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3587⟩
      (⟨128⟩ :: ⟨64⟩ :: ⟨0⟩ :: flipperSlotWord ⟨2⟩ σ I :: solcAddrMask ::
        tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendVatRefundCallMem mem σ I) (UInt256.ofNat 8) ByteArray.empty
      (cA, σ) k' C' := by
  let rawVat := flipperSlotWord ⟨2⟩ σ I
  let rawPacked := flipperSlotWord (bidPackedSlotOfWord (tendId I)) σ I
  let rawBid := bidBidWord (tendId I) σ I
  let memHash := tendPayHashMem mem I
  let base := solcMappingSlot ⟨1⟩ (tendId I)
  have hhashSize : memHash.size = 96 := by
    dsimp [memHash, tendPayHashMem]
    exact twoWordHashMem_size_96 (tendId I) ⟨1⟩ hmemSize
  have hhashRead64 : memHash.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memHash, tendPayHashMem]
    exact twoWordHashMem_read64 (tendId I) ⟨1⟩ hmemSize hmemRead64
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hguyCleanLeft :
      UInt256.land solcAddrMask rawPacked = bidGuyWord (tendId I) σ I := by
    simpa [rawPacked, bidGuyWord, flipperAddressReturnWord] using
      (u256_land_comm solcAddrMask rawPacked)
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ memHash.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (memHash.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hhashSize]; decide) (by decide) hhashRead64
  have rd3523 := evm_run h with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k3524, C3524, rd3524raw⟩ := rd3523.sload (by native_decide) (by evm_ov)
  have rd3524 : RD flipperBytecode I g s0 ⟨3524⟩
      [rawVat, ⟨2⟩, tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3524 C3524 := by
    simpa [rawVat, flipperSlotWord, solcSlotWord] using rd3524raw
  have rd3542pre := evm_run rd3524 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tendId I) mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 memHash (UInt256.ofNat 3)
      (by native_decide) mem_cost (by
        dsimp [memHash, tendPayHashMem, twoWordHashMem, wordAt32Mem, wordAt0Mem]
        rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw keccak256 0 base (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by simpa [base, memHash, tendPayHashMem, bidBaseOfWord] using
        twoWordHashMem_solcMappingSlot ⟨1⟩ (tendId I) hmemSize)
      (by decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k3543, C3543, rd3543raw⟩ := rd3542pre.sload (by native_decide) (by evm_ov)
  have rd3543 : RD flipperBytecode I g s0 ⟨3543⟩
      (rawPacked :: ⟨64⟩ :: ⟨0⟩ :: rawVat :: base :: tendBid I :: tendLot I ::
        tendId I :: ret :: sel :: [])
      memHash (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3543 C3543 := by
    have hslotAdd :
        base + (⟨2⟩ : UInt256) = bidPackedSlotOfWord (tendId I) := by
      simp [base, bidPackedSlotOfWord, bidBaseOfWord]
    simpa [rawPacked, flipperSlotWord, hslotAdd] using rd3543raw
  have rd3544pre := rd3543.swap4 (by native_decide) (by evm_ov)
  obtain ⟨k3545, C3545, rd3545raw⟩ := rd3544pre.sload (by native_decide) (by evm_ov)
  have rd3545 : RD flipperBytecode I g s0 ⟨3545⟩
      (rawBid :: ⟨64⟩ :: ⟨0⟩ :: rawVat :: rawPacked :: tendBid I ::
        tendLot I :: tendId I :: ret :: sel :: [])
      memHash (UInt256.ofNat 3) ByteArray.empty (cA, σ) k3545 C3545 := by
    simpa [rawBid, bidBidWord, bidBaseOfWord, flipperSlotWord, base] using rd3545raw
  let mem1 := writeWord memHash 128 yankVatMoveSelectorWord
  let mem2 := writeWord mem1 132 (solcSourceWord I)
  let mem3 := writeWord mem2 164 (bidGuyWord (tendId I) σ I)
  have rd3557 := evm_run rd3545 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64Hash (by decide) (by evm_ov),
    raw push4 ⟨3140843579⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 mem1 (UInt256.ofNat 5)
      (by native_decide) mem_cost (by
        dsimp [mem1, yankVatMoveSelectorWord, Reasoning.Theory.writeWord]
        rfl) (by decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 mem2 (UInt256.ofNat 6)
      (by native_decide) mem_cost (by
        dsimp [mem1, mem2, solcSourceWord, Reasoning.Theory.writeWord]
        rfl) (by decide) (by evm_ov)]
  have rd3579 := evm_run rd3557 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 mem3 (UInt256.ofNat 7)
      (by native_decide) mem_cost (by
        rw [hmask160, hguyCleanLeft]
        dsimp [mem2, mem3, Reasoning.Theory.writeWord]
        rfl) (by decide) (by evm_ov)]
  have rd3587 := evm_run rd3579 with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw mstore 3 (tendVatRefundCallMem mem σ I) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by
        dsimp [mem1, mem2, mem3, tendVatRefundCallMem, Reasoning.Theory.writeWord,
          writeCascade]
        rfl) (by decide) (by evm_ov)]
  exact ⟨_, _, by simpa [rawVat] using rd3587⟩

theorem flipperTendX_toRefundExtcodesizeGuard {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcaller : solcSourceWord I ≠ bidGuyWord (tendId I) σ I)
    (h : RD flipperBytecode I g s0 ⟨3486⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3616⟩
      (flipperVatTargetWord σ I :: flipperVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
        flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendVatRefundCallMem (twoWordHashMem (tendId I) ⟨1⟩ mem) σ I)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ) k' C' := by
  let memHash := twoWordHashMem (tendId I) ⟨1⟩ mem
  have hhashSize : memHash.size = 96 := by
    dsimp [memHash]
    exact twoWordHashMem_size_96 (tendId I) ⟨1⟩ hmemSize
  have hhashRead64 : memHash.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memHash]
    exact twoWordHashMem_read64 (tendId I) ⟨1⟩ hmemSize hmemRead64
  let rawVat := flipperSlotWord ⟨2⟩ σ I
  let rawPacked := flipperSlotWord (bidPackedSlotOfWord (tendId I)) σ I
  let rawBid := bidBidWord (tendId I) σ I
  let base := solcMappingSlot ⟨1⟩ (tendId I)
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hvatClean : UInt256.land rawVat solcAddrMask = flipperVatTargetWord σ I := by
    simp [rawVat, flipperVatTargetWord, flipperAddressReturnWord]
  have hguyCleanLeft :
      UInt256.land solcAddrMask rawPacked = bidGuyWord (tendId I) σ I := by
    simpa [rawPacked, bidGuyWord, flipperAddressReturnWord] using
      (u256_land_comm solcAddrMask rawPacked)
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ memHash.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (memHash.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hhashSize]; decide) (by decide) hhashRead64
  have hmload64Refund :
      (if (⟨64⟩ : UInt256).toNat ≥
            (tendVatRefundCallMem memHash σ I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((tendVatRefundCallMem memHash σ I).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [tendVatRefundCallMem_size σ I hhashSize]; decide)
      (by decide) (tendVatRefundCallMem_read64 σ I hhashSize hhashRead64)
  obtain ⟨_, _, rd3520⟩ :=
    flipperTendX_takeRefundBranch hmemSize hmemRead64 hcaller h
  obtain ⟨_, _, rd3587⟩ :=
    flipperTendX_refundCalldataReady hhashSize hhashRead64 rd3520
  have rd3616 := evm_run rd3587 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Refund (by decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 ⟨3140843579⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hsubAdd :
      UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨100⟩ = ⟨100⟩ := by
    native_decide
  have hadd : (⟨128⟩ : UInt256) + ⟨100⟩ = ⟨228⟩ := by
    native_decide
  have hvatClean' :
      UInt256.land (flipperSlotWord ⟨2⟩ σ I) solcAddrMask =
        flipperVatTargetWord σ I := by
    simpa [rawVat] using hvatClean
  rw [hsubAdd, hadd, hvatClean'] at rd3616
  exact ⟨_, _, by simpa using rd3616⟩

theorem flipperTendX_refundNoCode {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcaller : solcSourceWord I ≠ bidGuyWord (tendId I) σ I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨3486⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨_, _, rd3616⟩ := flipperTendX_toRefundExtcodesizeGuard
    hmemSize hmemRead64 hcaller h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨3616⟩) (okPc := ⟨3628⟩) rd3616
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem flipperTendX_toRefundCall {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcaller : solcSourceWord I ≠ bidGuyWord (tendId I) σ I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨3486⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ gasWord k' C', RD flipperBytecode I g s0 ⟨3631⟩
      (gasWord :: flipperVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
        flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendVatRefundCallMem (twoWordHashMem (tendId I) ⟨1⟩ mem) σ I)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd3616⟩ := flipperTendX_toRefundExtcodesizeGuard
    hmemSize hmemRead64 hcaller h
  obtain ⟨gasWord, k3631, C3631, rd3631⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3616⟩) (okPc := ⟨3628⟩) rd3616
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k3631, C3631, by simpa using rd3631⟩

theorem flipperTendX_refundDepthLimit {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcaller : solcSourceWord I ≠ bidGuyWord (tendId I) σ I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = (1024 : Fin 1025))
    (h : RD flipperBytecode I g s0 ⟨3486⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3632⟩
      (⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
        flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendVatRefundCallMem (twoWordHashMem (tendId I) ⟨1⟩ mem) σ I)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨gasWord, _, _, rd3631⟩ :=
    flipperTendX_toRefundCall hmemSize hmemRead64 hcaller hcodeSize h
  obtain ⟨k3632, C3632, rd3632raw⟩ :=
    RD.callDepthLimit rd3631 (by native_decide) hdepth (by evm_ov)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
    native_decide
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    rfl
  have rd3632 : RD flipperBytecode I g s0 ⟨3632⟩
      (⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
        flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (ByteArray.empty.write 0
        (tendVatRefundCallMem (twoWordHashMem (tendId I) ⟨1⟩ mem) σ I) 128
        (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ) k3632 C3632 := by
    simpa using haw ▸ rd3632raw
  rw [hmin, byteArray_write_len_zero] at rd3632
  exact ⟨_, _, rd3632⟩

theorem flipperTendX_refundPostCall
    {cA0 gh bl σbase σ₀ A I} {g : UInt256}
    {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap} {Acur : Substate}
    {k C : ℕ} {ret sel : UInt256} {mem : ByteArray}
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcaller : solcSourceWord I ≠ bidGuyWord (tendId I) σ I)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨3486⟩
      [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨3632⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: ⟨3140843579⟩ ::
          flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
        (tendVatRefundCallMem (twoWordHashMem (tendId I) ⟨1⟩ mem) σ I)
        (UInt256.ofNat 8) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ, substate := Acur, createdAccounts := cA })
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (tendRefundMoveArgValsOf
          ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ, substate := Acur, createdAccounts := cA }) I)
        (z,
          { { initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ, substate := Acur, createdAccounts := cA } with
            accountMap := σ', substate := A', createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd3631⟩ :=
    flipperTendX_toRefundCall hmemSize hmemRead64 hcaller hcodeSize h
  obtain ⟨cA', σ', z, out, A_in, callGas, k3632, C3632, hΘpack, rd3632raw,
      houtsz⟩ :=
    RD.call rd3631 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k3632, C3632, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
      native_decide
    have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      rfl
    have rd3632 : RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨3632⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: ⟨3140843579⟩ ::
          flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
        (out.write 0
          (tendVatRefundCallMem (twoWordHashMem (tendId I) ⟨1⟩ mem) σ I) 128
          (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 8) out (cA', σ') k3632 C3632 :=
      haw ▸ rd3632raw
    rw [hmin, byteArray_write_len_zero] at rd3632
    exact rd3632
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := flipperVatTargetWord σ I)
      (mem := tendVatRefundCallMem (twoWordHashMem (tendId I) ⟨1⟩ mem) σ I)
      (inOff := ⟨128⟩) (inSize := ⟨100⟩)
      (fun hdepthEq => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [initState] using hdepthEq
        exact absurd hdepth (by rw [hEq]; decide))
      (flipperVatEvmAddress_eq_target_of_accountMapEquiv (accountMapEquiv.refl σ))
      ?_ ?_
    · have hhashSize :
          (twoWordHashMem (tendId I) ⟨1⟩ mem).size = 96 :=
        twoWordHashMem_size_96 (tendId I) ⟨1⟩ hmemSize
      simpa [tendRefundMoveArgValsOf, initState, flipperSlotWord, solcSlotWord,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        bidGuyWord, bidPackedSlotOfWord, bidBidWord, bidBaseOfWord,
        flipperAddressReturnWord]
        using tendVatRefundCallMem_encode σ I hhashSize
    · simpa [initState, hperm] using hΘ

theorem flipperTendX_refundCallFailure {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target id ret sel selector bid lot : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨3632⟩
      (⟨0⟩ :: ⟨228⟩ :: selector :: target :: bid :: lot :: id :: ret :: sel :: [])
      mem aw out acc k C)
    (houtsz : out.size < UInt256.size) :
    RDrev flipperBytecode g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨3632⟩) (okPc := ⟨3648⟩) h
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    houtsz (by simp)

theorem flipperTendX_refundCallSuccessToStoreStart {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {aw target id ret sel selector bid lot : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD flipperBytecode I g s0 ⟨3632⟩
      (⟨1⟩ :: ⟨228⟩ :: selector :: target :: bid :: lot :: id :: ret :: sel :: [])
      mem aw out acc k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3652⟩
      (target :: bid :: lot :: id :: ret :: sel :: []) mem aw out acc k' C' := by
  obtain ⟨_, _, rd3649⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨3632⟩) (okPc := ⟨3648⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp)
  have rd3652 := evm_run rd3649 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd3652⟩

theorem flipperTendX_storeRefundGuyToPayStart {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {out mem : ByteArray} {target ret sel : UInt256}
    (hperm : I.perm = true)
    (hmemSize : 64 ≤ mem.size)
    (h : RD flipperBytecode I g s0 ⟨3652⟩
      [target, tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 8) out (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3686⟩
      [tendBid I, tendLot I, tendId I, ret, sel]
      (twoWordHashMem (tendId I) ⟨1⟩ mem) (UInt256.ofNat 8) out
      (cA, tendAfterRefundMap σ I) k' C' := by
  let mem1 := wordAt0Mem (tendId I) mem
  let mem2 := twoWordHashMem (tendId I) ⟨1⟩ mem
  let slot := bidPackedSlotOfWord (tendId I)
  let old := flipperSlotWord slot σ I
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hstoredRaw :
      UInt256.lor (solcSourceWord I)
          (UInt256.land (UInt256.lnot solcAddrMask) old) =
        setAddressOffset0Word old (solcSourceWord I) := by
    have hsourceClean :
        UInt256.land (solcSourceWord I) solcAddrMask = solcSourceWord I :=
      solcAddrMask_clean (solcSourceWord_canonical I)
    calc
      UInt256.lor (solcSourceWord I)
          (UInt256.land (UInt256.lnot solcAddrMask) old) =
          UInt256.lor (UInt256.land (UInt256.lnot solcAddrMask) old)
            (solcSourceWord I) := by
            exact u256_lor_comm _ _
      _ = UInt256.lor (UInt256.land old (UInt256.lnot solcAddrMask))
            (UInt256.land (solcSourceWord I) solcAddrMask) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) old, hsourceClean]
      _ = setAddressOffset0Word old (solcSourceWord I) := by
            rfl
  have rd3669 := evm_run h with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 mem1 (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 mem2 (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw keccak256 0 (bidBaseOfWord (tendId I)) (UInt256.ofNat 8)
      (by native_decide) mem_cost
      (by
        simpa [mem2, bidBaseOfWord] using
          tendTwoWordHashMem_solcMappingSlot_of_size_ge ⟨1⟩ (tendId I) hmemSize)
      (by decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k3671, C3671, rd3671raw⟩ := rd3669.sload (by native_decide) (by evm_ov)
  have rd3671 : RD flipperBytecode I g s0 ⟨3671⟩
      [old, slot, target, tendBid I, tendLot I, tendId I, ret, sel]
      mem2 (UInt256.ofNat 8) out (cA, σ) k3671 C3671 := by
    have hslotAdd :
        (⟨2⟩ : UInt256) + bidBaseOfWord (tendId I) = slot := by
      simpa [slot, bidPackedSlotOfWord] using
        (u256_add_comm (⟨2⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [old, slot, flipperSlotWord, solcSlotWord, hslotAdd] using rd3671raw
  have rd3684 := evm_run rd3671 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  rw [hmask160, hstoredRaw] at rd3684
  obtain ⟨k3685, C3685, rd3685raw⟩ := rd3684.sstore hperm (by native_decide) (by evm_ov)
  have rd3685 : RD flipperBytecode I g s0 ⟨3685⟩
      [target, tendBid I, tendLot I, tendId I, ret, sel]
      mem2 (UInt256.ofNat 8) out (cA, tendAfterRefundMap σ I) k3685 C3685 := by
    simpa [tendAfterRefundMap, old, slot, flipperSlotWord] using rd3685raw
  exact ⟨_, _, evm_run rd3685 with [
    raw pop (by native_decide) (by evm_ov)]⟩

theorem tendPayHashMem_size_228 {mem : ByteArray} (I : ExecutionEnv)
    (hmemSize : mem.size = 228) :
    (tendPayHashMem mem I).size = 228 := by
  unfold tendPayHashMem twoWordHashMem wordAt32Mem wordAt0Mem
  change (writeWord (writeWord mem 0 (tendId I)) 32 (⟨1⟩ : UInt256)).size = 228
  have h0 : (writeWord mem 0 (tendId I)).size = 228 := by
    rw [writeWord_size]
    · rw [hmemSize]; native_decide
    · rw [hmemSize]; native_decide
  rw [writeWord_size]
  · rw [h0]; native_decide
  · rw [h0]; native_decide

theorem tendPayHashMem_read64_228 {mem : ByteArray} (I : ExecutionEnv)
    (hmemSize : mem.size = 228)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (tendPayHashMem mem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold tendPayHashMem twoWordHashMem wordAt32Mem wordAt0Mem
  change (writeWord (writeWord mem 0 (tendId I)) 32 (⟨1⟩ : UInt256)).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩
  have h0size : (writeWord mem 0 (tendId I)).size = 228 := by
    rw [writeWord_size]
    · rw [hmemSize]; native_decide
    · rw [hmemSize]; native_decide
  rw [writeWord_read_preserved]
  · rw [writeWord_read_preserved]
    · exact hmemRead64
    · rw [hmemSize]; native_decide
    · right
      rw [hmemSize]
      constructor <;> omega
  · rw [h0size]; native_decide
  · right
    rw [h0size]
    constructor <;> omega

theorem tendVatPayCallMem_size_228 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 228) :
    (tendVatPayCallMem mem σ I).size = 228 := by
  unfold tendVatPayCallMem
  exact writeCascade_size_of_base (tendPayHashMem mem I)
    [(128, yankVatMoveSelectorWord),
     (132, solcSourceWord I),
     (164, bidGalWord (tendId I) σ I),
     (196, UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I))]
    (tendPayHashMem_size_228 I hmemSize)
    (by simp [WriteGapsOk] <;> native_decide)
    (by norm_num [writeCascadeSize])

theorem tendVatPayCallMem_read64_228 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 228)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (tendVatPayCallMem mem σ I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold tendVatPayCallMem
  rw [writeCascade_read_preserved_of_base (tendPayHashMem mem I)
    [(128, yankVatMoveSelectorWord),
     (132, solcSourceWord I),
     (164, bidGalWord (tendId I) σ I),
     (196, UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I))]
    (tendPayHashMem_size_228 I hmemSize)
    (by simp [WindowDisjointFromWrites] <;> native_decide)]
  exact tendPayHashMem_read64_228 I hmemSize hmemRead64

theorem tendVatPayCallMem_read128_4_228 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 228) :
    (tendVatPayCallMem mem σ I).readWithPadding 128 4 = moveSelector := by
  unfold tendVatPayCallMem
  rw [writeCascade_read_window_of_head (tendPayHashMem mem I) 128 0 4
    yankVatMoveSelectorWord
    [(132, solcSourceWord I),
     (164, bidGalWord (tendId I) σ I),
     (196, UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I))]
    (by rw [tendPayHashMem_size_228 I hmemSize]; native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)
    (by norm_num) (by norm_num) (by norm_num)]
  exact yankVatMoveSelectorWord_prefix

theorem tendVatPayCallMem_read132_228 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 228) :
    (tendVatPayCallMem mem σ I).readWithPadding 132 32 =
      UInt256.toByteArray (solcSourceWord I) := by
  unfold tendVatPayCallMem
  rw [writeCascade_cons]
  have hbase :
      (writeWord (tendPayHashMem mem I) 128 yankVatMoveSelectorWord).size = 228 := by
    rw [writeWord_size]
    · rw [tendPayHashMem_size_228 I hmemSize]; native_decide
    · rw [tendPayHashMem_size_228 I hmemSize]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord (tendPayHashMem mem I) 128 yankVatMoveSelectorWord)
    (base := 228) (off := 132) (word := solcSourceWord I)
    (rest := [(164, bidGalWord (tendId I) σ I),
      (196, UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I))])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem tendVatPayCallMem_read164_228 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 228) :
    (tendVatPayCallMem mem σ I).readWithPadding 164 32 =
      UInt256.toByteArray (bidGalWord (tendId I) σ I) := by
  unfold tendVatPayCallMem
  rw [writeCascade_cons, writeCascade_cons]
  let mem1 := writeWord (tendPayHashMem mem I) 128 yankVatMoveSelectorWord
  have hmem1 : mem1.size = 228 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [tendPayHashMem_size_228 I hmemSize]; native_decide
    · rw [tendPayHashMem_size_228 I hmemSize]; native_decide
  have hbase : (writeWord mem1 132 (solcSourceWord I)).size = 228 := by
    rw [writeWord_size]
    · rw [hmem1]; native_decide
    · rw [hmem1]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem1 132 (solcSourceWord I))
    (base := 228) (off := 164) (word := bidGalWord (tendId I) σ I)
    (rest := [(196, UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I))])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites] <;> native_decide)

theorem tendVatPayCallMem_read196_228 {mem : ByteArray} (σ : AccountMap)
    (I : ExecutionEnv) (hmemSize : mem.size = 228) :
    (tendVatPayCallMem mem σ I).readWithPadding 196 32 =
      UInt256.toByteArray (UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I)) := by
  unfold tendVatPayCallMem
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
  let mem1 := writeWord (tendPayHashMem mem I) 128 yankVatMoveSelectorWord
  let mem2 := writeWord mem1 132 (solcSourceWord I)
  have hmem1 : mem1.size = 228 := by
    dsimp [mem1]
    rw [writeWord_size]
    · rw [tendPayHashMem_size_228 I hmemSize]; native_decide
    · rw [tendPayHashMem_size_228 I hmemSize]; native_decide
  have hmem2 : mem2.size = 228 := by
    dsimp [mem2]
    rw [writeWord_size]
    · rw [hmem1]; native_decide
    · rw [hmem1]; native_decide
  have hbase : (writeWord mem2 164 (bidGalWord (tendId I) σ I)).size = 228 := by
    rw [writeWord_size]
    · rw [hmem2]; native_decide
    · rw [hmem2]; native_decide
  exact writeCascade_read_word_of_head_of_base
    (writeWord mem2 164 (bidGalWord (tendId I) σ I))
    (base := 228) (off := 196)
    (word := UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I))
    (rest := [])
    hbase (by native_decide)
    (by simp [WindowDisjointFromWrites])

theorem tendVatPayCallMem_read_228 {mem : ByteArray} (σ : AccountMap) (I : ExecutionEnv)
    (hmemSize : mem.size = 228) :
    (tendVatPayCallMem mem σ I).readWithPadding 128 100 =
      moveSelector ++
      UInt256.toByteArray (solcSourceWord I) ++
      UInt256.toByteArray (bidGalWord (tendId I) σ I) ++
      UInt256.toByteArray (UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I)) := by
  rw [byteArray_readWithPadding_split (tendVatPayCallMem mem σ I) 128 4 96
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [tendVatPayCallMem_size_228 σ I hmemSize])]
  rw [tendVatPayCallMem_read128_4_228 σ I hmemSize]
  rw [byteArray_readWithPadding_split (tendVatPayCallMem mem σ I) 132 32 64
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [tendVatPayCallMem_size_228 σ I hmemSize])]
  rw [tendVatPayCallMem_read132_228 σ I hmemSize]
  rw [byteArray_readWithPadding_split (tendVatPayCallMem mem σ I) 164 32 32
    (by omega) (by omega) (by norm_num) (by norm_num) (by norm_num)
    (by rw [tendVatPayCallMem_size_228 σ I hmemSize])]
  rw [tendVatPayCallMem_read164_228 σ I hmemSize, tendVatPayCallMem_read196_228 σ I hmemSize]
  simp [ByteArray.append_assoc]

theorem tendVatPayCallMem_encode_228 {mem : ByteArray} (σ : AccountMap) (I : ExecutionEnv)
    (hmemSize : mem.size = 228) :
    config.externalABI.encode? "move"
      [.address I.source,
        .address (AccountAddress.ofNat (bidGalWord (tendId I) σ I).toNat),
        .int (Int.ofNat (UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I)).toNat)] =
        some ((tendVatPayCallMem mem σ I).readWithPadding 128 100) := by
  rw [tendVatPayCallMem_read_228 σ I hmemSize]
  unfold config externalABI
  simp only [if_true]
  unfold ABI.encodeCallWithSelector?
  have hgal :
      encodeABIValue? addr
          (.address (AccountAddress.ofNat (bidGalWord (tendId I) σ I).toNat)) =
        some (UInt256.toByteArray (bidGalWord (tendId I) σ I)).toList := by
    simpa [bidGalWord, flipperAddressReturnWord] using
      yankEncodeABIValue_address_word (flipperSlotWord (bidSlotOfWord (tendId I) ⟨4⟩) σ I)
  have hpayload :
      encodeABIValues? [addr, addr, uint256]
        [.address I.source,
          .address (AccountAddress.ofNat (bidGalWord (tendId I) σ I).toNat),
          .int (Int.ofNat (UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I)).toNat)] =
          some (UInt256.toByteArray (solcSourceWord I) ++
            UInt256.toByteArray (bidGalWord (tendId I) σ I) ++
            UInt256.toByteArray
              (UInt256.sub (tendBid I) (bidBidWord (tendId I) σ I))).toList := by
    unfold encodeABIValues?
    rw [show abiTupleHeadSize? [addr, addr, uint256] = some 96 by native_decide]
    simp only [encodeABIValuesFrom?, Option.bind, bind]
    rw [yankEncodeABIValue_source_address, hgal, yankEncodeABIValue_uint256_word]
    simp [show isDynamicABIType addr = false by native_decide,
      show isDynamicABIType uint256 = false by native_decide,
      ByteArray.append_assoc, byteArray_toList_eq]
  rw [hpayload]
  apply congrArg some
  apply ByteArray.ext
  simp [moveSelector, byteArray_toList_eq, ByteArray.append_assoc]

theorem flipperTendX_toPayExtcodesizeGuardAw8 {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem rdata : ByteArray}
    (hmemSize : mem.size = 228)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD flipperBytecode I g s0 ⟨3686⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 8) rdata (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3784⟩
      (flipperVatTargetWord σ I :: flipperVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
        flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendVatPayCallMem mem σ I) (UInt256.ofNat 8) rdata (cA, σ) k' C' := by
  let rawVat := flipperSlotWord ⟨2⟩ σ I
  let rawGal := flipperSlotWord (bidSlotOfWord (tendId I) ⟨4⟩) σ I
  let base := solcMappingSlot ⟨1⟩ (tendId I)
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hvatClean : UInt256.land rawVat solcAddrMask = flipperVatTargetWord σ I := by
    simp [rawVat, flipperVatTargetWord, flipperAddressReturnWord]
  have hgalCleanLeft :
      UInt256.land solcAddrMask rawGal = bidGalWord (tendId I) σ I := by
    simpa [rawGal, bidGalWord, flipperAddressReturnWord] using
      (u256_land_comm solcAddrMask rawGal)
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ (tendPayHashMem mem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((tendPayHashMem mem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [tendPayHashMem_size_228 I hmemSize]; decide) (by decide)
      (tendPayHashMem_read64_228 I hmemSize hmemRead64)
  have hmload64Pay :
      (if (⟨64⟩ : UInt256).toNat ≥ (tendVatPayCallMem mem σ I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((tendVatPayCallMem mem σ I).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [tendVatPayCallMem_size_228 σ I hmemSize]; decide) (by decide)
      (tendVatPayCallMem_read64_228 σ I hmemSize hmemRead64)
  have rd3689 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k3690, C3690, rd3690raw⟩ := rd3689.sload (by native_decide) (by evm_ov)
  have rd3690 : RD flipperBytecode I g s0 ⟨3690⟩
      [rawVat, tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 8) rdata (cA, σ) k3690 C3690 := by
    simpa [rawVat, flipperSlotWord, solcSlotWord] using rd3690raw
  have rd3709pre := evm_run rd3690 with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (wordAt0Mem (tendId I) mem) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw mstore 0 (tendPayHashMem mem I) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by
        dsimp [tendPayHashMem, twoWordHashMem, wordAt32Mem, wordAt0Mem]
        rfl) (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw keccak256 0 base (UInt256.ofNat 8)
      (by native_decide) mem_cost
      (by
        have hmemGe : 64 ≤ mem.size := by
          rw [hmemSize]
          norm_num
        simpa [base, tendPayHashMem, bidBaseOfWord] using
          (tendTwoWordHashMem_solcMappingSlot_of_size_ge (mem := mem) ⟨1⟩
            (tendId I) hmemGe))
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨k3711, C3711, rd3711raw⟩ := rd3709pre.sload (by native_decide) (by evm_ov)
  have rd3711 : RD flipperBytecode I g s0 ⟨3711⟩
      (rawGal :: ⟨4⟩ :: base :: ⟨64⟩ :: ⟨0⟩ :: rawVat :: tendBid I ::
        tendLot I :: tendId I :: ret :: sel :: [])
      (tendPayHashMem mem I) (UInt256.ofNat 8) rdata (cA, σ) k3711 C3711 := by
    have hslotAdd :
        (⟨4⟩ : UInt256) + base = bidSlotOfWord (tendId I) ⟨4⟩ := by
      simpa [base, bidSlotOfWord, bidBaseOfWord] using
        (u256_add_comm (⟨4⟩ : UInt256) (bidBaseOfWord (tendId I)))
    simpa [rawGal, flipperSlotWord, hslotAdd] using rd3711raw
  have rd3712pre := rd3711.swap2 (by native_decide) (by evm_ov)
  obtain ⟨k3713, C3713, rd3713raw⟩ := rd3712pre.sload (by native_decide) (by evm_ov)
  have rd3713 : RD flipperBytecode I g s0 ⟨3713⟩
      (bidBidWord (tendId I) σ I :: ⟨4⟩ :: rawGal :: ⟨64⟩ :: ⟨0⟩ ::
        rawVat :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendPayHashMem mem I) (UInt256.ofNat 8) rdata (cA, σ) k3713 C3713 := by
    simpa [bidBidWord, bidBaseOfWord, flipperSlotWord, base] using rd3713raw
  let mem1 := writeWord (tendPayHashMem mem I) 128 yankVatMoveSelectorWord
  let mem2 := writeWord mem1 132 (solcSourceWord I)
  let mem3 := writeWord mem2 164 (bidGalWord (tendId I) σ I)
  have rd3724 := evm_run rd3713 with [
    raw dup4 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Hash (by decide) (by evm_ov),
    raw push4 ⟨3140843579⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 mem1 (UInt256.ofNat 8)
      (by native_decide) mem_cost (by
        dsimp [mem1, yankVatMoveSelectorWord, Reasoning.Theory.writeWord]
        rfl) (by decide) (by evm_ov)]
  have rd3732 := evm_run rd3724 with [
    raw caller (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw mstore 0 mem2 (UInt256.ofNat 8)
      (by native_decide) mem_cost (by
        dsimp [mem1, mem2, solcSourceWord, Reasoning.Theory.writeWord]
        rfl) (by decide) (by evm_ov)]
  have rd3748 := evm_run rd3732 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 mem3 (UInt256.ofNat 8)
      (by native_decide) mem_cost (by
        rw [hmask160, hgalCleanLeft]
        dsimp [mem2, mem3, Reasoning.Theory.writeWord]
        rfl) (by decide) (by evm_ov)]
  have rd3755 := evm_run rd3748 with [
    raw dup7 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (tendVatPayCallMem mem σ I) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by
        dsimp [mem1, mem2, mem3, tendVatPayCallMem, Reasoning.Theory.writeWord,
          writeCascade]
        rfl) (by decide) (by evm_ov)]
  have rd3784 := evm_run rd3755 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Pay (by decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 ⟨3140843579⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  rw [hmask160, hvatClean] at rd3784
  exact ⟨_, _, by simpa using rd3784⟩

theorem flipperTendX_payNoCodeAw8 {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem rdata : ByteArray}
    (hmemSize : mem.size = 228)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) = ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨3686⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 8) rdata (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  obtain ⟨_, _, rd3784⟩ := flipperTendX_toPayExtcodesizeGuardAw8
    hmemSize hmemRead64 h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨3784⟩) (okPc := ⟨3796⟩) rd3784
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem flipperTendX_toPayCallAw8 {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem rdata : ByteArray}
    (hmemSize : mem.size = 228)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (h : RD flipperBytecode I g s0 ⟨3686⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 8) rdata (cA, σ) k C) :
    ∃ gasWord k' C', RD flipperBytecode I g s0 ⟨3799⟩
      (gasWord :: flipperVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
        flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendVatPayCallMem mem σ I) (UInt256.ofNat 8) rdata
      (cA, σ) k' C' := by
  obtain ⟨_, _, rd3784⟩ := flipperTendX_toPayExtcodesizeGuardAw8
    hmemSize hmemRead64 h
  obtain ⟨gasWord, k3799, C3799, rd3799⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3784⟩) (okPc := ⟨3796⟩) rd3784
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k3799, C3799, by simpa using rd3799⟩

theorem flipperTendX_payDepthLimitAw8 {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {ret sel : UInt256} {mem rdata : ByteArray}
    (hmemSize : mem.size = 228)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = (1024 : Fin 1025))
    (h : RD flipperBytecode I g s0 ⟨3686⟩ [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 8) rdata (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨3800⟩
      (⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
        flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (tendVatPayCallMem mem σ I) (UInt256.ofNat 8) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨gasWord, _, _, rd3799⟩ :=
    flipperTendX_toPayCallAw8 hmemSize hmemRead64 hcodeSize h
  obtain ⟨k3800, C3800, rd3800raw⟩ :=
    RD.callDepthLimit rd3799 (by native_decide) hdepth (by evm_ov)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
    native_decide
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    rfl
  have rd3800 : RD flipperBytecode I g s0 ⟨3800⟩
      (⟨0⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
        flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
      (ByteArray.empty.write 0 (tendVatPayCallMem mem σ I) 128
        (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ) k3800 C3800 := by
    simpa using haw ▸ rd3800raw
  rw [hmin, byteArray_write_len_zero] at rd3800
  exact ⟨_, _, rd3800⟩

theorem flipperTendX_payPostCallAw8
    {cA0 gh bl σbase σ₀ A I} {g : UInt256}
    {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap} {Acur : Substate}
    {k C : ℕ} {ret sel : UInt256} {mem out0 : ByteArray}
    (hmemSize : mem.size = 228)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (flipperVatTargetWord σ I) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨3686⟩
      [tendBid I, tendLot I, tendId I, ret, sel]
      mem (UInt256.ofNat 8) out0 (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨3800⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: ⟨3140843579⟩ ::
          flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
        (tendVatPayCallMem mem σ I) (UInt256.ofNat 8) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ, substate := Acur, createdAccounts := cA })
        (EVM.address (flipperVatAddress σ I)) "move" 0
        (tendPayMoveArgValsOf
          ({ initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ, substate := Acur, createdAccounts := cA }) I)
        (z,
          { { initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ, substate := Acur, createdAccounts := cA } with
            accountMap := σ', substate := A', createdAccounts := cA' },
          out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd3799⟩ :=
    flipperTendX_toPayCallAw8 hmemSize hmemRead64 hcodeSize h
  obtain ⟨cA', σ', z, out, A_in, callGas, k3800, C3800, hΘpack, rd3800raw,
      houtsz⟩ :=
    RD.call rd3799 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k3800, C3800, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
      native_decide
    have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      rfl
    have rd3800 : RD flipperBytecode I (Sat256.ofUInt256 g)
        (initState cA0 gh bl σbase σ₀ (Sat256.ofUInt256 g) A I) ⟨3800⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: ⟨3140843579⟩ ::
          flipperVatTargetWord σ I :: tendBid I :: tendLot I :: tendId I :: ret :: sel :: [])
        (out.write 0 (tendVatPayCallMem mem σ I) 128
          (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 8) out (cA', σ') k3800 C3800 :=
      haw ▸ rd3800raw
    rw [hmin, byteArray_write_len_zero] at rd3800
    exact rd3800
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := flipperVatTargetWord σ I)
      (mem := tendVatPayCallMem mem σ I) (inOff := ⟨128⟩) (inSize := ⟨100⟩)
      (fun hdepthEq => by
        have hEq : I.depth = (1024 : Fin 1025) := by
          simpa [initState] using hdepthEq
        exact absurd hdepth (by rw [hEq]; decide))
      (flipperVatEvmAddress_eq_target_of_accountMapEquiv (accountMapEquiv.refl σ))
      ?_ ?_
    · simpa [tendPayMoveArgValsOf, initState, flipperSlotWord, solcSlotWord,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        bidGalWord, bidSlotOfWord, bidBidWord, bidBaseOfWord,
        flipperAddressReturnWord]
        using tendVatPayCallMem_encode_228 σ I hmemSize
    · simpa [initState, hperm] using hΘ

theorem flipperTendBodyFrom3486Refund
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {k C : ℕ} {mem : ByteArray} {sel : UInt256}
    (hcode : I.code = flipperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some tendTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (tendTransition.params.map Param.name)
        (transitionSignature tendTransition).paramTypes I.calldata = some (tendLocals I))
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hguySolm : bidGuyWord (tendId I) σ_solm I ≠ ⟨0⟩)
    (hticGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .gt (.storage (bidsF (.var "id") "tic")) (.env .timestamp))
          (.binary .eq (.storage (bidsF (.var "id") "tic")) (.intLit 0))) =
          .ok (.bool true))
    (hendGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.storage (bidsF (.var "id") "end")) (.env .timestamp)) =
          .ok (.bool true))
    (hlotGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "lot") (.storage (bidsF (.var "id") "lot"))) =
          .ok (.bool true))
    (htabGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .le (.var "bid") (.storage (bidsF (.var "id") "tab"))) =
          .ok (.bool true))
    (hbidGuard :
      evalExpr? config { contract := contract, locals := tendLocals I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .gt (.var "bid") (.storage (bidsF (.var "id") "bid"))) =
          .ok (.bool true))
    (hfitBid : (tendBid I).toNat * flipperONEWord.toNat < UInt256.size)
    (hfitBeg :
      (tendBegWord σ_solm I).toNat * (bidBidWord (tendId I) σ_solm I).toNat <
        UInt256.size)
    (hinc :
      evalExpr? config { contract := contract, locals := tendLocalsBidOneBegBid σ_solm I }
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .or
          (.binary .ge (.var "bidOne") (.var "begBid"))
          (.binary .eq (.var "bid") (.storage (bidsF (.var "id") "tab")))) =
          .ok (.bool true))
    (hcallerEvm : solcSourceWord I ≠ bidGuyWord (tendId I) σ_evm I)
    (hcallerSolm : solcSourceWord I ≠ bidGuyWord (tendId I) σ_solm I)
    (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3486⟩
      [tendBid I, tendLot I, tendId I, ⟨323⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let memHash := twoWordHashMem (tendId I) ⟨1⟩ mem
  have hhashSize : memHash.size = 96 := by
    dsimp [memHash]
    exact twoWordHashMem_size_96 (tendId I) ⟨1⟩ hmemSize
  have hhashRead64 : memHash.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    dsimp [memHash]
    exact twoWordHashMem_read64 (tendId I) ⟨1⟩ hmemSize hmemRead64
  by_cases hrefundZero :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (flipperVatTargetWord σ_evm I) = ⟨0⟩
  · have hrefundZeroSolm :
        Reasoning.Theory.extCodeSizeWord σ_solm
            (flipperVatTargetWord σ_solm I) = ⟨0⟩ :=
      flipperVatCodeSize_zero_accountMapEquiv hAccounts hrefundZero
    have hvatNoCode :=
      flipperVatCode_zero_of_codeSize_zero (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hrefundZeroSolm
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (tendLocals I) tendTransition.body .reverted := by
      simpa using
        (flipperTendSourceBodyRefundNoCode (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hwv hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid
          hfitBeg hinc hcallerSolm hvatNoCode)
    exact (flipperTendX_refundNoCode hmemSize hmemRead64 hcallerEvm hrefundZero h)
      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hrefundNeSolm :
        Reasoning.Theory.extCodeSizeWord σ_solm
            (flipperVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
      flipperVatCodeSize_ne_zero_accountMapEquiv hAccounts hrefundZero
    have hrefundCodeSolm :=
      flipperVatCode_pos_of_codeSize_ne_zero (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hrefundNeSolm
    by_cases hdepthEq : I.depth = (1024 : Fin 1025)
    · obtain ⟨_, _, rd3632⟩ :=
        flipperTendX_refundDepthLimit hmemSize hmemRead64 hcallerEvm hrefundZero
          hdepthEq h
      let evm0Solm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmRefundSolm :=
        { evm0Solm with
          substate :=
            (evm0Solm.addAccessedAccount
              (EVM.address
                (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))).substate }
      have hrefundEncode :
          config.externalABI.encode? "move" (tendRefundMoveArgValsOf evm0Solm I) =
            some ((tendVatRefundCallMem memHash σ_solm I).readWithPadding 128 100) := by
        simpa [evm0Solm, tendRefundMoveArgValsOf, initState, flipperSlotWord,
          solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
          bidGuyWord, bidPackedSlotOfWord, bidBidWord, bidBaseOfWord,
          flipperAddressReturnWord]
          using tendVatRefundCallMem_encode σ_solm I hhashSize
      have hcallRefundSolm :
          typedCallViaEVM config evm0Solm
            (EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
            "move" 0 (tendRefundMoveArgValsOf evm0Solm I)
            (false, evmRefundSolm, ByteArray.empty) true := by
        exact Reasoning.Theory.callNotMade_depthLimit (cfg := config) (evm := evm0Solm)
          (tgt := EVM.address
            (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
          (name := "move") (args := tendRefundMoveArgValsOf evm0Solm I)
          (calldata := (tendVatRefundCallMem memHash σ_solm I).readWithPadding 128 100)
          (callPerm := true) hrefundEncode (by simpa [evm0Solm, initState] using hdepthEq)
      have hbody :
          ExecTransitionBody config contract evm0Solm (tendLocals I) tendTransition.body
            .reverted := by
        simpa [evm0Solm] using
          (flipperTendSourceBodyRefundCallFailure
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) (evmRefund := evmRefundSolm)
            (outRefund := ByteArray.empty)
            hwv hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid
            hfitBeg hinc hcallerSolm hrefundCodeSolm hcallRefundSolm)
      exact (flipperTendX_refundCallFailure (by simpa using rd3632)
          (by norm_num [UInt256.size]))
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hdepthLt : I.depth.val < 1024 := by
        by_contra hnot
        have hle : I.depth.val ≤ 1024 := Nat.lt_succ_iff.mp I.depth.isLt
        have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hnot
        have hval : I.depth.val = 1024 := by omega
        exact hdepthEq (Fin.ext hval)
      obtain ⟨cA_ref, σ_ref, zRefund, outRefund, A_ref, k3632, C3632, rd3632,
          hcallRefundEvmRaw, houtRefund⟩ :=
        flipperTendX_refundPostCall (Acur := A) hmemSize hmemRead64 hcallerEvm
          hrefundZero hperm hdepthLt h
      let evm0Evm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
      let evm0Solm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evmRefundEvm : EVM.State :=
        { evm0Evm with
          accountMap := σ_ref
          substate := A_ref
          createdAccounts := cA_ref }
      have hcallRefundEvm :
          typedCallViaEVM config evm0Evm
            (EVM.address (flipperVatAddress σ_evm I)) "move" 0
            (tendRefundMoveArgValsOf evm0Evm I) (zRefund, evmRefundEvm, outRefund)
            true := by
        simpa [evm0Evm, evmRefundEvm] using hcallRefundEvmRaw
      obtain ⟨σ_ref_solm, A_ref_solm, hcallRefundSolmRaw, hRefundStateEquiv⟩ :=
        flipper_typedCallViaEVM_accountMapEquiv_noSubstate
          (evm_solm := evm0Solm) hcallRefundEvm
          (by simpa [evm0Evm, evm0Solm] using hAccounts)
          (by simp [evm0Evm, evm0Solm, initState])
          (by simp [evm0Evm, evm0Solm, initState])
          (by simp [evm0Evm, evm0Solm, initState])
          (by simp [evm0Evm, evm0Solm, initState])
          (by simp [evm0Evm, evm0Solm, initState])
      let evmRefundSolm : EVM.State :=
        { evm0Solm with
          accountMap := σ_ref_solm
          substate := A_ref_solm
          createdAccounts := cA_ref }
      have hrefundTargetEq :
          EVM.address (flipperVatAddress σ_evm I) =
            EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv) := by
        rw [flipperVatAddress_accountMapEquiv hAccounts]
        simp [evm0Solm, initState]
      have hrefundArgsEq :
          tendRefundMoveArgValsOf evm0Evm I = tendRefundMoveArgValsOf evm0Solm I := by
        have hloadPacked :
            Solm.EVM.storageLoad evm0Evm I.codeOwner (bidPackedSlotOfWord (tendId I)) =
              Solm.EVM.storageLoad evm0Solm I.codeOwner (bidPackedSlotOfWord (tendId I)) := by
          simpa [evm0Evm, evm0Solm, initState] using
            storageLoad_accountMapEquiv hAccounts I.codeOwner
              (bidPackedSlotOfWord (tendId I))
        have hloadBid :
            Solm.EVM.storageLoad evm0Evm I.codeOwner (bidBaseOfWord (tendId I)) =
              Solm.EVM.storageLoad evm0Solm I.codeOwner (bidBaseOfWord (tendId I)) := by
          simpa [evm0Evm, evm0Solm, initState] using
            storageLoad_accountMapEquiv hAccounts I.codeOwner (bidBaseOfWord (tendId I))
        simp [tendRefundMoveArgValsOf]
        constructor
        · simp [evm0Evm, evm0Solm, initState]
        · constructor
          · have hownerEvm : evm0Evm.executionEnv.codeOwner = I.codeOwner := by
              simp [evm0Evm, initState]
            have hownerSolm : evm0Solm.executionEnv.codeOwner = I.codeOwner := by
              simp [evm0Solm, initState]
            rw [hownerEvm, hownerSolm, hloadPacked]
          · have hownerEvm : evm0Evm.executionEnv.codeOwner = I.codeOwner := by
              simp [evm0Evm, initState]
            have hownerSolm : evm0Solm.executionEnv.codeOwner = I.codeOwner := by
              simp [evm0Solm, initState]
            rw [hownerEvm, hownerSolm, hloadBid]
      have hcallRefundSolm :
          typedCallViaEVM config evm0Solm
            (EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
            "move" 0 (tendRefundMoveArgValsOf evm0Solm I)
            (zRefund, evmRefundSolm, outRefund) true := by
        have hcallRefundSolmRaw' :
            typedCallViaEVM config evm0Solm
              (EVM.address (flipperVatAddress σ_evm I)) "move" 0
              (tendRefundMoveArgValsOf evm0Evm I) (zRefund, evmRefundSolm, outRefund)
              true := by
          simpa [evmRefundSolm, evmRefundEvm] using hcallRefundSolmRaw
        rw [hrefundTargetEq, hrefundArgsEq] at hcallRefundSolmRaw'
        exact hcallRefundSolmRaw'
      cases zRefund
      · have hcallRefundSolmFalse :
            typedCallViaEVM config evm0Solm
              (EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
              "move" 0 (tendRefundMoveArgValsOf evm0Solm I)
              (false, evmRefundSolm, outRefund) true := by
          simpa using hcallRefundSolm
        have hbody :
            ExecTransitionBody config contract evm0Solm (tendLocals I) tendTransition.body
              .reverted := by
          simpa [evm0Solm] using
            (flipperTendSourceBodyRefundCallFailure
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) (evmRefund := evmRefundSolm)
              (outRefund := outRefund)
              hwv hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid
              hfitBeg hinc hcallerSolm hrefundCodeSolm hcallRefundSolmFalse)
        exact (flipperTendX_refundCallFailure (by simpa using rd3632) houtRefund)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have rd3632True : RD flipperBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3632⟩
            (⟨1⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
              flipperVatTargetWord σ_evm I :: tendBid I :: tendLot I :: tendId I ::
              ⟨323⟩ :: sel :: [])
            (tendVatRefundCallMem memHash σ_evm I) (UInt256.ofNat 8) outRefund
            (cA_ref, σ_ref) k3632 C3632 := by
          simpa [memHash] using rd3632
        obtain ⟨_, _, rd3652⟩ := flipperTendX_refundCallSuccessToStoreStart rd3632True
        have hrefundMemSize : (tendVatRefundCallMem memHash σ_evm I).size = 228 := by
          exact tendVatRefundCallMem_size σ_evm I hhashSize
        have hrefundMemRead64 :
            (tendVatRefundCallMem memHash σ_evm I).readWithPadding 64 32 =
              UInt256.toByteArray ⟨128⟩ :=
          tendVatRefundCallMem_read64 σ_evm I hhashSize hhashRead64
        have hrefundMemGe : 64 ≤ (tendVatRefundCallMem memHash σ_evm I).size := by
          rw [hrefundMemSize]
          norm_num
        obtain ⟨_, _, rd3686⟩ := flipperTendX_storeRefundGuyToPayStart
          hperm hrefundMemGe rd3652
        let evmGuyEvm := Solm.EVM.storageStore evmRefundEvm
          evmRefundEvm.executionEnv.codeOwner (bidPackedSlotOfWord (tendId I))
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evmRefundEvm evmRefundEvm.executionEnv.codeOwner
              (bidPackedSlotOfWord (tendId I)))
            (solcSourceWord evmRefundEvm.executionEnv))
        let evmGuySolm := Solm.EVM.storageStore evmRefundSolm
          evmRefundSolm.executionEnv.codeOwner (bidPackedSlotOfWord (tendId I))
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evmRefundSolm evmRefundSolm.executionEnv.codeOwner
              (bidPackedSlotOfWord (tendId I)))
            (solcSourceWord evmRefundSolm.executionEnv))
        have hRefundStateEquiv' : EVMStateEquiv evmRefundEvm evmRefundSolm := by
          simpa [evmRefundEvm, evmRefundSolm] using hRefundStateEquiv
        have hpackedLoadEq :
            Solm.EVM.storageLoad evmRefundEvm evmRefundEvm.executionEnv.codeOwner
                (bidPackedSlotOfWord (tendId I)) =
              Solm.EVM.storageLoad evmRefundSolm evmRefundSolm.executionEnv.codeOwner
                (bidPackedSlotOfWord (tendId I)) :=
          hRefundStateEquiv'.storageLoad_codeOwner (bidPackedSlotOfWord (tendId I))
        have hsourceEq :
            solcSourceWord evmRefundEvm.executionEnv =
              solcSourceWord evmRefundSolm.executionEnv := by
          rw [hRefundStateEquiv'.executionEnv]
        have hstoredGuyEq :
            setAddressOffset0Word
                (Solm.EVM.storageLoad evmRefundEvm evmRefundEvm.executionEnv.codeOwner
                  (bidPackedSlotOfWord (tendId I)))
                (solcSourceWord evmRefundEvm.executionEnv) =
              setAddressOffset0Word
                (Solm.EVM.storageLoad evmRefundSolm evmRefundSolm.executionEnv.codeOwner
                  (bidPackedSlotOfWord (tendId I)))
                (solcSourceWord evmRefundSolm.executionEnv) := by
          rw [hpackedLoadEq, hsourceEq]
        have hGuyStateEquiv : EVMStateEquiv evmGuyEvm evmGuySolm := by
          simpa [evmGuyEvm, evmGuySolm] using
            EVMStateEquiv.storageStore_codeOwner hRefundStateEquiv'
              (bidPackedSlotOfWord (tendId I)) hstoredGuyEq
        have hmapGuyEvm : evmGuyEvm.accountMap = tendAfterRefundMap σ_ref I := by
          simpa [evmGuyEvm, evmRefundEvm, evm0Evm, tendAfterRefundMap,
            storageStore_accountMap, initState, Solm.EVM.storageLoad, State.lookupAccount,
            Account.lookupStorage, flipperSlotWord, solcSlotWord]
        let memPay := twoWordHashMem (tendId I) ⟨1⟩ (tendVatRefundCallMem memHash σ_evm I)
        have hmemPaySize : memPay.size = 228 := by
          dsimp [memPay]
          calc
            (twoWordHashMem (tendId I) ⟨1⟩
                (tendVatRefundCallMem memHash σ_evm I)).size =
                (tendVatRefundCallMem memHash σ_evm I).size :=
              tendTwoWordHashMem_size_of_size_ge (tendId I) ⟨1⟩ (by
                rw [hrefundMemSize]
                norm_num)
            _ = 228 := hrefundMemSize
        have hmemPayRead64 :
            memPay.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
          dsimp [memPay]
          exact tendPayHashMem_read64_228 I hrefundMemSize hrefundMemRead64
        have hcallRefundSolmTrue :
            typedCallViaEVM config evm0Solm
              (EVM.address (flipperVatAddress evm0Solm.accountMap evm0Solm.executionEnv))
              "move" 0 (tendRefundMoveArgValsOf evm0Solm I)
              (true, evmRefundSolm, outRefund) true := by
          simpa using hcallRefundSolm
        by_cases hpayZero :
            Reasoning.Theory.extCodeSizeWord (tendAfterRefundMap σ_ref I)
              (flipperVatTargetWord (tendAfterRefundMap σ_ref I) I) = ⟨0⟩
        · have hpayZeroEvm :
              Reasoning.Theory.extCodeSizeWord evmGuyEvm.accountMap
                (flipperVatTargetWord evmGuyEvm.accountMap I) = ⟨0⟩ := by
            simpa [hmapGuyEvm] using hpayZero
          have hpayZeroSolm :
              Reasoning.Theory.extCodeSizeWord evmGuySolm.accountMap
                (flipperVatTargetWord evmGuySolm.accountMap I) = ⟨0⟩ :=
            flipperVatCodeSize_zero_accountMapEquiv hGuyStateEquiv.accountMap hpayZeroEvm
          have hpayNoCodeSolm :
              (UInt256.ofNat
                ((evmGuySolm.lookupAccount
                  (flipperVatAddress evmGuySolm.accountMap
                    evmGuySolm.executionEnv)).option
                  0 (fun acc => acc.code.size))).toNat = 0 := by
            simpa [evmGuySolm, evmRefundSolm, evm0Solm, initState,
              storageStore_executionEnv, State.lookupAccount] using
              flipper_extCodeSizeWord_zero_lookup_code_zero
                (σ := evmGuySolm.accountMap)
                (target := flipperVatTargetWord evmGuySolm.accountMap I)
                (addr := flipperVatAddress evmGuySolm.accountMap I)
                (flipperVatAddress_eq_target evmGuySolm.accountMap I) hpayZeroSolm
          have hbody :
              ExecTransitionBody config contract evm0Solm (tendLocals I) tendTransition.body
                .reverted := by
            simpa [evm0Solm, evmGuySolm] using
              (flipperTendSourceBodyPayNoCodeAfterRefund
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) (evmRefund := evmRefundSolm)
                (outRefund := outRefund)
                hwv hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid
                hfitBeg hinc hcallerSolm hrefundCodeSolm hcallRefundSolmTrue
                hpayNoCodeSolm)
          exact (flipperTendX_payNoCodeAw8 hmemPaySize hmemPayRead64 hpayZero rd3686)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hpayNeEvm :
              Reasoning.Theory.extCodeSizeWord evmGuyEvm.accountMap
                (flipperVatTargetWord evmGuyEvm.accountMap I) ≠ ⟨0⟩ := by
            simpa [hmapGuyEvm] using hpayZero
          have hpayNeSolm :
              Reasoning.Theory.extCodeSizeWord evmGuySolm.accountMap
                (flipperVatTargetWord evmGuySolm.accountMap I) ≠ ⟨0⟩ :=
            flipperVatCodeSize_ne_zero_accountMapEquiv hGuyStateEquiv.accountMap hpayNeEvm
          have hpayCodeSolm :
              0 <
                (UInt256.ofNat
                  ((evmGuySolm.lookupAccount
                    (flipperVatAddress evmGuySolm.accountMap
                      evmGuySolm.executionEnv)).option
                    0 (fun acc => acc.code.size))).toNat := by
            simpa [evmGuySolm, evmRefundSolm, evm0Solm, initState,
              storageStore_executionEnv, State.lookupAccount] using
              flipper_extCodeSizeWord_pos_lookup_code_pos
                (σ := evmGuySolm.accountMap)
                (target := flipperVatTargetWord evmGuySolm.accountMap I)
                (addr := flipperVatAddress evmGuySolm.accountMap I)
                (flipperVatAddress_eq_target evmGuySolm.accountMap I) hpayNeSolm
          let evmGuyCallEvm : EVM.State :=
            { evm0Evm with
              accountMap := tendAfterRefundMap σ_ref I
              substate := A_ref
              createdAccounts := cA_ref }
          have hGuyCallStateEquiv : EVMStateEquiv evmGuyCallEvm evmGuySolm := by
            refine ⟨?_, ?_, ?_⟩
            · simp [evmGuyCallEvm, evmGuySolm, evmRefundSolm, evm0Evm, evm0Solm,
                storageStore_executionEnv, initState]
            · simp [evmGuyCallEvm, evmGuySolm, evmRefundSolm, evm0Solm,
                storageStore_createdAccounts, initState]
            · simpa [evmGuyCallEvm, hmapGuyEvm] using hGuyStateEquiv.accountMap
          obtain ⟨cA_pay, σ_pay, zPay, outPay, A_pay, k3800, C3800, rd3800,
              hcallPayEvmRaw, houtPay⟩ :=
            flipperTendX_payPostCallAw8 (Acur := A_ref) hmemPaySize hmemPayRead64
              hpayZero hperm hdepthLt rd3686
          let evmPayEvm : EVM.State :=
            { evmGuyCallEvm with
              accountMap := σ_pay
              substate := A_pay
              createdAccounts := cA_pay }
          have hcallPayEvm :
              typedCallViaEVM config evmGuyCallEvm
                (EVM.address
                  (flipperVatAddress evmGuyCallEvm.accountMap evmGuyCallEvm.executionEnv))
                "move" 0 (tendPayMoveArgValsOf evmGuyCallEvm I)
                (zPay, evmPayEvm, outPay) true := by
            simpa [evmPayEvm, evmGuyCallEvm, evm0Evm] using hcallPayEvmRaw
          obtain ⟨σ_pay_solm, A_pay_solm, hcallPaySolmRaw, hPayStateEquiv⟩ :=
            flipper_typedCallViaEVM_accountMapEquiv_noSubstate
              (evm_solm := evmGuySolm) hcallPayEvm hGuyCallStateEquiv.accountMap
              (by simp [evmGuyCallEvm, evmGuySolm, evmRefundSolm, evm0Evm, evm0Solm,
                tend_storageStore_sigma0, initState])
              (by simp [evmGuyCallEvm, evmGuySolm, evmRefundSolm, evm0Solm,
                storageStore_createdAccounts, initState])
              (by simp [evmGuyCallEvm, evmGuySolm, evmRefundSolm, evm0Evm, evm0Solm,
                tend_storageStore_genesisBlockHeader, initState])
              (by simp [evmGuyCallEvm, evmGuySolm, evmRefundSolm, evm0Evm, evm0Solm,
                tend_storageStore_blocks, initState])
              (by simpa using hGuyCallStateEquiv.executionEnv.symm)
          let evmPaySolm : EVM.State :=
            { evmGuySolm with
              accountMap := σ_pay_solm
              substate := A_pay_solm
              createdAccounts := cA_pay }
          have hpayTargetEq :
              EVM.address
                  (flipperVatAddress evmGuyCallEvm.accountMap evmGuyCallEvm.executionEnv) =
                EVM.address
                  (flipperVatAddress evmGuySolm.accountMap evmGuySolm.executionEnv) := by
            rw [hGuyCallStateEquiv.executionEnv]
            rw [flipperVatAddress_accountMapEquiv hGuyCallStateEquiv.accountMap]
          have hpayArgsEq :
              tendPayMoveArgValsOf evmGuyCallEvm I = tendPayMoveArgValsOf evmGuySolm I := by
            have hloadGal :
                Solm.EVM.storageLoad evmGuyCallEvm evmGuyCallEvm.executionEnv.codeOwner
                    (bidSlotOfWord (tendId I) ⟨4⟩) =
                  Solm.EVM.storageLoad evmGuySolm evmGuySolm.executionEnv.codeOwner
                    (bidSlotOfWord (tendId I) ⟨4⟩) :=
              hGuyCallStateEquiv.storageLoad_codeOwner (bidSlotOfWord (tendId I) ⟨4⟩)
            have hloadBid :
                Solm.EVM.storageLoad evmGuyCallEvm evmGuyCallEvm.executionEnv.codeOwner
                    (bidBaseOfWord (tendId I)) =
                  Solm.EVM.storageLoad evmGuySolm evmGuySolm.executionEnv.codeOwner
                    (bidBaseOfWord (tendId I)) :=
              hGuyCallStateEquiv.storageLoad_codeOwner (bidBaseOfWord (tendId I))
            simp [tendPayMoveArgValsOf]
            constructor
            · rw [hGuyCallStateEquiv.executionEnv]
            · constructor
              · rw [hloadGal]
              · rw [hloadBid]
          have hcallPaySolm :
              typedCallViaEVM config evmGuySolm
                (EVM.address
                  (flipperVatAddress evmGuySolm.accountMap evmGuySolm.executionEnv))
                "move" 0 (tendPayMoveArgValsOf evmGuySolm I)
                (zPay, evmPaySolm, outPay) true := by
            have hcallPaySolmRaw' :
                typedCallViaEVM config evmGuySolm
                  (EVM.address
                    (flipperVatAddress evmGuyCallEvm.accountMap evmGuyCallEvm.executionEnv))
                  "move" 0 (tendPayMoveArgValsOf evmGuyCallEvm I)
                  (zPay, evmPaySolm, outPay) true := by
              simpa [evmPaySolm, evmPayEvm] using hcallPaySolmRaw
            rw [hpayTargetEq, hpayArgsEq] at hcallPaySolmRaw'
            exact hcallPaySolmRaw'
          cases zPay
          · have hcallPaySolmFalse :
                typedCallViaEVM config evmGuySolm
                  (EVM.address
                    (flipperVatAddress evmGuySolm.accountMap evmGuySolm.executionEnv))
                  "move" 0 (tendPayMoveArgValsOf evmGuySolm I)
                  (false, evmPaySolm, outPay) true := by
              simpa using hcallPaySolm
            have hbody :
                ExecTransitionBody config contract evm0Solm (tendLocals I) tendTransition.body
                  .reverted := by
              simpa [evm0Solm, evmGuySolm] using
                (flipperTendSourceBodyPayCallFailureAfterRefund
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := g) (evmRefund := evmRefundSolm)
                  (evmPay := evmPaySolm) (outRefund := outRefund) (outPay := outPay)
                  hwv hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid
                  hfitBeg hinc hcallerSolm hrefundCodeSolm hcallRefundSolmTrue
                  hpayCodeSolm hcallPaySolmFalse)
            exact (flipperTendX_payCallFailure (by simpa using rd3800) houtPay)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have rd3800True : RD flipperBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3800⟩
                (⟨1⟩ :: ⟨228⟩ :: ⟨3140843579⟩ ::
                  flipperVatTargetWord (tendAfterRefundMap σ_ref I) I :: tendBid I ::
                  tendLot I :: tendId I :: ⟨323⟩ :: sel :: [])
                (tendVatPayCallMem memPay (tendAfterRefundMap σ_ref I) I)
                (UInt256.ofNat 8) outPay (cA_pay, σ_pay) k3800 C3800 := by
              simpa [memPay] using rd3800
            obtain ⟨_, _, rd3820⟩ := flipperTendX_payCallSuccessToStoreStart rd3800True
            have hpayMemGe :
                64 ≤ (tendVatPayCallMem memPay (tendAfterRefundMap σ_ref I) I).size := by
              rw [tendVatPayCallMem_size_228 (tendAfterRefundMap σ_ref I) I hmemPaySize]
              norm_num
            obtain ⟨_, _, rd6272⟩ := flipperTendX_storeBidToAdd48 hperm hpayMemGe rd3820
            have hcallPaySolmTrue :
                typedCallViaEVM config evmGuySolm
                  (EVM.address
                    (flipperVatAddress evmGuySolm.accountMap evmGuySolm.executionEnv))
                  "move" 0 (tendPayMoveArgValsOf evmGuySolm I)
                  (true, evmPaySolm, outPay) true := by
              simpa using hcallPaySolm
            let evmBidEvm := Solm.EVM.storageStore evmPayEvm
              evmPayEvm.executionEnv.codeOwner (bidBaseOfWord (tendId I)) (tendBid I)
            let evmBidSolm := Solm.EVM.storageStore evmPaySolm
              evmPaySolm.executionEnv.codeOwner (bidBaseOfWord (tendId I)) (tendBid I)
            have hPayStateEquiv' : EVMStateEquiv evmPayEvm evmPaySolm := by
              simpa [evmPayEvm, evmPaySolm] using hPayStateEquiv
            have hBidStateEquiv : EVMStateEquiv evmBidEvm evmBidSolm := by
              simpa [evmBidEvm, evmBidSolm] using
                EVMStateEquiv.storageStore_codeOwner hPayStateEquiv'
                  (bidBaseOfWord (tendId I)) (by rfl : tendBid I = tendBid I)
            have hmapBidEvm : evmBidEvm.accountMap = tendAfterBidMap σ_pay I := by
              have hownerCall : evmGuyCallEvm.executionEnv.codeOwner = I.codeOwner := by
                simp [evmGuyCallEvm, evm0Evm, initState]
              simpa [evmBidEvm, evmPayEvm, evmGuyCallEvm, evm0Evm, tendAfterBidMap,
                storageStore_accountMap, storageStore_executionEnv, hownerCall, initState]
            have httlEq :
                tendTtlWord evmBidEvm.accountMap I = tendTtlWord evmBidSolm.accountMap I := by
              unfold tendTtlWord flipperUint48Offset0Word flipperSlotWord solcSlotWord
              rw [accountMapEquiv_storage_findD hBidStateEquiv.accountMap I.codeOwner ⟨5⟩ ⟨0⟩]
            have httlEvmMap :
                tendTtlWord evmBidEvm.accountMap I =
                  tendTtlWord (tendAfterBidMap σ_pay I) I := by
              simpa [hmapBidEvm]
            by_cases hfitTicEvm :
                (tendNow48 I).toNat +
                    (tendTtlWord (tendAfterBidMap σ_pay I) I).toNat <
                  2 ^ 48
            · obtain ⟨_, _, rd3859⟩ := flipperTendX_add48Success hfitTicEvm rd6272
              have hticMemGe :
                  64 ≤
                    (twoWordHashMem (tendId I) ⟨1⟩
                      (tendVatPayCallMem memPay (tendAfterRefundMap σ_ref I) I)).size := by
                rw [tendTwoWordHashMem_size_of_size_ge]
                · exact hpayMemGe
                · exact hpayMemGe
              have hret := flipperTendX_storeTicReturn hperm hticMemGe rd3859
              have hfitTicSolm :
                  (tendNow48 I).toNat + (tendTtlWord evmBidSolm.accountMap I).toNat <
                    2 ^ 48 := by
                have httlSolmMap :
                    tendTtlWord evmBidSolm.accountMap I =
                      tendTtlWord (tendAfterBidMap σ_pay I) I := by
                  rw [← httlEq, httlEvmMap]
                simpa [httlSolmMap] using hfitTicEvm
              let evmTicEvm := Solm.EVM.storageStore evmBidEvm
                evmBidEvm.executionEnv.codeOwner (bidPackedSlotOfWord (tendId I))
                (setUint48Offset20Word
                  (Solm.EVM.storageLoad evmBidEvm evmBidEvm.executionEnv.codeOwner
                    (bidPackedSlotOfWord (tendId I)))
                  (tendTicNewWord evmBidEvm.accountMap I))
              let evmTicSolm := Solm.EVM.storageStore evmBidSolm
                evmBidSolm.executionEnv.codeOwner (bidPackedSlotOfWord (tendId I))
                (setUint48Offset20Word
                  (Solm.EVM.storageLoad evmBidSolm evmBidSolm.executionEnv.codeOwner
                    (bidPackedSlotOfWord (tendId I)))
                  (tendTicNewWord evmBidSolm.accountMap I))
              have hbody :
                  ExecTransitionBody config contract evm0Solm (tendLocals I)
                    tendTransition.body
                    (.returned
                      { contract := contract,
                        locals :=
                          tendLocalsAfterRefundWithTicFrom σ_solm evmBidSolm.accountMap I }
                      evmTicSolm none) := by
                simpa [evm0Solm, evmGuySolm, evmBidSolm, evmTicSolm] using
                  (flipperTendSourceBodySuccessAfterRefund
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g) (evmRefund := evmRefundSolm)
                    (evmPay := evmPaySolm) (outRefund := outRefund) (outPay := outPay)
                    hwv hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid
                    hfitBeg hinc hcallerSolm hrefundCodeSolm hcallRefundSolmTrue
                    hpayCodeSolm hcallPaySolmTrue
                    (by simp [evmPaySolm, evmGuySolm, evmRefundSolm, evm0Solm, initState,
                      storageStore_executionEnv])
                    (by simp [evmPaySolm, evmGuySolm, evmRefundSolm, evm0Solm, initState,
                      storageStore_executionEnv]) hfitTicSolm)
              have hpackedLoadEq :
                  Solm.EVM.storageLoad evmBidEvm evmBidEvm.executionEnv.codeOwner
                      (bidPackedSlotOfWord (tendId I)) =
                    Solm.EVM.storageLoad evmBidSolm evmBidSolm.executionEnv.codeOwner
                      (bidPackedSlotOfWord (tendId I)) :=
                hBidStateEquiv.storageLoad_codeOwner (bidPackedSlotOfWord (tendId I))
              have hticNewEq :
                  tendTicNewWord evmBidEvm.accountMap I =
                    tendTicNewWord evmBidSolm.accountMap I := by
                simp [tendTicNewWord, httlEq]
              have hstoredTicEq :
                  setUint48Offset20Word
                      (Solm.EVM.storageLoad evmBidEvm evmBidEvm.executionEnv.codeOwner
                        (bidPackedSlotOfWord (tendId I)))
                      (tendTicNewWord evmBidEvm.accountMap I) =
                    setUint48Offset20Word
                      (Solm.EVM.storageLoad evmBidSolm evmBidSolm.executionEnv.codeOwner
                        (bidPackedSlotOfWord (tendId I)))
                      (tendTicNewWord evmBidSolm.accountMap I) := by
                rw [hpackedLoadEq, hticNewEq]
              have hTicStateEquiv : EVMStateEquiv evmTicEvm evmTicSolm := by
                simpa [evmTicEvm, evmTicSolm] using
                  EVMStateEquiv.storageStore_codeOwner hBidStateEquiv
                    (bidPackedSlotOfWord (tendId I)) hstoredTicEq
              have hAccountsRet :
                  accountMapEquiv (tendStoreTicMap (tendAfterBidMap σ_pay I) I)
                    evmTicEvm.accountMap := by
                have hownerBid : evmBidEvm.executionEnv.codeOwner = I.codeOwner := by
                  simp [evmBidEvm, evmPayEvm, evmGuyCallEvm, evm0Evm,
                    storageStore_executionEnv, initState]
                simpa [evmTicEvm, hmapBidEvm, hownerBid, tendStoreTicMap,
                  tendStoredTicWord, flipperSlotWord, solcSlotWord, Solm.EVM.storageLoad,
                  State.lookupAccount, Account.lookupStorage, storageStore_accountMap]
                  using accountMapEquiv_refl (tendStoreTicMap (tendAfterBidMap σ_pay I) I)
              have henc : returnEquiv ByteArray.empty none tendTransition.returnType := by
                rw [show tendTransition.returnType = [] by rfl]
                exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
              exact hret.reEquivExecutionGenEVMStateEquiv hcode hdispatch hdecode hbody
                (by simp [evmTicEvm, evmBidEvm, evmPayEvm, storageStore_createdAccounts])
                hAccountsRet hTicStateEquiv henc
            · have hoverTicEvm :
                  2 ^ 48 ≤
                    (tendNow48 I).toNat +
                      (tendTtlWord (tendAfterBidMap σ_pay I) I).toNat :=
                Nat.le_of_not_gt hfitTicEvm
              have hoverTicSolm :
                  2 ^ 48 ≤ (tendNow48 I).toNat +
                    (tendTtlWord evmBidSolm.accountMap I).toNat := by
                have httlSolmMap :
                    tendTtlWord evmBidSolm.accountMap I =
                      tendTtlWord (tendAfterBidMap σ_pay I) I := by
                  rw [← httlEq, httlEvmMap]
                simpa [httlSolmMap] using hoverTicEvm
              have hbody :
                  ExecTransitionBody config contract evm0Solm (tendLocals I)
                    tendTransition.body .reverted := by
                simpa [evm0Solm, evmGuySolm, evmBidSolm] using
                  (flipperTendSourceBodyAdd48OverflowAfterRefund
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g) (evmRefund := evmRefundSolm)
                    (evmPay := evmPaySolm) (outRefund := outRefund) (outPay := outPay)
                    hwv hguySolm hticGuard hendGuard hlotGuard htabGuard hbidGuard hfitBid
                    hfitBeg hinc hcallerSolm hrefundCodeSolm hcallRefundSolmTrue
                    hpayCodeSolm hcallPaySolmTrue
                    (by simp [evmPaySolm, evmGuySolm, evmRefundSolm, evm0Solm, initState,
                      storageStore_executionEnv])
                    (by simp [evmPaySolm, evmGuySolm, evmRefundSolm, evm0Solm, initState,
                      storageStore_executionEnv]) hoverTicSolm)
              exact (flipperTendX_add48Overflow hoverTicEvm rd6272)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Flipper
