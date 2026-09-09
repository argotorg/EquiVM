import Benchmarks.WETH9.WithdrawBody

/-! # WETH9 `withdraw(uint256)` refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.WETH9

/-- Equivalent account maps have equal balances at every address. -/
private theorem weth9AccountMapEquiv_balance {σ τ : AccountMap} (h : accountMapEquiv σ τ)
    (addr : AccountAddress) :
    (σ.find? addr |>.elim ⟨0⟩ (·.balance)) = (τ.find? addr |>.elim ⟨0⟩ (·.balance)) := by
  have ha := h addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;> simp_all [accountEquiv]

/-- `withdraw(uint256 wad)` refines its Solm transition.  Non-payable; requires
    `balanceOf[caller] ≥ wad`, decrements it, and forwards `wad` to `caller` via an external `CALL`,
    reverting if the transfer fails. -/
theorem weth9WithdrawBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I (weth9SelBytes 4))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (weth9SelBytes 4) (by decide +native) hsel
  have hdisp := weth9SelectorDispatchWithdraw hsel
  -- shared balance-word equality
  have hbaleq : solcSlotWord σ_evm I (callerBalSlot I) = solcSlotWord σ_solm I (callerBalSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (callerBalSlot I) ⟨0⟩
  set gs := Sat256.ofUInt256 g with hgs
  set evmS := initState cA gh bl σ_solm σ₀ gs A I with hevmS
  -- Solm-side facts, reused across the call branches
  have hsrcS : evmS.executionEnv = I := rfl
  have hwvS' : evmS.executionEnv.weiValue = I.weiValue := rfl
  have hstoreLoadS : Solm.EVM.storageLoad evmS I.codeOwner (callerBalSlot I)
      = solcSlotWord σ_solm I (callerBalSlot I) := by
    simp [evmS, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, initState,
      Ethereum.Account.lookupStorage]
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz36 : 36 ≤ I.calldata.size
    · -- decode succeeds; reach the body
      have hdec := weth9Decode_withdraw_ok hsz36
      obtain ⟨_, _, h1395⟩ := weth9WithdrawReachBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
        (σ₀ := σ₀) (A := A) (g := gs) hcode hwv hsz36 hsize hsel
      by_cases hle : (withdrawWadWord I).toNat ≤ (solcSlotWord σ_evm I (callerBalSlot I)).toNat
      · -- `balanceOf[caller] ≥ wad`: store + external call
        have hleS : (withdrawWadWord I).toNat ≤ (solcSlotWord σ_solm I (callerBalSlot I)).toNat := by
          rw [← hbaleq]; exact hle
        have hleLoadS : (withdrawWadWord I).toNat ≤
            (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner (callerBalSlot I)).toNat := by
          rw [show evmS.executionEnv.codeOwner = I.codeOwner from rfl, hstoreLoadS]; exact hleS
        set evmSZero := withdrawStoreState evmS I with hevmSZero
        -- store-map equivalence
        have hStoreMap : accountMapEquiv (withdrawStoreMap σ_evm I) evmSZero.accountMap := by
          rw [hevmSZero, withdrawStoreState_accountMap]
          have : withdrawStoreMap σ_evm I =
              sstoreAccountMap I.codeOwner σ_evm (callerBalSlot I)
                (UInt256.sub (solcSlotWord σ_solm I (callerBalSlot I)) (withdrawWadWord I)) := by
            rw [show withdrawStoreMap σ_evm I =
              sstoreAccountMap I.codeOwner σ_evm (callerBalSlot I)
                (UInt256.sub (solcSlotWord σ_evm I (callerBalSlot I)) (withdrawWadWord I)) from rfl,
              hbaleq]
          rw [this]
          exact accountMapEquiv_sstoreAccountMap I.codeOwner (callerBalSlot I) _ hAccounts
        -- the source's transfer target and value
        have hAddressId (a : AccountAddress) : EVM.address a = a := by
          apply Fin.ext; simp [EVM.address, EVM.uintN]; exact Nat.mod_eq_of_lt a.isLt
        have hZeroEnv : evmSZero.executionEnv = I := by
          rw [hevmSZero, withdrawStoreState_executionEnv]; exact hsrcS
        have hTargetEq : EVM.address evmSZero.executionEnv.source
            = AccountAddress.ofUInt256 (solcSourceWord I) := by
          rw [hZeroEnv, hAddressId,
            show AccountAddress.ofUInt256 (solcSourceWord I) = I.source from by
              unfold solcSourceWord; exact accountAddress_roundtrip I.source]
        by_cases hdepthEq : I.depth = 1024
        · -- depth limit: the call fails, `require(success)` reverts
          have hrev := weth9WithdrawCallDepthRev (g := gs) hperm hle hdepthEq h1395
          set evmSFail : EVM.State := { evmSZero with
            substate := (evmSZero.addAccessedAccount
              (EVM.address evmSZero.executionEnv.source)).substate } with hevmSFail
          have hcall : callViaEVM evmSZero (EVM.address evmSZero.executionEnv.source)
              (Int.ofNat (withdrawWadWord I).toNat) ByteArray.empty
              (false, evmSFail, ByteArray.empty) := by
            apply callViaEVM.callNotMade rfl rfl
            rintro ⟨_, hdepthNe⟩
            exact hdepthNe (by rw [hZeroEnv]; exact hdepthEq)
          have hbody := weth9WithdrawBodyReverts_callFailure evmS evmSFail I ByteArray.empty
            hsrcS (by rw [hwvS']; exact hwv) hleLoadS (by rw [← hevmSZero]; exact hcall)
          exact weth9ReEquivExecRev hcode hrev hdisp hdec hbody
        · have hdepthLt : I.depth.val < 1024 :=
            lt_of_le_of_ne (Nat.le_of_lt_succ I.depth.isLt) (fun h => hdepthEq (Fin.ext h))
          by_cases hbalance : withdrawWadWord I ≤
              ((withdrawStoreMap σ_evm I).find? I.codeOwner |>.elim ⟨0⟩ (·.balance))
          · -- call is dispatched
            obtain ⟨cA', σ', z, o, A_in, callGas, ⟨g'', A', hΘeq⟩, hosz, _, _, rd1470⟩ :=
              weth9WithdrawCallMade (g := gs) hperm hle hbalance hdepthLt h1395
            set evmEZero : EVM.State :=
              { initState cA gh bl σ_evm σ₀ gs A I with accountMap := withdrawStoreMap σ_evm I }
              with hevmEZero
            set evmECall : EVM.State :=
              { evmEZero with accountMap := σ', substate := A', createdAccounts := cA' }
              with hevmECall
            have hcallE : callViaEVM evmEZero (AccountAddress.ofUInt256 (solcSourceWord I))
                (Int.ofNat (withdrawWadWord I).toNat) ByteArray.empty (z, evmECall, o) := by
              refine callViaEVM.callMade
                (valueWord := withdrawWadWord I) (cA' := cA') (σ' := σ') (g' := g'') (A' := A')
                (wordOfInt_ofNat_toNat (withdrawWadWord I)).symm ⟨callGas, A_in, ?_⟩ (by rw [hevmECall])
                (by rw [hevmEZero]; exact hbalance)
                (by rw [hevmEZero]; simp only [initState]; exact hdepthEq)
              rw [hevmEZero]
              simpa [initState, accountAddress_roundtrip, hperm] using hΘeq
            obtain ⟨σ'_solm, A'_solm, hcallSRaw, hPostAccounts⟩ :=
              callViaEVM_accountMapEquiv (storage := config.storage) (evm_solm := evmSZero) hcallE
                (by simpa [hevmEZero] using hStoreMap)
                (by simp [hevmEZero, hevmSZero, hevmS, withdrawStoreState_originalMap, initState])
                (by simp [hevmEZero, hevmSZero, hevmS, withdrawStoreState_createdAccounts, initState])
                (by simp [hevmEZero, hevmSZero, hevmS, withdrawStoreState_genesisBlockHeader,
                  initState])
                (by simp [hevmEZero, hevmSZero, hevmS, withdrawStoreState_blocks, initState])
                (by simp [hevmEZero, hevmSZero, hevmS, withdrawStoreState_substate, initState])
                (by rw [hevmEZero, hZeroEnv]; rfl)
            set evmSCall : EVM.State :=
              { evmSZero with accountMap := σ'_solm, substate := A'_solm, createdAccounts := evmECall.createdAccounts }
              with hevmSCall
            have hcallS : callViaEVM evmSZero (EVM.address evmSZero.executionEnv.source)
                (Int.ofNat (withdrawWadWord I).toNat) ByteArray.empty (z, evmSCall, o) := by
              rw [hTargetEq]; exact hcallSRaw
            cases z
            · -- call failed: revert
              have hbody := weth9WithdrawBodyReverts_callFailure evmS evmSCall I o
                hsrcS (by rw [hwvS']; exact hwv) hleLoadS (by rw [← hevmSZero]; exact hcallS)
              exact weth9ReEquivExecRev hcode (weth9WithdrawFailureTail hosz rd1470) hdisp hdec hbody
            · -- call succeeded: return
              have hbody := weth9WithdrawBodyReturns_success evmS evmSCall I o
                hsrcS (by rw [hwvS']; exact hwv) hleLoadS (by rw [← hevmSZero]; exact hcallS)
              refine weth9ReEquivExecGen hcode (weth9WithdrawSuccessTail hperm rd1470) hdisp hdec
                hbody ?_ ?_ (returnEquiv.fallthrough (dvs := []) rfl rfl (by decide +native))
              · simp only [hevmSCall, hevmECall]
              · simpa [hevmSCall, hevmECall] using hPostAccounts
          · -- insufficient balance: the call fails, `require(success)` reverts
            have hrev := weth9WithdrawCallInsufficientRev (g := gs) hperm hle hbalance hdepthLt h1395
            set evmSFail : EVM.State := { evmSZero with
              substate := (evmSZero.addAccessedAccount
                (EVM.address evmSZero.executionEnv.source)).substate } with hevmSFail
            have hBalEq : ((withdrawStoreMap σ_evm I).find? I.codeOwner |>.elim ⟨0⟩ (·.balance))
                = (evmSZero.accountMap.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)) :=
              weth9AccountMapEquiv_balance hStoreMap I.codeOwner
            have hcall : callViaEVM evmSZero (EVM.address evmSZero.executionEnv.source)
                (Int.ofNat (withdrawWadWord I).toNat) ByteArray.empty
                (false, evmSFail, ByteArray.empty) := by
              apply callViaEVM.callNotMade rfl rfl
              rintro ⟨hvalueBal, _⟩
              rw [wordOfInt_ofNat_toNat, show evmSZero.executionEnv.codeOwner = I.codeOwner from by
                rw [hZeroEnv]] at hvalueBal
              exact hbalance (by rw [hBalEq]; exact hvalueBal)
            have hbody := weth9WithdrawBodyReverts_callFailure evmS evmSFail I ByteArray.empty
              hsrcS (by rw [hwvS']; exact hwv) hleLoadS (by rw [← hevmSZero]; exact hcall)
            exact weth9ReEquivExecRev hcode hrev hdisp hdec hbody
      · -- `balanceOf[caller] < wad`: `require` reverts
        have hlt : (solcSlotWord σ_evm I (callerBalSlot I)).toNat < (withdrawWadWord I).toNat := by
          omega
        have hltS : (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner (callerBalSlot I)).toNat
            < (withdrawWadWord I).toNat := by
          rw [show evmS.executionEnv.codeOwner = I.codeOwner from rfl, hstoreLoadS, ← hbaleq]
          exact hlt
        have hrev := weth9WithdrawRequireRev hlt h1395
        have hbody := weth9WithdrawBodyReverts_geFalse evmS I hsrcS (by rw [hwvS']; exact hwv) hltS
        exact weth9ReEquivExecRev hcode hrev hdisp hdec hbody
    · -- calldata too short: decode reverts
      have hshort : I.calldata.size < 36 := by omega
      exact weth9ReEquivDecodeFailed hcode
        (weth9WithdrawDecodeRev (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
          (g := gs) hcode hwv hsz4 hshort hsize hsel)
        hdisp (weth9Decode_withdraw_none_short hsz4 hshort)
  · -- non-zero callvalue: the non-payable guard reverts
    exact weth9NonpayableRevert hcode
      (weth9WithdrawGuardRev (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (g := gs) hcode hwv hsz4 hsize hsel)
      hdisp (fun callargs _ => bodyReverts_nonPayable (by rw [hwvS']; exact hwv))

end Benchmarks.WETH9
