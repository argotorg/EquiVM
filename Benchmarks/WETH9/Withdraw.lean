import Benchmarks.WETH9.WithdrawBody

/-! # WETH9 `withdraw(uint256)` refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.WETH9

/-- `withdraw(uint256 wad)` refines its Solm transition.  Non-payable; requires
    `balanceOf[caller] ≥ wad`, decrements it, and forwards `wad` to `caller` via an external `CALL`,
    reverting if the transfer fails. -/
theorem weth9WithdrawBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I (weth9SelBytes 4)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (weth9SelBytes 4) (by native_decide) hsel
  have hdisp := weth9SelectorDispatchWithdraw hsel
  set gs := Sat256.ofUInt256 g with hgs
  set evmS := initState σ σ₀ gs A I with hevmS
  -- Solm-side facts, reused across the call branches
  have hsrcS : evmS.executionEnv = I := rfl
  have hwvS' : evmS.executionEnv.weiValue = I.weiValue := rfl
  have hstoreLoadS : Solm.EVM.storageLoad evmS I.codeOwner (callerBalSlot I)
      = solcSlotWord σ I (callerBalSlot I) := by
    simp [evmS, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, initState,
      Ethereum.Account.lookupStorage]
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz36 : 36 ≤ I.calldata.size
    · -- decode succeeds; reach the body
      have hdec := weth9Decode_withdraw_ok hsz36
      obtain ⟨_, _, h1395⟩ := weth9WithdrawReachBody (σ := σ)
        (σ₀ := σ₀) (A := A) (g := gs) hcode hwv hsz36 hsize hsel
      by_cases hle : (withdrawWadWord I).toNat ≤ (solcSlotWord σ I (callerBalSlot I)).toNat
      · -- `balanceOf[caller] ≥ wad`: store + external call
        have hleLoadS : (withdrawWadWord I).toNat ≤
            (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner (callerBalSlot I)).toNat := by
          rw [show evmS.executionEnv.codeOwner = I.codeOwner from rfl, hstoreLoadS]; exact hle
        set evmSZero := withdrawStoreState evmS I with hevmSZero
        have hStoreMap : withdrawStoreMap σ I = evmSZero.accountMap := by
          simpa [hevmSZero, withdrawStoreMap] using
            (withdrawStoreState_accountMap (σ := σ) (σ₀ := σ₀) (A := A)
              (I := I) (g := gs)).symm
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
              ((withdrawStoreMap σ I).get? I.codeOwner |>.elim ⟨0⟩ (·.balance))
          · -- call is dispatched
            obtain ⟨σ', z, o, A_in, callGas, ⟨g'', A', hΘeq⟩, hosz, _, _, rd1470⟩ :=
              weth9WithdrawCallMade (g := gs) hperm hle hbalance hdepthLt h1395
            set evmEZero : EVM.State :=
              { initState σ σ₀ gs A I with accountMap := withdrawStoreMap σ I }
              with hevmEZero
            set evmECall : EVM.State :=
              { evmEZero with accountMap := σ', substate := A' }
              with hevmECall
            have hcallE : callViaEVM evmEZero (AccountAddress.ofUInt256 (solcSourceWord I))
                (Int.ofNat (withdrawWadWord I).toNat) ByteArray.empty (z, evmECall, o) := by
              refine callViaEVM.callMade
                (valueWord := withdrawWadWord I) (σ' := σ') (g' := g'') (A' := A')
                (wordOfInt_ofNat_toNat (withdrawWadWord I)).symm ⟨callGas, A_in, ?_⟩ (by rw [hevmECall])
                (by rw [hevmEZero]; exact hbalance)
                (by rw [hevmEZero]; simp only [initState]; exact hdepthEq)
              rw [hevmEZero]
              simpa [initState, accountAddress_roundtrip, hperm] using hΘeq
            have hZeroState : evmEZero = evmSZero := by
              have hMap : evmEZero.accountMap = evmSZero.accountMap := by
                simpa [hevmEZero] using hStoreMap
              calc
                evmEZero = {evmS with accountMap := evmEZero.accountMap} := by
                  simp [hevmEZero, hevmS]
                _ = {evmS with accountMap := evmSZero.accountMap} := by
                  exact congrArg (fun accounts => {evmS with accountMap := accounts}) hMap
                _ = evmSZero := by
                  rw [hevmSZero]
                  unfold withdrawStoreState Solm.EVM.storageStore
                  cases evmS.lookupAccount evmS.executionEnv.codeOwner <;>
                    simp [Option.option, State.setAccount]
            set evmSCall : EVM.State :=
              { evmSZero with accountMap := σ', substate := A' }
              with hevmSCall
            have hcallS : callViaEVM evmSZero (EVM.address evmSZero.executionEnv.source)
                (Int.ofNat (withdrawWadWord I).toNat) ByteArray.empty (z, evmSCall, o) := by
              rw [hTargetEq]
              simpa [← hZeroState, hevmSCall, hevmECall] using hcallE
            cases z
            · -- call failed: revert
              have hbody := weth9WithdrawBodyReverts_callFailure evmS evmSCall I o
                hsrcS (by rw [hwvS']; exact hwv) hleLoadS (by rw [← hevmSZero]; exact hcallS)
              exact weth9ReEquivExecRev hcode (weth9WithdrawFailureTail hosz rd1470) hdisp hdec hbody
            · -- call succeeded: return
              have hbody := weth9WithdrawBodyReturns_success evmS evmSCall I o
                hsrcS (by rw [hwvS']; exact hwv) hleLoadS (by rw [← hevmSZero]; exact hcallS)
              refine weth9ReEquivExecGen hcode (weth9WithdrawSuccessTail hperm rd1470) hdisp hdec
                hbody ?_ (returnEquiv.fallthrough (dvs := []) rfl rfl (by native_decide))
              simp [hevmSCall]
          · -- insufficient balance: the call fails, `require(success)` reverts
            have hrev := weth9WithdrawCallInsufficientRev (g := gs) hperm hle hbalance hdepthLt h1395
            set evmSFail : EVM.State := { evmSZero with
              substate := (evmSZero.addAccessedAccount
                (EVM.address evmSZero.executionEnv.source)).substate } with hevmSFail
            have hcall : callViaEVM evmSZero (EVM.address evmSZero.executionEnv.source)
                (Int.ofNat (withdrawWadWord I).toNat) ByteArray.empty
                (false, evmSFail, ByteArray.empty) := by
              apply callViaEVM.callNotMade rfl rfl
              rintro ⟨hvalueBal, _⟩
              rw [wordOfInt_ofNat_toNat, show evmSZero.executionEnv.codeOwner = I.codeOwner from by
                rw [hZeroEnv]] at hvalueBal
              exact hbalance (by rw [hStoreMap]; exact hvalueBal)
            have hbody := weth9WithdrawBodyReverts_callFailure evmS evmSFail I ByteArray.empty
              hsrcS (by rw [hwvS']; exact hwv) hleLoadS (by rw [← hevmSZero]; exact hcall)
            exact weth9ReEquivExecRev hcode hrev hdisp hdec hbody
      · -- `balanceOf[caller] < wad`: `require` reverts
        have hlt : (solcSlotWord σ I (callerBalSlot I)).toNat < (withdrawWadWord I).toNat := by
          omega
        have hltS : (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner (callerBalSlot I)).toNat
            < (withdrawWadWord I).toNat := by
          rw [show evmS.executionEnv.codeOwner = I.codeOwner from rfl, hstoreLoadS]
          exact hlt
        have hrev := weth9WithdrawRequireRev hlt h1395
        have hbody := weth9WithdrawBodyReverts_geFalse evmS I hsrcS (by rw [hwvS']; exact hwv) hltS
        exact weth9ReEquivExecRev hcode hrev hdisp hdec hbody
    · -- calldata too short: decode reverts
      have hshort : I.calldata.size < 36 := by omega
      exact weth9ReEquivDecodeFailed hcode
        (weth9WithdrawDecodeRev (σ := σ) (σ₀ := σ₀) (A := A)
          (g := gs) hcode hwv hsz4 hshort hsize hsel)
        hdisp (weth9Decode_withdraw_none_short hsz4 hshort)
  · -- non-zero callvalue: the non-payable guard reverts
    exact weth9NonpayableRevert hcode
      (weth9WithdrawGuardRev (σ := σ) (σ₀ := σ₀) (A := A)
        (g := gs) hcode hwv hsz4 hsize hsel)
      hdisp (fun callargs _ => bodyReverts_nonPayable (by rw [hwvS']; exact hwv))

end Benchmarks.WETH9
