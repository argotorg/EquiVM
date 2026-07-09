import Benchmarks.Dss.DaiJoin.Dispatch
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.DaiJoin

/-! Shared target-address and code-size facts for DaiJoin external calls. -/

abbrev daiJoinVatTargetWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  daiJoinAddressReturnWord ⟨1⟩ σ I

abbrev daiJoinVatAddress (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (daiJoinVatTargetWord σ I).toNat

abbrev daiJoinDaiTargetWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  daiJoinAddressReturnWord ⟨2⟩ σ I

abbrev daiJoinDaiAddress (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (daiJoinDaiTargetWord σ I).toNat

theorem daiJoinVatTargetWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    daiJoinVatTargetWord σ I = daiJoinVatTargetWord τ I := by
  have hslot : daiJoinSlotWord ⟨1⟩ σ I = daiJoinSlotWord ⟨1⟩ τ I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  simp [daiJoinVatTargetWord, daiJoinAddressReturnWord, hslot]

theorem daiJoinDaiTargetWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    daiJoinDaiTargetWord σ I = daiJoinDaiTargetWord τ I := by
  have hslot : daiJoinSlotWord ⟨2⟩ σ I = daiJoinSlotWord ⟨2⟩ τ I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  simp [daiJoinDaiTargetWord, daiJoinAddressReturnWord, hslot]

theorem daiJoinVatAddress_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    daiJoinVatAddress σ I = daiJoinVatAddress τ I := by
  apply Fin.ext
  simp [daiJoinVatAddress, daiJoinVatTargetWord_accountMapEquiv hAccounts]

theorem daiJoinDaiAddress_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    daiJoinDaiAddress σ I = daiJoinDaiAddress τ I := by
  apply Fin.ext
  simp [daiJoinDaiAddress, daiJoinDaiTargetWord_accountMapEquiv hAccounts]

theorem daiJoinVatCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (daiJoinVatTargetWord σ I) = ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (daiJoinVatTargetWord τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (daiJoinVatTargetWord σ I)
  have htarget : daiJoinVatTargetWord σ I = daiJoinVatTargetWord τ I :=
    daiJoinVatTargetWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem daiJoinVatCodeSize_ne_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (daiJoinVatTargetWord σ I) ≠ ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (daiJoinVatTargetWord τ I) ≠ ⟨0⟩ := by
  intro hzero
  exact hne (daiJoinVatCodeSize_zero_accountMapEquiv hAccounts.symm hzero)

theorem daiJoinDaiCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (daiJoinDaiTargetWord σ I) = ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (daiJoinDaiTargetWord τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
      (daiJoinDaiTargetWord σ I)
  have htarget : daiJoinDaiTargetWord σ I = daiJoinDaiTargetWord τ I :=
    daiJoinDaiTargetWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem daiJoinDaiCodeSize_ne_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (daiJoinDaiTargetWord σ I) ≠ ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (daiJoinDaiTargetWord τ I) ≠ ⟨0⟩ := by
  intro hzero
  exact hne (daiJoinDaiCodeSize_zero_accountMapEquiv hAccounts.symm hzero)

theorem daiJoinAddress_eq_target (word : UInt256) :
    AccountAddress.ofNat word.toNat = AccountAddress.ofUInt256 word := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]

theorem daiJoinVatAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    daiJoinVatAddress σ I = AccountAddress.ofUInt256 (daiJoinVatTargetWord σ I) := by
  exact daiJoinAddress_eq_target _

theorem daiJoinDaiAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    daiJoinDaiAddress σ I = AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ I) := by
  exact daiJoinAddress_eq_target _

theorem daiJoinEvmAddress_accountAddress (a : AccountAddress) :
    EVM.address a.val = a := by
  apply Fin.ext
  show a.val % EVM.addressModulus = a.val
  rw [show EVM.addressModulus = AccountAddress.size from by decide]
  exact Nat.mod_eq_of_lt a.isLt

theorem daiJoinVatEvmAddress_eq_target_of_accountMapEquiv {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    EVM.address (daiJoinVatAddress σ_solm I) =
      AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I) := by
  have haddr : daiJoinVatAddress σ_solm I = daiJoinVatAddress σ_evm I :=
    (daiJoinVatAddress_accountMapEquiv hAccounts).symm
  rw [haddr, daiJoinVatAddress_eq_target σ_evm I]
  exact daiJoinEvmAddress_accountAddress _

theorem daiJoinDaiEvmAddress_eq_target_of_accountMapEquiv {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    EVM.address (daiJoinDaiAddress σ_solm I) =
      AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ_evm I) := by
  have haddr : daiJoinDaiAddress σ_solm I = daiJoinDaiAddress σ_evm I :=
    (daiJoinDaiAddress_accountMapEquiv hAccounts).symm
  rw [haddr, daiJoinDaiAddress_eq_target σ_evm I]
  exact daiJoinEvmAddress_accountAddress _

theorem daiJoin_uniswapExtCodeSizeWord_zero_lookup_code_zero {σ : AccountMap}
    {target : UInt256} {addr : AccountAddress}
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

theorem daiJoinCode_zero_of_codeSize_zero {evm : EVM.State} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap target = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount addr).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  simpa [State.lookupAccount] using
    daiJoin_uniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := evm.accountMap) haddr hzero

theorem daiJoinCode_pos_of_codeSize_ne_zero {evm : EVM.State} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap target ≠ ⟨0⟩) :
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
        Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap target := by
    subst addr
    cases hacc : evm.accountMap.find? (AccountAddress.ofUInt256 target) <;>
      simp [State.lookupAccount, Reasoning.Theory.uniswapExtCodeSizeWord, hacc,
        Option.option] <;>
      native_decide
  exact hne (by rw [← hword, hwordZero])

theorem daiJoinVatCode_zero_of_codeSize_zero {evm : EVM.State}
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (daiJoinVatTargetWord evm.accountMap evm.executionEnv) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (daiJoinVatAddress evm.accountMap evm.executionEnv)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  exact daiJoinCode_zero_of_codeSize_zero
    (daiJoinVatAddress_eq_target evm.accountMap evm.executionEnv) hzero

theorem daiJoinVatCode_pos_of_codeSize_ne_zero {evm : EVM.State}
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (daiJoinVatTargetWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩) :
    0 <
      (UInt256.ofNat
        ((evm.lookupAccount (daiJoinVatAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat := by
  exact daiJoinCode_pos_of_codeSize_ne_zero
    (daiJoinVatAddress_eq_target evm.accountMap evm.executionEnv) hne

theorem daiJoinDaiCode_zero_of_codeSize_zero {evm : EVM.State}
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (daiJoinDaiTargetWord evm.accountMap evm.executionEnv) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (daiJoinDaiAddress evm.accountMap evm.executionEnv)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  exact daiJoinCode_zero_of_codeSize_zero
    (daiJoinDaiAddress_eq_target evm.accountMap evm.executionEnv) hzero

theorem daiJoinDaiCode_pos_of_codeSize_ne_zero {evm : EVM.State}
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (daiJoinDaiTargetWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩) :
    0 <
      (UInt256.ofNat
        ((evm.lookupAccount (daiJoinDaiAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat := by
  exact daiJoinCode_pos_of_codeSize_ne_zero
    (daiJoinDaiAddress_eq_target evm.accountMap evm.executionEnv) hne

theorem daiJoin_typedCallViaEVM_zero_substate_irrel {cfg : Config} {evm evm' : EVM.State}
    {A0 : Substate} {tgt : EVM.Address} {name : Ident} {args : List Value}
    {z : Bool} {out : ByteArray} {callPerm : Bool}
    (hcall : typedCallViaEVM cfg { evm with substate := A0 } tgt name 0 args
      (z, evm', out) callPerm)
    (hdepth : evm.executionEnv.depth ≠ 1024) :
    typedCallViaEVM cfg evm tgt name 0 args (z, evm', out) callPerm := by
  rcases hcall with ⟨calldata, henc, hraw⟩
  refine ⟨calldata, henc, ?_⟩
  cases hraw with
  | callMade hvalue hTheta hevm' hvalue' hdepth' =>
      obtain ⟨callGas, A_in, hTheta⟩ := hTheta
      exact callViaEVM.callMade (perm := callPerm) hvalue
        ⟨callGas, A_in, by simpa using hTheta⟩
        (by simpa using hevm')
        (by simpa using hvalue')
        (by simpa using hdepth')
  | callNotMade _hsubstate _hevm' hvalue =>
      exfalso
      apply hvalue
      constructor
      · rw [wordOfInt_zero]
        show (⟨0⟩ : UInt256) ≤ _
        exact Fin.zero_le _
      · exact hdepth

end Benchmarks.Dss.DaiJoin
