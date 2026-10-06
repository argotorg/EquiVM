import Benchmarks.Dss.DaiJoin.Dispatch
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

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

theorem daiJoinVatEvmAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    EVM.address (daiJoinVatAddress σ I) =
      AccountAddress.ofUInt256 (daiJoinVatTargetWord σ I) := by
  rw [daiJoinEvmAddress_accountAddress]
  exact daiJoinVatAddress_eq_target σ I

theorem daiJoinDaiEvmAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    EVM.address (daiJoinDaiAddress σ I) =
      AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ I) := by
  rw [daiJoinEvmAddress_accountAddress]
  exact daiJoinDaiAddress_eq_target σ I

theorem daiJoin_extCodeSizeWord_zero_lookup_code_zero {σ : AccountMap}
    {target : UInt256} {addr : AccountAddress}
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

theorem daiJoinCode_zero_of_codeSize_zero {evm : EVM.State} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : Reasoning.Theory.extCodeSizeWord evm.accountMap target = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount addr).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  simpa [State.lookupAccount] using
    daiJoin_extCodeSizeWord_zero_lookup_code_zero
      (σ := evm.accountMap) haddr hzero

theorem daiJoinCode_pos_of_codeSize_ne_zero {evm : EVM.State} {target : UInt256}
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
      native_decide
  exact hne (by rw [← hword, hwordZero])

theorem daiJoinVatCode_zero_of_codeSize_zero {evm : EVM.State}
    (hzero :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (daiJoinVatTargetWord evm.accountMap evm.executionEnv) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (daiJoinVatAddress evm.accountMap evm.executionEnv)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  exact daiJoinCode_zero_of_codeSize_zero
    (daiJoinVatAddress_eq_target evm.accountMap evm.executionEnv) hzero

theorem daiJoinVatCode_pos_of_codeSize_ne_zero {evm : EVM.State}
    (hne :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (daiJoinVatTargetWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩) :
    0 <
      (UInt256.ofNat
        ((evm.lookupAccount (daiJoinVatAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat := by
  exact daiJoinCode_pos_of_codeSize_ne_zero
    (daiJoinVatAddress_eq_target evm.accountMap evm.executionEnv) hne

theorem daiJoinDaiCode_zero_of_codeSize_zero {evm : EVM.State}
    (hzero :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (daiJoinDaiTargetWord evm.accountMap evm.executionEnv) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (daiJoinDaiAddress evm.accountMap evm.executionEnv)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  exact daiJoinCode_zero_of_codeSize_zero
    (daiJoinDaiAddress_eq_target evm.accountMap evm.executionEnv) hzero

theorem daiJoinDaiCode_pos_of_codeSize_ne_zero {evm : EVM.State}
    (hne :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
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
