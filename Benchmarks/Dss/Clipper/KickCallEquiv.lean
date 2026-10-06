import Benchmarks.Dss.Clipper.KickRevertEVM
import Benchmarks.Dss.Clipper.KickStateEquiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/-! State facts preserved while the compiler and source interpreter make the
three external calls used by `kick`'s `getFeedPrice` helper. -/

structure ClipperKickCallAligned (s0 : EVM.State) (σ : AccountMap)
    (I : ExecutionEnv) (evm : EVM.State) : Prop where
  accounts : σ = evm.accountMap
  originalAccounts : s0.σ₀ = evm.σ₀
  executionEnv : evm.executionEnv = I

theorem clipperKickCallAligned_transport {v : ClipperImmutables}
    {s0 evm : EVM.State} {σ σ' : AccountMap} {I : ExecutionEnv} {tgt : EVM.Address}
    {name : Ident} {value : ℤ} {args : List Value} {z : Bool}
    {out : ByteArray} {A' : Substate} {callPerm : Bool}
    (halign : ClipperKickCallAligned s0 σ I evm)
    (hcall : typedCallViaEVM (config v)
      {s0 with accountMap := σ, executionEnv := I}
      tgt name value args
      (z, { {s0 with accountMap := σ, executionEnv := I} with
            accountMap := σ', substate := A' }, out)
      callPerm) :
    ∃ (σSolm : AccountMap) (ASolm : Substate) (evm' : EVM.State),
      evm' = { evm with accountMap := σSolm, substate := ASolm } ∧
      typedCallViaEVM (config v) evm tgt name value args (z, evm', out) callPerm ∧
      ClipperKickCallAligned s0 σ' I evm' := by
  have hInputAccounts : ({s0 with accountMap := σ, executionEnv := I} : EVM.State).accountMap =
      evm.accountMap := by simpa using halign.accounts
  have hInputOriginal : ({s0 with accountMap := σ, executionEnv := I} : EVM.State).σ₀ =
      evm.σ₀ := by simpa using halign.originalAccounts
  have hInputEnv : ({s0 with accountMap := σ, executionEnv := I} : EVM.State).executionEnv =
      evm.executionEnv := by simpa [halign.executionEnv]
  obtain ⟨σSolm, ASolm, hcallSolm, hAccounts⟩ :=
    typedCallViaEVM_sameInputs hcall hInputAccounts hInputOriginal hInputEnv
  let evm' : EVM.State := { evm with accountMap := σSolm, substate := ASolm }
  refine ⟨σSolm, ASolm, evm', rfl, ?_, ?_⟩
  · simpa [evm'] using hcallSolm
  · exact ⟨by simpa [evm'] using hAccounts,
      halign.originalAccounts, halign.executionEnv⟩

theorem clipperKickSpotterAddress_eq_of_aligned
    {s0 evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (halign : ClipperKickCallAligned s0 σ I evm) :
    clipperGetFeedPriceSpotterAddress evm =
      AccountAddress.ofUInt256 (clipperSpotterTarget σ I) := by
  change AccountAddress.ofUInt256
    (clipperSpotterTarget evm.accountMap evm.executionEnv) = _
  rw [halign.executionEnv, ← halign.accounts]

theorem clipperKickNoCode_of_aligned
    {s0 evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {target : UInt256}
    {addr : AccountAddress}
    (halign : ClipperKickCallAligned s0 σ I evm)
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : extCodeSizeWord σ target = ⟨0⟩) :
    (UInt256.ofNat ((evm.lookupAccount addr).option 0
      (fun acc => acc.code.size))).toNat = 0 := by
  have hzeroEvm : extCodeSizeWord evm.accountMap target = ⟨0⟩ := by
    simpa only [← halign.accounts] using hzero
  simpa [State.lookupAccount] using
    extCodeSizeWord_zero_lookup_code_zero haddr hzeroEvm

theorem clipperKickHasCode_of_aligned
    {s0 evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {target : UInt256}
    {addr : AccountAddress}
    (halign : ClipperKickCallAligned s0 σ I evm)
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : extCodeSizeWord σ target ≠ ⟨0⟩) :
    0 < (UInt256.ofNat ((evm.lookupAccount addr).option 0
      (fun acc => acc.code.size))).toNat := by
  have hneEvm : extCodeSizeWord evm.accountMap target ≠ ⟨0⟩ := by
    simpa only [← halign.accounts] using hne
  simpa [State.lookupAccount] using
    extCodeSizeWord_ne_zero_lookup_code_pos haddr hneEvm

end Benchmarks.Dss.Clipper
