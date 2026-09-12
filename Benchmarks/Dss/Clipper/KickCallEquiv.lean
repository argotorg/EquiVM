import Benchmarks.Dss.Clipper.KickRevertEVM
import Benchmarks.Dss.Clipper.KickStateEquiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

/-! State facts preserved while the compiler and source interpreter make the
three external calls used by `kick`'s `getFeedPrice` helper. -/

structure ClipperKickCallAligned (s0 : EVM.State)
    (cA : Batteries.RBSet AccountAddress compare) (σ : AccountMap)
    (I : ExecutionEnv) (evm : EVM.State) : Prop where
  accounts : accountMapEquiv σ evm.accountMap
  originalAccounts : s0.σ₀ = evm.σ₀
  createdAccounts : evm.createdAccounts = cA
  genesisBlockHeader : evm.genesisBlockHeader = s0.genesisBlockHeader
  blocks : evm.blocks = s0.blocks
  executionEnv : evm.executionEnv = I

theorem clipperKickCallAligned_transport {v : ClipperImmutables}
    {s0 evm : EVM.State} {cA cA' : Batteries.RBSet AccountAddress compare}
    {σ σ' : AccountMap} {I : ExecutionEnv} {tgt : EVM.Address}
    {name : Ident} {value : ℤ} {args : List Value} {z : Bool}
    {out : ByteArray} {A' : Substate} {callPerm : Bool}
    (halign : ClipperKickCallAligned s0 cA σ I evm)
    (hcall : typedCallViaEVM (config v)
      {s0 with accountMap := σ, createdAccounts := cA, executionEnv := I}
      tgt name value args
      (z,
        { {s0 with accountMap := σ, createdAccounts := cA, executionEnv := I} with
          accountMap := σ', substate := A', createdAccounts := cA' }, out)
      callPerm) :
    ∃ (σSolm : AccountMap) (ASolm : Substate) (evm' : EVM.State),
      evm' = { { { evm with accountMap := σSolm } with substate := ASolm } with
        createdAccounts := cA'} ∧
      typedCallViaEVM (config v) evm tgt name value args (z, evm', out) callPerm ∧
      ClipperKickCallAligned s0 cA' σ' I evm' := by
  obtain ⟨σSolm, ASolm, hcallSolm, hAccounts⟩ :=
    typedCallViaEVM_accountMapEquiv_noSubstate hcall halign.accounts
      (by simpa using halign.originalAccounts)
      (by simpa using halign.createdAccounts)
      (by simpa using halign.genesisBlockHeader)
      (by simpa using halign.blocks)
      (by simpa using halign.executionEnv)
  let evm' : EVM.State :=
    { { { evm with accountMap := σSolm } with substate := ASolm } with
      createdAccounts := cA'}
  refine ⟨σSolm, ASolm, evm', rfl, ?_, ?_⟩
  · simpa [evm'] using hcallSolm
  · exact
      { accounts := by simpa using hAccounts
        originalAccounts := halign.originalAccounts
        createdAccounts := rfl
        genesisBlockHeader := halign.genesisBlockHeader
        blocks := halign.blocks
        executionEnv := halign.executionEnv }

theorem clipperKickSpotterAddress_eq_of_aligned
    {s0 evm : EVM.State} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap} {I : ExecutionEnv}
    (halign : ClipperKickCallAligned s0 cA σ I evm) :
    clipperGetFeedPriceSpotterAddress evm =
      AccountAddress.ofUInt256 (clipperSpotterTarget σ I) := by
  have hslot := accountMapEquiv_storage_findD halign.accounts I.codeOwner ⟨3⟩ ⟨0⟩
  have hword : solcSlotWord σ I ⟨3⟩ =
      solcSlotWord evm.accountMap I ⟨3⟩ := by
    simpa [solcSlotWord] using hslot
  simp only [clipperGetFeedPriceSpotterAddress, clipperSpotterTarget]
  rw [halign.executionEnv, ← hword]

theorem clipperKickNoCode_of_aligned
    {s0 evm : EVM.State} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap} {I : ExecutionEnv} {target : UInt256}
    {addr : AccountAddress}
    (halign : ClipperKickCallAligned s0 cA σ I evm)
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : extCodeSizeWord σ target = ⟨0⟩) :
    (UInt256.ofNat ((evm.lookupAccount addr).option 0
      (fun acc => acc.code.size))).toNat = 0 := by
  simpa [State.lookupAccount] using
    clipperExtCodeSizeWord_zero_lookup_code_zero_of_accountMapEquiv
      halign.accounts haddr hzero

theorem clipperKickHasCode_of_aligned
    {s0 evm : EVM.State} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap} {I : ExecutionEnv} {target : UInt256}
    {addr : AccountAddress}
    (halign : ClipperKickCallAligned s0 cA σ I evm)
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : extCodeSizeWord σ target ≠ ⟨0⟩) :
    0 < (UInt256.ofNat ((evm.lookupAccount addr).option 0
      (fun acc => acc.code.size))).toNat := by
  simpa [State.lookupAccount] using
    clipperExtCodeSizeWord_ne_zero_lookup_code_pos_of_accountMapEquiv
      halign.accounts haddr hne

end Benchmarks.Dss.Clipper
