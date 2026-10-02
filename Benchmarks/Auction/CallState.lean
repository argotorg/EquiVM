import Benchmarks.Auction.Storage
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: the source state paired with an RD cursor across external calls.
structure SourceState (s0 : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (evm : EVM.State) : Prop where
  world : RDWorld s0 evm
  env : evm.executionEnv = I
  accounts : σ = evm.accountMap

theorem SourceState.init {σ σ₀ A I g} :
    SourceState (initState σ σ₀ g A I) I σ (initState σ σ₀ g A I) :=
  ⟨rfl, rfl, rfl⟩

-- LIBRARY CANDIDATE: read and update a storage word through the source/RD relation.
theorem SourceState.storageRead {s0 I σ evm} (hs : SourceState s0 I σ evm)
    (slot : UInt256) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot = storedWord σ I slot := by
  simp [storedWord, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    ← hs.accounts, hs.env]

def callState (evm : EVM.State) (σ : AccountMap) : EVM.State :=
  { evm with accountMap := σ }

theorem SourceState.callTransport {s0 I σ evm} (hs : SourceState s0 I σ evm)
    {target : EVM.Address} {value : Int} {calldata : ByteArray}
    {z : Bool} {evm' : EVM.State} {out : ByteArray}
    (hcall : callViaEVM (callState evm σ) target value calldata (z, evm', out)) :
    ∃ evmS', callViaEVM evm target value calldata (z, evmS', out) ∧
      SourceState s0 I evm'.accountMap evmS' := by
  obtain ⟨σS', AS', hcallS, haccounts⟩ := callViaEVM_accountMapEquiv
    (evm_solm := evm) hcall hs.accounts rfl rfl
  exact ⟨_, hcallS, ⟨hs.world, hs.env, haccounts⟩⟩

theorem callStateMade {s0 I σ evm} (hs : SourceState s0 I σ evm)
    {target value : UInt256} {calldata : ByteArray}
    {σ' : AccountMap} {gasLeft callGas : UInt256} {AS' AIn : Substate} {z : Bool} {out : ByteArray}
    (hperm : I.perm = true)
    (hbalance : value ≤ (σ.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024)
    (hΘ : (σ', gasLeft, AS', z, out) = Θ σ s0.σ₀ AIn
      (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
      (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
      callGas (UInt256.ofNat I.gasPrice) value value calldata (I.depth + 1) I.header
      I.blobVersionedHashes I.blocks I.perm) :
    callViaEVM (callState evm σ) (AccountAddress.ofUInt256 target) (Int.ofNat value.toNat)
      calldata (z,
        { callState evm σ with
          accountMap := σ'
          substate := AS' }, out) := by
  apply callViaEVM.callMade (valueWord := value) (g' := gasLeft) (A' := AS')
    (wordOfInt_ofNat_toNat value).symm ?_ rfl ?_ ?_
  · refine ⟨callGas, AIn, ?_⟩
    simp only [callState, hs.env]
    rw [hs.world]
    simpa only [accountAddress_roundtrip, hperm] using hΘ
  · simpa only [callState, hs.env] using hbalance
  · simp only [callState, hs.env]
    intro hd
    have hval := congrArg Fin.val hd
    change I.depth.val = 1024 at hval
    omega

theorem callStateNotMade {s0 I σ evm} (hs : SourceState s0 I σ evm)
    {target value : UInt256} {calldata : ByteArray}
    (hn : ¬ (value ≤ (σ.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)) ∧ I.depth ≠ 1024)) :
    callViaEVM (callState evm σ) (AccountAddress.ofUInt256 target) (Int.ofNat value.toNat)
      calldata (false,
        { callState evm σ with substate :=
          ((callState evm σ).addAccessedAccount (AccountAddress.ofUInt256 target)).substate },
        ByteArray.empty) := by
  apply callViaEVM.callNotMade rfl rfl
  simpa only [callState, hs.env, wordOfInt_ofNat_toNat] using hn

end Auction
