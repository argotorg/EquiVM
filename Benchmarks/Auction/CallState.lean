import Benchmarks.Auction.Storage
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: the source state paired with an RD cursor across external calls.
structure SourceState (s0 : EVM.State) (I : ExecutionEnv)
    (cA : Batteries.RBSet AccountAddress compare) (σ : AccountMap) (evm : EVM.State) : Prop where
  world : RDWorld s0 evm
  env : evm.executionEnv = I
  created : evm.createdAccounts = cA
  accounts : accountMapEquiv σ evm.accountMap

theorem SourceState.init {cA gh bl σ_evm σ_solm σ₀ A I g}
    (h : accountMapEquiv σ_evm σ_solm) :
    SourceState (initState cA gh bl σ_evm σ₀ g A I) I cA σ_evm
      (initState cA gh bl σ_solm σ₀ g A I) :=
  ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, h⟩

-- LIBRARY CANDIDATE: read and update a storage word through the source/RD relation.
theorem SourceState.storageRead {s0 I cA σ evm} (hs : SourceState s0 I cA σ evm)
    (slot : UInt256) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot = storedWord σ I slot := by
  rw [storedWord_equiv hs.accounts, ← hs.env]
  rfl

def callState (evm : EVM.State) (cA : Batteries.RBSet AccountAddress compare) (σ : AccountMap) :
    EVM.State :=
  { evm with accountMap := σ, createdAccounts := cA }

theorem SourceState.callTransport {s0 I cA σ evm} (hs : SourceState s0 I cA σ evm)
    {target : EVM.Address} {value : Int} {calldata : ByteArray}
    {z : Bool} {evm' : EVM.State} {out : ByteArray}
    (hcall : callViaEVM (callState evm cA σ) target value calldata (z, evm', out)) :
    ∃ evmS', callViaEVM evm target value calldata (z, evmS', out) ∧
      SourceState s0 I evm'.createdAccounts evm'.accountMap evmS' := by
  obtain ⟨σS', AS', hcallS, haccounts⟩ := callViaEVM_accountMapEquiv
    (storage := auctionConfig.storage) (evm_solm := evm) hcall hs.accounts rfl hs.created
    rfl rfl rfl rfl
  exact ⟨_, hcallS, ⟨hs.world, hs.env, rfl, haccounts⟩⟩

theorem callStateMade {s0 I cA σ evm} (hs : SourceState s0 I cA σ evm)
    {target value : UInt256} {calldata : ByteArray} {cA' : Batteries.RBSet AccountAddress compare}
    {σ' : AccountMap} {gasLeft callGas : UInt256} {AS' AIn : Substate} {z : Bool} {out : ByteArray}
    (hperm : I.perm = true)
    (hbalance : value ≤ (σ.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024)
    (hΘ : (cA', σ', gasLeft, AS', z, out) = Θ I.blobVersionedHashes cA
      s0.genesisBlockHeader s0.blocks σ s0.σ₀ AIn
      (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
      (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
      callGas (UInt256.ofNat I.gasPrice) value value calldata (I.depth + 1) I.header I.perm) :
    callViaEVM (callState evm cA σ) (AccountAddress.ofUInt256 target) (Int.ofNat value.toNat)
      calldata (z,
        { callState evm cA σ with
          accountMap := σ'
          substate := AS'
          createdAccounts := cA' }, out) := by
  apply callViaEVM.callMade (valueWord := value) (g' := gasLeft) (A' := AS')
    (wordOfInt_ofNat_toNat value).symm ?_ rfl ?_ ?_
  · refine ⟨callGas, AIn, ?_⟩
    simp only [callState, hs.env, hs.world.1, hs.world.2.1, hs.world.2.2]
    simpa only [accountAddress_roundtrip, hperm] using hΘ
  · simpa only [callState, hs.env] using hbalance
  · simp only [callState, hs.env]
    intro hd
    have hval := congrArg Fin.val hd
    change I.depth.val = 1024 at hval
    omega

theorem callStateNotMade {s0 I cA σ evm} (hs : SourceState s0 I cA σ evm)
    {target value : UInt256} {calldata : ByteArray}
    (hn : ¬ (value ≤ (σ.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)) ∧ I.depth ≠ 1024)) :
    callViaEVM (callState evm cA σ) (AccountAddress.ofUInt256 target) (Int.ofNat value.toNat)
      calldata (false,
        { callState evm cA σ with substate :=
          ((callState evm cA σ).addAccessedAccount (AccountAddress.ofUInt256 target)).substate },
        ByteArray.empty) := by
  apply callViaEVM.callNotMade rfl rfl
  simpa only [callState, hs.env, wordOfInt_ofNat_toNat] using hn

end Auction
