import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

-- LIBRARY CANDIDATE: transport a zero-value opaque call witness to a source state,
-- preserving the context needed by subsequent calls.
theorem rawZeroCall_source_of_theta
    {storage : StorageLayout} {evm : EVM.State} {s0 : State} {I : ExecutionEnv}
    {σ σ' : AccountMap} {cA cA' : Batteries.RBSet AccountAddress compare}
    {targetWord callGas : UInt256} {A_in : Substate} {z : Bool} {data out : ByteArray}
    (hAccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I)
    (hcreated : evm.createdAccounts = cA) (hσ0 : evm.σ₀ = s0.σ₀)
    (hgenesis : evm.genesisBlockHeader = s0.genesisBlockHeader) (hblocks : evm.blocks = s0.blocks)
    (hdepth : I.depth.val < 1024) (hperm : I.perm = true)
    (hΘ : ∃ (g'' : UInt256) (A' : Substate),
      (cA', σ', g'', A', z, out) =
        Ethereum.EVM.Θ I.blobVersionedHashes cA s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256 targetWord) (toExecute σ (AccountAddress.ofUInt256 targetWord))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩ data (I.depth + 1) I.header I.perm) :
    ∃ evm', callViaEVM evm (AccountAddress.ofUInt256 targetWord) 0 data (z, evm', out) ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.createdAccounts = cA' ∧
      evm'.σ₀ = s0.σ₀ ∧ evm'.genesisBlockHeader = s0.genesisBlockHeader ∧
      evm'.blocks = s0.blocks ∧ evm'.executionEnv = I := by
  let evmE : EVM.State :=
    { evm with
      accountMap := σ
      createdAccounts := cA
      σ₀ := s0.σ₀
      genesisBlockHeader := s0.genesisBlockHeader
      blocks := s0.blocks
      executionEnv := I }
  obtain ⟨g', A', hΘ⟩ := hΘ
  have hcallE : callViaEVM evmE (AccountAddress.ofUInt256 targetWord) 0 data
      (z, { evmE with accountMap := σ', createdAccounts := cA', substate := A' }, out) := by
    refine callViaEVM.callMade (perm := true) (g' := g') wordOfInt_zero.symm ?_ rfl ?_ ?_
    · refine ⟨callGas, A_in, ?_⟩
      simpa only [evmE, hperm, accountAddress_roundtrip] using hΘ
    · exact Fin.zero_le _
    · intro h
      have hlt := hdepth
      change I.depth = 1024 at h
      rw [h] at hlt
      exact absurd hlt (by decide)
  obtain ⟨σSolm, ASolm, hcall, hpost⟩ := callViaEVM_accountMapEquiv (storage := storage)
    (evm_solm := evm) hcallE hAccounts hσ0.symm hcreated hgenesis hblocks rfl henv
  exact ⟨{ evm with accountMap := σSolm, createdAccounts := cA', substate := ASolm },
    hcall, hpost, rfl, hσ0, hgenesis, hblocks, henv⟩

-- LIBRARY CANDIDATE: normalization is identity on an already bounded address.
theorem uniswapAddress_self (a : AccountAddress) : EVM.address a.val = a := by
  apply Fin.ext
  show a.val % EVM.addressModulus = a.val
  rw [show EVM.addressModulus = AccountAddress.size from by decide]
  exact Nat.mod_eq_of_lt a.isLt


end UniswapV2Pair
