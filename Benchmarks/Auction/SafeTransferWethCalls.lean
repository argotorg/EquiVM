import Benchmarks.Auction.SafeTransferWethResult
import Benchmarks.Auction.SettleAuctionTransferBranchHelpers

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

set_option maxHeartbeats 1000000 in
theorem auctionCoupledValueCall {cA gh bl σ σ₀ A I} {g : Sat256}
    {cACall : Batteries.RBSet AccountAddress compare} {σCall : AccountMap}
    {pc gasArg target value inOff inSize outOff outSize aw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {k C : Nat}
    (evm : EVM.State) (henv : evm.executionEnv = I)
    (hcreated : evm.createdAccounts = cACall) (hσ₀ : evm.σ₀ = σ₀)
    (hgenesis : evm.genesisBlockHeader = gh) (hblocks : evm.blocks = bl)
    (haccounts : accountMapEquiv σCall evm.accountMap)
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024)
    (hbalance : value ≤ (σCall.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdec : decode auctionBytecode pc = some (.CALL, .none)) (hR : R.length + 1 ≤ 1024)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) pc
      (gasArg :: target :: value :: inOff :: inSize :: outOff :: outSize :: R)
      mem aw rdata (cACall, σCall) k C) :
    ∃ cA' σ' τ' A' z out k' C',
      callViaEVM evm (AccountAddress.ofUInt256 target) (Int.ofNat value.toNat)
        (mem.readWithPadding inOff.toNat inSize.toNat)
        (z, { evm with accountMap := τ', substate := A', createdAccounts := cA' }, out) true ∧
      accountMapEquiv σ' τ' ∧ out.size < 2 ^ 138 ∧
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) (pc + ⟨1⟩)
        ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        (out.write 0 mem outOff.toNat (min outSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOff.toNat inSize.toNat)
          outOff.toNat outSize.toNat)) out (cA', σ') k' C' := by
  obtain ⟨cA', σ', z, out, AIn, callGas, k', C', ⟨g'', A', hTheta⟩, hrd, _⟩ :=
    RD.callValueMade rd hdec hperm hbalance hdepth hR
  let evmE := { evm with accountMap := σCall }
  obtain ⟨τ', AS', hcall, hpost⟩ := auctionCallViaEVM_callMadeTheta_accountMapEquiv_perm
    (evm_evm := evmE) (evm_solm := evm)
    (wordOfInt_ofNat_toNat value).symm
    (by simpa only [evmE, henv, hcreated, hσ₀, hgenesis, hblocks, hperm] using hTheta)
    (by simpa only [evmE, henv] using hbalance)
    (by
      change evm.executionEnv.depth ≠ 1024
      rw [henv]
      intro hh
      have hv := congrArg Fin.val hh
      change I.depth.val = 1024 at hv
      omega)
    haccounts rfl rfl rfl rfl rfl
  have hsize : out.size < 2 ^ 138 :=
    Theta_returnData_size_lt_2pow138_of_eq (hΘ := hTheta)
      (hd := Ethereum.EVM.ByteArray.readWithPadding_size_le_maxReturnDataSizeByGas _ _ _)
  exact ⟨cA', σ', τ', AS', z, out, k', C', hcall, hpost, hsize, hrd⟩

theorem auctionWethTarget_accountMapEquiv {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv}
    (haccounts : accountMapEquiv σ evm.accountMap) (henv : evm.executionEnv = I) :
    auctionWethTarget evm =
      AccountAddress.ofUInt256 (UInt256.land (auctionSlotWord ⟨202⟩ σ I) solcAddrMask) := by
  have hw := transferBranchWethWordAt haccounts rfl (congrArg (·.codeOwner) henv)
  exact transferBranchWethTarget hw rfl

end Auction
