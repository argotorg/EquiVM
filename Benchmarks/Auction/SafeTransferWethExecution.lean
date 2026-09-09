import Benchmarks.Auction.SafeTransferWethMemory
import Benchmarks.Auction.SafeTransferWithMemorySource
import Benchmarks.Auction.SettleAuctionTransferReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

def auctionWethTarget (evm : EVM.State) : AccountAddress :=
  EVM.address (AccountAddress.ofNat
    (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨202⟩) solcAddrMask).toNat)

def auctionWethCodePresent (evm : EVM.State) : Prop :=
  let weth := AccountAddress.ofNat
    (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨202⟩) solcAddrMask).toNat
  0 < (UInt256.ofNat ((evm.lookupAccount weth).option 0 (fun acc => acc.code.size))).toNat

-- Keep the concrete returned memory so callers can use the allocator result.
inductive AuctionWethExecution (s0 : EVM.State) (I : ExecutionEnv) (g : Sat256)
    (evmCall : EVM.State) (recipient : AccountAddress) (amount owner : UInt256)
    (mem : ByteArray) (aw ret : UInt256) (R : List UInt256) : Prop where
  | depositFailure (evmDeposit : EVM.State) (outDeposit : ByteArray)
      (hdeposit : typedCallViaEVM auctionConfig evmCall (auctionWethTarget evmCall)
        "deposit" (Int.ofNat amount.toNat) [] (false, evmDeposit, outDeposit) true)
      (rd : RDrev auctionBytecode g s0)
  | transferFailure (evmDeposit evmTransfer : EVM.State) (outDeposit outTransfer : ByteArray)
      (hdeposit : typedCallViaEVM auctionConfig evmCall (auctionWethTarget evmCall)
        "deposit" (Int.ofNat amount.toNat) [] (true, evmDeposit, outDeposit) true)
      (htransfer : typedCallViaEVM auctionConfig evmDeposit (auctionWethTarget evmDeposit)
        "transfer" 0 [.address recipient, .int (Int.ofNat amount.toNat)]
        (false, evmTransfer, outTransfer) true)
      (rd : RDrev auctionBytecode g s0)
  | decodeFailure (evmDeposit evmTransfer : EVM.State) (outDeposit outTransfer : ByteArray)
      (hdeposit : typedCallViaEVM auctionConfig evmCall (auctionWethTarget evmCall)
        "deposit" (Int.ofNat amount.toNat) [] (true, evmDeposit, outDeposit) true)
      (htransfer : typedCallViaEVM auctionConfig evmDeposit (auctionWethTarget evmDeposit)
        "transfer" 0 [.address recipient, .int (Int.ofNat amount.toNat)]
        (true, evmTransfer, outTransfer) true)
      (hdecode : auctionConfig.externalABI.decode? "transfer" outTransfer = none)
      (rd : RDrev auctionBytecode g s0)
  | returned (evmDeposit : EVM.State) (outDeposit outTransfer : ByteArray) (b : Bool)
      (cA' : Batteries.RBSet AccountAddress compare) (σ' τ' : AccountMap) (A' : Substate)
      (hdeposit : typedCallViaEVM auctionConfig evmCall (auctionWethTarget evmCall)
        "deposit" (Int.ofNat amount.toNat) [] (true, evmDeposit, outDeposit) true)
      (htransfer : typedCallViaEVM auctionConfig evmDeposit (auctionWethTarget evmDeposit)
        "transfer" 0 [.address recipient, .int (Int.ofNat amount.toNat)]
        (true, { evmCall with accountMap := τ', substate := A', createdAccounts := cA' },
          outTransfer) true)
      (hdecode : auctionConfig.externalABI.decode? "transfer" outTransfer = some [.bool b])
      (haccounts : accountMapEquiv σ' τ') (hlen : 32 ≤ outTransfer.size)
      (hsize : outTransfer.size < 2 ^ 255)
      (rd : ∃ k C, RD auctionBytecode I g s0 ret R
        (auctionSafeTransferDecodedMem (auctionSettleAuctionDynMload64 mem aw)
          (auctionWethTransferReturnMem mem aw amount owner outTransfer)
          outTransfer)
        (auctionSafeTransferDecodedAw (auctionSettleAuctionDynMload64 mem aw)
          (auctionWethTransferCallAw mem aw)) outTransfer (cA', σ') k C)

end Auction
