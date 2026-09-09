import Benchmarks.Auction.SafeTransferWethReturn
import Benchmarks.Auction.DynamicMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def auctionWethTransferMem (mem : ByteArray) (aw amount owner : UInt256) : ByteArray :=
  auctionSettleAuctionDynTransferMem (auctionSettleAuctionDynDepositMem mem aw)
    (auctionSettleAuctionDynMload64 mem aw) amount owner

def auctionWethTransferCallAw (mem : ByteArray) (aw : UInt256) : UInt256 :=
  let free := auctionSettleAuctionDynMload64 mem aw
  let before := auctionSettleAuctionDynTransferAwAfterMload64
    (auctionSettleAuctionDynDepositCallAw mem aw) free
  UInt256.ofNat (MachineState.M (MachineState.M before.toNat free.toNat 68) free.toNat 32)

def auctionWethTransferReturnMem (mem : ByteArray) (aw amount owner : UInt256)
    (out : ByteArray) : ByteArray :=
  out.write 0 (auctionWethTransferMem mem aw amount owner)
    (auctionSettleAuctionDynMload64 mem aw).toNat (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat

structure AuctionWethMemory (mem : ByteArray) (aw amount owner finish : UInt256) : Prop where
  depositFree : auctionSettleAuctionDynMload64
      (auctionSettleAuctionDynDepositMem mem aw) (auctionSettleAuctionDynDepositAw mem aw) =
    auctionSettleAuctionDynMload64 mem aw
  depositLen : UInt256.sub (⟨4⟩ + auctionSettleAuctionDynMload64 mem aw)
    (auctionSettleAuctionDynMload64 mem aw) = ⟨4⟩
  depositEncode : auctionConfig.externalABI.encode? "deposit" [] =
    some ((auctionSettleAuctionDynDepositMem mem aw).readWithPadding
      (auctionSettleAuctionDynMload64 mem aw).toNat 4)
  depositCallFree : auctionSettleAuctionDynMload64 (auctionSettleAuctionDynDepositMem mem aw)
    (auctionSettleAuctionDynDepositCallAw mem aw) = auctionSettleAuctionDynMload64 mem aw
  transferFree : auctionSettleAuctionDynMload64 (auctionWethTransferMem mem aw amount owner)
      (auctionSettleAuctionDynTransferAw (auctionSettleAuctionDynDepositCallAw mem aw)
        (auctionSettleAuctionDynMload64 mem aw)) = auctionSettleAuctionDynMload64 mem aw
  transferLen : UInt256.sub (⟨68⟩ + auctionSettleAuctionDynMload64 mem aw)
    (auctionSettleAuctionDynMload64 mem aw) = ⟨68⟩
  transferEncode : auctionConfig.externalABI.encode? "transfer"
      [.address (AccountAddress.ofUInt256 owner), .int (Int.ofNat amount.toNat)] =
    some ((auctionWethTransferMem mem aw amount owner).readWithPadding
      (auctionSettleAuctionDynMload64 mem aw).toNat 68)
  returnFree (out : ByteArray) (hsize : out.size < UInt256.size) :
    auctionLoadWord (auctionWethTransferReturnMem mem aw amount owner out)
      (auctionWethTransferCallAw mem aw) ⟨64⟩ = auctionSettleAuctionDynMload64 mem aw
  returnWord (out : ByteArray) (hsize : out.size < UInt256.size) (hlen : 32 ≤ out.size) :
    auctionLoadWord (auctionSafeTransferDecodedMem (auctionSettleAuctionDynMload64 mem aw)
      (auctionWethTransferReturnMem mem aw amount owner out) out)
      (auctionGrowWords (auctionGrowWords (auctionWethTransferCallAw mem aw) ⟨64⟩ 32) ⟨64⟩ 32)
      (auctionSettleAuctionDynMload64 mem aw) =
      UInt256.ofNat (fromByteArrayBigEndian (out.readWithPadding 0 32))
  returnBase (out : ByteArray) (hsize : out.size < 2 ^ 255) :
    (auctionSettleAuctionDynMload64 mem aw).toNat + out.size < UInt256.size
  returnFinish (out : ByteArray) (hsize : out.size < UInt256.size) (hlen : 32 ≤ out.size) :
    auctionLoadWord (auctionSafeTransferDecodedMem (auctionSettleAuctionDynMload64 mem aw)
      (auctionWethTransferReturnMem mem aw amount owner out) out)
      (auctionSafeTransferDecodedAw (auctionSettleAuctionDynMload64 mem aw)
        (auctionWethTransferCallAw mem aw)) ⟨224⟩ = finish

end Auction
