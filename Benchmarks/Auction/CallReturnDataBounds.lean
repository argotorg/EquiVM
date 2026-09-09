import Benchmarks.Auction.ReturnDataBounds
import Benchmarks.Auction.Spec
import Reasoning.Memory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Auction

-- LIBRARY CANDIDATE: short EVM calls have representable byte-array return buffers.
theorem callViaEVM_returnData_size_lt_2pow64
    {evm evm' : EVM.State} {target : AccountAddress} {value : Int}
    {calldata out : ByteArray} {z perm : Bool}
    (hdata : calldata.size ≤ 96) (hcall : callViaEVM evm target value calldata (z, evm', out) perm) :
    out.size < 2 ^ 64 := by
  cases hcall with
  | callMade hvalue htheta hevm hbalance hdepth =>
    obtain ⟨gas, A, htheta⟩ := htheta
    have hbound := ReturnDataProperties.theta_size_lt_2pow64
      evm.executionEnv.blobVersionedHashes evm.createdAccounts evm.genesisBlockHeader evm.blocks
      evm.accountMap evm.σ₀ A evm.executionEnv.codeOwner evm.executionEnv.sender target
      (toExecute evm.accountMap target) calldata gas (UInt256.ofNat evm.executionEnv.gasPrice)
      (EVM.wordOfInt value) (EVM.wordOfInt value) (evm.executionEnv.depth + 1)
      evm.executionEnv.header perm hdata
    rw [← hvalue, ← htheta] at hbound
    exact hbound
  | callNotMade _ _ _ => simp

theorem auctionTransferCalldata_size {recipient : AccountAddress} {amount : UInt256}
    {calldata : ByteArray}
    (hencode : auctionConfig.externalABI.encode? "transfer"
      [.address recipient, .int (Int.ofNat amount.toNat)] = some calldata) :
    calldata.size = 68 := by
  have hamount : amount.toNat < EVM.twoPow 256 := amount.val.isLt
  simp [auctionConfig, auctionExternalABI, encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, uint256, uint256Int, hamount] at hencode
  subst calldata
  have hlen (w : UInt256) : (EVM.Word.toBytesBE w).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size w
  simp [transferSelector, selectorBytes, hlen, ByteArray.size]

theorem auctionTransferReturnData_size_lt_2pow64
    {evm evm' : EVM.State} {target recipient : AccountAddress} {amount : UInt256}
    {out : ByteArray} {z perm : Bool}
    (hcall : typedCallViaEVM auctionConfig evm target "transfer" 0
      [.address recipient, .int (Int.ofNat amount.toNat)] (z, evm', out) perm) :
    out.size < 2 ^ 64 := by
  obtain ⟨calldata, hencode, hcall⟩ := hcall
  exact callViaEVM_returnData_size_lt_2pow64 (by rw [auctionTransferCalldata_size hencode]; decide)
    hcall

theorem auctionMintReturnData_size_lt_2pow64 {evm evm' : EVM.State}
    {target : AccountAddress} {out : ByteArray} {z : Bool}
    (hcall : typedCallViaEVM auctionConfig evm target "mint" 0 [] (z, evm', out) true) :
    out.size < 2 ^ 64 := by
  obtain ⟨data, hencode, hc⟩ := hcall
  have hd : data = mintSelector := by
    change some mintSelector = some data at hencode
    exact (Option.some.inj hencode).symm
  subst data
  exact callViaEVM_returnData_size_lt_2pow64 (by decide) hc

end Auction
