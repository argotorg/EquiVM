import Benchmarks.Auction.BidRoutine
import Benchmarks.Auction.Decoders
import Benchmarks.Auction.Events

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem createBidBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I (entryBytes 6))
    (hreach : EntryReached 6 cA gh bl σ_evm σ₀ A I g)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor auctionConfig auctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := dispatchEntry 6 hsel
  have hsz := calldata_size_ge_of_selIs I (entryBytes 6) (entryBytes_size 6) hsel
  obtain ⟨_, _, rd500⟩ := hreach
  have rd5357 := evm_run rd500 with [jumpdest, push2 ⟨413⟩, push2 ⟨514⟩, calldatasize,
    push1 ⟨4⟩, push2 ⟨5357⟩, jump (by jump_dest)]
  by_cases hlen : 36 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
          (createBidTransition.params.map Param.name)
          (transitionSignature createBidTransition).paramTypes I.calldata =
            some (bidParams (calldataWord I.calldata 4)) :=
        decodeCalldata_uint256_ok hlen hhi
      obtain ⟨_, _, rd514⟩ := decodeUint256Ok rd5357 hlen hhi hsize (by jump_dest) (by evm_ov)
      have rd1165 := evm_run rd514 with [jumpdest, push2 ⟨1165⟩, jump (by jump_dest)]
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hs0 : SourceState (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
          I cA σ_evm evm0 := SourceState.init hAccounts
      rcases bidRoutine rd1165 hs0 hperm freshHeapMemory (by jump_dest) (by evm_ov) with
        ⟨evm', cA', σ', locals', mem', aw', out, _, _, hbody, hs', rd413⟩ | ⟨hbody, hr⟩
      · exact (auctionStop rd413 (by evm_ov)).reEquivExecutionGenAccountMapEquiv
          hcode hd hdec (ExecFuncBody.execBlockOK hbody) hs'.created.symm hs'.accounts
          (.fallthrough rfl rfl (by native_decide))
      · exact hr.reEquivExecutionRevert hcode hd hdec (ExecFuncBody.execBlockRevert hbody)
    · have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
          (createBidTransition.params.map Param.name)
          (transitionSignature createBidTransition).paramTypes I.calldata = none :=
        decodeCalldata_uint256_none_huge (by omega)
      exact (decodeUint256Fail rd5357
        (solcDecodeLenCheckHuge_4_32 (by omega) hsize) (by evm_ov)).reEquivDecodingFailed
        hcode hd hdec
  · have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
        (createBidTransition.params.map Param.name)
        (transitionSignature createBidTransition).paramTypes I.calldata = none :=
      decodeCalldata_uint256_none_short (by omega)
    exact (decodeUint256Fail rd5357
      (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize) (by evm_ov)).reEquivDecodingFailed
      hcode hd hdec

end Auction
