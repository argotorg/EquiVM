import Benchmarks.Auction.UnpauseCreateAuction

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

def auctionCreateAuctionMemoryLocals (free : UInt256) : Store :=
  (∅ : Store).insert "_freePtr" (.int (Int.ofNat free.toNat))

def auctionCreateAuctionMemorySuccessFrame (free nounId : UInt256) (evm : EVM.State) : Frame :=
  { contract := auctionContract
    locals := ((((auctionCreateAuctionMemoryLocals free).insert "nounId"
      (.int (Int.ofNat nounId.toNat))).insert "startTime"
      (.int (Int.ofNat (auctionCreateAuctionStartWord evm).toNat))).insert "endTime"
      (.int (Int.ofNat (auctionCreateAuctionEndWord evm).toNat))) }

theorem auctionCreateAuctionWithMemoryReturns_success {evm evmCall : EVM.State}
    {out : ByteArray} {nounId : UInt256} (free : UInt256)
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (true, evmCall, out) true)
    (hdec : ABI.decodeReturnValue? uint256 out = some (.int (Int.ofNat nounId.toNat)))
    (hadd : (auctionCreateAuctionStartWord evmCall).toNat +
        (auctionCreateAuctionDurationWord evmCall).toNat < UInt256.size) :
    ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionCreateAuctionMemoryLocals free }
      evm createAuctionWithMemoryFn.body
      (.returned (auctionCreateAuctionMemorySuccessFrame free nounId evmCall)
        (auctionCreateAuctionSourceSuccessPostState evmCall nounId) none) := by
  refine ExecFuncBody.execBlockOK (ExecBlock.consNormal ?_ ExecBlock.nil)
  refine ExecStmt.checkedCallSuccess
    (evalExpr_createAuction_nouns_frame evm _ (by simp [auctionCreateAuctionMemoryLocals]))
    (by simp [evalExpr?, pure]) (by rfl) hcall (auctionExternalABI_decode_mint hdec) ?_
  exact auctionCreateAuctionSuccessBlock_frame evmCall nounId _ (store_get_self _ _ _)
    (by simp [auctionCreateAuctionMemoryLocals])
    (by simp [auctionCreateAuctionMemoryLocals]) hadd

theorem auctionCreateAuctionWithMemoryReverts_addOverflow {evm evmCall : EVM.State}
    {out : ByteArray} {nounId : UInt256} (free : UInt256)
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (true, evmCall, out) true)
    (hdec : ABI.decodeReturnValue? uint256 out = some (.int (Int.ofNat nounId.toNat)))
    (hover : UInt256.size ≤ (auctionCreateAuctionStartWord evmCall).toNat +
        (auctionCreateAuctionDurationWord evmCall).toNat) :
    ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionCreateAuctionMemoryLocals free }
      evm createAuctionWithMemoryFn.body .reverted := by
  refine ExecFuncBody.execBlockRevert (ExecBlock.consRevert ?_)
  refine ExecStmt.checkedCallSuccess
    (evalExpr_createAuction_nouns_frame evm _ (by simp [auctionCreateAuctionMemoryLocals]))
    (by simp [evalExpr?, pure]) (by rfl) hcall (auctionExternalABI_decode_mint hdec) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalExpr_createAuction_now evmCall _)) ?_
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert
    (evalExpr_createAuction_endTime_expr_revert_frame evmCall _
      (store_get_self _ _ _) (by simp [auctionCreateAuctionMemoryLocals]) hover))

theorem auctionCreateAuctionWithMemoryReverts_decodeFailure {evm evmCall : EVM.State}
    {out : ByteArray} (free : UInt256)
    (hcall : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
          solcAddrMask).toNat))) "mint" 0 [] (true, evmCall, out) true)
    (hdec : ABI.decodeReturnValue? uint256 out = none) :
    ExecFuncBody auctionConfig
      { contract := auctionContract, locals := auctionCreateAuctionMemoryLocals free }
      evm createAuctionWithMemoryFn.body .reverted := by
  refine ExecFuncBody.execBlockRevert (ExecBlock.consRevert ?_)
  exact ExecStmt.checkedCallReturnDecodeRevert
    (evalExpr_createAuction_nouns_frame evm _ (by simp [auctionCreateAuctionMemoryLocals]))
    (by simp [evalExpr?, pure]) (by rfl) hcall (auctionExternalABI_decode_mint_none hdec)

end Auction
