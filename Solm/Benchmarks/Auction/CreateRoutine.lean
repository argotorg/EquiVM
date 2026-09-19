import Solm.Benchmarks.Auction.CreateSuccess
import Solm.Benchmarks.Auction.CreateCatch
import Solm.Benchmarks.Auction.MintRoutine
import Solm.Benchmarks.Auction.NounSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem createRoutine {I g s0 ret R mem aw ptr rdata cA σ k C evm locals}
    (h : RD auctionBytecode I g s0 ⟨3000⟩ (ret :: R) mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ptr) (hb : ptr.toNat + 2 ^ 140 ≤ 2 ^ 200)
    (hp : locals.get? "_freePtr" = some (.int (Int.ofNat ptr.toNat)))
    (hnouns : locals.get? "nouns" = none) (ha : locals.get? "auction" = none)
    (hd : locals.get? "duration" = none) (hpause : locals.get? "_paused" = none)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 19 ≤ 1024) :
    (∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (locals' : Store) (mem' : ByteArray) (aw' : UInt256) (out : ByteArray) (k' C' : Nat),
      ExecFuncBody auctionConfig { contract := auctionContract, locals := locals } evm
        createAuctionFn.body (.returned { contract := auctionContract, locals := locals' } evm'
          none) ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ret R mem' aw' out (cA', σ') k' C') ∨
    (ExecFuncBody auctionConfig { contract := auctionContract, locals := locals } evm
      createAuctionFn.body .reverted ∧ RDrev auctionBytecode g s0) := by
  obtain ⟨evmM, cAM, σM, z, out, hc, hsM, ho, hmint⟩ :=
    mintRoutine h hs hperm hm (by omega) (by omega)
  have hr := nounsSourceRead (locals := locals) hs hnouns
  have hv : evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.intLit 0) = .ok (.int 0) := by simp only [evalExpr?, pure]
  have hargs : evalExprs? auctionConfig { contract := auctionContract, locals := locals } evm [] =
      .ok [] := by simp only [evalExprs?, pure]
  have ht : typedCallViaEVM auctionConfig evm
      (EVM.address (AccountAddress.ofUInt256 (nounsWord σ I))) "mint" 0 [] (z, evmM, out) := by
    rw [addressOfAddress]
    exact ⟨mintSelector, rfl, hc⟩
  rcases hmint with ⟨hz, hl, ⟨_, _, rd3172⟩, hh, _, _, hhi, _⟩ |
      ⟨hz, hl, hrev⟩ | ⟨hz, ⟨_, _, rd3116⟩, hh, _, _⟩
  · subst z
    have hdecode : auctionConfig.externalABI.decode? "mint" out =
        some [.int (Int.ofNat (calldataWord out 0).toNat)] := by
      change (ABI.decodeReturnValue? uint256 out).map (fun value ↦ [value]) = _
      simp only [uint256, uint256Int, decodeReturnUint_long hl (by omega), Option.map_some]
    rcases createSuccessRoutine rd3172 hsM hperm hh (by omega)
        ((store_get_ne _ _ (by decide)).trans ha) ((store_get_ne _ _ (by decide)).trans hd)
        (store_get_self _ _ _) hret (by omega) with
      ⟨evm', σ', locals', mem', aw', _, _, hsrc, hs', hrd⟩ | ⟨hsrc, hrd⟩
    · refine Or.inl ⟨evm', cAM, σ', locals', mem', aw', out, _, _, ?_, hs', hrd⟩
      exact ExecFuncBody.execBlockOK (ExecBlock.consNormal
        (ExecStmt.checkedCallSuccess hr hv hargs ht hdecode hsrc) ExecBlock.nil)
    · exact Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consRevert
        (ExecStmt.checkedCallSuccess hr hv hargs ht hdecode hsrc)), hrd⟩
  · subst z
    have hdecode : auctionConfig.externalABI.decode? "mint" out = none := by
      change (ABI.decodeReturnValue? uint256 out).map (fun value ↦ [value]) = _
      simp only [uint256, uint256Int, decodeReturnUint_short hl, Option.map_none]
    exact Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consRevert
      (ExecStmt.checkedCallReturnDecodeRevert hr hv hargs ht hdecode)), hrev⟩
  · subst z
    have hin : ptr.toNat ≤ (mintCallMem mem out ptr).size := by
      rw [mintCallMem_size hm out (by change out.size < 2 ^ 256; omega)]
      omega
    rcases createCatchRoutine rd3116 hsM hperm hh hin (by omega) (store_get_self _ _ _)
        ((store_get_ne _ _ (by decide)).trans hp)
        ((store_get_ne _ _ (by decide)).trans hpause) hret hov with
      ⟨evm', σ', locals', mem', aw', _, _, hsrc, hs', hrd⟩ | ⟨hsrc, hrd⟩
    · refine Or.inl ⟨evm', cAM, σ', locals', mem', aw', out, _, _, ?_, hs', hrd⟩
      exact ExecFuncBody.execBlockOK (ExecBlock.consNormal
        (ExecStmt.checkedCallFail hr hv hargs ht hsrc) ExecBlock.nil)
    · exact Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consRevert
        (ExecStmt.checkedCallFail hr hv hargs ht hsrc)), hrd⟩

end Auction
