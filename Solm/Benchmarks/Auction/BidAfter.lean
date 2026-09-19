import Solm.Benchmarks.Auction.BidRefund
import Solm.Benchmarks.Auction.BidExtension
import Solm.Benchmarks.Auction.BidEvents

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def bidAfterStmts : List Stmt :=
  bidRefundStmts ++ (bidStoreStmts ++ (bidExtendStmts ++ [.assign .storage statusRef notEntered]))

theorem bidAfterRoutine {I g s0 s noun ret R mem aw rdata cA σ k C evm locals}
    (h : RD auctionBytecode I g s0 ⟨1681⟩ (⟨128⟩ :: noun :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : HeapMemory mem aw ⟨320⟩) (hsm : SnapshotMemory s mem aw ⟨128⟩)
    (hv : BidValues locals s noun)
    (ht : (UInt256.ofNat I.header.timestamp).toNat < s.endTime.toNat)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 28 ≤ 1024) :
    (∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
        (locals' : Store) (mem' : ByteArray) (aw' : UInt256) (out : ByteArray) (k' C' : Nat),
      ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
        bidAfterStmts (.ok { contract := auctionContract, locals := locals' } evm') ∧
      SourceState s0 I cA' σ' evm' ∧
      RD auctionBytecode I g s0 ret R mem' aw' out (cA', σ') k' C') ∨
    (ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      bidAfterStmts .reverted ∧ RDrev auctionBytecode g s0) := by
  rcases bidRefundRoutine h hs hperm hm hsm hv hov with
    ⟨evmR, cAR, σR, localsR, memR, awR, _, outR, _, _, hrefund, hvR, hsR,
      rd1715, _, hsmR, _, _⟩ | ⟨hrefund, hr⟩
  · have hstores := bidStoresSource (evm := evmR) (hvR.storage _ (by decide))
    obtain ⟨_, _, rd1738⟩ := bidStoresRuntime rd1715 hperm (by omega)
    rcases bidExtensionRoutine rd1738 hsR.bidStores hperm hsmR hvR ht (by omega) with
      ⟨evmE, σE, localsE, extended, memE, awE, _, _, hextend, hvE, hsE, rd1792⟩ |
        ⟨hextend, hr⟩
    · obtain ⟨mem', aw', _, _, rd1923⟩ := bidEvents rd1792 hperm (by omega)
      obtain ⟨_, _, rdret⟩ := bidExit rd1923 hperm hret (by omega)
      have hexit := statusStoreSource (evm := evmE) (e := notEntered) (word := ⟨1⟩)
        (hvE.storage _ (by decide)) (by simp only [notEntered, evalExpr?, pure]; rfl)
      exact Or.inl ⟨statusState evmE ⟨1⟩, cAR, _, localsE, mem', aw', outR, _, _,
        execBlock_append hrefund (execBlock_append hstores
          (execBlock_append hextend (ExecBlock.consNormal hexit ExecBlock.nil))),
        hsE.status ⟨1⟩, rdret⟩
    · exact Or.inr ⟨execBlock_append hrefund (execBlock_append hstores
        (execBlock_append_term hextend (by simp))), hr⟩
  · exact Or.inr ⟨execBlock_append_term hrefund (by simp), hr⟩

end Auction
