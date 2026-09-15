import Benchmarks.Auction.DepositSource
import Benchmarks.Auction.BurnCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem nounsSourceRead {s0 I cA σ evm locals}
    (hs : SourceState s0 I cA σ evm) (hb : locals.get? "nouns" = none) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm (.storage
      nounsRef) =
      .ok (.address (AccountAddress.ofUInt256 (nounsWord σ I))) := by
  rw [nounsRef, scalarRead evm locals "nouns" .address (auctionAddrLoc ⟨201⟩)
    hb (by native_decide) rfl, loadAddress]
  have hw : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩ = storedWord σ I ⟨201⟩ := by
    exact hs.storageRead _
  rw [hw, addressOfWord_eq]
  rfl

theorem nounsCodeGuardSource {s0 I cA σ evm locals}
    (hs : SourceState s0 I cA σ evm) (hb : locals.get? "nouns" = none) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage nounsRef)) (.intLit 0)) =
      .ok (.bool (decide (extCodeSizeWord σ (nounsWord σ I) ≠ ⟨0⟩))) := by
  have he := extCodeSource hs.accounts (nounsSourceRead hs hb)
  simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?]
  congr 2
  congr 1
  simp only [Int.ofNat_eq_natCast, Int.natCast_pos]
  apply propext
  constructor
  · intro hp hz
    rw [hz] at hp
    exact (by decide : ¬ 0 < 0) hp
  · intro hn
    by_contra hz
    exact hn (uint256_toNat_eq_zero (by omega))

theorem checkedNounSourceNoCode {s0 I cA σ evm locals name retVar args}
    (hs : SourceState s0 I cA σ evm) (hb : locals.get? "nouns" = none)
    (hno : extCodeSizeWord σ (nounsWord σ I) = ⟨0⟩) :
    ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      (checkedExternalCallStmts (.storage nounsRef) name (.intLit 0) args retVar) .reverted := by
  exact ExecBlock.consRevert (ExecStmt.requireFalse (by
    rw [nounsCodeGuardSource hs hb, hno]
    rfl))

theorem checkedNounSourceSuccess {s0 I cA σ evm evm' locals name retVar args values cdata out}
    (hs : SourceState s0 I cA σ evm) (hb : locals.get? "nouns" = none)
    (hyes : extCodeSizeWord σ (nounsWord σ I) ≠ ⟨0⟩)
    (hargs : evalExprs? auctionConfig { contract := auctionContract, locals := locals } evm args =
      .ok values)
    (hencode : auctionConfig.externalABI.encode? name values = some cdata)
    (hc : callViaEVM evm (AccountAddress.ofUInt256 (nounsWord σ I)) 0 cdata (true, evm', out))
    (hdecode : auctionConfig.externalABI.decode? name out = some []) :
    ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      (checkedExternalCallStmts (.storage nounsRef) name (.intLit 0) args retVar)
      (.ok { contract := auctionContract, locals := locals.insert retVar (collapseReturns []) }
        evm') := by
  apply checkedExternalCallSuccess (target := AccountAddress.ofUInt256 (nounsWord σ I))
    ?_ (nounsSourceRead hs hb) hargs ?_ hdecode
  · rw [nounsCodeGuardSource hs hb, decide_eq_true hyes]
  · rw [addressOfAddress]
    exact ⟨cdata, hencode, hc⟩

theorem checkedNounSourceFailure {s0 I cA σ evm evm' locals name retVar args values cdata out}
    (hs : SourceState s0 I cA σ evm) (hb : locals.get? "nouns" = none)
    (hyes : extCodeSizeWord σ (nounsWord σ I) ≠ ⟨0⟩)
    (hargs : evalExprs? auctionConfig { contract := auctionContract, locals := locals } evm args =
      .ok values)
    (hencode : auctionConfig.externalABI.encode? name values = some cdata)
    (hc : callViaEVM evm (AccountAddress.ofUInt256 (nounsWord σ I)) 0 cdata (false, evm', out)) :
    ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      (checkedExternalCallStmts (.storage nounsRef) name (.intLit 0) args retVar) .reverted := by
  apply checkedExternalCallFailure (evm' := evm') (out := out)
    (target := AccountAddress.ofUInt256 (nounsWord σ I))
    ?_ (nounsSourceRead hs hb) hargs ?_
  · rw [nounsCodeGuardSource hs hb, decide_eq_true hyes]
  · rw [addressOfAddress]
    exact ⟨cdata, hencode, hc⟩

end Auction
