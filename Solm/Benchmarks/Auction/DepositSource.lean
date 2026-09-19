import Solm.Benchmarks.Auction.PaymentLocals
import Solm.Benchmarks.Auction.DepositCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem wethSourceRead {s0 I cA σ evm locals}
    (hs : SourceState s0 I cA σ evm) (hb : locals.get? "weth" = none) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm (.storage
      wethRef) =
      .ok (.address (AccountAddress.ofUInt256 (wethWord σ I))) := by
  rw [wethRef, scalarRead evm locals "weth" .address (auctionAddrLoc ⟨202⟩)
    hb (by native_decide) rfl, loadAddress]
  have hw : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨202⟩ = storedWord σ I ⟨202⟩ := by
    exact hs.storageRead _
  rw [hw, addressOfWord_eq]
  rfl

-- LIBRARY CANDIDATE: the source code-size expression agrees under account-map equivalence.
theorem extCodeSource {cfg frame evm σ target receiver}
    (hs : accountMapEquiv σ evm.accountMap)
    (hr : evalExpr? cfg frame evm receiver =
      .ok (.address (AccountAddress.ofUInt256 target))) :
    evalExpr? cfg frame evm (.extCodeSize receiver) =
      .ok (.int (Int.ofNat (extCodeSizeWord σ target).toNat)) := by
  simp only [evalExpr?, hr, pure, bind, EvalResult.bind]
  rw [extCodeSizeWord_accountMapEquiv hs]
  unfold State.lookupAccount extCodeSizeWord
  cases evm.accountMap.find? (AccountAddress.ofUInt256 target) <;> rfl

theorem wethCodeGuardSource {s0 I cA σ evm locals}
    (hs : SourceState s0 I cA σ evm) (hb : locals.get? "weth" = none) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage wethRef)) (.intLit 0)) =
      .ok (.bool (decide (extCodeSizeWord σ (wethWord σ I) ≠ ⟨0⟩))) := by
  have he := extCodeSource hs.accounts (wethSourceRead hs hb)
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

theorem depositTypedCall {evm evm' target out z} {amount : UInt256}
    (hc : callViaEVM evm target (Int.ofNat amount.toNat) depositSelector (z, evm', out)) :
    typedCallViaEVM auctionConfig evm (EVM.address target.val) "deposit"
      (Int.ofNat amount.toNat) [] (z, evm', out) := by
  rw [addressOfAddress]
  exact ⟨depositSelector, rfl, hc⟩

theorem depositSourceSuccess {s0 I cA σ evm evm' locals recipient amount ptr out}
    (hs : SourceState s0 I cA σ evm) (hv : PaymentValues locals recipient amount ptr)
    (hyes : extCodeSizeWord σ (wethWord σ I) ≠ ⟨0⟩)
    (hc : callViaEVM evm (AccountAddress.ofUInt256 (wethWord σ I))
      (Int.ofNat amount.toNat) depositSelector (true, evm', out)) :
    ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      (checkedExternalCallStmts (.storage wethRef) "deposit" (.var "amount") [] "_dep")
      (.ok { contract := auctionContract, locals := locals.insert "_dep" (collapseReturns []) }
        evm') := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · rw [wethCodeGuardSource hs hv.weth, decide_eq_true hyes]
  · refine ExecBlock.consNormal (ExecStmt.externalCallSuccess (wethSourceRead hs hv.weth)
      ?_ ?_ (depositTypedCall hc) rfl) ExecBlock.nil
    · simp only [evalExpr?, hv.amount, EvalResult.ofOption]
    · simp [evalExprs?, pure]

theorem depositSourceFailure {s0 I cA σ evm evm' locals recipient amount ptr out}
    (hs : SourceState s0 I cA σ evm) (hv : PaymentValues locals recipient amount ptr)
    (hyes : extCodeSizeWord σ (wethWord σ I) ≠ ⟨0⟩)
    (hc : callViaEVM evm (AccountAddress.ofUInt256 (wethWord σ I))
      (Int.ofNat amount.toNat) depositSelector (false, evm', out)) :
    ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      paymentFallbackStmts .reverted := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · rw [wethCodeGuardSource hs hv.weth, decide_eq_true hyes]
  · exact ExecBlock.consRevert (ExecStmt.externalCallFailure (wethSourceRead hs hv.weth)
      (by simp only [evalExpr?, hv.amount, EvalResult.ofOption])
      (by simp [evalExprs?, pure]) (depositTypedCall hc))

theorem depositSourceNoCode {s0 I cA σ evm locals recipient amount ptr}
    (hs : SourceState s0 I cA σ evm) (hv : PaymentValues locals recipient amount ptr)
    (hno : extCodeSizeWord σ (wethWord σ I) = ⟨0⟩) :
    ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      paymentFallbackStmts .reverted := by
  exact ExecBlock.consRevert (ExecStmt.requireFalse (by
    rw [wethCodeGuardSource hs hv.weth, hno]
    rfl))

end Auction
