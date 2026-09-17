import Benchmarks.Auction.SettleStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def statusState (evm : EVM.State) (word : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨101⟩ word

theorem statusRead {s0 I cA σ evm locals} (hs : SourceState s0 I cA σ evm)
    (hl : locals.get? "_status" = none) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.storage statusRef) = .ok (.int (Int.ofNat (storedWord σ I ⟨101⟩).toNat)) := by
  rw [statusRef, scalarRead evm locals "_status" (.int uint256Int) (auctionUint256Loc ⟨101⟩)
    hl (by native_decide) rfl, loadUint256]
  have hw : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ =
      storedWord σ I ⟨101⟩ := by
    exact hs.storageRead _
  rw [hw]

theorem statusGuardSource {s0 I cA σ evm locals} (hs : SourceState s0 I cA σ evm)
    (hl : locals.get? "_status" = none) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .ne (.storage statusRef) entered) =
      .ok (.bool (decide (storedWord σ I ⟨101⟩ ≠ ⟨2⟩))) := by
  simp only [entered, evalExpr?, statusRead hs hl, pure, bind, EvalResult.bind, evalBinaryOp?]
  congr 2
  by_cases hz : storedWord σ I ⟨101⟩ = ⟨2⟩
  · rw [hz]; rfl
  · have hv : Value.int (Int.ofNat (storedWord σ I ⟨101⟩).toNat) ≠ .int 2 := by
      intro he
      have hn := Value.int.inj he
      apply hz
      apply u256_inj
      change (storedWord σ I ⟨101⟩).toNat = 2
      simp only [Int.ofNat_eq_natCast] at hn
      exact_mod_cast hn
    rw [beq_eq_false_iff_ne.mpr hv, decide_eq_true hz]
    rfl

theorem statusStoreSource {evm locals e word}
    (hl : locals.get? "_status" = none)
    (he : evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm e =
      .ok (.int (Int.ofNat (UInt256.toNat word)))) :
    ExecStmt auctionConfig { contract := auctionContract, locals := locals } evm
      (.assign .storage statusRef e)
      (.ok { contract := auctionContract, locals := locals } (statusState evm word)) := by
  apply ExecStmt.assign he
  exact scalarWrite evm _ locals "_status" (.elem (.int uint256Int)) (auctionUint256Loc ⟨101⟩)
    _ hl (by native_decide) rfl (by trivial) (storageLocStore_uint256 evm ⟨101⟩ word)

theorem SourceState.status {s0 I cA σ evm} (hs : SourceState s0 I cA σ evm) (word : UInt256) :
    SourceState s0 I cA (sstoreAccountMap I.codeOwner σ ⟨101⟩ word) (statusState evm word) := by
  unfold statusState
  rw [hs.env]
  exact hs.storageWrite _ _

end Auction
