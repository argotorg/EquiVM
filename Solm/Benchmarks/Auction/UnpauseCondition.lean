import Solm.Benchmarks.Auction.UnpauseSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def unpauseCreateExpr : Expr :=
  .binary .or (.binary .eq (.storage (aField "startTime")) (.intLit 0))
    (.storage (aField "settled"))

def UnpauseCreates (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  (snapshotOf σ I).startTime = ⟨0⟩ ∨ (snapshotOf σ I).settledByte ≠ ⟨0⟩

instance (σ : AccountMap) (I : ExecutionEnv) : Decidable (UnpauseCreates σ I) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem unpauseCreateSource {s0 I cA σ evm locals} (hs : SourceState s0 I cA σ evm)
    (ha : locals.get? "auction" = none) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      unpauseCreateExpr = .ok (.bool (decide (UnpauseCreates σ I))) := by
  have hw (slot : UInt256) : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot =
      storedWord σ I slot := by
    exact hs.storageRead _
  have ht := auctionFieldRead evm locals "startTime" (.int uint256Int)
    (auctionUint256Loc ⟨209⟩) ha (by native_decide) rfl
  rw [loadUint256, hw] at ht
  have hb := auctionFieldRead evm locals "settled" .bool (auctionBoolLocAt ⟨211⟩ 20)
    ha (by native_decide) rfl
  rw [loadBoolAt, hw] at hb
  have hpow : UInt256.ofNat (256 ^ (20 : Fin 32).val) = (⟨2 ^ 160⟩ : UInt256) := by
    native_decide
  rw [hpow, wordToElemBool] at hb
  change evalExpr? _ _ _ _ = .ok (.bool (!decide ((snapshotOf σ I).settledByte = ⟨0⟩))) at hb
  have ht' : evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .eq (.storage (aField "startTime")) (.intLit 0)) =
      .ok (.bool (decide ((snapshotOf σ I).startTime = ⟨0⟩))) := by
    simp only [evalExpr?, ht, pure, bind, EvalResult.bind, evalBinaryOp?]
    change EvalResult.ok
      (Value.bool ((Value.int (Int.ofNat (snapshotOf σ I).startTime.toNat)) == Value.int 0)) = _
    by_cases hz : (snapshotOf σ I).startTime = ⟨0⟩
    · rw [hz]; rfl
    · have hn : (snapshotOf σ I).startTime.toNat ≠ 0 := fun hh ↦ hz (u256_inj hh)
      simp [hz, hn]
  by_cases hz : (snapshotOf σ I).startTime = ⟨0⟩
  · simp only [unpauseCreateExpr, evalExpr?, ht', hz, decide_true,
      EvalResult.bind, bind, pure, UnpauseCreates, true_or]
  · simp only [unpauseCreateExpr, evalExpr?, ht', hz, decide_false,
      EvalResult.bind, bind, pure, hb, UnpauseCreates, false_or, decide_not]

def unpauseCreateWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  if (snapshotOf σ I).startTime = ⟨0⟩ then ⟨1⟩ else (snapshotOf σ I).settledByte

theorem unpauseCreateWord_nonzero (σ : AccountMap) (I : ExecutionEnv) :
    unpauseCreateWord σ I ≠ ⟨0⟩ ↔ UnpauseCreates σ I := by
  unfold unpauseCreateWord UnpauseCreates
  by_cases hz : (snapshotOf σ I).startTime = ⟨0⟩
  · simp only [hz, if_true, true_or, iff_true]
    decide
  · simp only [hz, if_false, false_or]

theorem unpauseCondition {I g s0 R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨1126⟩ R mem aw rdata (cA, σ) k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨1150⟩ (unpauseCreateWord σ I :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd1129 := evm_run h with [jumpdest, push1 ⟨209⟩]
  obtain ⟨_, _, rd1130⟩ := rd1129.sload (by native_decide) (by evm_ov)
  change RD _ _ _ _ _ (storedWord σ I ⟨209⟩ :: R) _ _ _ _ _ _ at rd1130
  have rd1135 := evm_run rd1130 with [iszero, dup1, push2 ⟨1150⟩]
  by_cases hz : (snapshotOf σ I).startTime = ⟨0⟩
  · change storedWord σ I ⟨209⟩ = ⟨0⟩ at hz
    have rd1150 := evm_run rd1135 with [jumpiT (by rw [hz]; decide) (by jump_dest)]
    exact ⟨_, _, by simpa only [unpauseCreateWord, snapshotOf, hz, if_pos rfl,
      show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from rfl] using rd1150⟩
  · have hsz : storedWord σ I ⟨209⟩ ≠ ⟨0⟩ := hz
    have rd1139 := evm_run rd1135 with [jumpiNT (isZero_eq_zero_of_ne hsz), pop, push1 ⟨211⟩]
    obtain ⟨_, _, rd1140⟩ := rd1139.sload (by native_decide) (by evm_ov)
    change RD _ _ _ _ _ (storedWord σ I ⟨211⟩ :: R) _ _ _ _ _ _ at rd1140
    have rd1150 := evm_run rd1140 with [push1 ⟨1⟩, push1 ⟨160⟩, shl, swap1, div,
      push1 ⟨255⟩, and]
    rw [u256_land_comm ⟨255⟩] at rd1150
    have hshift : UInt256.shiftLeft ⟨1⟩ ⟨160⟩ = ⟨2 ^ 160⟩ := by native_decide
    rw [hshift] at rd1150
    exact ⟨_, _, by simpa only [unpauseCreateWord, if_neg hsz, snapshotOf,
      Snapshot.settledByte, Snapshot.settledSourceWord] using rd1150⟩

end Auction
