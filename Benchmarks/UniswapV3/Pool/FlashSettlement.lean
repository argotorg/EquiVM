import Benchmarks.UniswapV3.Pool.FlashUpdates
import Benchmarks.UniswapV3.Pool.FlashFinish

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem flashSettlementX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat}
    {aw junk after1 after0 before1 before0 fee1 fee0 liquidity len start amount1 amount0 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (recipient : AccountAddress) (locals : Store)
    (rd : RD (deployedRuntime v) ee g s0 ⟨7003⟩
      (after1 :: junk :: after0 :: before1 :: before0 :: fee1 :: fee0 :: liquidity :: len :: start ::
        amount1 :: amount0 :: EVM.word recipient.val :: ⟨857⟩ :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hrepay : FlashRepayValues locals before0 before1 fee0 fee1 after0 after1)
    (hcore : FlashCoreValues locals recipient amount0 amount1 liquidity)
    (hliquidity : liquidity.toNat < 2 ^ 128) (hov : R.length + 33 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
        (flashTransition.body.drop 17) .reverted) ∨
    ∃ evm' locals',
      ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
        (flashTransition.body.drop 17)
        (.ok {contract := contract, locals := locals', immutables := immStore v} evm') ∧
      RDret (deployedRuntime v) g s0 evm'.accountMap ByteArray.empty := by
  rcases flashRepaymentX (v := v) rd (by evm_ov) with
    ⟨rdBad, hvBad⟩ | ⟨hv0, hv1, kRepaid, CRepaid, rdRepaid⟩
  · refine Or.inl ⟨rdBad, ?_⟩
    rw [← List.take_append_drop 4 (flashTransition.body.drop 17)]
    exact execBlockAppendReverted
      (flashRepaymentReverts v locals evm _ _ _ _ _ _ hrepay hvBad)
  · have hsourceRepay := flashRepaymentReturns v locals evm _ _ _ _ _ _ hrepay ⟨hv0, hv1⟩
    let repaid := flashRepaidFrame v locals before0 before1 fee0 fee1
    have hsourcePaid := flashPaidSource v repaid.locals evm before0 before1 after0 after1
      (by simpa [repaid, flashRepaidFrame, flashRepayFrame, flashRepayName,
        Std.HashMap.getElem?_insert] using hrepay.before0)
      (by simpa [repaid, flashRepaidFrame, flashRepayFrame, flashRepayName,
        Std.HashMap.getElem?_insert] using hrepay.before1)
      (by simpa [repaid, flashRepaidFrame, flashRepayFrame, flashRepayName,
        Std.HashMap.getElem?_insert] using hrepay.after0)
      (by simpa [repaid, flashRepaidFrame, flashRepayFrame, flashRepayName,
        Std.HashMap.getElem?_insert] using hrepay.after1)
    let paid := flashPaidFrame v repaid.locals before0 before1 after0 after1
    have hcorePaid : FlashCoreValues paid.locals recipient amount0 amount1 liquidity :=
      (hcore.repaid v before0 before1 fee0 fee1).paid v before0 before1 after0 after1
    obtain ⟨_, _, rdPaid⟩ := flashPaidX (v := v) rdRepaid (by evm_ov)
    rcases flashUpdatesX (v := v) paid.locals rdPaid hs hperm hcorePaid
        (by simp [paid, flashPaidFrame, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
        (by simp [paid, flashPaidFrame]) hliquidity (by evm_ov) with
      ⟨rdBad, hbad⟩ | ⟨evm2, σ2, locals2, k2, C2, hs2, hsourceUpdates, rdDone, hcore2, hp0, hp1⟩
    · refine Or.inl ⟨rdBad, ?_⟩
      rw [← List.take_append_drop 4 (flashTransition.body.drop 17)]
      apply execBlock_append_ok hsourceRepay
      change ExecBlock _ _ _ (flashTransition.body.drop 21) _
      rw [← List.take_append_drop 2 (flashTransition.body.drop 21)]
      apply execBlock_append_ok hsourcePaid
      change ExecBlock _ _ _ (flashTransition.body.drop 23) _
      rw [← List.take_append_drop 2 (flashTransition.body.drop 23)]
      exact execBlockAppendReverted hbad
    · refine Or.inr ⟨storeSlot0Unlocked evm2 true, locals2, ?_,
        flashFinishX (v := v) rdDone hs2 hperm (by evm_ov)⟩
      rw [← List.take_append_drop 4 (flashTransition.body.drop 17)]
      apply execBlock_append_ok hsourceRepay
      change ExecBlock _ _ _ (flashTransition.body.drop 21) _
      rw [← List.take_append_drop 2 (flashTransition.body.drop 21)]
      apply execBlock_append_ok hsourcePaid
      change ExecBlock _ _ _ (flashTransition.body.drop 23) _
      rw [← List.take_append_drop 2 (flashTransition.body.drop 23)]
      apply execBlock_append_ok hsourceUpdates
      exact flashFinishSource locals2 (immStore v) evm2 recipient amount0 amount1 _ _
        hcore2.recipient hcore2.amount0 hcore2.amount1 hp0 hp1 hcore2.slot0

end Benchmarks.UniswapV3.Pool
