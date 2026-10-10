import Benchmarks.CompoundIII.Comet.TransferBaseSupplyTotalsEvm
import Benchmarks.CompoundIII.Comet.TransferBaseBorrowTotalsEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

theorem cometTransferBaseTotals {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw supplied repaid withdrawn borrowed srcNext srcPtr dstNext dstPtr balance src : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hS : supplied.toNat < 2^104) (hW : withdrawn.toNat < 2^104)
    (hB : borrowed.toNat < 2^104) (hR : repaid.toNat < 2^104)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨14841⟩
      (supplied :: repaid :: srcNext :: srcPtr :: dstNext :: dstPtr :: balance :: withdrawn ::
        src :: borrowed :: R) mem aw rdata σ k C) :
    internalRun (deployedRuntime v) ee g s0 mem aw rdata ⟨14930⟩
      (srcNext :: srcPtr :: dstNext :: dstPtr :: balance :: withdrawn :: src :: supplied :: R)
      (transferBaseTotalsOutcome evm supplied withdrawn borrowed repaid) := by
  have hfirst := cometTransferBaseSupplyTotals hstack hS hW hs h
  cases ho : totalsChangeOutcome evm false supplied withdrawn with
  | reverted =>
      simpa only [transferBaseTotalsOutcome, ho] using hfirst
  | staticViolation =>
      simpa only [transferBaseTotalsOutcome, ho] using hfirst
  | ok evm' =>
      simp only [ho, internalRun] at hfirst
      obtain ⟨σ1, k1, C1, hs1, r1⟩ := hfirst
      have hsecond := cometTransferBaseBorrowTotals
        (by change R.length + 8 + 7 ≤ 1024; omega) hB hR (totalsChangeOutcome_perm ho) hs1 r1
      simpa only [transferBaseTotalsOutcome, ho] using hsecond

end Benchmarks.CompoundIII.Comet
