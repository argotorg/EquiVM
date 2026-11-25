import Benchmarks.Midnight.MulticallStep
import Benchmarks.Midnight.MulticallArrayDecode

variable {fork : Ethereum.Fork}

/-! A malformed later calldata tail still forces the complete multicall to revert. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMulticallInvalidLoop (remaining : Nat) {I : ExecutionEnv} {g : UInt256}
    {s0 evm : State} {mem rdata : ByteArray} {aw root base index count : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024) (hr : count.toNat = index.toNat + remaining)
    (hn : count.toNat < 2^64) (hsz : I.calldata.size < 2^255)
    (hspan : base.toNat + 32 * count.toNat ≤ I.calldata.size)
    (hbad : ¬ MulticallTailsValid I.calldata base index.toNat remaining)
    (hm : 832 ≤ mem.size) (hl : 832 ≤ root.toNat)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hh : TransferHeap mem aw root C) (hgas : midnightGasBound g) (hfork : fork ≥ .osaka)
    (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨3605⟩
      (index :: base :: multicallTailBound I.calldata base :: count :: R) mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0 := by
  induction remaining generalizing evm mem rdata aw root index σ k C with
  | zero => exact False.elim (hbad (by intro i hi; omega))
  | succ remaining ih =>
    have hi : index.toNat < count.toNat := by omega
    have hadd : (index + (⟨1⟩ : UInt256)).toNat = index.toNat + 1 :=
      uadd_word_ofNat_toNat index 1 (by change index.toNat + 1 < 2^256; omega)
    rcases midnightMulticallStep hstack hi hn hsz hspan hm hl hz hh hgas hfork hs rd with
      hoog | ⟨_, hrev⟩ | ⟨_, _, _, _, _, hrev⟩ | hsuccess
    · exact Or.inl hoog
    · exact Or.inr hrev
    · exact Or.inr hrev
    · obtain ⟨evm1, σ1, out, mem1, root1, aw1, k1, C1, hv, _, _, hs1, hp, hroot, hh1, rd1⟩ :=
        hsuccess
      apply ih (by rw [hadd]; omega) ?_ (hm.trans hp.size) (hl.trans hroot) ?_ hh1 hs1 rd1
      · rw [hadd]
        intro hnext
        exact hbad ((multicallTailsValid_succ _ _ _ _).mpr ⟨hv, hnext⟩)
      · rw [hp.load (UInt256.ofNat 800) (by decide) hl hm, hz]

end Benchmarks.Midnight
