import Benchmarks.Midnight.MulticallCall
import Benchmarks.Midnight.MulticallTailTrace
import Benchmarks.Midnight.RuntimeBlocks_016

variable {fork : Ethereum.Fork}

/-! A complete iteration of the multicall runtime loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMulticallStep {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {mem rdata : ByteArray} {aw root base index count : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 14 ≤ 1024)
    (hi : index.toNat < count.toNat) (hn : count.toNat < 2^64)
    (hsz : I.calldata.size < 2^255) (hspan : base.toNat + 32 * count.toNat ≤ I.calldata.size)
    (hm : 832 ≤ mem.size) (hl : 832 ≤ root.toNat)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hh : TransferHeap mem aw root C) (hgas : midnightGasBound g) (hfork : fork ≥ .osaka)
    (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨3605⟩
      (index :: base :: multicallTailBound I.calldata base :: count :: R) mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (¬ MulticallTailValid I.calldata base index.toNat ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    (∃ evm' success out, delegateCallViaEVM fork evm I.codeOwner
        (multicallBytesAt I.calldata base index.toNat) (success, evm', out) ∧
      (success = false ∨ 2^64 ≤ out.size) ∧ RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (out mem' : ByteArray) (root' aw' : UInt256) (k' C' : Nat),
      MulticallTailValid I.calldata base index.toNat ∧
      delegateCallViaEVM fork evm I.codeOwner (multicallBytesAt I.calldata base index.toNat)
        (true, evm', out) ∧ out.size < 2^64 ∧
      SourceState s0 I σ' evm' ∧ MemoryPrefix mem mem' root.toNat ∧
      root.toNat ≤ root'.toNat ∧ TransferHeap mem' aw' root' C' ∧
      RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨3605⟩
        ((index + ⟨1⟩) :: base :: multicallTailBound I.calldata base :: count :: R)
        mem' aw' out σ' k' C' := by
  have hc : UInt256.isZero (UInt256.lt index count) = ⟨0⟩ := by rw [ult_one hi]; rfl
  have rd1 := midnightBlocks.midnight_block_3605_fallthrough (by omega) hc rd
  rcases midnightMulticallTail (by simp only [List.length_cons]; omega) (by omega)
      (by change _ < 2^256; omega) rd1 with
    ⟨hbad, hrev⟩ | ⟨hv, k2, C2, hc2, rd2⟩
  · exact Or.inr (Or.inl ⟨hbad, hrev⟩)
  · rcases midnightMulticallCall (by simp only [List.length_cons]; omega) hm hl hz hv.2.1
        (hv.copyBounds hsz (by omega)) (hh.mono (by omega)) hgas hfork hs rd2 with
      hoog | hrev | ⟨evm', σ', out, mem', root', retptr, aw3, k3, C3,
        hcall, hout, hs', hp, hroot, hh3, rd3⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inr (Or.inl hrev))
    · have rd4 := midnightBlocks.midnight_block_3707
        (by simp only [List.length_cons]; omega) (by jump_dest) rd3
      simp only [midnightBlocks.midnight_block_3707_stack,
        u256_add_comm (UInt256.ofNat 1) index] at rd4
      exact Or.inr (Or.inr (Or.inr ⟨evm', σ', out, mem', root', aw3, _, _, hv,
        hcall, hout, hs', hp, hroot, hh3.mono (by omega), rd4⟩))

end Benchmarks.Midnight
