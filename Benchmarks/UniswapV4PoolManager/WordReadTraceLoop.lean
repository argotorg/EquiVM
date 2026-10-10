import Benchmarks.UniswapV4PoolManager.WordArrayReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 3000

-- LIBRARY CANDIDATE: one word of progress in a natural-addressed memory loop.
theorem wordArrayStepWord (base i : Nat) :
    UInt256.ofNat (base+32*i) + UInt256.ofNat 32 = UInt256.ofNat (base+32*(i+1)) :=
  (ofNat_add_words _ _).trans (congrArg UInt256.ofNat (by omega))

def wordReadTraceStack (cursor : Nat → UInt256) (stride : UInt256) (n i : Nat) (R : List UInt256) : List UInt256 :=
  UInt256.ofNat (224+32*i) :: UInt256.ofNat 32 :: stride :: cursor i ::
  UInt256.ofNat (224+32*n) :: UInt256.ofNat (160+32*n) :: UInt256.ofNat 160 :: R

def wordReadTraceExitStack (cursor : Nat → UInt256) (n i : Nat) (R : List UInt256) : List UInt256 :=
  UInt256.ofNat 160 :: UInt256.ofNat (224+32*i) :: cursor i ::
  UInt256.ofNat (224+32*n) :: UInt256.ofNat (160+32*n) :: UInt256.ofNat 160 :: R

/-- Iterate a word-array read step while retaining the exact sequence of memory stores. -/
theorem wordReadTraceLoop {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {σ : AccountMap} {R : List UInt256} {n : Nat}
    {values cursor : Nat → UInt256} {loopPC stride : UInt256}
    (step : ∀ i mem aw k C, i < max 1 n →
      RD code I g s0 loopPC (wordReadTraceStack cursor stride n i R) mem aw rdata σ k C →
      ∃ aw' k' C', RD code I g s0 (if i+1 < n then loopPC else ⟨2508⟩)
        (if i+1 < n then wordReadTraceStack cursor stride n (i+1) R else wordReadTraceExitStack cursor n (i+1) R)
        (writeWord mem (224+32*i) (values i)) aw' rdata σ k' C')
    (remaining : Nat) :
    ∀ i mem aw k C, i + remaining + 1 = n →
      RD code I g s0 loopPC (wordReadTraceStack cursor stride n i R) mem aw rdata σ k C →
      ∃ aw' k' C', RD code I g s0 ⟨2508⟩ (wordReadTraceExitStack cursor n n R)
        (wordSequenceMemory mem (224+32*i) (wordArrayWords values i (remaining+1)))
        aw' rdata σ k' C' := by
  induction remaining with
  | zero =>
      intro i mem aw k C hi h
      obtain ⟨aw1, k1, C1, rd⟩ := step i mem aw k C (by omega) h
      refine ⟨aw1, k1, C1, ?_⟩
      simpa only [show ¬ i+1 < n by omega, if_false, show i+1 = n by omega,
        lt_self_iff_false, wordArrayWords, wordSequenceMemory] using rd
  | succ remaining ih =>
      intro i mem aw k C hi h
      obtain ⟨aw1, k1, C1, rd⟩ := step i mem aw k C (by omega) h
      simp only [show i+1 < n by omega, if_true] at rd
      obtain ⟨aw2, k2, C2, rd2⟩ := ih (i+1) _ aw1 k1 C1 (by omega) rd
      refine ⟨aw2, k2, C2, ?_⟩
      simpa only [wordArrayWords, wordSequenceMemory,
        show 224+32*i+32 = 224+32*(i+1) by omega] using rd2

end Benchmarks.UniswapV4PoolManager
