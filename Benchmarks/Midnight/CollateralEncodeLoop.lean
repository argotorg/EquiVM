import Benchmarks.Midnight.CollateralEncodeStep
import Benchmarks.Midnight.CollateralHeapMemory

variable {fork : Ethereum.Fork}

/-! The ABI encoder's collateral-array loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightCollateralEncodeLoop {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw writePtr output index count market outputBase : UInt256}
    {σ : AccountMap} {limit k C : Nat} {R : List UInt256} (cs : List CollateralData)
    (hstack : R.length + 15 ≤ 1024)
    (hs : CollateralListStored mem writePtr limit cs)
    (hc : count.toNat = index.toNat + cs.length)
    (hbelow : limit ≤ output.toNat) (hout : output.toNat + 128 * cs.length < UInt256.size)
    (rd : RD fork midnightBytecode I g s0 ⟨19261⟩
      (index :: count :: writePtr :: market :: outputBase :: output :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ⟨19269⟩
      (count :: count :: (writePtr + UInt256.ofNat (32 * cs.length)) :: market :: outputBase ::
        (output + UInt256.ofNat (128 * cs.length)) :: R)
      (writeWordArray mem output.toNat (cs.flatMap CollateralData.words)) aw' rdata σ k' C' := by
  induction cs generalizing mem writePtr output index aw k C with
  | nil =>
    have he : index = count := by
      cases index; cases count; congr 1; apply Fin.ext; simpa using hc.symm
    have hcond : UInt256.lt index count = UInt256.ofNat 0 := ult_zero (by simpa using hc.le)
    have rd1 := midnightBlocks.midnight_block_19261_fallthrough
      (by simp only [List.length_cons]; omega) hcond rd
    exact ⟨_, _, _, by simpa only [he, List.length_nil, Nat.mul_zero, wordAddNat_zero,
      List.flatMap_nil, writeWordArray] using rd1⟩
  | cons c cs ih =>
    simp only [List.length_cons] at hc hout
    rcases hs with ⟨ptr, _, _, _, hptr, _, hplim, hm, ht⟩
    have hlt : UInt256.lt index count = UInt256.ofNat 1 := ult_one (by omega)
    have rd1 := midnightBlocks.midnight_block_19261_taken
      (by simp only [List.length_cons]; omega) (by rw [hlt]; decide) (by jump_dest) rd
    obtain ⟨aw1, k1, C1, rd2⟩ := midnightCollateralEncodeStep c hstack hptr hm
      (by omega) (by omega) rd1
    have hi : (index + UInt256.ofNat 1).toNat = index.toNat + 1 :=
      uadd_word_ofNat_toNat _ _ (by have hh : count.toNat < UInt256.size := count.val.isLt; omega)
    have ho : (output + UInt256.ofNat 128).toNat = output.toNat + 128 :=
      uadd_word_ofNat_toNat _ _ (by omega)
    have ht' := ht.preserve (memoryPrefix_writeWordArray mem output.toNat limit c.words hbelow)
    obtain ⟨aw2, k2, C2, rd3⟩ := ih ht' (by rw [hi]; omega)
      (by rw [ho]; omega) (by rw [ho]; omega) rd2
    refine ⟨aw2, k2, C2, ?_⟩
    simpa only [List.length_cons, List.flatMap_cons, writeWordArray_append,
      show c.words.length = 4 from rfl, Nat.reduceMul, ho, wordAddNat_add,
      show 32 + 32 * cs.length = 32 * (cs.length + 1) by omega,
      show 128 + 128 * cs.length = 128 * (cs.length + 1) by omega] using rd3

end Benchmarks.Midnight
