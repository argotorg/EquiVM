import Benchmarks.Morpho.MorphoBlue.AccrueMathRoutines
import Benchmarks.Morpho.MorphoBlue.AccrueRoutinesStart

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def accrueEventMem (mem : ByteArray) (rate interest shares : UInt256) : ByteArray :=
  let fp := memLoad (UInt256.ofNat 64) mem
  writeWord (writeWord (writeWord mem fp.toNat rate) (fp + UInt256.ofNat 32).toNat interest)
    (fp + UInt256.ofNat 64).toNat shares

section Routines
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {id rate interest shares ret : UInt256} {R : List UInt256}

theorem morphoAccrueLogReturn {j0 j7 j10 : UInt256} (hstack : R.length + 23 ≤ 1024)
    (hp : ee.perm = true) (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13706)
      ([j0, UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, id,
        UInt256.ofNat 32, j7, interest, shares, j10] ++ accrueMathTail id rate ret R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret R
      (twoWordHashMem id (UInt256.ofNat 3) (accrueEventMem mem rate interest shares)) aw' rdata
      (storeMarketFieldAccounts σ ee id ⟨4, by decide⟩
        (halfWord false (UInt256.ofNat ee.header.timestamp))) k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_13706_packed
    (immWords := wordsOf (immStore v))
    (by simp only [accrueMathTail, List.append]; omega) hp
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoAccrueStoreTimestamp (v := v) id (by omega) hp hvalid rd1

theorem morphoAccrueFeeLogReturn (hstack : R.length + 24 ≤ 1024)
    (hp : ee.perm = true) (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13863)
      ([interest, shares] ++ accrueMathTail id rate ret R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret R
      (twoWordHashMem id (UInt256.ofNat 3) (accrueEventMem mem rate interest shares)) aw' rdata
      (storeMarketFieldAccounts σ ee id ⟨4, by decide⟩
        (halfWord false (UInt256.ofNat ee.header.timestamp))) k' C' := by
  have rd1 := morphoBlocks.morpho_block_13863 (immWords := wordsOf (immStore v))
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  exact morphoAccrueLogReturn (v := v) (by omega) hp hvalid rd1

end Routines
end Benchmarks.Morpho.MorphoBlue
