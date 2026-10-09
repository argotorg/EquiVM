import Benchmarks.Morpho.MorphoBlue.MarketParamsMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: every indexed load from a freshly written contiguous word buffer.
theorem memLoad_writeReturnWords (ws : List UInt256) (mem : ByteArray) (off : Nat)
    (i : Fin ws.length) (hg : off - mem.size < USize.size)
    (hb : off + 32 * ws.length < UInt256.size) :
    memLoad (UInt256.ofNat (off + 32 * i.val))
      (writeCascade mem (returnWordWrites off ws)) = ws[i] := by
  induction ws generalizing mem off with
  | nil => exact Fin.elim0 i
  | cons w ws ih =>
    have hs := writeWord_size mem off w hg
    have hg' : off + 32 - (writeWord mem off w).size < USize.size := by
      rw [hs]; have hp := USize.size_pos; omega
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero,
        returnWordWrites, writeCascade_cons]
      rw [memLoad_writeReturnWords_below _ _ _ _ hg']
      · exact memLoad_writeWord_self_of_offset mem off w (UInt256.ofNat off) hg
          (UInt256.toNat_ofNat_of_lt (by have := hb; omega)).symm
      · rw [UInt256.toNat_ofNat_of_lt (by have := hb; omega), hs]; omega
      · rw [UInt256.toNat_ofNat_of_lt (by have := hb; omega)]
    | succ i =>
      have hi := ih (writeWord mem off w) (off + 32) i hg' (by
        simp only [List.length_cons] at hb; omega)
      simpa only [returnWordWrites, writeCascade_cons, Fin.val_succ, List.getElem_cons_succ,
        Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

end Benchmarks.Morpho.MorphoBlue
