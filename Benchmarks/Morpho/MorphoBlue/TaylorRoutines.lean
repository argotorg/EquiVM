import Benchmarks.Morpho.MorphoBlue.ArithmeticRoutines
import Benchmarks.Morpho.MorphoBlue.MathValues

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

section Taylor
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {x n ret assets b0 b1 b2 b3 b4 b5 b6 : UInt256} {R : List UInt256}

theorem morphoTaylorReachSquare (hstack : R.length + 25 ≤ 1024)
    (hfit : x.toNat * n.toNat < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14395)
      ([x, n, UInt256.ofNat 13488, ret, assets, b0, b1, b2, b3, b4, b5, b6,
        UInt256.ofNat 13552] ++ R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14395)
      ([taylorTerm1 x n, taylorTerm1 x n, UInt256.ofNat 13511,
        UInt256.ofNat 2000000000000000000, UInt256.ofNat 13557, assets, ret,
        taylorTerm1 x n, b0, b1, b2, b3, b4, b5, b6, UInt256.ofNat 13552] ++ R)
      mem aw rdata σ k' C' := by
  obtain ⟨k1, C1, rd1⟩ := morphoCheckedMulOk (v := v)
    (by simp only [List.append, List.length_cons, List.length_append, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hfit h
  have rd2 := morphoBlocks.morpho_block_13488 (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons, List.length_append, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  exact ⟨_, _, rd2⟩

theorem morphoTaylorReachCube (hstack : R.length + 25 ≤ 1024)
    (hfit : (taylorTerm1 x n).toNat * (taylorTerm1 x n).toNat < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14395)
      ([taylorTerm1 x n, taylorTerm1 x n, UInt256.ofNat 13511,
        UInt256.ofNat 2000000000000000000, UInt256.ofNat 13557, assets, ret,
        taylorTerm1 x n, b0, b1, b2, b3, b4, b5, b6, UInt256.ofNat 13552] ++ R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14395)
      ([taylorTerm2 x n, taylorTerm1 x n, UInt256.ofNat 13545,
        UInt256.ofNat 3000000000000000000, taylorTerm2 x n, UInt256.ofNat 13552,
        taylorTerm1 x n, UInt256.ofNat 13557, assets, ret, wad,
        b0, b1, b2, b3, b4, b5, b6, wad] ++ R)
      mem aw rdata σ k' C' := by
  obtain ⟨k1, C1, rd1⟩ := morphoCheckedMulOk (v := v)
    (by simp only [List.append, List.length_cons, List.length_append, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hfit h
  have rd2 := morphoBlocks.morpho_block_13511 (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons, List.length_append, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  exact ⟨_, _, rd2⟩

theorem morphoTaylorReachAdd (hstack : R.length + 25 ≤ 1024)
    (hfit : (taylorTerm2 x n).toNat * (taylorTerm1 x n).toNat < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14395)
      ([taylorTerm2 x n, taylorTerm1 x n, UInt256.ofNat 13545,
        UInt256.ofNat 3000000000000000000, taylorTerm2 x n, UInt256.ofNat 13552,
        taylorTerm1 x n, UInt256.ofNat 13557, assets, ret, wad,
        b0, b1, b2, b3, b4, b5, b6, wad] ++ R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12651)
      ([taylorTerm1 x n, taylorTerm2 x n, UInt256.ofNat 13552, taylorTerm3 x n,
        UInt256.ofNat 13557, assets, ret, wad, b0, b1, b2, b3, b4, b5, b6, wad] ++ R)
      mem aw rdata σ k' C' := by
  obtain ⟨k1, C1, rd1⟩ := morphoCheckedMulOk (v := v)
    (by simp only [List.append, List.length_cons, List.length_append, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hfit h
  have rd2 := morphoBlocks.morpho_block_13545 (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons, List.length_append, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  exact ⟨_, _, rd2⟩

theorem morphoTaylorReachLastAdd (hstack : R.length + 25 ≤ 1024)
    (hfit : (taylorTerm1 x n).toNat + (taylorTerm2 x n).toNat < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12651)
      ([taylorTerm1 x n, taylorTerm2 x n, UInt256.ofNat 13552, taylorTerm3 x n,
        UInt256.ofNat 13557, assets, ret, wad, b0, b1, b2, b3, b4, b5, b6, wad] ++ R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12651)
      ([taylorTerm1 x n + taylorTerm2 x n, taylorTerm3 x n, UInt256.ofNat 13557,
        assets, ret, wad, b0, b1, b2, b3, b4, b5, b6, wad] ++ R)
      mem aw rdata σ k' C' := by
  obtain ⟨k1, C1, rd1⟩ := morphoCheckedAddOk (v := v)
    (by simp only [List.append, List.length_cons, List.length_append, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hfit h
  have rd2 := morphoBlocks.morpho_block_13552 (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons, List.length_append, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  exact ⟨_, _, rd2⟩

theorem morphoTaylorOk (hstack : R.length + 25 ≤ 1024) (hfit : TaylorFits x n)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14395)
      ([x, n, UInt256.ofNat 13488, ret, assets, b0, b1, b2, b3, b4, b5, b6,
        UInt256.ofNat 13552] ++ R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14395)
      ([assets, taylorWord x n, ret, wad, b0, b1, b2, b3, b4, b5, b6, wad] ++ R)
      mem aw rdata σ k' C' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hfit
  obtain ⟨k1, C1, rd1⟩ := morphoTaylorReachSquare (v := v) hstack h1 h
  obtain ⟨k2, C2, rd2⟩ := morphoTaylorReachCube (v := v) hstack h2 rd1
  obtain ⟨k3, C3, rd3⟩ := morphoTaylorReachAdd (v := v) hstack h3 rd2
  obtain ⟨k4, C4, rd4⟩ := morphoTaylorReachLastAdd (v := v) hstack h4 rd3
  obtain ⟨k5, C5, rd5⟩ := morphoCheckedAddOk (v := v)
    (by simp only [List.append, List.length_cons, List.length_append, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) h5 rd4
  have rd6 := morphoBlocks.morpho_block_13557 (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons, List.length_append, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd5
  exact ⟨_, _, rd6⟩

theorem morphoTaylorReverts (hstack : R.length + 25 ≤ 1024) (hbad : ¬ TaylorFits x n)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14395)
      ([x, n, UInt256.ofNat 13488, ret, assets, b0, b1, b2, b3, b4, b5, b6,
        UInt256.ofNat 13552] ++ R) mem aw rdata σ k C) : RDrev (deployedRuntime v) g s0 := by
  by_cases h1 : x.toNat * n.toNat < UInt256.size
  · obtain ⟨k1, C1, rd1⟩ := morphoTaylorReachSquare (v := v) hstack h1 h
    by_cases h2 : (taylorTerm1 x n).toNat * (taylorTerm1 x n).toNat < UInt256.size
    · obtain ⟨k2, C2, rd2⟩ := morphoTaylorReachCube (v := v) hstack h2 rd1
      by_cases h3 : (taylorTerm2 x n).toNat * (taylorTerm1 x n).toNat < UInt256.size
      · obtain ⟨k3, C3, rd3⟩ := morphoTaylorReachAdd (v := v) hstack h3 rd2
        by_cases h4 : (taylorTerm1 x n).toNat + (taylorTerm2 x n).toNat < UInt256.size
        · obtain ⟨k4, C4, rd4⟩ := morphoTaylorReachLastAdd (v := v) hstack h4 rd3
          have h5 : UInt256.size ≤ (taylorTerm1 x n + taylorTerm2 x n).toNat +
              (taylorTerm3 x n).toNat := Nat.le_of_not_gt (fun h5 ↦ hbad ⟨h1, h2, h3, h4, h5⟩)
          exact morphoCheckedAddReverts (v := v)
            (by simp only [List.append, List.length_cons, List.length_nil]; omega) h5 rd4
        · exact morphoCheckedAddReverts (v := v)
            (by simp only [List.append, List.length_cons, List.length_nil]; omega)
            (Nat.le_of_not_gt h4) rd3
      · exact morphoCheckedMulReverts (v := v)
          (by simp only [List.append, List.length_cons, List.length_nil]; omega)
          (Nat.le_of_not_gt h3) rd2
    · exact morphoCheckedMulReverts (v := v)
        (by simp only [List.append, List.length_cons, List.length_nil]; omega)
        (Nat.le_of_not_gt h2) rd1
  · exact morphoCheckedMulReverts (v := v)
      (by simp only [List.append, List.length_cons, List.length_nil]; omega)
      (Nat.le_of_not_gt h1) h

end Taylor
end Benchmarks.Morpho.MorphoBlue
