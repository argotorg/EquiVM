import Benchmarks.Morpho.MorphoBlue.TaylorRoutines
import Benchmarks.Morpho.MorphoBlue.WadSource
import Benchmarks.Morpho.MorphoBlue.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def accrueEventTopic : UInt256 :=
  UInt256.ofNat 71288448643491992918194495602724740086573393211427040093798850238947999600263

def accrueMathTail (id rate ret : UInt256) (R : List UInt256) : List UInt256 :=
  [rate, UInt256.ofNat 96, accrueEventTopic, id, id, UInt256.ofNat 32, UInt256.ofNat 3,
    UInt256.ofNat 0, UInt256.ofNat 64, UInt256.ofNat 2, uint128Mask, ret] ++ R

def accrueInterestWord (σ : AccountMap) (I : ExecutionEnv) (id rate elapsed : UInt256) : UInt256 :=
  wMulDownResult (marketFieldWord σ I id 2) (taylorWord rate elapsed)

section Routines
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {id rate elapsed ret : UInt256} {R : List UInt256}

theorem morphoAccrueReachTaylor (hstack : R.length + 40 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13407)
      ([UInt256.ofNat 96, elapsed, solcAddrMask, id, UInt256.ofNat 32, UInt256.ofNat 3,
        UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, ret, rate] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14395)
      ([rate, elapsed, UInt256.ofNat 13488, UInt256.ofNat 13563, marketFieldWord σ ee id 2,
        UInt256.ofNat 64, uint128Mask, id, UInt256.ofNat 32, solcAddrMask,
        UInt256.ofNat 0, UInt256.ofNat 3, UInt256.ofNat 13552] ++ accrueMathTail id rate ret R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_13407_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _
    ([rate, elapsed, UInt256.ofNat 13488, UInt256.ofNat 13563,
      UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem id (UInt256.ofNat 3) mem) + UInt256.ofNat 1) σ ee) uint128Mask,
      UInt256.ofNat 64, uint128Mask, id, UInt256.ofNat 32, solcAddrMask,
      UInt256.ofNat 0, UInt256.ofNat 3, UInt256.ofNat 13552] ++ accrueMathTail id rate ret R)
    (twoWordHashMem id (UInt256.ofNat 3) mem) _ _ _ _ _ at rd1
  have hh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem id (UInt256.ofNat 3) mem) = solcMappingSlot ⟨3⟩ id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  rw [hh] at rd1
  exact ⟨aw1, k1, C1, rd1⟩

theorem morphoAccrueReachInterestMul (hstack : R.length + 40 ≤ 1024) (hfit : TaylorFits rate elapsed)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13407)
      ([UInt256.ofNat 96, elapsed, solcAddrMask, id, UInt256.ofNat 32, UInt256.ofNat 3,
        UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, ret, rate] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14395)
      ([marketFieldWord σ ee id 2, taylorWord rate elapsed, UInt256.ofNat 13563, wad,
        UInt256.ofNat 64, uint128Mask, id, UInt256.ofNat 32, solcAddrMask,
        UInt256.ofNat 0, UInt256.ofNat 3, wad] ++ accrueMathTail id rate ret R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueReachTaylor (v := v) hstack h
  obtain ⟨k2, C2, rd2⟩ := morphoTaylorOk (v := v)
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega) hfit rd1
  exact ⟨aw1, k2, C2, rd2⟩

theorem morphoAccrueMathReverts (hstack : R.length + 40 ≤ 1024)
    (hbad : ¬ TaylorFits rate elapsed ∨ UInt256.size ≤
      (marketFieldWord σ ee id 2).toNat * (taylorWord rate elapsed).toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13407)
      ([UInt256.ofNat 96, elapsed, solcAddrMask, id, UInt256.ofNat 32, UInt256.ofNat 3,
        UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, ret, rate] ++ R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  by_cases hf : TaylorFits rate elapsed
  · obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueReachInterestMul (v := v) hstack hf h
    exact morphoCheckedMulReverts (v := v)
      (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega) (hbad.resolve_left (not_not.mpr hf)) rd1
  · obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueReachTaylor (v := v) hstack h
    exact morphoTaylorReverts (v := v)
      (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega) hf rd1

theorem morphoAccrueInterestOk (hstack : R.length + 40 ≤ 1024) (ht : TaylorFits rate elapsed)
    (hm : (marketFieldWord σ ee id 2).toNat * (taylorWord rate elapsed).toNat < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13407)
      ([UInt256.ofNat 96, elapsed, solcAddrMask, id, UInt256.ofNat 32, UInt256.ofNat 3,
        UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, ret, rate] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([accrueInterestWord σ ee id rate elapsed, UInt256.ofNat 13574, UInt256.ofNat 0,
        UInt256.ofNat 64, uint128Mask, id, UInt256.ofNat 32, solcAddrMask,
        accrueInterestWord σ ee id rate elapsed, UInt256.ofNat 3, wad] ++ accrueMathTail id rate ret R)
      (twoWordHashMem id (UInt256.ofNat 3) mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccrueReachInterestMul (v := v) hstack ht h
  obtain ⟨k2, C2, rd2⟩ := morphoCheckedMulOk (v := v)
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hm rd1
  have rd3 := morphoBlocks.morpho_block_13563 (immWords := wordsOf (immStore v))
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  exact ⟨aw1, _, _, rd3⟩

end Routines
end Benchmarks.Morpho.MorphoBlue
