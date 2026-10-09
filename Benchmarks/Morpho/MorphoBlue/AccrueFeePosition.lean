import Benchmarks.Morpho.MorphoBlue.AccrueMathRoutines
import Benchmarks.Morpho.MorphoBlue.MarketWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def accrueFeeRecipient (σ : AccountMap) (I : ExecutionEnv) : UInt256 := solcAddressSlotWord ⟨1⟩ σ I

def accrueFeePositionSlot (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) : UInt256 :=
  positionSlot id (accrueFeeRecipient σ I)

def accrueFeePositionMem (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) (mem : ByteArray) : ByteArray :=
  twoWordHashMem (accrueFeeRecipient σ I) (solcMappingSlot ⟨2⟩ id) (twoWordHashMem id (UInt256.ofNat 2) mem)

section Routines
variable {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
  {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
  {id rate interest shares ret : UInt256} {R : List UInt256}

theorem morphoAccruePositionReachAdd (hstack : R.length + 22 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13793)
      ([shares, interest, solcAddrMask] ++ accrueMathTail id rate ret R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12651)
      ([solcSlotWordAt (accrueFeePositionSlot σ ee id) σ ee, shares, UInt256.ofNat 13826,
        accrueFeePositionSlot σ ee id, interest, shares] ++ accrueMathTail id rate ret R)
      (accrueFeePositionMem σ ee id mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_13793_packed
    (immWords := wordsOf (immStore v))
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  let m1 := twoWordHashMem id (UInt256.ofNat 2) mem
  have hh1 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1 = solcMappingSlot ⟨2⟩ id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  let m2 := twoWordHashMem (accrueFeeRecipient σ ee)
    (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m1) m1
  have hm2 : m2 = accrueFeePositionMem σ ee id mem := by dsimp only [m2]; rw [hh1]; rfl
  have hh2 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (accrueFeePositionMem σ ee id mem) =
      accrueFeePositionSlot σ ee id := twoWordHashMem_solcMappingSlot_any _ _ _
  change RD _ _ _ _ _
    ([solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2) σ ee, shares,
      UInt256.ofNat 13826, keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) m2, interest, shares] ++
      accrueMathTail id rate ret R) m2 _ _ _ _ _ at rd1
  rw [hm2, hh2] at rd1
  exact ⟨aw1, k1, C1, rd1⟩

theorem morphoAccruePositionAddOk (hstack : R.length + 22 ≤ 1024)
    (hfit : (solcSlotWordAt (accrueFeePositionSlot σ ee id) σ ee).toNat + shares.toNat < UInt256.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13793)
      ([shares, interest, solcAddrMask] ++ accrueMathTail id rate ret R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13826)
      ([solcSlotWordAt (accrueFeePositionSlot σ ee id) σ ee + shares,
        accrueFeePositionSlot σ ee id, interest, shares] ++ accrueMathTail id rate ret R)
      (accrueFeePositionMem σ ee id mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccruePositionReachAdd (v := v) hstack h
  obtain ⟨k2, C2, rd2⟩ := morphoCheckedAddOk (v := v)
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hfit rd1
  exact ⟨aw1, k2, C2, rd2⟩

theorem morphoAccruePositionAddReverts (hstack : R.length + 22 ≤ 1024)
    (hover : UInt256.size ≤ (solcSlotWordAt (accrueFeePositionSlot σ ee id) σ ee).toNat + shares.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13793)
      ([shares, interest, solcAddrMask] ++ accrueMathTail id rate ret R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoAccruePositionReachAdd (v := v) hstack h
  exact morphoCheckedAddReverts (v := v)
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega) hover rd1

theorem morphoAccruePositionStore (hstack : R.length + 18 ≤ 1024) (hp : ee.perm = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13826)
      ([solcSlotWordAt (accrueFeePositionSlot σ ee id) σ ee + shares,
        accrueFeePositionSlot σ ee id, interest, shares] ++ accrueMathTail id rate ret R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15480)
      ([shares, UInt256.ofNat 13840, UInt256.ofNat 13863, interest, shares] ++ accrueMathTail id rate ret R)
      mem aw rdata (sstoreAccountMap ee.codeOwner σ (accrueFeePositionSlot σ ee id)
        (solcSlotWordAt (accrueFeePositionSlot σ ee id) σ ee + shares)) k' C' := by
  exact morphoBlocks.morpho_block_13826 (immWords := wordsOf (immStore v))
    (by simp only [accrueMathTail, List.append, List.length_append, List.length_cons, List.length_nil]; omega) hp
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h

end Routines
end Benchmarks.Morpho.MorphoBlue
