import Benchmarks.EAS.EAS.BytesClearPrepare

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem easBytesClean {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src dataPtr slot word len old t1 t2 t3 t4 : UInt256} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+24 ≤ 1024) (hp : ee.perm = true)
    (hold : old.toNat < 2^255) (hlen : len.toNat+31 < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordBytesDecodedPC site)
      (old::dataPtr::len::slot::recordBytesSaved site word src t1 t2 t3 t4 R) mem aw rdata σ k C) :
    ∃ mem' aw' k' C',
      (mem' = mem ∨ mem' = Reasoning.Theory.writeWord mem 0 (slot+⟨6⟩)) ∧
      RD fork (deployedRuntime v) ee g s0 (recordBytesCleanPC site)
        (old::dataPtr::len::slot::recordBytesSaved site word src t1 t2 t3 t4 R) mem' aw' rdata
        (bytesCleanAccounts σ ee (slot+⟨6⟩) old.toNat len.toNat) k' C' := by
  have hd := easBytesCleanDispatch v site hstack rd
  by_cases hskip : old.toNat < 32 ∨ old.toNat ≤ len.toNat
  · rw [if_pos hskip] at hd
    obtain ⟨aw',k',C',hr⟩ := hd
    refine ⟨mem,aw',k',C',Or.inl rfl,?_⟩
    simpa only [bytesClearAccounts_skip σ ee (slot+⟨6⟩) old.toNat len.toNat hskip] using hr
  · rw [if_neg hskip] at hd
    have ho : ¬ old.toNat < 32 := fun h => hskip (Or.inl h)
    have hless : len.toNat < old.toNat := by
      have hle : ¬ old.toNat ≤ len.toNat := fun h => hskip (Or.inr h)
      omega
    obtain ⟨aw1,k1,C1,hr1⟩ := hd
    obtain ⟨aw2,k2,C2,hr2⟩ := easBytesClearPrepare v site hstack hlen hr1
    let first := bytesFirstClear len.toNat
    let count := solidityBytesDataWordCount old.toNat
    have hf : first ≤ count := bytesFirstClear_le hless
    have hcb : count < 2^251 := by dsimp only [count,solidityBytesDataWordCount]; omega
    have hcu : count < UInt256.size := lt_trans hcb (by decide)
    have hlimit : (bytesClearLimit old (UInt256.ofNat first)).toNat = 0+(count-first) := by
      unfold bytesClearLimit
      rw [bytesWordCount_word old (by change old.toNat+31 < 2^256; omega)]
      simpa only [Nat.zero_add] using usub_ofNat_lit_toNat hf hcu
    obtain ⟨aw3,k3,C3,hr3⟩ := easBytesClearLoop v site
      (by cases site <;> simp only [bytesClearLoopSaved,recordBytesSaved,List.length_cons] <;> omega)
      hp 0 (count-first) hlimit hr2
    rw [clearDataWordsForwardFrom_shift_ofNat first (UInt256.ofNat 0) (count-first) (by omega)] at hr3
    have hz : UInt256.ofNat first + UInt256.ofNat 0 = UInt256.ofNat first := uint256_add_zero_right _
    rw [hz] at hr3
    obtain ⟨aw4,k4,C4,hr4⟩ := easBytesClearFinish v site hstack hr3
    refine ⟨Reasoning.Theory.writeWord mem 0 (slot+⟨6⟩),aw4,k4,C4,?_,?_⟩
    · right
      rfl
    · simpa only [bytesCleanAccounts,if_neg ho,bytesFirstClear,first,count] using hr4

end Benchmarks.EAS.EAS
