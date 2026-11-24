import Benchmarks.EAS.EAS.RecordArrayLoopViews

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def recordArrayStack (base array : UInt256) (ats : List AttestationRecord) (i : Nat) (R : List UInt256) : List UInt256 :=
  UInt256.ofNat (recordArrayHead base i)::UInt256.ofNat i::UInt256.ofNat ats.length::
    UInt256.ofNat (array.toNat+32+32*i)::base::UInt256.ofNat (recordArrayTail base ats i)::R

theorem easEncodeRecordArrayStep_view {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {before mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {base array : UInt256} {ats : List AttestationRecord} {limit i : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+23 ≤ 1024)
    (harray : AttestationArrayMemoryView before array ats limit)
    (h : RecordArrayLoopView before mem base ats limit i) (hi : i < ats.length)
    (hbase : limit ≤ base.toNat)
    (hbound : base.toNat+128+attestationArrayOffset ats ats.length < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨14292⟩ (recordArrayStack base array ats i R) mem aw rdata σ k C) :
    ∃ mem' aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨14292⟩ (recordArrayStack base array ats (i+1) R) mem' aw' rdata σ k' C' ∧
      RecordArrayLoopView before mem' base ats limit (i+1) := by
  have hlimit : limit < UInt256.size := by omega
  have hav := harray.preserve h.front hlimit
  obtain ⟨src, dataPtr, hload, hsrcview, hsrc, hdata⟩ := hav.records i hi
  have ho := attestationArrayOffset_le ats i
  have hon := attestationArrayOffset_le ats (i+1)
  have he := (ats[i]).encoding_size
  have hs := (attestationArray_step ats i hi).2.2
  have hh : recordArrayHead base i < UInt256.size := by unfold recordArrayHead attestationArrayOffset at *; omega
  have ht : recordArrayTail base ats i < UInt256.size := by unfold recordArrayTail; omega
  have hhn : (UInt256.ofNat (recordArrayHead base i)).toNat = recordArrayHead base i := ulit_toNat' _ hh
  have htn : (UInt256.ofNat (recordArrayTail base ats i)).toNat = recordArrayTail base ats i := ulit_toNat' _ ht
  have hsn : (UInt256.ofNat (array.toNat+32+32*i)).toNat = array.toNat+32+32*i :=
    ulit_toNat' _ (by have := harray.span; omega)
  have hlen : ats.length < UInt256.size := by have := harray.span; omega
  have hiw : (UInt256.ofNat i).toNat < (UInt256.ofNat ats.length).toNat := by
    rw [ulit_toNat' _ (by omega), ulit_toNat' _ hlen]
    exact hi
  have hhead : limit ≤ (UInt256.ofNat (recordArrayHead base i)).toNat := by rw [hhn]; unfold recordArrayHead; omega
  have htail : (UInt256.ofNat (recordArrayHead base i)).toNat+32 ≤
      (UInt256.ofNat (recordArrayTail base ats i)).toNat := by
    rw [hhn, htn]
    unfold recordArrayHead recordArrayTail attestationArrayOffset
    omega
  have hfit : (UInt256.ofNat (recordArrayTail base ats i)).toNat+384+32*((ats[i].data.size+31)/32) < UInt256.size := by
    rw [htn]
    unfold recordArrayTail
    omega
  obtain ⟨aw1,k1,C1,rd1⟩ := easEncodeRecordArrayStep v limit hstack hiw hsrcview
    (by rw [hsn]; have := harray.low; omega)
    (by rw [hsn]; have := hav.covered; omega)
    (by rw [hsn]; have := harray.span; omega) hload hsrc hdata hhead htail hfit rd
  have hv := recordArrayStepMemory_view mem (UInt256.ofNat (recordArrayHead base i)) base
    (UInt256.ofNat (recordArrayTail base ats i)) src dataPtr ats[i] hsrcview
    (le_trans hsrc hhead) (le_trans hdata hhead) htail hfit
  have hi' : RecordArrayLoopView before _ base ats limit (i+1) := recordArrayLoopStep_view h hi
    (by have := harray.low; have := harray.span; omega) hbase hbound hv
  have hhinc : UInt256.ofNat (recordArrayHead base i)+(⟨32⟩ : UInt256) = UInt256.ofNat (recordArrayHead base (i+1)) := by
    rw [u256_add_comm]
    simpa only [recordArrayHead_step] using u256_32_add_ofNat (recordArrayHead base i)
  have hiinc : UInt256.ofNat i+(⟨1⟩ : UInt256) = UInt256.ofNat (i+1) := by
    rw [u256_add_comm]
    exact u256_one_add_ofNat i
  have hsinc : UInt256.ofNat (array.toNat+32+32*i)+(⟨32⟩ : UInt256) = UInt256.ofNat (array.toNat+32+32*(i+1)) := by
    rw [u256_add_comm, u256_32_add_ofNat]
    congr 1
  rw [hhinc, hiinc, hsinc, htn, ← recordArrayTail_step base ats i hi] at rd1
  exact ⟨_,aw1,k1,C1,rd1,hi'⟩

structure RecordArrayCursor where
  index : Nat
  memory : ByteArray
  active : UInt256

theorem easEncodeRecordArrayLoop {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {before mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {base array : UInt256} {ats : List AttestationRecord} {limit i : Nat} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+23 ≤ 1024)
    (harray : AttestationArrayMemoryView before array ats limit)
    (h : RecordArrayLoopView before mem base ats limit i)
    (hbase : limit ≤ base.toNat)
    (hbound : base.toNat+128+attestationArrayOffset ats ats.length < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨14292⟩ (recordArrayStack base array ats i R) mem aw rdata σ k C) :
    ∃ mem' aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨14300⟩ (recordArrayStack base array ats ats.length R) mem' aw' rdata σ k' C' ∧
      RecordArrayLoopView before mem' base ats limit ats.length := by
  let Inv := fun n (c : RecordArrayCursor) => c.index+n=ats.length ∧ RecordArrayLoopView before c.memory base ats limit c.index
  let stk := fun c : RecordArrayCursor => recordArrayStack base array ats c.index R
  have hx : ∀ c, Inv 0 c → ∀ k C,
      RD fork (deployedRuntime v) ee g s0 ⟨14292⟩ (stk c) c.memory c.active rdata σ k C →
      ∃ k' C', RD fork (deployedRuntime v) ee g s0 ⟨14300⟩ (stk c) c.memory c.active rdata σ k' C' := by
    intro c hc k C rd
    have hi0 : c.index=ats.length := by have := hc.1; omega
    have hlt : UInt256.lt (UInt256.ofNat c.index) (UInt256.ofNat ats.length) = ⟨0⟩ := by
      rw [hi0]
      exact ult_zero (le_refl _)
    have rd1 := easBlocks.eas_block_14292_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hlt rd
    exact ⟨_,_,rd1⟩
  have hs : ∀ n c, Inv (n+1) c → ∀ k C,
      RD fork (deployedRuntime v) ee g s0 ⟨14292⟩ (stk c) c.memory c.active rdata σ k C →
      ∃ c' k' C', Inv n c' ∧ RD fork (deployedRuntime v) ee g s0 ⟨14292⟩ (stk c') c'.memory c'.active rdata σ k' C' := by
    intro n c hc k C rd
    have hi : c.index < ats.length := by have := hc.1; omega
    obtain ⟨mem',aw',k',C',rd',hv⟩ := easEncodeRecordArrayStep_view v hstack harray hc.2 hi hbase hbound rd
    refine ⟨⟨c.index+1,mem',aw'⟩,k',C',⟨?_,hv⟩,rd'⟩
    have := hc.1
    dsimp only
    omega
  obtain ⟨c,k',C',hc,rd'⟩ := RD.whileLoopCarry ⟨14292⟩ ⟨14300⟩ Inv stk RecordArrayCursor.memory RecordArrayCursor.active stk
    hx hs (ats.length-i) ⟨i,mem,aw⟩ ⟨by have := h.index; dsimp only; omega, h⟩ k C rd
  have hi0 : c.index=ats.length := by have := hc.1; omega
  refine ⟨c.memory,c.active,k',C',?_,?_⟩
  · simpa only [stk, hi0] using rd'
  · exact hi0 ▸ hc.2

end Benchmarks.EAS.EAS
