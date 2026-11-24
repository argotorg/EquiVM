import Benchmarks.EAS.EAS.ResolverManyBounds
import Benchmarks.EAS.EAS.ResolverManyStart
import Benchmarks.EAS.EAS.ResolverReturn
import Benchmarks.EAS.EAS.CallBridgeOr

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem resolverManyEVM {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {junk0 junk1 junk2 array target valuesPtr last available value ptr : UInt256} {R : List UInt256}
    {ats : List AttestationRecord} {values : List UInt256} (v : EASImmutables) (rev : Bool)
    (hstack : R.length+35 ≤ 1024) (hperm : ee.perm = true ∨ value = ⟨0⟩)
    (hstate : SourceState s0 ee σ evm)
    (harray : AttestationArrayMemoryView mem array ats ptr.toNat)
    (hvalues : WordArrayMemoryView mem valuesPtr values ptr.toNat)
    (hheap : ptr.toNat ≤ 2^64-1) (hlo : 124 ≤ ptr.toNat)
    (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolverManyEntryPC rev)
      (resolverManyEntryStack rev junk0 junk1 junk2 array target valuesPtr last available value R) mem aw rdata σ k C) :
    ∃ (evm' : EVM.State) (σ' : AccountMap) (success : Bool) (out finalMem : ByteArray),
      callViaEVM fork evm (AccountAddress.ofUInt256 target) (Int.ofNat value.toNat)
        (resolverManyPayload ats values rev) (success, evm', out) ∧
      SourceState s0 ee σ' evm' ∧ out.size < 2^138 ∧
      MemoryPrefix mem finalMem ptr.toNat ∧
      memLoad (UInt256.ofNat 64) finalMem = UInt256.ofNat (allocateNext ptr.toNat (min out.size 32)) ∧
      (if resolverCallValid ptr.toNat success out then
        ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (resolverDonePC true rev)
          (UInt256.ofNat (deployedRuntime v).size::calldataWord out 0::last::available::value::R)
          finalMem aw' out σ' k' C'
       else RDrev fork (deployedRuntime v) g s0) := by
  let head := resolverManyHeaderMemory mem ptr rev
  let base := ptr+UInt256.ofNat 4
  have hsize := resolverManyBody_bound harray hvalues hheap
  have hb : ptr.toNat+4+(resolverArraysBody ats values).size < UInt256.size := by
    change ptr.toNat+4+(resolverArraysBody ats values).size < 2^256
    omega
  have hbase : base.toNat = ptr.toNat+4 := uadd_word_ofNat_toNat ptr 4 (by omega)
  have hhead : MemoryPrefix mem head ptr.toNat := resolverManyHeaderMemory_prefix mem ptr rev
  have hav : AttestationArrayMemoryView head array ats base.toNat :=
    (harray.preserve hhead ptr.val.isLt).mono (by rw [hbase]; omega)
  have hvv : WordArrayMemoryView head valuesPtr values base.toNat :=
    (hvalues.preserve hhead ptr.val.isLt).mono (by rw [hbase]; omega)
  have hret : (D_J (deployedRuntime v) 0).contains (resolverPreparePC true rev) = true := by
    cases rev <;> rw [easPatchedValidJumps v] <;> unfold resolverPreparePC <;> jump_dest
  obtain ⟨aw1,k1,C1,rd1⟩ := resolverManyStart v rev (by omega) hh rd
  obtain ⟨enc,aw2,k2,C2,rd2,henc,hread,hcovered⟩ := easEncodeResolverArrays v
    (by simp only [List.length_cons]; omega) hav hvv (le_refl _) (by rw [hbase]; exact hb) hret rd1
  obtain ⟨gasArg,aw3,k3,C3,rd3⟩ := resolverPrepare v true rev (by simp only [List.length_cons]; omega) rd2
  have hlen : (UInt256.sub (UInt256.ofNat (base.toNat+(resolverArraysBody ats values).size)) ptr).toNat =
      (resolverManyPayload ats values rev).size := by
    rw [usub_ofNat_word_toNat (by rw [hbase]; omega) (by rw [hbase]; omega), resolverManyPayload_size, hbase]
    omega
  have hinput : enc.readWithPadding ptr.toNat
      (UInt256.sub (UInt256.ofNat (base.toNat+(resolverArraysBody ats values).size)) ptr).toNat =
      resolverManyPayload ats values rev := by
    rw [hlen]
    exact resolverManyEncoded_read hlo (by simpa only [hbase] using henc)
      (by simpa only [hbase] using hread) (by simpa only [hbase] using hcovered)
  obtain ⟨evm',σ',success,out,k4,C4,hcall,hstate',rd4,hout⟩ :=
    callBridgeOr (calldata := resolverManyPayload ats values rev) rd3 hstate hperm
      (resolverCall_decode v true rev) hinput (resolverManyPayload_small rev harray hvalues hheap)
      (by simp only [List.length_cons]; omega)
  have hpc : resolverCallPC true rev + (⟨1⟩ : UInt256) = resolverAfterCallPC true rev := by cases rev <;> rfl
  change RD fork (deployedRuntime v) ee g s0 (resolverCallPC true rev + (⟨1⟩ : UInt256))
    ((if success then ⟨1⟩ else ⟨0⟩)::ptr::last::available::value::R)
    (callOutputMem enc out ptr ⟨32⟩) _ out σ' k4 C4 at rd4
  rw [hpc] at rd4
  have hc : ptr.toNat+32 ≤ enc.size := by
    rw [hbase, resolverArraysBody_size, attestationArrayEncoding_size] at hcovered
    omega
  have hbout : out.size < UInt256.size := by change out.size < 2^256; omega
  let finalMem := resolverReturnMemory (callOutputMem enc out ptr ⟨32⟩) ptr out
  have hp : MemoryPrefix mem finalMem ptr.toNat :=
    (hhead.trans (henc.mono (by rw [hbase]; omega))).trans
      ((callOutput32_prefix enc out ptr hbout hc).trans
        (memoryPrefix_sparse_writeWord _ 64 ptr.toNat _ (Or.inr (by decide))))
  refine ⟨evm',σ',success,out,finalMem,hcall,hstate',hout,hp,resolverReturnMemory_heap _ _ _,?_⟩
  exact resolverReturn v true rev success (by simp only [List.length_cons]; omega) hbout (by omega)
    (by rw [callOutput32_size _ _ _ hbout hc]; exact hc) (by change ptr.toNat+32 < 2^256; omega)
    (fun hl => callOutput32_load_word enc out ptr hbout hl hc) rd4

end Benchmarks.EAS.EAS
