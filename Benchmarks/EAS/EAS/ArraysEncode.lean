import Benchmarks.EAS.EAS.ArraysTailViews
import Benchmarks.EAS.EAS.RecordArrayStart
import Benchmarks.EAS.EAS.ValuesEncodeEVM
import Benchmarks.EAS.EAS.WordArrayMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easEncodeResolverArraysTail {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {before mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {base array valuesPtr ret : UInt256} {ats : List AttestationRecord} {values : List UInt256}
    {limit : Nat} {R : List UInt256} (v : EASImmutables) (hstack : R.length+8 ≤ 1024)
    (hvalues : WordArrayMemoryView before valuesPtr values limit)
    (h : RecordArrayLoopView before mem base ats limit ats.length)
    (hbase : limit ≤ base.toNat)
    (hbound : base.toNat+(resolverArraysBody ats values).size < UInt256.size)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨14300⟩
      (recordArrayStack base array ats ats.length (valuesPtr::ret::R)) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (UInt256.ofNat (base.toNat+(resolverArraysBody ats values).size)::R)
      (resolverArraysTailMemory mem base ats values) aw' rdata σ k' C' := by
  have hb : base.toNat+64+(attestationArrayEncoding ats).size+32+32*values.length < UInt256.size := by
    rw [resolverArraysBody_size] at hbound
    omega
  have hlimit : limit < UInt256.size := by omega
  let tail := UInt256.ofNat (recordArrayTail base ats ats.length)
  let mid := Reasoning.Theory.writeWord mem (base.toNat+32) (UInt256.ofNat (64+(attestationArrayEncoding ats).size))
  let vm := Reasoning.Theory.writeWord mid (recordArrayTail base ats ats.length) (UInt256.ofNat values.length)
  have htn : tail.toNat = recordArrayTail base ats ats.length := ulit_toNat' _ (by rw [recordArrayTail_eq_encoding]; omega)
  have hp : MemoryPrefix mem mid limit := memoryPrefix_sparse_writeWord mem (base.toNat+32) limit _ (Or.inl (by omega))
  have hv := hvalues.preserve (h.front.trans hp) hlimit
  have hl : memLoad valuesPtr mid = UInt256.ofNat values.length := hv.length
  have hpp : MemoryPrefix mid vm limit := memoryPrefix_sparse_writeWord mid (recordArrayTail base ats ats.length) limit _
    (Or.inl (by rw [recordArrayTail_eq_encoding]; omega))
  have hvv := hv.preserve hpp hlimit
  have h32 : (base+UInt256.ofNat 32).toNat = base.toNat+32 := uadd_word_ofNat_toNat base 32 (by omega)
  have hoff : UInt256.sub tail base = UInt256.ofNat (64+(attestationArrayEncoding ats).size) := by
    apply u256_inj
    rw [usub_toNat (by rw [htn, recordArrayTail_eq_encoding]; omega), htn, recordArrayTail_eq_encoding,
      ulit_toNat' _ (by omega)]
    omega
  obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_14300_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) rd
  change RD fork (deployedRuntime v) ee g s0 ⟨14327⟩
    (⟨0⟩::memLoad valuesPtr ((UInt256.sub tail base).toByteArray.write 0 mem (base+UInt256.ofNat 32).toNat 32)::
      (valuesPtr+UInt256.ofNat 32)::(tail+UInt256.ofNat 32)::ret::R)
    ((memLoad valuesPtr ((UInt256.sub tail base).toByteArray.write 0 mem (base+UInt256.ofNat 32).toNat 32)).toByteArray.write 0
      ((UInt256.sub tail base).toByteArray.write 0 mem (base+UInt256.ofNat 32).toNat 32) tail.toNat 32) aw1 rdata σ k1 C1 at rd1
  rw [hoff, h32] at rd1
  change memLoad valuesPtr ((UInt256.ofNat (64+(attestationArrayEncoding ats).size)).toByteArray.write 0 mem (base.toNat+32) 32) = _ at hl
  rw [hl, htn] at rd1
  have hsrc : (valuesPtr+UInt256.ofNat 32).toNat = valuesPtr.toNat+32 :=
    uadd_word_ofNat_toNat valuesPtr 32 (by have := hvalues.span; omega)
  have hdst : (tail+UInt256.ofNat 32).toNat = recordArrayTail base ats ats.length+32 := by
    rw [uadd_word_ofNat_toNat tail 32 (by rw [htn, recordArrayTail_eq_encoding]; omega), htn]
  obtain ⟨aw2,k2,C2,rd2⟩ := easEncodeValues v values (by omega)
    (by rw [hsrc]; have := hvalues.low; omega)
    (by rw [hsrc, hdst, recordArrayTail_eq_encoding]; have := hvalues.span; omega)
    (by rw [hsrc]; exact hvv.covered)
    (by rw [hdst, recordArrayTail_eq_encoding]; omega)
    (by rw [hsrc]; exact hvv.words) hvalid rd1
  rw [hdst] at rd2
  have hend : recordArrayTail base ats ats.length+32+32*values.length = base.toNat+(resolverArraysBody ats values).size := by
    rw [recordArrayTail_eq_encoding, resolverArraysBody_size]
    omega
  rw [hend] at rd2
  exact ⟨aw2,k2,C2,rd2⟩

theorem easEncodeResolverArrays {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {base array valuesPtr ret : UInt256} {ats : List AttestationRecord} {values : List UInt256}
    {limit : Nat} {R : List UInt256} (v : EASImmutables) (hstack : R.length+25 ≤ 1024)
    (harray : AttestationArrayMemoryView mem array ats limit)
    (hvalues : WordArrayMemoryView mem valuesPtr values limit)
    (hbase : limit ≤ base.toNat)
    (hbound : base.toNat+(resolverArraysBody ats values).size < UInt256.size)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨14256⟩ (base::array::valuesPtr::ret::R) mem aw rdata σ k C) :
    ∃ mem' aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (UInt256.ofNat (base.toNat+(resolverArraysBody ats values).size)::R)
      mem' aw' rdata σ k' C' ∧ MemoryPrefix mem mem' limit ∧
      mem'.readWithPadding base.toNat (resolverArraysBody ats values).size = resolverArraysBody ats values ∧
      base.toNat+(resolverArraysBody ats values).size ≤ mem'.size := by
  have hb : base.toNat+128+attestationArrayOffset ats ats.length < UInt256.size := by
    rw [resolverArraysBody_size, attestationArrayEncoding_size] at hbound
    omega
  obtain ⟨mem1,aw1,k1,C1,rd1,hv⟩ := easEncodeRecordArray v (by simp only [List.length_cons]; omega) harray hbase hb rd
  obtain ⟨aw2,k2,C2,rd2⟩ := easEncodeResolverArraysTail v (by omega) hvalues hv hbase hbound hvalid rd1
  exact ⟨_,aw2,k2,C2,rd2, hv.front.trans (resolverArraysTailMemory_prefix mem1 base ats values limit hbase),
    resolverArraysTailMemory_read values hv, resolverArraysTailMemory_covers mem1 base ats values⟩

end Benchmarks.EAS.EAS
