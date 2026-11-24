import Benchmarks.EAS.EAS.AttestationEncode
import Benchmarks.EAS.EAS.AttestationABI

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem getAttestationReturnEVM {evm : EVM.State} {g : Sat256} {s0 : State}
    {base : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {k C : Nat} {word heap : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+17 ≤ 1024) (hlo : 96 ≤ heap.toNat)
    (hv : copyStoredValid evm word heap.toNat)
    (rd : RD fork (deployedRuntime v) evm.executionEnv g s0 ⟨2628⟩ (heap::⟨398⟩::R)
      (copyStoredOutputMemory evm word heap base) aw rdata evm.accountMap k C) :
    RDret fork (deployedRuntime v) g s0 evm.accountMap (attestationReturnBytes evm word) := by
  let mem := copyStoredOutputMemory evm word heap base
  let len := (attestationPayload evm word).size
  let n := copyStoredNext heap.toNat (attestationPayload evm word)
  let fp := UInt256.ofNat n
  let dst := fp+UInt256.ofNat 32
  let dataPtr := copyStoredBytePtr heap
  let m := Reasoning.Theory.writeWord mem n (UInt256.ofNat 32)
  have hn : n = heap.toNat+352+32*((len+31)/32) := by
    rw [show n = copyStoredNext heap.toNat (attestationPayload evm word) from rfl,
      copyStoredNext_eq evm word heap.toNat hv.1, ← attestationPayload_size]
    dsimp only [bytesAllocation, len]
    omega
  have hn64 : n ≤ 2^64-1 := hv.2.2.1
  have hfn : fp.toNat = n := ulit_toNat' _ (by change n < 2^256; omega)
  have hdn : dst.toNat = n+32 := by
    dsimp only [dst]
    rw [uadd_word_ofNat_toNat fp 32 (by rw [hfn]; change n+32 < 2^256; omega), hfn]
  have hbp : dataPtr.toNat = heap.toNat+320 := copyStoredBytePtr_nat hv.1
  have hc : n ≤ mem.size := by
    have h := copyStoredOutputMemory_coversRounded evm word heap base hv
    change dataPtr.toNat+32+32*((len+31)/32) ≤ mem.size at h
    omega
  have hm : memLoad (UInt256.ofNat 64) mem = fp := copyStoredOutputMemory_heap evm word heap base hlo
  have hp : MemoryPrefix mem m n := memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (le_refl _))
  have hptrn : (heap+UInt256.ofNat 288).toNat = heap.toNat+288 :=
    uadd_word_ofNat_toNat heap 288 (by change heap.toNat+288 < 2^256; omega)
  have hptr : memLoad (heap+UInt256.ofNat 288) m = dataPtr :=
    (memLoad_of_prefix hp _ (by rw [hptrn]; omega) (by rw [hptrn]; omega) (by rw [hptrn]; omega)).trans
      (copyStoredOutputMemory_loadDataPointer evm word heap base hv.1)
  have hlen : memLoad dataPtr m = UInt256.ofNat len :=
    (memLoad_of_prefix hp dataPtr (by omega) (by omega) (by omega)).trans
      (copyStoredOutputMemory_loadLength evm word heap base hlo hv)
  have hbound : dst.toNat+384+32*((len+31)/32) < UInt256.size := by
    rw [hdn]
    change n+32+384+32*((len+31)/32) < 2^256
    omega
  obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_2628_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  change RD fork (deployedRuntime v) evm.executionEnv g s0 (UInt256.ofNat 4502)
    (easBlocks.eas_block_2628_stack (mem := mem) (x0 := heap) (x1 := ⟨398⟩) (R := R))
    (easBlocks.eas_block_2628_memory (mem := mem)) aw1 rdata evm.accountMap k1 C1 at rd1
  simp only [easBlocks.eas_block_2628_stack, easBlocks.eas_block_2628_memory, hm, hfn, ← writeWord_as_write] at rd1
  obtain ⟨aw2,k2,C2,rd2⟩ := easEncodeAttestation v (by simp only [List.length_cons]; omega) hlo (by omega)
    (by rw [hdn]; omega) (by have hg := hp.size; omega)
    (by rw [hdn, hbp]; omega) (by have hg := hp.size; omega) hptr hlen hbound
    (by rw [easPatchedValidJumps v]; jump_dest) rd1
  have hr := easBlocks.eas_block_398 (immWords := wordsOf (immStore v)) (by omega) rd2
  have hlenRet : (UInt256.sub (UInt256.ofNat (dst.toNat+352+32*((len+31)/32))) fp).toNat = 384+32*((len+31)/32) := by
    rw [usub_ofNat_word_toNat (by rw [hfn, hdn]; omega) (by omega), hfn, hdn]
    omega
  change RDret fork (deployedRuntime v) g s0 evm.accountMap
    ((attestationEncodedMemory m heap dst dataPtr).readWithPadding fp.toNat
      (UInt256.sub (UInt256.ofNat (dst.toNat+352+32*((len+31)/32))) fp).toNat) at hr
  rw [hfn, hlenRet] at hr
  have hhead : attestationEncodeHeadWords m heap = storedAttestationWords evm.accountMap evm.executionEnv (dbSlot word) ++ [UInt256.ofNat 320] :=
    (attestationHeadWords_of_prefix hp heap hlo (by omega) (by omega) (by change heap.toNat+320 < 2^256; omega)).trans
      (copyStoredOutputMemory_headWords evm word heap base hv.1 hlo)
  have hdata : m.readWithPadding (dataPtr.toNat+32) len = attestationPayload evm word := by
    rw [show m = Reasoning.Theory.writeWord mem n (UInt256.ofNat 32) from rfl,
      writeWord_read_below_len _ _ _ _ _ (by omega) (by omega)]
    exact copyStoredOutputMemory_data evm word heap base hlo hv
  have hout := attestationEncodedMemory_read m heap dst dataPtr len (by omega)
    (by rw [hdn]; omega) (by have hg := hp.size; omega) hlen hbound
  rw [hhead, hdata, hdn] at hout
  have hcov := attestationEncodedMemory_covers m heap dst dataPtr len (by omega)
    (by rw [hdn]; omega) (by have hg := hp.size; omega) hlen hbound
  rw [hdn] at hcov
  have hpre := attestationEncodedMemory_prefix m heap dst dataPtr len (by omega)
    (by rw [hdn]; omega) (by have hg := hp.size; omega) hlen hbound
  have htag : (attestationEncodedMemory m heap dst dataPtr).readWithPadding n 32 = (UInt256.ofNat 32).toByteArray := by
    rw [hpre.read n (by omega) (by rw [hdn]) (by dsimp only [m]; rw [writeWord_sparse_size]; omega)]
    exact writeWord_sparse_read_back _ _ _
  have hret : (attestationEncodedMemory m heap dst dataPtr).readWithPadding n (384+32*((len+31)/32)) = attestationReturnBytes evm word := by
    rw [show 384+32*((len+31)/32) = 32+(352+32*((len+31)/32)) by omega,
      byteArray_readWithPadding_split_unbounded _ _ 32 (352+32*((len+31)/32)) (by decide) (by omega) (by omega), htag, hout]
    simp only [attestationReturnBytes, wordBytes_append, wordBytes, ByteArray.append_empty, ByteArray.append_assoc]
    rfl
  rw [hret] at hr
  exact hr

end Benchmarks.EAS.EAS
