import Benchmarks.EAS.EAS.StructEncodeViews

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem roundedBytes_word (len : Nat) (hb : len+31 < UInt256.size) :
    UInt256.land (UInt256.ofNat len + ⟨31⟩) (UInt256.lnot ⟨31⟩) = UInt256.ofNat (32*((len+31)/32)) := by
  apply u256_inj
  rw [longDataCutoff_toNat]
  change (UInt256.ofNat len + UInt256.ofNat 31).toNat / 32 * 32 = _
  rw [uadd_word_ofNat_toNat (UInt256.ofNat len) 31 (by rw [ulit_toNat' _ (by omega)]; exact hb),
    ulit_toNat' _ (by omega), ulit_toNat' _ (by omega)]
  omega

theorem attestationEncoded_end (dst : UInt256) (len : Nat)
    (hb : dst.toNat+384+32*((len+31)/32) < UInt256.size) :
    (UInt256.land (UInt256.ofNat len + ⟨31⟩) (UInt256.lnot ⟨31⟩) + (dst+UInt256.ofNat 320)) + ⟨32⟩ =
      UInt256.ofNat (dst.toNat+352+32*((len+31)/32)) := by
  rw [roundedBytes_word len (by omega)]
  have hd : (dst+UInt256.ofNat 320).toNat = dst.toNat+320 := uadd_word_ofNat_toNat dst 320 (by omega)
  apply u256_inj
  rw [u256_add_comm (UInt256.ofNat (32*((len+31)/32))) _]
  change (dst+UInt256.ofNat 320+UInt256.ofNat (32*((len+31)/32))+UInt256.ofNat 32).toNat = _
  rw [uadd_word_ofNat_toNat _ 32 (by rw [uadd_word_ofNat_toNat _ _ (by rw [hd]; omega), hd]; omega),
    uadd_word_ofNat_toNat _ _ (by rw [hd]; omega), hd, ulit_toNat' _ (by omega)]
  omega

def attestationEncodedMemory (mem : ByteArray) (src dst dataPtr : UInt256) : ByteArray :=
  easEncodeBytesMemory dataPtr (dst+UInt256.ofNat 320) (attestationEncodeHeadMemory mem src dst)

theorem attestationEncodeHead_prefix (mem : ByteArray) (src dst : UInt256) :
    MemoryPrefix mem (attestationEncodeHeadMemory mem src dst) dst.toNat :=
  writeWordSequence_prefix _ _ _ _ (le_refl _)

theorem attestationEncodeHead_dataLength (mem : ByteArray) (src dst dataPtr : UInt256) (len : Nat)
    (hlo : 96 ≤ dataPtr.toNat) (hdisj : dataPtr.toNat+32 ≤ dst.toNat)
    (hin : dataPtr.toNat+32 ≤ mem.size) (hh : memLoad dataPtr mem = UInt256.ofNat len) :
    memLoad dataPtr (attestationEncodeHeadMemory mem src dst) = UInt256.ofNat len :=
  (memLoad_of_prefix (attestationEncodeHead_prefix mem src dst) dataPtr hlo hdisj hin).trans hh

theorem easEncodeAttestation {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {src dst dataPtr ret : UInt256} {len : Nat} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+15 ≤ 1024) (hlo : 96 ≤ src.toNat) (hdlo : 96 ≤ dataPtr.toNat)
    (hdisj : src.toNat+320 ≤ dst.toNat) (hin : src.toNat+320 ≤ mem.size)
    (hdataDisj : dataPtr.toNat+32+32*((len+31)/32) ≤ dst.toNat)
    (hdataIn : dataPtr.toNat+32+32*((len+31)/32) ≤ mem.size)
    (hptr : memLoad (src+UInt256.ofNat 288) mem = dataPtr)
    (hh : memLoad dataPtr mem = UInt256.ofNat len)
    (hbound : dst.toNat+384+32*((len+31)/32) < UInt256.size)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4502⟩ (src::dst::ret::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret
      (UInt256.ofNat (dst.toNat+352+32*((len+31)/32)) :: R)
      (attestationEncodedMemory mem src dst dataPtr) aw' rdata σ k' C' := by
  obtain ⟨aw1,k1,C1,rd1⟩ := easEncodeAttestationHead v (by simp only [List.length_cons]; omega) hlo hdisj hin (by omega) rd
  rw [hptr] at rd1
  have hh' := attestationEncodeHead_dataLength mem src dst dataPtr len hdlo (by omega) (by omega) hh
  obtain ⟨aw2,k2,C2,rd2⟩ := easEncodeBytes v (by simp only [List.length_cons]; omega)
    (by rw [hh', ulit_toNat' _ (by omega)]; omega)
    (by rw [easPatchedValidJumps v]; jump_dest) rd1
  rw [hh', attestationEncoded_end dst len hbound] at rd2
  obtain ⟨aw3,k3,C3,rd3⟩ := easBlocks.eas_block_4692_packed (immWords := wordsOf (immStore v))
    (by omega) hvalid rd2
  exact ⟨aw3,k3,C3,rd3⟩


theorem attestationEncodedMemory_covers (mem : ByteArray) (src dst dataPtr : UInt256) (len : Nat)
    (hdlo : 96 ≤ dataPtr.toNat) (hdataDisj : dataPtr.toNat+32+32*((len+31)/32) ≤ dst.toNat)
    (hdataIn : dataPtr.toNat+32+32*((len+31)/32) ≤ mem.size)
    (hh : memLoad dataPtr mem = UInt256.ofNat len)
    (hbound : dst.toNat+384+32*((len+31)/32) < UInt256.size) :
    dst.toNat+352+32*((len+31)/32) ≤ (attestationEncodedMemory mem src dst dataPtr).size := by
  have hd : (dst+UInt256.ofNat 320).toNat = dst.toNat+320 := uadd_word_ofNat_toNat dst 320 (by omega)
  have hp := attestationEncodeHead_prefix mem src dst
  have hh' := attestationEncodeHead_dataLength mem src dst dataPtr len hdlo (by omega) (by omega) hh
  have hc := easEncodeBytesMemory_covers dataPtr (dst+UInt256.ofNat 320)
    (attestationEncodeHeadMemory mem src dst) len hh' hdlo (by rw [hd]; omega)
    (le_trans hdataIn hp.size) (by rw [hd]; omega)
  simpa only [hd, show dst.toNat+320+32 = dst.toNat+352 by omega] using hc

theorem attestationEncodedMemory_prefix (mem : ByteArray) (src dst dataPtr : UInt256) (len : Nat)
    (hdlo : 96 ≤ dataPtr.toNat) (hdataDisj : dataPtr.toNat+32+32*((len+31)/32) ≤ dst.toNat)
    (hdataIn : dataPtr.toNat+32+32*((len+31)/32) ≤ mem.size)
    (hh : memLoad dataPtr mem = UInt256.ofNat len)
    (hbound : dst.toNat+384+32*((len+31)/32) < UInt256.size) :
    MemoryPrefix mem (attestationEncodedMemory mem src dst dataPtr) dst.toNat := by
  have hd : (dst+UInt256.ofNat 320).toNat = dst.toNat+320 := uadd_word_ofNat_toNat dst 320 (by omega)
  have hp := attestationEncodeHead_prefix mem src dst
  have hh' := attestationEncodeHead_dataLength mem src dst dataPtr len hdlo (by omega) (by omega) hh
  exact hp.trans ((easEncodeBytesMemory_prefix dataPtr (dst+UInt256.ofNat 320)
    (attestationEncodeHeadMemory mem src dst) len hh' hdlo (by rw [hd]; omega)
    (le_trans hdataIn hp.size) (by rw [hd]; omega)).mono (by rw [hd]; omega))

theorem attestationEncodedMemory_read (mem : ByteArray) (src dst dataPtr : UInt256) (len : Nat)
    (hdlo : 96 ≤ dataPtr.toNat) (hdataDisj : dataPtr.toNat+32+32*((len+31)/32) ≤ dst.toNat)
    (hdataIn : dataPtr.toNat+32+32*((len+31)/32) ≤ mem.size)
    (hh : memLoad dataPtr mem = UInt256.ofNat len)
    (hbound : dst.toNat+384+32*((len+31)/32) < UInt256.size) :
    (attestationEncodedMemory mem src dst dataPtr).readWithPadding dst.toNat (352+32*((len+31)/32)) =
      wordBytes (attestationEncodeHeadWords mem src) ++
        ((UInt256.ofNat len).toByteArray ++ (mem.readWithPadding (dataPtr.toNat+32) len ++
          ByteArray.zeroes (32*((len+31)/32)-len))) := by
  have hd : (dst+UInt256.ofNat 320).toNat = dst.toNat+320 := uadd_word_ofNat_toNat dst 320 (by omega)
  have hp := attestationEncodeHead_prefix mem src dst
  have hh' := attestationEncodeHead_dataLength mem src dst dataPtr len hdlo (by omega) (by omega) hh
  have hout := attestationEncodedMemory_covers mem src dst dataPtr len hdlo hdataDisj hdataIn hh hbound
  have hbytes := easEncodeBytesMemory_read dataPtr (dst+UInt256.ofNat 320)
    (attestationEncodeHeadMemory mem src dst) len hh' hdlo (by rw [hd]; omega)
    (le_trans hdataIn hp.size) (by rw [hd]; omega)
  have hbp := easEncodeBytesMemory_prefix dataPtr (dst+UInt256.ofNat 320)
    (attestationEncodeHeadMemory mem src dst) len hh' hdlo (by rw [hd]; omega)
    (le_trans hdataIn hp.size) (by rw [hd]; omega)
  have hn : (attestationEncodeHeadWords mem src).length = 10 := rfl
  have hheadCover : dst.toNat+320 ≤ (attestationEncodeHeadMemory mem src dst).size := by
    have hc := writeWordSequence_covers mem dst.toNat (attestationEncodeHeadWords mem src)
      (by intro he; have h := congrArg List.length he; rw [hn] at h; contradiction)
    simpa only [hn] using hc
  have hhead : (attestationEncodedMemory mem src dst dataPtr).readWithPadding dst.toNat 320 =
      wordBytes (attestationEncodeHeadWords mem src) := by
    rw [attestationEncodedMemory, show 320 = 32*10 from rfl,
      memoryPrefix_read_words hbp dst.toNat 10 (by omega) (by rw [hd]) hheadCover (by omega)]
    have hr := writeWordSequence_read mem dst.toNat (attestationEncodeHeadWords mem src)
    simpa only [hn] using hr
  have hdata : (attestationEncodeHeadMemory mem src dst).readWithPadding (dataPtr.toNat+32) len =
      mem.readWithPadding (dataPtr.toNat+32) len :=
    writeWordSequence_read_below_len mem dst.toNat (dataPtr.toNat+32) len _ (by omega) (by omega)
  rw [hd, hdata] at hbytes
  rw [show 352+32*((len+31)/32) = 320+(32+32*((len+31)/32)) by omega,
    byteArray_readWithPadding_split_unbounded _ _ 320 (32+32*((len+31)/32))
      (by decide) (by omega) (by omega), hhead]
  exact congrArg (fun b : ByteArray => wordBytes (attestationEncodeHeadWords mem src) ++ b) hbytes

end Benchmarks.EAS.EAS
