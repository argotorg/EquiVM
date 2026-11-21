import Benchmarks.Midnight.TakeTailDecoder

/-! The three materialized dynamic inputs and lower memory after take's ABI decoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

structure TakeInputStored (mem : ByteArray) (callbackPtr ratifierPtr takerPtr root : UInt256)
    (offer : OfferData) (ratifierData data : ByteArray) : Prop where
  offer : OfferStored mem ⟨832⟩ ⟨1312⟩ ⟨1568⟩ callbackPtr ratifierPtr offer
  ratifier : MemoryByteString mem ratifierPtr ratifierData
  taker : MemoryByteString mem takerPtr data
  ratifierEnd : ratifierPtr.toNat + 32 + paddedSize ratifierData.size = takerPtr.toNat
  takerEnd : takerPtr.toNat + 32 + paddedSize data.size = root.toNat
  bound : root.toNat < 2^64

theorem TakeInputStored.preserve {before after : ByteArray}
    {callbackPtr ratifierPtr takerPtr root : UInt256} {offer : OfferData}
    {ratifierData data : ByteArray}
    (h : TakeInputStored before callbackPtr ratifierPtr takerPtr root offer ratifierData data)
    (hp : MemoryPrefix before after root.toNat) :
    TakeInputStored after callbackPtr ratifierPtr takerPtr root offer ratifierData data := by
  have hr := h.ratifierEnd
  have ht := h.takerEnd
  exact ⟨h.offer.preserve (hp.mono (by omega)), h.ratifier.preserve hp (by omega),
    h.taker.preserve hp (by omega), h.ratifierEnd, h.takerEnd, h.bound⟩

theorem TakeInputStored.writeWord_below {mem : ByteArray}
    {callbackPtr ratifierPtr takerPtr root : UInt256} {offer : OfferData}
    {ratifierData data : ByteArray} {off : Nat}
    (h : TakeInputStored mem callbackPtr ratifierPtr takerPtr root offer ratifierData data)
    (word : UInt256) (hbelow : off + 32 ≤ 832) :
    TakeInputStored (writeWord mem off word) callbackPtr ratifierPtr takerPtr root
      offer ratifierData data := by
  have hm := h.offer.market.extent
  have ho := h.offer.extent
  have hr := h.ratifierEnd
  have ht := h.takerEnd
  have hb := h.bound
  change 1568 + 32 ≤ callbackPtr.toNat at hm
  exact ⟨h.offer.writeWord_below word hbelow,
    h.ratifier.writeWord_below word (by omega) (by omega),
    h.taker.writeWord_below word (by omega) (by omega), hr, ht, hb⟩

theorem takeTailMemory_stored {mem bytes ratifierData data : ByteArray}
    {callbackPtr ratifierPtr : UInt256} {offer : OfferData}
    (ho : OfferStored mem ⟨832⟩ ⟨1312⟩ ⟨1568⟩ callbackPtr ratifierPtr offer)
    (hr : decodeCalldataBytes bytes 36 = some ratifierData)
    (hd : decodeCalldataBytes bytes 196 = some data)
    (hrfit : ratifierPtr.toNat + returnDataAllocation ratifierData.size < 2^64)
    (hdfit : (returnDataPtr ratifierPtr ratifierData.size).toNat +
      returnDataAllocation data.size < 2^64) :
    TakeInputStored
      (takeTailMemory mem bytes ratifierPtr (returnDataPtr ratifierPtr ratifierData.size))
      callbackPtr ratifierPtr (returnDataPtr ratifierPtr ratifierData.size)
      (returnDataPtr (returnDataPtr ratifierPtr ratifierData.size) data.size)
      offer ratifierData data := by
  have hrat := decodeCalldataBytes_success_at hr
  have hdata := decodeCalldataBytes_success_at hd
  have hlo : 1600 ≤ ratifierPtr.toNat := by
    have hm := ho.market.extent
    have he := ho.extent
    change 1568 + 32 ≤ callbackPtr.toNat at hm
    omega
  let m1 := bytesCalldataMemory mem bytes ratifierPtr (4 + (calldataWord bytes 36).toNat)
  let m2 := takeScalarsMemory m1 bytes
  let takerPtr := returnDataPtr ratifierPtr ratifierData.size
  have ht : takerPtr.toNat = ratifierPtr.toNat + 32 + paddedSize ratifierData.size := by
    rw [returnDataPtr_toNat hrfit, returnDataAllocation_eq]
    omega
  have hp1 := bytesCalldataMemory_prefix (mem := mem) (ptr := ratifierPtr) hrat
  have ho2 : OfferStored m2 ⟨832⟩ ⟨1312⟩ ⟨1568⟩ callbackPtr ratifierPtr offer :=
    takeScalarsMemory_offer (ho.preserve hp1)
  have hr2 : MemoryByteString m2 ratifierPtr ratifierData :=
    takeScalarsMemory_bytes (bytesCalldataMemory_stored hrat (by omega) hrfit) (by omega)
      (by rw [returnDataAllocation_eq] at hrfit; omega)
  have hp2 := bytesCalldataMemory_prefix (mem := m2) (ptr := takerPtr) hdata
  refine ⟨ho2.preserve (hp2.mono (by omega)), hr2.preserve hp2 (by omega),
    bytesCalldataMemory_stored (ptr := takerPtr) hdata (by omega) hdfit, ht.symm, ?_, ?_⟩
  · rw [returnDataPtr_toNat hdfit, returnDataAllocation_eq]
    omega
  · rw [returnDataPtr_toNat hdfit]
    exact hdfit

theorem takeTailMemory_free {mem bytes ratifierData data : ByteArray} {ratifierPtr : UInt256}
    (hlo : 96 ≤ ratifierPtr.toNat)
    (hd : decodeCalldataBytes bytes 196 = some data)
    (hrfit : ratifierPtr.toNat + returnDataAllocation ratifierData.size < 2^64) :
    memLoad (UInt256.ofNat 64)
      (takeTailMemory mem bytes ratifierPtr (returnDataPtr ratifierPtr ratifierData.size)) =
      returnDataPtr (returnDataPtr ratifierPtr ratifierData.size) data.size :=
  bytesCalldataMemory_free (decodeCalldataBytes_success_at hd)
    (by rw [returnDataPtr_toNat hrfit]; omega)

theorem takeTailMemory_size {mem bytes ratifierData data : ByteArray} {ratifierPtr : UInt256}
    (hd : decodeCalldataBytes bytes 196 = some data)
    (hdfit : (returnDataPtr ratifierPtr ratifierData.size).toNat +
      returnDataAllocation data.size < 2^64) :
    (returnDataPtr (returnDataPtr ratifierPtr ratifierData.size) data.size).toNat ≤
      (takeTailMemory mem bytes ratifierPtr (returnDataPtr ratifierPtr ratifierData.size)).size := by
  rw [returnDataPtr_toNat hdfit]
  exact bytesCalldataMemory_size (decodeCalldataBytes_success_at hd)

theorem takeTailMemory_low {before mem bytes ratifierData data : ByteArray} {ratifierPtr : UInt256}
    (hk : MemoryWords mem 96 (memoryWordSnapshot before 96 23)) (hb : 832 ≤ before.size)
    (hlo : 832 ≤ ratifierPtr.toNat)
    (hr : decodeCalldataBytes bytes 36 = some ratifierData)
    (hd : decodeCalldataBytes bytes 196 = some data)
    (hrfit : ratifierPtr.toNat + returnDataAllocation ratifierData.size < 2^64) :
    MemoryWords
      (takeTailMemory mem bytes ratifierPtr (returnDataPtr ratifierPtr ratifierData.size)) 96
      (memoryWordSnapshot (takeScalarsMemory before bytes) 96 23) := by
  have hk1 := bytesCalldataMemory_low (ptr := ratifierPtr)
    (decodeCalldataBytes_success_at hr) hk (by decide)
    (by rw [memoryWordSnapshot_length]; exact hlo)
  have hk2 := takeScalarsMemory_low (bytes := bytes) hk1 hb
  exact bytesCalldataMemory_low (decodeCalldataBytes_success_at hd) hk2 (by decide)
    (by rw [memoryWordSnapshot_length, returnDataPtr_toNat hrfit]; omega)

end Benchmarks.Midnight
