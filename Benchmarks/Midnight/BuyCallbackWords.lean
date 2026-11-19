import Benchmarks.Midnight.BuyCallbackLayout

/-! The contiguous word prefix of onBuy's ABI input. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def buyCallbackWords (m : MarketData) (id assets units fee user : UInt256) (len : Nat) : List UInt256 :=
  [id, UInt256.ofNat 224, assets, units, fee, user, UInt256.ofNat (512 + 128 * m.collaterals.length)] ++
    (m.words (UInt256.ofNat 256) ++
      UInt256.ofNat m.collaterals.length :: m.collaterals.flatMap CollateralData.words) ++
    [UInt256.ofNat len]

theorem buyCallbackWords_length (m : MarketData) (id assets units fee user : UInt256) (len : Nat) :
    (buyCallbackWords m id assets units fee user len).length = 17 + 4 * m.collaterals.length := by
  simp only [buyCallbackWords, List.length_append, List.length_cons, List.length_nil,
    collateralWords_length, show (m.words (UInt256.ofNat 256)).length = 8 from rfl]
  omega

theorem buyCallbackMemory_words (mem : ByteArray) (root : Nat) (m : MarketData)
    (id assets units fee user : UInt256) (ptr len : Nat) (hroot : 96 ≤ root)
    (hd : ptr + 32 + len ≤ mem.size) (hb : root + 548 + 128 * m.collaterals.length < UInt256.size) :
    MemoryWords (buyCallbackMemory mem root m id assets units fee user ptr len) (root + 4)
      (buyCallbackWords m id assets units fee user len) := by
  let head := buyCallbackHeaderMemory mem root id
  let encoded := marketEncodeMemory head (root + 228) m
  let fields := buyCallbackFieldsMemory mem root m id assets units fee user
  let ws := m.words (UInt256.ofNat 256) ++
    UInt256.ofNat m.collaterals.length :: m.collaterals.flatMap CollateralData.words
  have hwlen : ws.length = 9 + 4 * m.collaterals.length := by
    simp only [ws, List.length_append, List.length_cons, collateralWords_length,
      show (m.words (UInt256.ofNat 256)).length = 8 from rfl]
    omega
  have hh : MemoryWords head (root + 4) [id, UInt256.ofNat 224] := by
    have h := MemoryWords.of_writeWordArray
      (writeWord mem root (UInt256.ofNat (470529357 * 2^224))) (root + 4)
      [id, UInt256.ofNat 224] (by simp only [List.length_cons, List.length_nil]; omega) (by simp)
    simpa only [head, buyCallbackHeaderMemory, writeWordArray, Nat.add_assoc] using h
  have hp := marketEncodeMemory_prefix head (root + 228) (root + 68) m (by omega)
  have hh' : MemoryWords encoded (root + 4) [id, UInt256.ofNat 224] := by
    apply hh.preserve hp.size
    intro read hlo hhi
    exact hp.load read (by omega) (by
      simp only [List.length_cons, List.length_nil] at hhi; omega) (hhi.trans hh.size)
  have hhead : MemoryWords fields (root + 4)
      [id, UInt256.ofNat 224, assets, units, fee, user,
        UInt256.ofNat (512 + 128 * m.collaterals.length)] := by
    have hh'' := hh'.append_writeWordArray
      [assets, units, fee, user, UInt256.ofNat (512 + 128 * m.collaterals.length)]
      (by simp only [List.length_cons, List.length_nil, List.length_append]; omega)
    simpa only [fields, buyCallbackFieldsMemory, encoded, head, List.length_cons,
      List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc,
      List.cons_append, List.nil_append] using hh''
  have hm : MemoryWords encoded (root + 228) ws :=
    marketEncodeMemory_words head (root + 228) m (by omega)
  have hm' := hm.writeWords (off := root + 68)
      [assets, units, fee, user, UInt256.ofNat (512 + 128 * m.collaterals.length)]
      (Or.inr (by simp only [List.length_cons, List.length_nil]; omega))
  change MemoryWords fields (root + 228) ws at hm'
  have hall := hhead.append (last := ws) (by simpa using hm')
  have hsrc : ptr + 32 + len ≤ fields.size := hd.trans
    (buyCallbackFieldsMemory_prefix mem root root m id assets units fee user le_rfl).size
  have hbefore := hall.memoryBytesEncode (ptr := ptr) (len := len)
    (output := root + 516 + 128 * m.collaterals.length) hsrc
    (by simp only [List.length_append, List.length_cons, List.length_nil, hwlen]; omega)
  have hlen := memoryBytesEncodeMemory_header fields ptr
    (root + 516 + 128 * m.collaterals.length) len hsrc (by omega)
  have hfull := hbefore.append (last := [UInt256.ofNat len]) (by
    convert hlen using 1
    simp only [List.length_append, List.length_cons, List.length_nil, hwlen]
    omega)
  exact hfull

end Benchmarks.Midnight
