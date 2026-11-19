import Benchmarks.Midnight.SellCallbackLayout

/-! The contiguous word prefix of onSell's ABI input. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def sellCallbackWords (m : MarketData) (id assets units fee user receiver : UInt256) (len : Nat) : List UInt256 :=
  [id, UInt256.ofNat 256, assets, units, fee, user, receiver, UInt256.ofNat (544 + 128 * m.collaterals.length)] ++
    (m.words (UInt256.ofNat 256) ++
      UInt256.ofNat m.collaterals.length :: m.collaterals.flatMap CollateralData.words) ++
    [UInt256.ofNat len]

theorem sellCallbackWords_length (m : MarketData) (id assets units fee user receiver : UInt256) (len : Nat) :
    (sellCallbackWords m id assets units fee user receiver len).length = 18 + 4 * m.collaterals.length := by
  simp only [sellCallbackWords, List.length_append, List.length_cons, List.length_nil,
    collateralWords_length, show (m.words (UInt256.ofNat 256)).length = 8 from rfl]
  omega

theorem sellCallbackMemory_words (mem : ByteArray) (root : Nat) (m : MarketData)
    (id assets units fee user receiver : UInt256) (ptr len : Nat) (hroot : 96 ≤ root)
    (hd : ptr + 32 + len ≤ mem.size) (hb : root + 580 + 128 * m.collaterals.length < UInt256.size) :
    MemoryWords (sellCallbackMemory mem root m id assets units fee user receiver ptr len) (root + 4)
      (sellCallbackWords m id assets units fee user receiver len) := by
  let head := sellCallbackHeaderMemory mem root id
  let encoded := marketEncodeMemory head (root + 260) m
  let fields := sellCallbackFieldsMemory mem root m id assets units fee user receiver
  let ws := m.words (UInt256.ofNat 256) ++
    UInt256.ofNat m.collaterals.length :: m.collaterals.flatMap CollateralData.words
  have hwlen : ws.length = 9 + 4 * m.collaterals.length := by
    simp only [ws, List.length_append, List.length_cons, collateralWords_length,
      show (m.words (UInt256.ofNat 256)).length = 8 from rfl]
    omega
  have hh : MemoryWords head (root + 4) [id, UInt256.ofNat 256] := by
    have h := MemoryWords.of_writeWordArray
      (writeWord mem root (UInt256.ofNat (1827805250 * 2^224))) (root + 4)
      [id, UInt256.ofNat 256] (by simp only [List.length_cons, List.length_nil]; omega) (by simp)
    simpa only [head, sellCallbackHeaderMemory, writeWordArray, Nat.add_assoc] using h
  have hp := marketEncodeMemory_prefix head (root + 260) (root + 68) m (by omega)
  have hh' : MemoryWords encoded (root + 4) [id, UInt256.ofNat 256] := by
    apply hh.preserve hp.size
    intro read hlo hhi
    exact hp.load read (by omega) (by
      simp only [List.length_cons, List.length_nil] at hhi; omega) (hhi.trans hh.size)
  have hhead : MemoryWords fields (root + 4)
      [id, UInt256.ofNat 256, assets, units, fee, user, receiver,
        UInt256.ofNat (544 + 128 * m.collaterals.length)] := by
    have hh'' := hh'.append_writeWordArray
      [assets, units, fee, user, receiver, UInt256.ofNat (544 + 128 * m.collaterals.length)]
      (by simp only [List.length_cons, List.length_nil, List.length_append]; omega)
    simpa only [fields, sellCallbackFieldsMemory, encoded, head, List.length_cons,
      List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc,
      List.cons_append, List.nil_append] using hh''
  have hm : MemoryWords encoded (root + 260) ws :=
    marketEncodeMemory_words head (root + 260) m (by omega)
  have hm' := hm.writeWords (off := root + 68)
      [assets, units, fee, user, receiver, UInt256.ofNat (544 + 128 * m.collaterals.length)]
      (Or.inr (by simp only [List.length_cons, List.length_nil]; omega))
  change MemoryWords fields (root + 260) ws at hm'
  have hall := hhead.append (last := ws) (by simpa using hm')
  have hsrc : ptr + 32 + len ≤ fields.size := hd.trans
    (sellCallbackFieldsMemory_prefix mem root root m id assets units fee user receiver le_rfl).size
  have hbefore := hall.memoryBytesEncode (ptr := ptr) (len := len)
    (output := root + 548 + 128 * m.collaterals.length) hsrc
    (by simp only [List.length_append, List.length_cons, List.length_nil, hwlen]; omega)
  have hlen := memoryBytesEncodeMemory_header fields ptr
    (root + 548 + 128 * m.collaterals.length) len hsrc (by omega)
  have hfull := hbefore.append (last := [UInt256.ofNat len]) (by
    convert hlen using 1
    simp only [List.length_append, List.length_cons, List.length_nil, hwlen]
    omega)
  exact hfull

end Benchmarks.Midnight
