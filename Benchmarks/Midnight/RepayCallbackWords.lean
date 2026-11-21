import Benchmarks.Midnight.RepayCallbackPrepare

/-! The contiguous word prefix of onRepay's ABI input. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def repayCallbackWords (m : MarketData) (id units user : UInt256) (dl : Nat) : List UInt256 :=
  [id, UInt256.ofNat 160, units, user, UInt256.ofNat (448 + 128 * m.collaterals.length)] ++
    (m.words (UInt256.ofNat 256) ++
      UInt256.ofNat m.collaterals.length :: m.collaterals.flatMap CollateralData.words) ++
    [UInt256.ofNat dl]

theorem repayCallbackWords_length (m : MarketData) (id units user : UInt256) (dl : Nat) :
    (repayCallbackWords m id units user dl).length = 15 + 4 * m.collaterals.length := by
  simp only [repayCallbackWords, List.length_append, List.length_cons, List.length_nil,
    collateralWords_length, show (m.words (UInt256.ofNat 256)).length = 8 from rfl]
  omega

theorem repayCallbackMemory_words (mem bytes : ByteArray) (root : Nat) (m : MarketData)
    (id units user : UInt256) (dp dl : Nat) (hroot : 96 ≤ root)
    (hd : dp + dl ≤ bytes.size) (hb : root + 484 + 128 * m.collaterals.length < UInt256.size) :
    MemoryWords (repayCallbackMemory mem bytes root m id units user dp dl) (root + 4)
      (repayCallbackWords m id units user dl) := by
  let head := repayCallbackHeaderMemory mem root id
  let encoded := marketEncodeMemory head (root + 164) m
  let fields := repayCallbackFieldsMemory mem root m id units user
  let ws := m.words (UInt256.ofNat 256) ++
    UInt256.ofNat m.collaterals.length :: m.collaterals.flatMap CollateralData.words
  have hwlen : ws.length = 9 + 4 * m.collaterals.length := by
    simp only [ws, List.length_append, List.length_cons, collateralWords_length,
      show (m.words (UInt256.ofNat 256)).length = 8 from rfl]
    omega
  have hh : MemoryWords head (root + 4) [id, UInt256.ofNat 160] := by
    have h := MemoryWords.of_writeWordArray
      (writeWord mem root (UInt256.ofNat (688845988 * 2^224))) (root + 4)
      [id, UInt256.ofNat 160] (by simp only [List.length_cons, List.length_nil]; omega) (by simp)
    simpa only [head, repayCallbackHeaderMemory, writeWordArray, Nat.add_assoc] using h
  have hp := marketEncodeMemory_prefix head (root + 164) (root + 68) m (by omega)
  have hh' : MemoryWords encoded (root + 4) [id, UInt256.ofNat 160] := by
    apply hh.preserve hp.size
    intro read hlo hhi
    exact hp.load read (by omega) (by
      simp only [List.length_cons, List.length_nil] at hhi; omega) (hhi.trans hh.size)
  have hhead : MemoryWords fields (root + 4)
      [id, UInt256.ofNat 160, units, user, UInt256.ofNat (448 + 128 * m.collaterals.length)] := by
    have hh'' := hh'.append_writeWordArray
      [units, user, UInt256.ofNat (448 + 128 * m.collaterals.length)]
      (by simp only [List.length_cons, List.length_nil, List.length_append]; omega)
    simpa only [fields, repayCallbackFieldsMemory, encoded, head, List.length_cons,
      List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc, writeWordArray,
      List.cons_append, List.nil_append] using hh''
  have hm : MemoryWords encoded (root + 164) ws :=
    marketEncodeMemory_words head (root + 164) m (by omega)
  have hm' : MemoryWords fields (root + 164) ws :=
    ((hm.writeWord (off := root + 68) units (Or.inr (by omega))).writeWord
      (off := root + 100) user (Or.inr (by omega))).writeWord
      (off := root + 132) (UInt256.ofNat (448 + 128 * m.collaterals.length)) (Or.inr (by omega))
  have hall := hhead.append (last := ws) (by simpa using hm')
  have hbefore := hall.calldataBytesEncode (bytes := bytes)
    (output := root + 452 + 128 * m.collaterals.length) hd
    (by simp only [List.length_append, List.length_cons, List.length_nil, hwlen]; omega)
  have hlen := calldataBytesEncodeMemory_header fields bytes
    (root + 452 + 128 * m.collaterals.length) dp dl hd (by omega)
  have hfull := hbefore.append (last := [UInt256.ofNat dl]) (by
    convert hlen using 1
    simp only [List.length_append, List.length_cons, List.length_nil, hwlen]
    omega)
  exact hfull

end Benchmarks.Midnight
