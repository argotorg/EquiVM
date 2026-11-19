import Benchmarks.Midnight.LiquidateCallbackPrepare
import Benchmarks.Midnight.MarketEncodeMemory

/-! The contiguous ABI word prefix of the liquidation callback. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem liquidateCallbackFieldsMemory_eq (mem : ByteArray) (root : Nat)
    (sender : AccountAddress) (m : MarketData) (id index seized repaid borrower receiver : UInt256) :
    liquidateCallbackFieldsMemory (liquidateCallbackMarketPrefixMemory mem root sender id m)
      root m index seized repaid borrower receiver =
    writeWordArray (marketEncodeMemory (liquidateCallbackPrefixMemory mem root sender id)
      (root + 324) m) (root + 100)
      [index, seized, repaid, borrower, receiver,
        UInt256.ofNat (608 + 128 * m.collaterals.length)] := by
  simp only [liquidateCallbackFieldsMemory, liquidateCallbackMarketPrefixMemory,
    liquidateCallbackArrayHeadMemory, liquidateCallbackHeadMemory, marketEncodeMemory,
    marketEncodeHeadMemory, MarketData.headWords, MarketData.firstWords, MarketData.tailWords,
    List.cons_append, List.nil_append, writeWordArray, Nat.add_assoc, Nat.reduceAdd]

def liquidateCallbackWords (sender : AccountAddress) (m : MarketData)
    (id index seized repaid borrower receiver badDebt : UInt256) (dl : Nat) : List UInt256 :=
  [UInt256.ofNat sender.val, id, UInt256.ofNat 320, index, seized, repaid, borrower, receiver,
    UInt256.ofNat (608 + 128 * m.collaterals.length), badDebt] ++
    (m.words (UInt256.ofNat 256) ++
      UInt256.ofNat m.collaterals.length :: m.collaterals.flatMap CollateralData.words) ++
    [UInt256.ofNat dl]

theorem liquidateCallbackWords_length (sender : AccountAddress) (m : MarketData)
    (id index seized repaid borrower receiver badDebt : UInt256) (dl : Nat) :
    (liquidateCallbackWords sender m id index seized repaid borrower receiver badDebt dl).length =
      20 + 4 * m.collaterals.length := by
  simp only [liquidateCallbackWords, List.length_append, List.length_cons, List.length_nil,
    collateralWords_length, show (m.words (UInt256.ofNat 256)).length = 8 from rfl]
  omega

theorem liquidateCallbackMemory_words (mem bytes : ByteArray) (root : Nat)
    (sender : AccountAddress) (m : MarketData)
    (id index seized repaid borrower receiver badDebt : UInt256) (dp dl : Nat) (hroot : 96 ≤ root)
    (hd : dp + dl ≤ bytes.size) (hb : root + 644 + 128 * m.collaterals.length < UInt256.size) :
    MemoryWords (liquidateCallbackMemory mem bytes root sender m id index seized repaid borrower
      receiver dp dl badDebt) (root + 4)
      (liquidateCallbackWords sender m id index seized repaid borrower receiver badDebt dl) := by
  let head := liquidateCallbackPrefixMemory mem root sender id
  let encoded := marketEncodeMemory head (root + 324) m
  let fields := writeWordArray encoded (root + 100)
    [index, seized, repaid, borrower, receiver,
      UInt256.ofNat (608 + 128 * m.collaterals.length)]
  let ws := m.words (UInt256.ofNat 256) ++
    UInt256.ofNat m.collaterals.length :: m.collaterals.flatMap CollateralData.words
  have hwlen : ws.length = 9 + 4 * m.collaterals.length := by
    simp only [ws, List.length_append, List.length_cons, collateralWords_length,
      show (m.words (UInt256.ofNat 256)).length = 8 from rfl]
    omega
  have hh : MemoryWords head (root + 4) [UInt256.ofNat sender.val, id, UInt256.ofNat 320] :=
    MemoryWords.of_writeWordArray _ _ _
      (by simp only [List.length_cons, List.length_nil]; omega) (by simp)
  have hp := marketEncodeMemory_prefix head (root + 324) (root + 100) m (by omega)
  have hh' : MemoryWords encoded (root + 4) [UInt256.ofNat sender.val, id, UInt256.ofNat 320] := by
    apply hh.preserve hp.size
    intro read hlo hhi
    exact hp.load read (by omega) (by
      simp only [List.length_cons, List.length_nil] at hhi; omega) (hhi.trans hh.size)
  have hhead : MemoryWords fields (root + 4)
      [UInt256.ofNat sender.val, id, UInt256.ofNat 320, index, seized, repaid, borrower, receiver,
        UInt256.ofNat (608 + 128 * m.collaterals.length)] := by
    have h := hh'.append_writeWordArray
      [index, seized, repaid, borrower, receiver,
        UInt256.ofNat (608 + 128 * m.collaterals.length)]
      (by simp only [List.length_cons, List.length_nil, List.length_append]; omega)
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc,
      List.cons_append, List.nil_append, fields] using h
  have hm : MemoryWords encoded (root + 324) ws :=
    marketEncodeMemory_words head (root + 324) m (by omega)
  have hm' : MemoryWords fields (root + 324) ws := hm.writeWords _
    (Or.inr (by simp only [List.length_cons, List.length_nil]; omega))
  let dataMem := calldataBytesEncodeMemory fields bytes
    (root + 612 + 128 * m.collaterals.length) dp dl
  have hbefore : MemoryWords dataMem (root + 4)
      [UInt256.ofNat sender.val, id, UInt256.ofNat 320, index, seized, repaid, borrower, receiver,
        UInt256.ofNat (608 + 128 * m.collaterals.length)] :=
    hhead.calldataBytesEncode hd
      (by simp only [List.length_cons, List.length_nil]; omega)
  have hmdata : MemoryWords dataMem (root + 324) ws := hm'.calldataBytesEncode hd
    (by rw [hwlen]; omega)
  have hlen := calldataBytesEncodeMemory_header fields bytes
    (root + 612 + 128 * m.collaterals.length) dp dl hd (by omega)
  have hsuffix := hmdata.append (last := [UInt256.ofNat dl]) (by
    convert hlen using 1
    rw [hwlen]; omega)
  have hsuffix' := hsuffix.writeWord (off := root + 292) badDebt (Or.inr (by omega))
  have hhead' := hbefore.append_writeWordArray [badDebt]
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc,
    writeWordArray, List.cons_append, List.nil_append] at hhead'
  have hall := hhead'.append (last := ws ++ [UInt256.ofNat dl]) (by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc]
      using hsuffix')
  simpa only [liquidateCallbackMemory, liquidateCallbackFieldsMemory_eq, liquidateCallbackWords,
    List.append_assoc, dataMem, fields, encoded, head, ws] using hall

end Benchmarks.Midnight
