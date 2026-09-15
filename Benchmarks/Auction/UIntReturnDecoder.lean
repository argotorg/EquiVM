import Benchmarks.Auction.CalldataHead
import Benchmarks.Auction.DynamicMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

set_option synthInstance.maxSize 1024 in
theorem uintReturnHeadWf : calldataHeadWf auctionBytecode ⟨5820⟩ ⟨5836⟩ ⟨32⟩ := by
  unfold calldataHeadWf
  native_decide

theorem uintReturnDecodeOk {I g s0 off finish ret R mem aw rdata acc k C word}
    (h : RD auctionBytecode I g s0 ⟨5820⟩ (off :: finish :: ret :: R)
      mem aw rdata acc k C)
    (hcheck : UInt256.slt (UInt256.sub finish off) ⟨32⟩ = ⟨0⟩)
    (hload : loadedWord mem aw off = word)
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret (word :: R)
      mem (expandedWords aw off ⟨32⟩) rdata acc k' C' := by
  obtain ⟨_, _, rd5836⟩ := calldataHeadOk h uintReturnHeadWf hcheck hov
  have rd5839 := evm_run rd5836 with [jumpdest, pop,
    raw mloadSymbolic (by native_decide) (by evm_ov)]
  rw [hload] at rd5839
  exact ⟨_, _, evm_run rd5839 with [swap2, swap1, pop, jump hret]⟩

theorem uintReturnDecodeShort {I g s0 off finish ret R mem aw rdata acc k C}
    (h : RD auctionBytecode I g s0 ⟨5820⟩ (off :: finish :: ret :: R)
      mem aw rdata acc k C)
    (hcheck : UInt256.slt (UInt256.sub finish off) ⟨32⟩ = ⟨1⟩)
    (hov : R.length + 8 ≤ 1024) : RDrev auctionBytecode g s0 :=
  calldataHeadFail h uintReturnHeadWf hcheck hov

-- LIBRARY CANDIDATE: strict one-word return decoding, independent of the contract.
theorem decodeReturnUint_long {out : ByteArray} (hl : 32 ≤ out.size) (hb : out.size < 2 ^ 255) :
    ABI.decodeReturnValue? (.elem (.int (.uint ⟨256, by decide⟩))) out =
      some (.int (Int.ofNat (calldataWord out 0).toNat)) := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hword := decode_word_at_eq out 0 (by omega) (by decide)
  have h32 : ((out.toList.drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, hlen]
    omega
  unfold ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (by decide)]
  rw [if_neg (by simp only [List.isEmpty_cons, hlen]; omega)]
  simp only [decodeScalarWords?, decodeScalarWord_uint256_ok h32, hword, bind, Option.bind]

theorem decodeReturnUint_short {out : ByteArray} (hl : out.size < 32) :
    ABI.decodeReturnValue? (.elem (.int (.uint ⟨256, by decide⟩))) out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have h32 : ¬ ((out.toList.drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, hlen]
    omega
  unfold ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (by decide)]
  rw [if_neg (by simp only [List.isEmpty_cons, hlen]; omega)]
  simp only [decodeScalarWords?, decodeScalarWord_uint256_none_short h32, bind, Option.bind]

end Auction
