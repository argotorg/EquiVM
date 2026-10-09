import Benchmarks.Morpho.MorphoBlue.SafeTransferFrames
import Benchmarks.Morpho.MorphoBlue.WordBufferCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def safeTransferParamTypes (isFrom : Bool) : List ABIType :=
  (if isFrom then [abiAddress] else []) ++ [abiAddress, abiUInt256]
def safeTransferCallWords (isFrom : Bool) (sender recipient : AccountAddress) (value : UInt256) :
    List UInt256 :=
  (if isFrom then [UInt256.ofNat sender.val] else []) ++ [UInt256.ofNat recipient.val, value]
def safeTransferSelector (isFrom : Bool) : ByteArray :=
  if isFrom then ⟨#[35, 184, 114, 221]⟩ else ⟨#[169, 5, 156, 187]⟩
def safeTransferSelectorWord (isFrom : Bool) : UInt256 :=
  UInt256.ofNat (if isFrom then 16156842317565293874272834530371880720966471053262404558597773956279093428224
    else 76450787359836037641860180984291677749980919077056822294353438043884394381312)
def safeTransferCalldata (isFrom : Bool) (sender recipient : AccountAddress) (value : UInt256) : ByteArray :=
  safeTransferSelector isFrom ++ returnWordBytes (safeTransferCallWords isFrom sender recipient value)

set_option maxHeartbeats 0 in
theorem safeTransferSelectorFact (isFrom : Bool) :
    (KEC (ABI.printSignature ⟨if isFrom then "transferFrom" else "transfer",
      safeTransferParamTypes isFrom⟩).toUTF8).extract 0 4 = safeTransferSelector isFrom := by
  have hsig : ABI.printSignature ⟨if isFrom then "transferFrom" else "transfer",
      safeTransferParamTypes isFrom⟩ =
      if isFrom then "transferFrom(address,address,uint256)" else "transfer(address,uint256)" := by
    cases isFrom <;> simp [ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr,
      ABI.intTypeToSigStr, safeTransferParamTypes, abiAddress, abiUInt256, abiUInt256Int,
      show Nat.repr 256 = "256" by decide +kernel]
    <;> decide +kernel
  rw [hsig]
  cases isFrom <;> decide +kernel

theorem safeTransferSelectorWord_bytes (isFrom : Bool) :
    (safeTransferSelectorWord isFrom).toByteArray.extract 0 4 = safeTransferSelector isFrom := by
  cases isFrom <;> decide +kernel

theorem safeTransferCalldata_size (isFrom : Bool) (sender recipient : AccountAddress) (value : UInt256) :
    (safeTransferCalldata isFrom sender recipient value).size = if isFrom then 100 else 68 := by
  rw [safeTransferCalldata, ByteArray.size_append, returnWordBytes_size]
  cases isFrom <;> rfl

-- LIBRARY CANDIDATE: an arbitrary address's elementary ABI encoding.
theorem encodeABIValue_accountAddress (a : AccountAddress) :
    encodeABIValue? abiAddress (.address a) = some (EVM.Word.toBytesBE (UInt256.ofNat a.val)) := by
  simp [abiAddress, encodeABIValue?, encodeABIWord?]
  rfl

-- LIBRARY CANDIDATE: call encoding is return-value encoding prefixed by the selector.
theorem encodeCallWithSelector_of_return {types : List ABIType} {values : List Value} {out : ByteArray}
    (selector : ByteArray) (he : encodeReturnValues? types values = some out) :
    encodeCallWithSelector? selector types values = some (selector ++ out) := by
  unfold encodeReturnValues? at he
  unfold encodeCallWithSelector?
  cases h : encodeABIValues? types values with
  | none => simp [h] at he
  | some bytes =>
    have ho : bytes.toByteArray = out := by
      have heq : ByteArray.mk bytes.toArray = out := Option.some.inj (by simpa [h] using he)
      simpa only [mk_toArray_eq] using heq
    simp only [h, bind, Option.bind, ho]

theorem encodeSafeTransfer (isFrom : Bool) (sender recipient : AccountAddress) (value : UInt256) :
    config.externalABI.encode? (if isFrom then "transferFrom" else "transfer")
      (safeTransferCallArgs isFrom sender recipient value) =
      some (safeTransferCalldata isFrom sender recipient value) := by
  let entries : List (ElemType × Value × UInt256) :=
    (if isFrom then [(.address, .address sender, UInt256.ofNat sender.val)] else []) ++
      [(.address, .address recipient, UInt256.ofNat recipient.val),
        (.int (.uint ⟨256, by decide⟩), .int (Int.ofNat value.toNat), value)]
  have ht : entries.map (fun e => .elem e.1) = safeTransferParamTypes isFrom := by
    cases isFrom <;> rfl
  have hv : entries.map (fun e => e.2.1) = safeTransferCallArgs isFrom sender recipient value := by
    cases isFrom <;> rfl
  have hw : entries.map (fun e => e.2.2) = safeTransferCallWords isFrom sender recipient value := by
    cases isFrom <;> rfl
  have he : ∀ e ∈ entries, encodeABIValue? (.elem e.1) e.2.1 = some (EVM.Word.toBytesBE e.2.2) := by
    intro e he
    cases isFrom <;> simp only [entries, ↓reduceIte, Bool.false_eq_true, List.nil_append,
      List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at he
    · rcases he with rfl | rfl
      · exact encodeABIValue_accountAddress recipient
      · exact encodeABIValue_uint256 value
    · rcases he with rfl | rfl | rfl
      · exact encodeABIValue_accountAddress sender
      · exact encodeABIValue_accountAddress recipient
      · exact encodeABIValue_uint256 value
  have hr := elementaryWordsReturnEncoding entries he
  rw [ht, hv, hw] at hr
  have hs : Syntax.externalSignature (if isFrom then "transferFrom" else "transfer") =
      some ⟨if isFrom then "transferFrom" else "transfer", safeTransferParamTypes isFrom⟩ := by
    cases isFrom <;> rfl
  change (do
    let sig ← Syntax.externalSignature (if isFrom then "transferFrom" else "transfer")
    ABI.encodeCallWithSelector? ((KEC (ABI.printSignature sig).toUTF8).extract 0 4)
      sig.paramTypes (safeTransferCallArgs isFrom sender recipient value)) = _
  rw [hs]
  simp only [bind, Option.bind, safeTransferSelectorFact]
  exact encodeCallWithSelector_of_return _ hr

theorem safeTransferCalldata_read (isFrom : Bool) (sender recipient : AccountAddress) (value : UInt256)
    (mem : ByteArray) (off : Nat) (hg : off - mem.size < USize.size) :
    (staticWordCallMem (safeTransferSelectorWord isFrom)
      (safeTransferCallWords isFrom sender recipient value) mem off).readWithPadding
        off (if isFrom then 100 else 68) = safeTransferCalldata isFrom sender recipient value := by
  have hr := staticWordCallMem_read (safeTransferSelectorWord isFrom)
    (safeTransferCallWords isFrom sender recipient value) mem off
    (by cases isFrom <;> simp [safeTransferCallWords]) hg
  rw [safeTransferSelectorWord_bytes] at hr
  cases isFrom <;> exact hr

end Benchmarks.Morpho.MorphoBlue
