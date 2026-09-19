import Solm.Benchmarks.Auction.Memory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

/-- Recover the scalar byte list from an already-proved one-word return encoding. -/
theorem scalarValueEncoding {ty : ABIType} {value : Value} {w : UInt256}
    (hhead : abiTupleHeadSize? [ty] = some 32) (hdyn : isDynamicABIType ty = false)
    (hret : encodeReturnValue? ty value = some (UInt256.toByteArray w)) :
    encodeABIValue? ty value = some (EVM.Word.toBytesBE w) := by
  cases henc : encodeABIValue? ty value with
  | none =>
    simp only [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, hhead,
      encodeABIValuesFrom?, henc, bind, Option.bind] at hret
    cases hret
  | some bs =>
    have hbytes : (⟨bs.toArray⟩ : ByteArray) = UInt256.toByteArray w := by
      simpa only [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, hhead,
        encodeABIValuesFrom?, henc, hdyn, bind, Option.bind, if_false,
        Bool.false_eq_true, List.nil_append, List.append_nil, Option.some.injEq] using hret
    have heq : bs = EVM.Word.toBytesBE w := by
      rw [toByteArray_eq_toBytesBE] at hbytes
      simpa using congrArg (fun b : ByteArray => b.data.toList) hbytes
    exact congrArg some heq

end Auction
