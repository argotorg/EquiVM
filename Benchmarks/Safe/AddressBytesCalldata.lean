import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: successful decoding of an address/bytes tuple has the declared value shapes.
theorem decodeAddressBytesShape {cd : ByteArray} {x y : Ident} {args : Store}
    (hd : decodeCalldata [x, y] [abiAddress, .bytes] cd = some args) :
    ∃ target payload, args =
      (((∅ : Store).insert x (.address target)).insert y (.bytes payload)) := by
  simp only [decodeCalldata, abiAddress, isDynamicABIType, List.any_cons, List.any_nil,
    Bool.or_true, Bool.true_or, Bool.false_or, List.isEmpty_cons, solcTotalSizeDynamicGuard,
    Bool.false_eq_true, Bool.true_eq, true_and, false_and, if_false] at hd
  split at hd
  · contradiction
  split at hd
  · contradiction
  split at hd
  · contradiction
  simp only [decodeCalldata.decodeArgs, abiTupleHeadSize?, isDynamicABIType,
    staticABIEncodedSize?, bind, Option.bind, Bool.false_eq_true, if_false, if_true,
    Nat.reduceAdd, Nat.add_zero] at hd
  split at hd
  next decoded store endOffset hresult =>
    cases hd
    split at hresult
    · contradiction
    simp only [decodeABIValues?, decodeABIValue?, decodeABIWord?, isDynamicABIType,
      staticABIEncodedSize?, bind, Option.bind, Bool.false_eq_true, Bool.true_eq, if_false,
      if_true, Nat.zero_add, Nat.add_zero] at hresult
    cases hw : readWord? (cd.toList.drop 4) 0 with
    | none => simp only [hw] at hresult; contradiction
    | some word =>
      by_cases hc : word.val.val < EVM.addressModulus
      · simp only [hw, hc, ↓reduceIte] at hresult
        cases ho : readNat? (cd.toList.drop 4) 32 with
        | none => simp only [ho] at hresult; contradiction
        | some off =>
          by_cases hm : solcMaxLen .modern < off
          · simp only [ho, hm, ↓reduceIte] at hresult; contradiction
          · simp only [ho, hm, ↓reduceIte] at hresult
            cases hn : readNat? (cd.toList.drop 4) off with
            | none => simp only [hn] at hresult; contradiction
            | some n =>
              by_cases hbig : solcMaxLen .modern < n
              · simp only [hn, hbig, ↓reduceIte] at hresult; contradiction
              · simp only [hn, hbig, ↓reduceIte] at hresult
                cases hb : readBytes? (cd.toList.drop 4) (off + 32) n with
                | none => simp only [hb] at hresult; contradiction
                | some bs =>
                  simp only [hb, decodeCalldata.insertValues] at hresult
                  cases hresult
                  exact ⟨_, _, rfl⟩
      · simp only [hw, hc, ↓reduceIte] at hresult; contradiction
  next => contradiction

end Benchmarks.Safe
