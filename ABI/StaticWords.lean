import ABI.Encode
import ABI.Decode

/-! Flattening static ABI types into the word-scalar leaves they occupy. -/

namespace ABI

/-- Repeat a list `n` times and concatenate the copies. -/
def repeatList (n : Nat) (xs : List α) : List α :=
  List.foldr (fun ys acc => ys ++ acc) [] (List.replicate n xs)

/-- ABI types whose scalar encoding/decoding is mediated by a single EVM word. -/
def isWordScalar : ABIType → Bool
  | .elem .bool => true
  | .elem .address => true
  | .elem (.int _) => true
  | _ => false

mutual
  /-- Flatten a static ABI type into the word-scalar leaves it occupies, in ABI order.

  Dynamic ABI types and static elementary types not represented by `decodeABIWord?` return `none`.
  -/
  def staticWordTypes? : ABIType → Option (List ABIType)
    | ty@(.elem _) =>
        if isWordScalar ty then some [ty] else none
    | .array ty n => do
        let elemTypes <- staticWordTypes? ty
        some (repeatList n elemTypes)
    | .tuple tys =>
        staticWordTypesList? tys
    | .bytes | .string | .dynamicArray _ =>
        none

  def staticWordTypesList? : List ABIType → Option (List ABIType)
    | [] => some []
    | ty :: tys => do
        let tyWords <- staticWordTypes? ty
        let restWords <- staticWordTypesList? tys
        some (tyWords ++ restWords)
end

mutual
  /-- Flatten a static ABI value into `(type, value)` word-scalar leaves, in ABI order.

  The function succeeds only when every scalar leaf is accepted by `encodeABIWord?`.
  -/
  def staticWordPairs? : ABIType → Solm.Value → Option (List (ABIType × Solm.Value))
    | ty@(.elem _), value =>
        if isWordScalar ty then
          match encodeABIWord? ty value with
          | some _ => some [(ty, value)]
          | none => none
        else
          none
    | .array ty n, .array values =>
        if values.length = n then staticWordPairsList? ty values else none
    | .array _ _, _ =>
        none
    | .tuple tys, .array values =>
        staticWordPairsZip? tys values
    | .tuple _, _ =>
        none
    | .bytes, _ | .string, _ | .dynamicArray _, _ =>
        none

  def staticWordPairsList? (ty : ABIType) : List Solm.Value → Option (List (ABIType × Solm.Value))
    | [] => some []
    | value :: values => do
        let valueWords <- staticWordPairs? ty value
        let restWords <- staticWordPairsList? ty values
        some (valueWords ++ restWords)

  def staticWordPairsZip? : List ABIType → List Solm.Value → Option (List (ABIType × Solm.Value))
    | [], [] => some []
    | ty :: tys, value :: values => do
        let valueWords <- staticWordPairs? ty value
        let restWords <- staticWordPairsZip? tys values
        some (valueWords ++ restWords)
    | _, _ => none
end

theorem staticWordTypes?_wordScalar {ty : ABIType} (h : isWordScalar ty = true) :
    staticWordTypes? ty = some [ty] := by
  cases ty with
  | elem elemTy =>
      cases elemTy <;> simp [staticWordTypes?, isWordScalar] at h ⊢
  | array ty n =>
      simp [isWordScalar] at h
  | bytes =>
      simp [isWordScalar] at h
  | string =>
      simp [isWordScalar] at h
  | dynamicArray ty =>
      simp [isWordScalar] at h
  | tuple tys =>
      simp [isWordScalar] at h

theorem staticWordPairs?_wordScalar {ty : ABIType} {value : Solm.Value}
    (hscalar : isWordScalar ty = true) (hword : encodeABIWord? ty value = some word) :
    staticWordPairs? ty value = some [(ty, value)] := by
  cases ty with
  | elem elemTy =>
      cases elemTy <;> simp [staticWordPairs?, isWordScalar] at hscalar ⊢
      all_goals try rw [hword]
  | array ty n =>
      simp [isWordScalar] at hscalar
  | bytes =>
      simp [isWordScalar] at hscalar
  | string =>
      simp [isWordScalar] at hscalar
  | dynamicArray ty =>
      simp [isWordScalar] at hscalar
  | tuple tys =>
      simp [isWordScalar] at hscalar

end ABI
