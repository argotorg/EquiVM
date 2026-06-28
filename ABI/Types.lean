
namespace ABI

def BitWidth := { m : Nat // 0 < m ∧ m ≤ 256 ∧ m % 8 = 0}
  deriving DecidableEq, Repr

def FinPos N := { n : Nat // 0 < n ∧ n ≤ N }
  deriving DecidableEq, Repr

/- Integer types used by Solidity-style ABI values. -/
inductive IntType where
  | uint : BitWidth -> IntType
  | sint : BitWidth -> IntType
  deriving DecidableEq, Repr

/- Fixed-point decimal number types used by Solidity-style ABI values. -/
-- Note: Just added to have complete coverage of ABI, will not implement right now
inductive FixedType where
  | ufixed : BitWidth -> FinPos 80 -> FixedType
  | fixed : BitWidth -> FinPos 81 -> FixedType
  deriving DecidableEq, Repr

/- Elemnrary first-order types, per the Solidity ABI. -/
inductive ElemType where
  | bool : ElemType
  | address : ElemType
  /-- Legacy/optimizer solc external wrappers that mask address calldata words instead of rejecting
      non-canonical high bits. It has the same ABI signature and encoding as `address`. -/
  | legacyAddress : ElemType
  | int : IntType -> ElemType
  | fixed : FixedType -> ElemType
  | bytes : Fin 32 -> ElemType
  | function : ElemType
  deriving DecidableEq, Repr, Inhabited

/- ABI types for parameters, locals, and return values. -/
inductive ABIType where
  | elem : ElemType -> ABIType
  | array : ABIType -> Nat -> ABIType
  | bytes : ABIType
  | string : ABIType
  | dynamicArray : ABIType -> ABIType
  | tuple : List ABIType -> ABIType
  deriving Repr, Inhabited

mutual
  private def ABIType.decEq : (a b : ABIType) -> Decidable (a = b)
    | .elem p, .elem q =>
        match (inferInstance : Decidable (p = q)) with
        | isTrue h => isTrue (by subst q; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .array t n, .array u m =>
        match ABIType.decEq t u, (inferInstance : Decidable (n = m)) with
        | isTrue ht, isTrue hn => isTrue (by subst u; subst m; rfl)
        | isFalse ht, _ => isFalse (by intro h'; cases h'; exact ht rfl)
        | _, isFalse hn => isFalse (by intro h'; cases h'; exact hn rfl)
    | .bytes, .bytes =>
        isTrue (by rfl)
    | .string, .string =>
        isTrue (by rfl)
    | .dynamicArray t, .dynamicArray u =>
        match ABIType.decEq t u with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .tuple ts, .tuple us =>
        match ABIType.decEqList ts us with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .elem _, .array _ _ => isFalse (by intro h; cases h)
    | .elem _, .bytes => isFalse (by intro h; cases h)
    | .elem _, .string => isFalse (by intro h; cases h)
    | .elem _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .elem _, .tuple _ => isFalse (by intro h; cases h)
    | .array _ _, .elem _ => isFalse (by intro h; cases h)
    | .array _ _, .bytes => isFalse (by intro h; cases h)
    | .array _ _, .string => isFalse (by intro h; cases h)
    | .array _ _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .array _ _, .tuple _ => isFalse (by intro h; cases h)
    | .bytes, .elem _ => isFalse (by intro h; cases h)
    | .bytes, .array _ _ => isFalse (by intro h; cases h)
    | .bytes, .string => isFalse (by intro h; cases h)
    | .bytes, .dynamicArray _ => isFalse (by intro h; cases h)
    | .bytes, .tuple _ => isFalse (by intro h; cases h)
    | .string, .elem _ => isFalse (by intro h; cases h)
    | .string, .array _ _ => isFalse (by intro h; cases h)
    | .string, .bytes => isFalse (by intro h; cases h)
    | .string, .dynamicArray _ => isFalse (by intro h; cases h)
    | .string, .tuple _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .elem _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .array _ _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .bytes => isFalse (by intro h; cases h)
    | .dynamicArray _, .string => isFalse (by intro h; cases h)
    | .dynamicArray _, .tuple _ => isFalse (by intro h; cases h)
    | .tuple _, .elem _ => isFalse (by intro h; cases h)
    | .tuple _, .array _ _ => isFalse (by intro h; cases h)
    | .tuple _, .bytes => isFalse (by intro h; cases h)
    | .tuple _, .string => isFalse (by intro h; cases h)
    | .tuple _, .dynamicArray _ => isFalse (by intro h; cases h)

  private def ABIType.decEqList : (as bs : List ABIType) -> Decidable (as = bs)
    | [], [] => isTrue rfl
    | a :: as, b :: bs =>
        match ABIType.decEq a b, ABIType.decEqList as bs with
        | isTrue ha, isTrue hs => isTrue (by cases ha; cases hs; rfl)
        | isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, isFalse hs => isFalse (by intro h; cases h; exact hs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq ABIType :=
  ABIType.decEq

mutual
  def isDynamicABIType : ABIType → Bool
    | .elem _ => false
    | .array ty _ => isDynamicABIType ty
    | .tuple tys => isDynamicABITypeList tys
    | .bytes | .string | .dynamicArray _ => true

  def isDynamicABITypeList : List ABIType → Bool
    | [] => false
    | ty :: tys => isDynamicABIType ty || isDynamicABITypeList tys
end

mutual
  def usesLegacyAddressType : ABIType → Bool
    | .elem .legacyAddress => true
    | .elem _ => false
    | .array ty _ => usesLegacyAddressType ty
    | .tuple tys => usesLegacyAddressTypes tys
    | .bytes | .string => false
    | .dynamicArray ty => usesLegacyAddressType ty

  def usesLegacyAddressTypes : List ABIType → Bool
    | [] => false
    | ty :: tys => usesLegacyAddressType ty || usesLegacyAddressTypes tys
end

mutual
  def staticABIEncodedSize? : ABIType → Option Nat
    | .elem _ => some 32
    | .array ty n => do
        let elemSize <- staticABIEncodedSize? ty
        some (n * elemSize)
    | .tuple tys => staticABIEncodedSizeList? tys 0
    | .bytes | .string | .dynamicArray _ => none

  def staticABIEncodedSizeList? (types : List ABIType) (size : Nat) : Option Nat :=
    match types with
    | [] => some size
    | ty :: rest => do
        let tySize <- staticABIEncodedSize? ty
        staticABIEncodedSizeList? rest (size + tySize)
end

def abiTupleHeadSize? (types : List ABIType) : Option Nat :=
  match types with
  | [] => some 0
  | ty :: rest => do
      let restSize <- abiTupleHeadSize? rest
      if isDynamicABIType ty then
        some (32 + restSize)
      else do
        let tySize <- staticABIEncodedSize? ty
        some (tySize + restSize)
  termination_by (sizeOf types, 1, 0)
decreasing_by
  all_goals simp_wf
  all_goals decreasing_tactic

def paddedSize (n : Nat) : Nat :=
  32 * ((n + 31) / 32)
