import ABI.Types

namespace Solm

open ABI

abbrev Ident := String

/- Storage slots may either hold Elementary ABI values or nested mappings. -/
-- Note: name changed from StorageRefType, because in Solidity terminology
-- a slot is a storage word, not a location for an item in storage
-- of which there may be multiple in a given word
-- TODO: separate handling for bytes and string (both dynamicArrays), because of Solidity compacting
--       Or should we have that be implemented at "runtime" within the code?
inductive StorageType where
  | elem : ElemType -> StorageType
  | mapping : ElemType -> StorageType -> StorageType  -- Check more on Keytype here
  | contract : Ident -> StorageType
  -- Keeping the fields inside the struct so that recursion over StorageType is well-founded
  -- So right now this refers to the AST, not the surface syntax
  | struct : Ident -> List (Ident × StorageType) -> StorageType
  | tuple : List StorageType -> StorageType
  | array : StorageType -> Nat -> StorageType
  | dynamicArray : StorageType -> StorageType
  deriving Repr, Inhabited

mutual
  private def StorageType.decEq : (a b : StorageType) -> Decidable (a = b)
    | .elem p, .elem q =>
        match (inferInstance : Decidable (p = q)) with
        | isTrue h => isTrue (by subst q; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .mapping k t, .mapping l u =>
        match (inferInstance : Decidable (k = l)), StorageType.decEq t u with
        | isTrue hk, isTrue ht => isTrue (by subst l; subst u; rfl)
        | isFalse hk, _ => isFalse (by intro h'; cases h'; exact hk rfl)
        | _, isFalse ht => isFalse (by intro h'; cases h'; exact ht rfl)
    | .contract x, .contract y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .struct x fx, .struct y fy =>
        match (inferInstance : Decidable (x = y)), StorageType.decEqNamedList fx fy with
        | isTrue h, isTrue hf => isTrue (by subst y; cases hf; rfl)
        | _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
        | isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
    | .tuple xs, .tuple ys =>
        match StorageType.decEqList xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .array t n, .array u m =>
        match StorageType.decEq t u, (inferInstance : Decidable (n = m)) with
        | isTrue ht, isTrue hn => isTrue (by subst u; subst m; rfl)
        | isFalse ht, _ => isFalse (by intro h'; cases h'; exact ht rfl)
        | _, isFalse hn => isFalse (by intro h'; cases h'; exact hn rfl)
    | .dynamicArray t, .dynamicArray u =>
        match StorageType.decEq t u with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .elem _, .mapping _ _ => isFalse (by intro h; cases h)
    | .elem _, .contract _ => isFalse (by intro h; cases h)
    | .elem _, .struct _ _ => isFalse (by intro h; cases h)
    | .elem _, .tuple _ => isFalse (by intro h; cases h)
    | .elem _, .array _ _ => isFalse (by intro h; cases h)
    | .elem _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .mapping _ _, .elem _ => isFalse (by intro h; cases h)
    | .mapping _ _, .contract _ => isFalse (by intro h; cases h)
    | .mapping _ _, .struct _ _ => isFalse (by intro h; cases h)
    | .mapping _ _, .tuple _ => isFalse (by intro h; cases h)
    | .mapping _ _, .array _ _ => isFalse (by intro h; cases h)
    | .mapping _ _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .contract _, .elem _ => isFalse (by intro h; cases h)
    | .contract _, .mapping _ _ => isFalse (by intro h; cases h)
    | .contract _, .struct _ _ => isFalse (by intro h; cases h)
    | .contract _, .tuple _ => isFalse (by intro h; cases h)
    | .contract _, .array _ _ => isFalse (by intro h; cases h)
    | .contract _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .struct _ _, .elem _ => isFalse (by intro h; cases h)
    | .struct _ _, .mapping _ _ => isFalse (by intro h; cases h)
    | .struct _ _, .contract _ => isFalse (by intro h; cases h)
    | .struct _ _, .tuple _ => isFalse (by intro h; cases h)
    | .struct _ _, .array _ _ => isFalse (by intro h; cases h)
    | .struct _ _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .tuple _, .elem _ => isFalse (by intro h; cases h)
    | .tuple _, .mapping _ _ => isFalse (by intro h; cases h)
    | .tuple _, .contract _ => isFalse (by intro h; cases h)
    | .tuple _, .struct _ _ => isFalse (by intro h; cases h)
    | .tuple _, .array _ _ => isFalse (by intro h; cases h)
    | .tuple _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .array _ _, .elem _ => isFalse (by intro h; cases h)
    | .array _ _, .mapping _ _ => isFalse (by intro h; cases h)
    | .array _ _, .contract _ => isFalse (by intro h; cases h)
    | .array _ _, .struct _ _ => isFalse (by intro h; cases h)
    | .array _ _, .tuple _ => isFalse (by intro h; cases h)
    | .array _ _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .elem _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .mapping _ _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .contract _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .struct _ _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .tuple _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .array _ _ => isFalse (by intro h; cases h)

  private def StorageType.decEqList : (as bs : List StorageType) -> Decidable (as = bs)
    | [], [] => isTrue rfl
    | a :: as, b :: bs =>
        match StorageType.decEq a b, StorageType.decEqList as bs with
        | isTrue ha, isTrue hs => isTrue (by cases ha; cases hs; rfl)
        | isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, isFalse hs => isFalse (by intro h; cases h; exact hs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)

  private def StorageType.decEqNamedList : (as bs : List (Ident × StorageType)) -> Decidable (as = bs)
    | [], [] => isTrue rfl
    | (an, al) :: as, (bn, bl) :: bs =>
        match String.decEq an bn, StorageType.decEq al bl, StorageType.decEqNamedList as bs with
        | isTrue han, isTrue ha, isTrue hs => isTrue (by cases ha; cases hs; cases han; rfl)
        | isFalse han, _, _ => isFalse (by intro h; cases h; exact han rfl)
        | _, isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, _, isFalse hs => isFalse (by intro h; cases h; exact hs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq StorageType :=
  StorageType.decEq

inductive EnvVar where
  | caller
  | origin
  | callvalue
  | this
  | timestamp
  deriving DecidableEq, Repr, Inhabited

inductive UnaryOp where
  | not
  | neg
  deriving DecidableEq, Repr, Inhabited

inductive BinaryOp where
  | add
  | sub
  | mul
  | div
  | mod
  | eq
  | ne
  | lt
  | le
  | gt
  | ge
  | and
  | or
  deriving DecidableEq, Repr, Inhabited

mutual

/- Expressions are intentionally lightweight for now. We are aiming for a meaningful
   subset of Solidity. -/
inductive Expr where
  | intLit : Int -> Expr
  | boolLit : Bool -> Expr
  | bytesLit : ByteArray -> Expr
  /- `new bytes(len)`: a fresh zero-filled byte string of dynamic length `len` -/
  | newBytes : Expr -> Expr
  | var : Ident -> Expr
  | env : EnvVar -> Expr
  /- for struct fields -/
  | field : Expr -> Ident -> Expr
  /- array index. Shall we differentiate between the two? -/
  /- Zoe: do we really need aindex and field for memory arrays and structs? TODO investigate-/
  | aindex : Expr -> Expr -> Expr
  | storage : StorageRef -> Expr
  /- TODO what types allow casting? -/
  | inRange : IntType -> Expr -> Expr
  | cast : Expr -> StorageType -> Expr /- TODO do we really need casting?-/
  | addrOf : Expr -> Expr
  | unary : UnaryOp -> Expr -> Expr
  | binary : BinaryOp -> Expr -> Expr -> Expr
  | ite : Expr -> Expr -> Expr -> Expr

inductive StorageRefStep where
  | field : Ident -> StorageRefStep
  | mindex : Expr -> StorageRefStep
  | aindex : Expr -> StorageRefStep

structure StorageRef where
  base : Ident
  steps : List StorageRefStep := []

/- Zoe: Shall we use StorageRef at the Expr level too instead of having field, mindex, aindex? -/

end

instance : Repr ByteArray where
  reprPrec b _ := repr b.data

deriving instance Repr for Expr
deriving instance Inhabited for Expr
deriving instance Repr for StorageRefStep
deriving instance Inhabited for StorageRefStep
deriving instance Repr for StorageRef
deriving instance Inhabited for StorageRef

mutual
  private def Expr.decEq : (a b : Expr) -> Decidable (a = b)
    | .intLit x, .intLit y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .boolLit x, .boolLit y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .bytesLit x, .bytesLit y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .newBytes x, .newBytes y =>
        match Expr.decEq x y with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .var x, .var y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .env x, .env y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .field x fx, .field y fy =>
        match Expr.decEq x y, (inferInstance : Decidable (fx = fy)) with
        | isTrue hx, isTrue hf => isTrue (by subst y; subst fy; rfl)
        | isFalse hx, _ => isFalse (by intro h'; cases h'; exact hx rfl)
        | _, isFalse hf => isFalse (by intro h'; cases h'; exact hf rfl)
    | .aindex x ix, .aindex y iy =>
        match Expr.decEq x y, Expr.decEq ix iy with
        | isTrue hx, isTrue hi => isTrue (by cases hx; cases hi; rfl)
        | isFalse hx, _ => isFalse (by intro h'; cases h'; exact hx rfl)
        | _, isFalse hi => isFalse (by intro h'; cases h'; exact hi rfl)
    | .storage x, .storage y =>
        match StorageRef.decEq x y with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .inRange tx x, .inRange ty y =>
        match (inferInstance : Decidable (tx = ty)), Expr.decEq x y with
        | isTrue ht, isTrue hx => isTrue (by cases ht; cases hx; rfl)
        | isFalse ht, _ => isFalse (by intro h'; cases h'; exact ht rfl)
        | _, isFalse hx => isFalse (by intro h'; cases h'; exact hx rfl)
    | .cast x tx, .cast y ty =>
        match Expr.decEq x y, (inferInstance : Decidable (tx = ty)) with
        | isTrue hx, isTrue ht => isTrue (by cases hx; cases ht; rfl)
        | isFalse hx, _ => isFalse (by intro h'; cases h'; exact hx rfl)
        | _, isFalse ht => isFalse (by intro h'; cases h'; exact ht rfl)
    | .addrOf x, .addrOf y =>
        match Expr.decEq x y with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .unary ox x, .unary oy y =>
        match (inferInstance : Decidable (ox = oy)), Expr.decEq x y with
        | isTrue ho, isTrue hx => isTrue (by cases ho; cases hx; rfl)
        | isFalse ho, _ => isFalse (by intro h'; cases h'; exact ho rfl)
        | _, isFalse hx => isFalse (by intro h'; cases h'; exact hx rfl)
    | .binary ox lx rx, .binary oy ly ry =>
        match (inferInstance : Decidable (ox = oy)), Expr.decEq lx ly, Expr.decEq rx ry with
        | isTrue ho, isTrue hl, isTrue hr => isTrue (by cases ho; cases hl; cases hr; rfl)
        | isFalse ho, _, _ => isFalse (by intro h'; cases h'; exact ho rfl)
        | _, isFalse hl, _ => isFalse (by intro h'; cases h'; exact hl rfl)
        | _, _, isFalse hr => isFalse (by intro h'; cases h'; exact hr rfl)
    | .ite cx tx fx, .ite cy ty fy =>
        match Expr.decEq cx cy, Expr.decEq tx ty, Expr.decEq fx fy with
        | isTrue hc, isTrue ht, isTrue hf => isTrue (by cases hc; cases ht; cases hf; rfl)
        | isFalse hc, _, _ => isFalse (by intro h'; cases h'; exact hc rfl)
        | _, isFalse ht, _ => isFalse (by intro h'; cases h'; exact ht rfl)
        | _, _, isFalse hf => isFalse (by intro h'; cases h'; exact hf rfl)
    | .intLit _, .boolLit _ => isFalse (by intro h; cases h)
    | .intLit _, .var _ => isFalse (by intro h; cases h)
    | .intLit _, .env _ => isFalse (by intro h; cases h)
    | .intLit _, .field _ _ => isFalse (by intro h; cases h)
    | .intLit _, .aindex _ _ => isFalse (by intro h; cases h)
    | .intLit _, .storage _ => isFalse (by intro h; cases h)
    | .intLit _, .inRange _ _ => isFalse (by intro h; cases h)
    | .intLit _, .cast _ _ => isFalse (by intro h; cases h)
    | .intLit _, .addrOf _ => isFalse (by intro h; cases h)
    | .intLit _, .unary _ _ => isFalse (by intro h; cases h)
    | .intLit _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .intLit _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .boolLit _, .intLit _ => isFalse (by intro h; cases h)
    | .boolLit _, .var _ => isFalse (by intro h; cases h)
    | .boolLit _, .env _ => isFalse (by intro h; cases h)
    | .boolLit _, .field _ _ => isFalse (by intro h; cases h)
    | .boolLit _, .aindex _ _ => isFalse (by intro h; cases h)
    | .boolLit _, .storage _ => isFalse (by intro h; cases h)
    | .boolLit _, .inRange _ _ => isFalse (by intro h; cases h)
    | .boolLit _, .cast _ _ => isFalse (by intro h; cases h)
    | .boolLit _, .addrOf _ => isFalse (by intro h; cases h)
    | .boolLit _, .unary _ _ => isFalse (by intro h; cases h)
    | .boolLit _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .boolLit _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .var _, .intLit _ => isFalse (by intro h; cases h)
    | .var _, .boolLit _ => isFalse (by intro h; cases h)
    | .var _, .env _ => isFalse (by intro h; cases h)
    | .var _, .field _ _ => isFalse (by intro h; cases h)
    | .var _, .aindex _ _ => isFalse (by intro h; cases h)
    | .var _, .storage _ => isFalse (by intro h; cases h)
    | .var _, .inRange _ _ => isFalse (by intro h; cases h)
    | .var _, .cast _ _ => isFalse (by intro h; cases h)
    | .var _, .addrOf _ => isFalse (by intro h; cases h)
    | .var _, .unary _ _ => isFalse (by intro h; cases h)
    | .var _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .var _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .env _, .intLit _ => isFalse (by intro h; cases h)
    | .env _, .boolLit _ => isFalse (by intro h; cases h)
    | .env _, .var _ => isFalse (by intro h; cases h)
    | .env _, .field _ _ => isFalse (by intro h; cases h)
    | .env _, .aindex _ _ => isFalse (by intro h; cases h)
    | .env _, .storage _ => isFalse (by intro h; cases h)
    | .env _, .inRange _ _ => isFalse (by intro h; cases h)
    | .env _, .cast _ _ => isFalse (by intro h; cases h)
    | .env _, .addrOf _ => isFalse (by intro h; cases h)
    | .env _, .unary _ _ => isFalse (by intro h; cases h)
    | .env _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .env _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .field _ _, .intLit _ => isFalse (by intro h; cases h)
    | .field _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .field _ _, .var _ => isFalse (by intro h; cases h)
    | .field _ _, .env _ => isFalse (by intro h; cases h)
    | .field _ _, .aindex _ _ => isFalse (by intro h; cases h)
    | .field _ _, .storage _ => isFalse (by intro h; cases h)
    | .field _ _, .inRange _ _ => isFalse (by intro h; cases h)
    | .field _ _, .cast _ _ => isFalse (by intro h; cases h)
    | .field _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .field _ _, .unary _ _ => isFalse (by intro h; cases h)
    | .field _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .field _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .aindex _ _, .intLit _ => isFalse (by intro h; cases h)
    | .aindex _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .aindex _ _, .var _ => isFalse (by intro h; cases h)
    | .aindex _ _, .env _ => isFalse (by intro h; cases h)
    | .aindex _ _, .field _ _ => isFalse (by intro h; cases h)
    | .aindex _ _, .storage _ => isFalse (by intro h; cases h)
    | .aindex _ _, .inRange _ _ => isFalse (by intro h; cases h)
    | .aindex _ _, .cast _ _ => isFalse (by intro h; cases h)
    | .aindex _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .aindex _ _, .unary _ _ => isFalse (by intro h; cases h)
    | .aindex _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .aindex _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .storage _, .intLit _ => isFalse (by intro h; cases h)
    | .storage _, .boolLit _ => isFalse (by intro h; cases h)
    | .storage _, .var _ => isFalse (by intro h; cases h)
    | .storage _, .env _ => isFalse (by intro h; cases h)
    | .storage _, .field _ _ => isFalse (by intro h; cases h)
    | .storage _, .aindex _ _ => isFalse (by intro h; cases h)
    | .storage _, .inRange _ _ => isFalse (by intro h; cases h)
    | .storage _, .cast _ _ => isFalse (by intro h; cases h)
    | .storage _, .addrOf _ => isFalse (by intro h; cases h)
    | .storage _, .unary _ _ => isFalse (by intro h; cases h)
    | .storage _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .storage _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .intLit _ => isFalse (by intro h; cases h)
    | .inRange _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .inRange _ _, .var _ => isFalse (by intro h; cases h)
    | .inRange _ _, .env _ => isFalse (by intro h; cases h)
    | .inRange _ _, .field _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .aindex _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .storage _ => isFalse (by intro h; cases h)
    | .inRange _ _, .cast _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .inRange _ _, .unary _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .intLit _ => isFalse (by intro h; cases h)
    | .cast _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .cast _ _, .var _ => isFalse (by intro h; cases h)
    | .cast _ _, .env _ => isFalse (by intro h; cases h)
    | .cast _ _, .field _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .aindex _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .storage _ => isFalse (by intro h; cases h)
    | .cast _ _, .inRange _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .cast _ _, .unary _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .addrOf _, .intLit _ => isFalse (by intro h; cases h)
    | .addrOf _, .boolLit _ => isFalse (by intro h; cases h)
    | .addrOf _, .var _ => isFalse (by intro h; cases h)
    | .addrOf _, .env _ => isFalse (by intro h; cases h)
    | .addrOf _, .field _ _ => isFalse (by intro h; cases h)
    | .addrOf _, .aindex _ _ => isFalse (by intro h; cases h)
    | .addrOf _, .storage _ => isFalse (by intro h; cases h)
    | .addrOf _, .inRange _ _ => isFalse (by intro h; cases h)
    | .addrOf _, .cast _ _ => isFalse (by intro h; cases h)
    | .addrOf _, .unary _ _ => isFalse (by intro h; cases h)
    | .addrOf _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .addrOf _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .intLit _ => isFalse (by intro h; cases h)
    | .unary _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .unary _ _, .var _ => isFalse (by intro h; cases h)
    | .unary _ _, .env _ => isFalse (by intro h; cases h)
    | .unary _ _, .field _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .aindex _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .storage _ => isFalse (by intro h; cases h)
    | .unary _ _, .inRange _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .cast _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .unary _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .intLit _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .var _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .env _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .field _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .aindex _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .storage _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .inRange _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .cast _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .unary _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .intLit _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .var _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .env _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .field _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .aindex _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .storage _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .inRange _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .cast _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .unary _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .intLit _ => isFalse (by intro h; cases h)
    | .bytesLit _, .boolLit _ => isFalse (by intro h; cases h)
    | .bytesLit _, .var _ => isFalse (by intro h; cases h)
    | .bytesLit _, .env _ => isFalse (by intro h; cases h)
    | .bytesLit _, .field _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .aindex _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .storage _ => isFalse (by intro h; cases h)
    | .bytesLit _, .inRange _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .cast _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .addrOf _ => isFalse (by intro h; cases h)
    | .bytesLit _, .unary _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .newBytes _ => isFalse (by intro h; cases h)
    | .intLit _, .bytesLit _ => isFalse (by intro h; cases h)
    | .boolLit _, .bytesLit _ => isFalse (by intro h; cases h)
    | .var _, .bytesLit _ => isFalse (by intro h; cases h)
    | .env _, .bytesLit _ => isFalse (by intro h; cases h)
    | .field _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .aindex _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .storage _, .bytesLit _ => isFalse (by intro h; cases h)
    | .inRange _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .cast _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .addrOf _, .bytesLit _ => isFalse (by intro h; cases h)
    | .unary _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .newBytes _, .intLit _ => isFalse (by intro h; cases h)
    | .newBytes _, .boolLit _ => isFalse (by intro h; cases h)
    | .newBytes _, .var _ => isFalse (by intro h; cases h)
    | .newBytes _, .env _ => isFalse (by intro h; cases h)
    | .newBytes _, .field _ _ => isFalse (by intro h; cases h)
    | .newBytes _, .aindex _ _ => isFalse (by intro h; cases h)
    | .newBytes _, .storage _ => isFalse (by intro h; cases h)
    | .newBytes _, .inRange _ _ => isFalse (by intro h; cases h)
    | .newBytes _, .cast _ _ => isFalse (by intro h; cases h)
    | .newBytes _, .addrOf _ => isFalse (by intro h; cases h)
    | .newBytes _, .unary _ _ => isFalse (by intro h; cases h)
    | .newBytes _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .newBytes _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .newBytes _, .bytesLit _ => isFalse (by intro h; cases h)
    | .intLit _, .newBytes _ => isFalse (by intro h; cases h)
    | .boolLit _, .newBytes _ => isFalse (by intro h; cases h)
    | .var _, .newBytes _ => isFalse (by intro h; cases h)
    | .env _, .newBytes _ => isFalse (by intro h; cases h)
    | .field _ _, .newBytes _ => isFalse (by intro h; cases h)
    | .aindex _ _, .newBytes _ => isFalse (by intro h; cases h)
    | .storage _, .newBytes _ => isFalse (by intro h; cases h)
    | .inRange _ _, .newBytes _ => isFalse (by intro h; cases h)
    | .cast _ _, .newBytes _ => isFalse (by intro h; cases h)
    | .addrOf _, .newBytes _ => isFalse (by intro h; cases h)
    | .unary _ _, .newBytes _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .newBytes _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .newBytes _ => isFalse (by intro h; cases h)

  private def StorageRefStep.decEq : (a b : StorageRefStep) -> Decidable (a = b)
    | .field x, .field y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .mindex x, .mindex y =>
        match Expr.decEq x y with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .aindex x, .aindex y =>
        match Expr.decEq x y with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .field _, .mindex _ => isFalse (by intro h; cases h)
    | .field _, .aindex _ => isFalse (by intro h; cases h)
    | .mindex _, .field _ => isFalse (by intro h; cases h)
    | .mindex _, .aindex _ => isFalse (by intro h; cases h)
    | .aindex _, .field _ => isFalse (by intro h; cases h)
    | .aindex _, .mindex _ => isFalse (by intro h; cases h)

  private def StorageRef.decEq : (a b : StorageRef) -> Decidable (a = b)
    | ⟨base, steps⟩, ⟨base', steps'⟩ =>
        match (inferInstance : Decidable (base = base')), StorageRefStep.decEqList steps steps' with
        | isTrue hb, isTrue hs => isTrue (by cases hb; cases hs; rfl)
        | isFalse hb, _ => isFalse (by intro h; cases h; exact hb rfl)
        | _, isFalse hs => isFalse (by intro h; cases h; exact hs rfl)

  private def StorageRefStep.decEqList : (as bs : List StorageRefStep) -> Decidable (as = bs)
    | [], [] => isTrue rfl
    | a :: as, b :: bs =>
        match StorageRefStep.decEq a b, StorageRefStep.decEqList as bs with
        | isTrue ha, isTrue hs => isTrue (by cases ha; cases hs; rfl)
        | isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, isFalse hs => isFalse (by intro h; cases h; exact hs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq Expr :=
  Expr.decEq

instance : DecidableEq StorageRefStep :=
  StorageRefStep.decEq

instance : DecidableEq StorageRef :=
  StorageRef.decEq

namespace StorageRef

def var (name : Ident) : StorageRef :=
  { base := name }

end StorageRef

inductive AssignRhs where
  | expr : Expr -> AssignRhs
  -- Do we want non-determinism?
  -- | havoc
  deriving DecidableEq, Repr, Inhabited

inductive Stmt where
  /- local variable -/
  | letDecl : Ident -> Option ABIType -> Expr -> Stmt
  /- storage variable assignment -/
  | assign : StorageRef -> Expr -> Stmt
  | require : Expr -> Stmt
  | while : Expr -> List Stmt -> Stmt
  /- conditional: `if cond { thenBranch } else { elseBranch }`; a no-`else` `if` is `elseBranch = []` -/
  | ite : Expr -> List Stmt -> List Stmt -> Stmt
  /- constructor call -/
  | new : Ident -> Expr /- ETH to send -/ -> List Expr -> Ident /- return value binder -/ -> Stmt
  /- internal and external call results are explicitly let-bound -/
  | internalCall : Ident -> List Expr -> Ident /- return value binder -/ -> Stmt
  | externalCall : Expr -> Ident -> Expr /- ETH to send -/ -> List Expr -> Ident /- return value binder -/ -> Stmt
  /- low-level `target.call{value: v}(data)`: raw call, binds a success `bool` to `okVar`,
     returndata dropped, callee revert does NOT propagate -/
  | lowLevelCall : Expr /- target -/ -> Expr /- ETH to send -/ -> Expr /- calldata bytes -/ -> Ident /- success binder -/ -> Stmt
  | return : Expr -> Stmt
  | break : Stmt
  | continue : Stmt
  deriving Repr, Inhabited


mutual
  private def Stmt.decEq : (a b : Stmt) -> Decidable (a = b)
    | .letDecl nx tx ex, .letDecl ny ty ey =>
        match (inferInstance : Decidable (nx = ny)), (inferInstance : Decidable (tx = ty)), Expr.decEq ex ey with
        | isTrue hn, isTrue ht, isTrue he => isTrue (by cases hn; cases ht; cases he; rfl)
        | isFalse hn, _, _ => isFalse (by intro h; cases h; exact hn rfl)
        | _, isFalse ht, _ => isFalse (by intro h; cases h; exact ht rfl)
        | _, _, isFalse he => isFalse (by intro h; cases h; exact he rfl)
    | .assign sx ex, .assign sy ey =>
        match StorageRef.decEq sx sy, Expr.decEq ex ey with
        | isTrue hs, isTrue he => isTrue (by cases hs; cases he; rfl)
        | isFalse hs, _ => isFalse (by intro h; cases h; exact hs rfl)
        | _, isFalse he => isFalse (by intro h; cases h; exact he rfl)
    | .require ex, .require ey =>
        match Expr.decEq ex ey with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .while cx bx, .while cy bodyY =>
        match Expr.decEq cx cy, Stmt.decEqList bx bodyY with
        | isTrue hc, isTrue hb => isTrue (by cases hc; cases hb; rfl)
        | isFalse hc, _ => isFalse (by intro h; cases h; exact hc rfl)
        | _, isFalse hb => isFalse (by intro h; cases h; exact hb rfl)
    | .ite cx tx ex, .ite cy ty ey =>
        match Expr.decEq cx cy, Stmt.decEqList tx ty, Stmt.decEqList ex ey with
        | isTrue hc, isTrue ht, isTrue he => isTrue (by cases hc; cases ht; cases he; rfl)
        | isFalse hc, _, _ => isFalse (by intro h; cases h; exact hc rfl)
        | _, isFalse ht, _ => isFalse (by intro h; cases h; exact ht rfl)
        | _, _, isFalse he => isFalse (by intro h; cases h; exact he rfl)
    | .new nx vx ax rx, .new ny vy ay ry =>
        match (inferInstance : Decidable (nx = ny)), Expr.decEq vx vy, (inferInstance : Decidable (ax = ay)), (inferInstance : Decidable (rx = ry)) with
        | isTrue hn, isTrue hv, isTrue ha, isTrue hr => isTrue (by cases hn; cases hv; cases ha; cases hr; rfl)
        | isFalse hn, _, _, _ => isFalse (by intro h; cases h; exact hn rfl)
        | _, isFalse hv, _, _ => isFalse (by intro h; cases h; exact hv rfl)
        | _, _, isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, _, _, isFalse hr => isFalse (by intro h; cases h; exact hr rfl)
    | .internalCall nx ax rx, .internalCall ny ay ry =>
        match (inferInstance : Decidable (nx = ny)), (inferInstance : Decidable (ax = ay)), (inferInstance : Decidable (rx = ry)) with
        | isTrue hn, isTrue ha, isTrue hr => isTrue (by cases hn; cases ha; cases hr; rfl)
        | isFalse hn, _, _ => isFalse (by intro h; cases h; exact hn rfl)
        | _, isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, _, isFalse hr => isFalse (by intro h; cases h; exact hr rfl)
    | .externalCall tx nx vx ax rx, .externalCall ty ny vy ay ry =>
        match Expr.decEq tx ty, (inferInstance : Decidable (nx = ny)), Expr.decEq vx vy, (inferInstance : Decidable (ax = ay)), (inferInstance : Decidable (rx = ry)) with
        | isTrue ht, isTrue hn, isTrue hv, isTrue ha, isTrue hr => isTrue (by cases ht; cases hn; cases hv; cases ha; cases hr; rfl)
        | isFalse ht, _, _, _, _ => isFalse (by intro h; cases h; exact ht rfl)
        | _, isFalse hn, _, _, _ => isFalse (by intro h; cases h; exact hn rfl)
        | _, _, isFalse hv, _, _ => isFalse (by intro h; cases h; exact hv rfl)
        | _, _, _, isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, _, _, _, isFalse hr => isFalse (by intro h; cases h; exact hr rfl)
    | .lowLevelCall tx vx cx ox, .lowLevelCall ty vy cy oy =>
        match Expr.decEq tx ty, Expr.decEq vx vy, Expr.decEq cx cy, (inferInstance : Decidable (ox = oy)) with
        | isTrue ht, isTrue hv, isTrue hc, isTrue ho => isTrue (by cases ht; cases hv; cases hc; cases ho; rfl)
        | isFalse ht, _, _, _ => isFalse (by intro h; cases h; exact ht rfl)
        | _, isFalse hv, _, _ => isFalse (by intro h; cases h; exact hv rfl)
        | _, _, isFalse hc, _ => isFalse (by intro h; cases h; exact hc rfl)
        | _, _, _, isFalse ho => isFalse (by intro h; cases h; exact ho rfl)
    | .return ex, .return ey =>
        match Expr.decEq ex ey with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .break, .break => isTrue rfl
    | .continue, .continue => isTrue rfl
    | .letDecl _ _ _, .assign _ _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .require _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .while _ _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .return _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .break => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .continue => isFalse (by intro h; cases h)
    | .assign _ _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .assign _ _, .require _ => isFalse (by intro h; cases h)
    | .assign _ _, .while _ _ => isFalse (by intro h; cases h)
    | .assign _ _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .assign _ _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .assign _ _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .assign _ _, .return _ => isFalse (by intro h; cases h)
    | .assign _ _, .break => isFalse (by intro h; cases h)
    | .assign _ _, .continue => isFalse (by intro h; cases h)
    | .require _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .require _, .assign _ _ => isFalse (by intro h; cases h)
    | .require _, .while _ _ => isFalse (by intro h; cases h)
    | .require _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .require _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .require _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .require _, .return _ => isFalse (by intro h; cases h)
    | .require _, .break => isFalse (by intro h; cases h)
    | .require _, .continue => isFalse (by intro h; cases h)
    | .while _ _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .while _ _, .assign _ _ => isFalse (by intro h; cases h)
    | .while _ _, .require _ => isFalse (by intro h; cases h)
    | .while _ _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .while _ _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .while _ _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .while _ _, .return _ => isFalse (by intro h; cases h)
    | .while _ _, .break => isFalse (by intro h; cases h)
    | .while _ _, .continue => isFalse (by intro h; cases h)
    | .new _ _ _ _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .assign _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .require _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .while _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .return _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .break => isFalse (by intro h; cases h)
    | .new _ _ _ _, .continue => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .assign _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .require _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .while _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .return _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .break => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .continue => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .assign _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .require _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .while _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .return _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .break => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .continue => isFalse (by intro h; cases h)
    | .return _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .return _, .assign _ _ => isFalse (by intro h; cases h)
    | .return _, .require _ => isFalse (by intro h; cases h)
    | .return _, .while _ _ => isFalse (by intro h; cases h)
    | .return _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .return _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .return _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .return _, .break => isFalse (by intro h; cases h)
    | .return _, .continue => isFalse (by intro h; cases h)
    | .break, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .break, .assign _ _ => isFalse (by intro h; cases h)
    | .break, .require _ => isFalse (by intro h; cases h)
    | .break, .while _ _ => isFalse (by intro h; cases h)
    | .break, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .break, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .break, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .break, .return _ => isFalse (by intro h; cases h)
    | .break, .continue => isFalse (by intro h; cases h)
    | .continue, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .continue, .assign _ _ => isFalse (by intro h; cases h)
    | .continue, .require _ => isFalse (by intro h; cases h)
    | .continue, .while _ _ => isFalse (by intro h; cases h)
    | .continue, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .continue, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .continue, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .continue, .return _ => isFalse (by intro h; cases h)
    | .continue, .break => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .assign _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .require _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .while _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .return _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .break, .ite _ _ _ => isFalse (by intro h; cases h)
    | .continue, .ite _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .assign _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .require _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .while _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .return _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .break => isFalse (by intro h; cases h)
    | .ite _ _ _, .continue => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _, .assign _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _, .require _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _, .while _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _, .return _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _, .break => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _, .continue => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .lowLevelCall _ _ _ _ => isFalse (by intro h; cases h)
    | .assign _ _, .lowLevelCall _ _ _ _ => isFalse (by intro h; cases h)
    | .require _, .lowLevelCall _ _ _ _ => isFalse (by intro h; cases h)
    | .while _ _, .lowLevelCall _ _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .lowLevelCall _ _ _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .lowLevelCall _ _ _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .lowLevelCall _ _ _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .lowLevelCall _ _ _ _ => isFalse (by intro h; cases h)
    | .return _, .lowLevelCall _ _ _ _ => isFalse (by intro h; cases h)
    | .break, .lowLevelCall _ _ _ _ => isFalse (by intro h; cases h)
    | .continue, .lowLevelCall _ _ _ _ => isFalse (by intro h; cases h)

  private def Stmt.decEqList : (as bs : List Stmt) -> Decidable (as = bs)
    | [], [] => isTrue rfl
    | a :: as, b :: bs =>
        match Stmt.decEq a b, Stmt.decEqList as bs with
        | isTrue ha, isTrue hs => isTrue (by cases ha; cases hs; rfl)
        | isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, isFalse hs => isFalse (by intro h; cases h; exact hs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq Stmt :=
  Stmt.decEq

abbrev Body := List Stmt

structure Param where
  name : Ident
  ty : ABI.ABIType
  deriving DecidableEq, Repr, Inhabited

structure StorageDecl where
  name : Ident
  ty : StorageType
  deriving DecidableEq, Repr, Inhabited

structure ConstructorDecl where
  params : List Param
  body : List Stmt
  deriving DecidableEq, Repr, Inhabited

-- Currently this covers storage structs
-- The ABI technically has no structs,
-- Solidity implements call-parameter structs through ABI tuples
structure StructDecl where
  name : Ident
  fields : List StorageDecl
  deriving DecidableEq, Repr, Inhabited

structure FunctionDecl where
  name : Ident
  params : List Param
  returnType : Option ABIType := none
  body : List Stmt
  deriving DecidableEq, Repr, Inhabited

structure TransitionDecl where
  name : Ident
  params : List Param
  returnType : Option ABIType := none
  body : List Stmt
  deriving DecidableEq, Repr, Inhabited

structure ContractDecl where
  name : Ident
  storage : List StorageDecl
  ctor : ConstructorDecl
  structs : List StructDecl := [] -- Maybe these should not be per-contract. Zoe: if we are inlining them anyway, do we still need this?
  functions : List FunctionDecl := []
  transitions : List TransitionDecl := []
  deriving DecidableEq, Repr, Inhabited

abbrev Program := List ContractDecl

end Solm
