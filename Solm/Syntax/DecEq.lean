import Solm.Syntax.Basic

/-!
`DecidableEq` instances for the `Solm` syntax types.

The recursive syntax types contain nested lists, a shape Lean's `DecidableEq`
deriver does not support. The hand-written deciders below keep those instances
computable while avoiding the large constructor cross-product that previously
made this module expensive to compile.
-/

namespace Solm

open ABI

deriving instance DecidableEq for KeyValue
deriving instance DecidableEq for EvaledStorageRefStep
deriving instance DecidableEq for EvaledStorageRef

set_option maxHeartbeats 2000000 in
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
    | .bytes, .bytes => isTrue rfl
    | .string, .string => isTrue rfl
    | .elem _, .mapping _ _ => isFalse (by intro h; cases h)
    | .elem _, .contract _ => isFalse (by intro h; cases h)
    | .elem _, .struct _ _ => isFalse (by intro h; cases h)
    | .elem _, .tuple _ => isFalse (by intro h; cases h)
    | .elem _, .array _ _ => isFalse (by intro h; cases h)
    | .elem _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .elem _, .bytes => isFalse (by intro h; cases h)
    | .elem _, .string => isFalse (by intro h; cases h)
    | .mapping _ _, .elem _ => isFalse (by intro h; cases h)
    | .mapping _ _, .contract _ => isFalse (by intro h; cases h)
    | .mapping _ _, .struct _ _ => isFalse (by intro h; cases h)
    | .mapping _ _, .tuple _ => isFalse (by intro h; cases h)
    | .mapping _ _, .array _ _ => isFalse (by intro h; cases h)
    | .mapping _ _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .mapping _ _, .bytes => isFalse (by intro h; cases h)
    | .mapping _ _, .string => isFalse (by intro h; cases h)
    | .contract _, .elem _ => isFalse (by intro h; cases h)
    | .contract _, .mapping _ _ => isFalse (by intro h; cases h)
    | .contract _, .struct _ _ => isFalse (by intro h; cases h)
    | .contract _, .tuple _ => isFalse (by intro h; cases h)
    | .contract _, .array _ _ => isFalse (by intro h; cases h)
    | .contract _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .contract _, .bytes => isFalse (by intro h; cases h)
    | .contract _, .string => isFalse (by intro h; cases h)
    | .struct _ _, .elem _ => isFalse (by intro h; cases h)
    | .struct _ _, .mapping _ _ => isFalse (by intro h; cases h)
    | .struct _ _, .contract _ => isFalse (by intro h; cases h)
    | .struct _ _, .tuple _ => isFalse (by intro h; cases h)
    | .struct _ _, .array _ _ => isFalse (by intro h; cases h)
    | .struct _ _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .struct _ _, .bytes => isFalse (by intro h; cases h)
    | .struct _ _, .string => isFalse (by intro h; cases h)
    | .tuple _, .elem _ => isFalse (by intro h; cases h)
    | .tuple _, .mapping _ _ => isFalse (by intro h; cases h)
    | .tuple _, .contract _ => isFalse (by intro h; cases h)
    | .tuple _, .struct _ _ => isFalse (by intro h; cases h)
    | .tuple _, .array _ _ => isFalse (by intro h; cases h)
    | .tuple _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .tuple _, .bytes => isFalse (by intro h; cases h)
    | .tuple _, .string => isFalse (by intro h; cases h)
    | .array _ _, .elem _ => isFalse (by intro h; cases h)
    | .array _ _, .mapping _ _ => isFalse (by intro h; cases h)
    | .array _ _, .contract _ => isFalse (by intro h; cases h)
    | .array _ _, .struct _ _ => isFalse (by intro h; cases h)
    | .array _ _, .tuple _ => isFalse (by intro h; cases h)
    | .array _ _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .array _ _, .bytes => isFalse (by intro h; cases h)
    | .array _ _, .string => isFalse (by intro h; cases h)
    | .dynamicArray _, .elem _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .mapping _ _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .contract _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .struct _ _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .tuple _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .array _ _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .bytes => isFalse (by intro h; cases h)
    | .dynamicArray _, .string => isFalse (by intro h; cases h)
    | .bytes, .elem _ => isFalse (by intro h; cases h)
    | .bytes, .mapping _ _ => isFalse (by intro h; cases h)
    | .bytes, .contract _ => isFalse (by intro h; cases h)
    | .bytes, .struct _ _ => isFalse (by intro h; cases h)
    | .bytes, .tuple _ => isFalse (by intro h; cases h)
    | .bytes, .array _ _ => isFalse (by intro h; cases h)
    | .bytes, .dynamicArray _ => isFalse (by intro h; cases h)
    | .bytes, .string => isFalse (by intro h; cases h)
    | .string, .elem _ => isFalse (by intro h; cases h)
    | .string, .mapping _ _ => isFalse (by intro h; cases h)
    | .string, .contract _ => isFalse (by intro h; cases h)
    | .string, .struct _ _ => isFalse (by intro h; cases h)
    | .string, .tuple _ => isFalse (by intro h; cases h)
    | .string, .array _ _ => isFalse (by intro h; cases h)
    | .string, .dynamicArray _ => isFalse (by intro h; cases h)
    | .string, .bytes => isFalse (by intro h; cases h)

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

deriving instance DecidableEq for EnvVar
deriving instance DecidableEq for UnaryOp
deriving instance DecidableEq for BinaryOp
deriving instance DecidableEq for VarOrigin

private def decEqOfIff {α : Type} {a b : α} (p : Prop) [Decidable p]
    (hp : p → a = b) (hn : a = b → p) : Decidable (a = b) :=
  match (inferInstance : Decidable p) with
  | isTrue h => isTrue (hp h)
  | isFalse h => isFalse (fun hab => h (hn hab))

set_option maxHeartbeats 2000000 in
mutual
  private def Expr.decEq (a b : Expr) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first
      | exact isFalse (by intro h; contradiction)
      | skip
    next x y =>
        exact decEqOfIff (x = y) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next x y =>
        exact decEqOfIff (x = y) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next x y =>
        exact decEqOfIff (x = y) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next x y =>
        letI : Decidable (x = y) := Expr.decEq x y
        exact decEqOfIff (x = y) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next tx x ty y =>
        letI : Decidable (x = y) := Expr.decEq x y
        exact decEqOfIff (tx = ty ∧ x = y)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)
    next nx fx ny fy =>
        letI : Decidable (fx = fy) := Expr.decEqNamedList fx fy
        exact decEqOfIff (nx = ny ∧ fx = fy)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)
    next xs ys =>
        exact match Expr.decEqList xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    next xs ys =>
        exact match Expr.decEqList xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    next x ix y iy =>
        letI : Decidable (x = y) := Expr.decEq x y
        exact decEqOfIff (x = y ∧ ix = iy)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)
    next bx sx ex byx sy ey =>
        letI : Decidable (bx = byx) := Expr.decEq bx byx
        letI : Decidable (sx = sy) := Expr.decEq sx sy
        letI : Decidable (ex = ey) := Expr.decEq ex ey
        exact decEqOfIff (bx = byx ∧ sx = sy ∧ ex = ey)
          (by rintro ⟨rfl, rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl, rfl⟩)
    next x y =>
        exact decEqOfIff (x = y) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next x y =>
        exact decEqOfIff (x = y) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next x fx y fy =>
        letI : Decidable (x = y) := Expr.decEq x y
        exact decEqOfIff (x = y ∧ fx = fy)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)
    next x y =>
        letI : Decidable (x = y) := StorageRef.decEq x y
        exact decEqOfIff (x = y) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next tx x ty y =>
        letI : Decidable (x = y) := Expr.decEq x y
        exact decEqOfIff (tx = ty ∧ x = y)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)
    next x tx y ty =>
        letI : Decidable (x = y) := Expr.decEq x y
        exact decEqOfIff (x = y ∧ tx = ty)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)
    next x y =>
        letI : Decidable (x = y) := Expr.decEq x y
        exact decEqOfIff (x = y) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next ox x oy y =>
        letI : Decidable (x = y) := Expr.decEq x y
        exact decEqOfIff (ox = oy ∧ x = y)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)
    next ox lx rx oy ly ry =>
        letI : Decidable (lx = ly) := Expr.decEq lx ly
        letI : Decidable (rx = ry) := Expr.decEq rx ry
        exact decEqOfIff (ox = oy ∧ lx = ly ∧ rx = ry)
          (by rintro ⟨rfl, rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl, rfl⟩)
    next bx ix byx iy =>
        letI : Decidable (bx = byx) := Expr.decEq bx byx
        letI : Decidable (ix = iy) := Expr.decEq ix iy
        exact decEqOfIff (bx = byx ∧ ix = iy)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)
    next cx tx fx cy ty fy =>
        letI : Decidable (cx = cy) := Expr.decEq cx cy
        letI : Decidable (tx = ty) := Expr.decEq tx ty
        letI : Decidable (fx = fy) := Expr.decEq fx fy
        exact decEqOfIff (cx = cy ∧ tx = ty ∧ fx = fy)
          (by rintro ⟨rfl, rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl, rfl⟩)
    next ox x oy y =>
        letI : Decidable (x = y) := StorageRef.decEq x y
        exact decEqOfIff (ox = oy ∧ x = y)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)
    next x y =>
        letI : Decidable (x = y) := Expr.decEq x y
        exact decEqOfIff (x = y) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next xs ys =>
        letI : Decidable (xs = ys) := Expr.decEqTypedList xs ys
        exact decEqOfIff (xs = ys) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next nx xs ny ys =>
        letI : Decidable (xs = ys) := Expr.decEqList xs ys
        exact decEqOfIff (nx = ny ∧ xs = ys)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)
    next tx x ty y =>
        letI : Decidable (x = y) := Expr.decEq x y
        exact decEqOfIff (tx = ty ∧ x = y)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)
    next x y =>
        letI : Decidable (x = y) := Expr.decEq x y
        exact decEqOfIff (x = y) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next ax lx ay ly =>
        letI : Decidable (ax = ay) := Expr.decEq ax ay
        letI : Decidable (lx = ly) := Expr.decEq lx ly
        exact decEqOfIff (ax = ay ∧ lx = ly)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)
    next x y =>
        letI : Decidable (x = y) := Expr.decEq x y
        exact decEqOfIff (x = y) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next x y =>
        letI : Decidable (x = y) := Expr.decEq x y
        exact decEqOfIff (x = y) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next x y =>
        letI : Decidable (x = y) := Expr.decEq x y
        exact decEqOfIff (x = y) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next nx bx ny bys =>
        exact decEqOfIff (nx = ny ∧ bx = bys)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)

  private def Expr.decEqList : (as bs : List Expr) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | a :: as, b :: bs =>
        letI : Decidable (a = b) := Expr.decEq a b
        letI : Decidable (as = bs) := Expr.decEqList as bs
        decEqOfIff (a = b ∧ as = bs)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)

  private def Expr.decEqNamedList : (as bs : List (Ident × Expr)) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | (an, ax) :: as, (bn, bx) :: bs =>
        letI : Decidable (an = bn) := String.decEq an bn
        letI : Decidable (ax = bx) := Expr.decEq ax bx
        letI : Decidable (as = bs) := Expr.decEqNamedList as bs
        decEqOfIff (an = bn ∧ ax = bx ∧ as = bs)
          (by rintro ⟨rfl, rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl, rfl⟩)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)

  private def Expr.decEqTypedList : (as bs : List (ABIType × Expr)) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | (aty, ax) :: as, (bty, bx) :: bs =>
        letI : Decidable (ax = bx) := Expr.decEq ax bx
        letI : Decidable (as = bs) := Expr.decEqTypedList as bs
        decEqOfIff (aty = bty ∧ ax = bx ∧ as = bs)
          (by rintro ⟨rfl, rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl, rfl⟩)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)

  private def StorageRefStep.decEq (a b : StorageRefStep) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first
      | exact isFalse (by intro h; contradiction)
      | skip
    next x y =>
        exact decEqOfIff (x = y) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next x y =>
        letI : Decidable (x = y) := Expr.decEq x y
        exact decEqOfIff (x = y) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next x y =>
        letI : Decidable (x = y) := Expr.decEq x y
        exact decEqOfIff (x = y) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
  private def StorageRef.decEq : (a b : StorageRef) → Decidable (a = b)
    | ⟨baseA, stepsA⟩, ⟨baseB, stepsB⟩ =>
        letI : Decidable (baseA = baseB) := String.decEq baseA baseB
        letI : Decidable (stepsA = stepsB) := StorageRefStep.decEqList stepsA stepsB
        decEqOfIff (baseA = baseB ∧ stepsA = stepsB)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)

  private def StorageRefStep.decEqList :
      (as bs : List StorageRefStep) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | a :: as, b :: bs =>
        letI : Decidable (a = b) := StorageRefStep.decEq a b
        letI : Decidable (as = bs) := StorageRefStep.decEqList as bs
        decEqOfIff (a = b ∧ as = bs)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq Expr := Expr.decEq
instance : DecidableEq StorageRefStep := StorageRefStep.decEq
instance : DecidableEq StorageRef := StorageRef.decEq

deriving instance DecidableEq for AssignRhs

mutual
  private def Stmt.decEq (a b : Stmt) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first
      | exact isFalse (by intro h; contradiction)
      | skip
    next nx tx ex ny ty ey =>
        letI : Decidable (ex = ey) := Expr.decEq ex ey
        exact decEqOfIff (nx = ny ∧ tx = ty ∧ ex = ey)
          (by rintro ⟨rfl, rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl, rfl⟩)
    next nx rx ny ry =>
        letI : Decidable (rx = ry) := StorageRef.decEq rx ry
        exact decEqOfIff (nx = ny ∧ rx = ry)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)
    next nx ny =>
        exact decEqOfIff (nx = ny) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next ox rx ex oy ry ey =>
        letI : Decidable (rx = ry) := StorageRef.decEq rx ry
        letI : Decidable (ex = ey) := Expr.decEq ex ey
        exact decEqOfIff (ox = oy ∧ rx = ry ∧ ex = ey)
          (by rintro ⟨rfl, rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl, rfl⟩)
    next ex ey =>
        letI : Decidable (ex = ey) := Expr.decEq ex ey
        exact decEqOfIff (ex = ey) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next cx bx cy bys =>
        letI : Decidable (cx = cy) := Expr.decEq cx cy
        letI : Decidable (bx = bys) := Stmt.decEqList bx bys
        exact decEqOfIff (cx = cy ∧ bx = bys)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)
    next ix cx px bx iy cy py bys =>
        letI : Decidable (ix = iy) := Stmt.decEqList ix iy
        letI : Decidable (cx = cy) := Expr.decEq cx cy
        letI : Decidable (px = py) := Stmt.decEqList px py
        letI : Decidable (bx = bys) := Stmt.decEqList bx bys
        exact decEqOfIff (ix = iy ∧ cx = cy ∧ px = py ∧ bx = bys)
          (by rintro ⟨rfl, rfl, rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl, rfl, rfl⟩)
    next cx tx fx cy ty fy =>
        letI : Decidable (cx = cy) := Expr.decEq cx cy
        letI : Decidable (tx = ty) := Stmt.decEqList tx ty
        letI : Decidable (fx = fy) := Stmt.decEqList fx fy
        exact decEqOfIff (cx = cy ∧ tx = ty ∧ fx = fy)
          (by rintro ⟨rfl, rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl, rfl⟩)
    next nx vx argsx retx saltx ny vy argsy rety salty =>
        letI : Decidable (vx = vy) := Expr.decEq vx vy
        exact decEqOfIff (nx = ny ∧ vx = vy ∧ argsx = argsy ∧ retx = rety ∧ saltx = salty)
          (by rintro ⟨rfl, rfl, rfl, rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    next nx xs rx ny ys ry =>
        exact decEqOfIff (nx = ny ∧ xs = ys ∧ rx = ry)
          (by rintro ⟨rfl, rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl, rfl⟩)
    next rx nx vx argsx retx permx ry ny vy argsy rety permy =>
        letI : Decidable (rx = ry) := Expr.decEq rx ry
        letI : Decidable (vx = vy) := Expr.decEq vx vy
        exact decEqOfIff
          (rx = ry ∧ nx = ny ∧ vx = vy ∧ argsx = argsy ∧ retx = rety ∧ permx = permy)
          (by rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    next tx vx cdx okx datax permx ty vy cdy oky datay permy =>
        letI : Decidable (tx = ty) := Expr.decEq tx ty
        letI : Decidable (vx = vy) := Expr.decEq vx vy
        letI : Decidable (cdx = cdy) := Expr.decEq cdx cdy
        exact decEqOfIff
          (tx = ty ∧ vx = vy ∧ cdx = cdy ∧ okx = oky ∧ datax = datay ∧ permx = permy)
          (by rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    next tx cdx okx datax ty cdy oky datay =>
        letI : Decidable (tx = ty) := Expr.decEq tx ty
        letI : Decidable (cdx = cdy) := Expr.decEq cdx cdy
        exact decEqOfIff (tx = ty ∧ cdx = cdy ∧ okx = oky ∧ datax = datay)
          (by rintro ⟨rfl, rfl, rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl, rfl, rfl⟩)
    next rx nx vx argsx retx sx errx fx permx ry ny vy argsy rety sy erry fy permy =>
        letI : Decidable (rx = ry) := Expr.decEq rx ry
        letI : Decidable (vx = vy) := Expr.decEq vx vy
        letI : Decidable (sx = sy) := Stmt.decEqList sx sy
        letI : Decidable (fx = fy) := Stmt.decEqList fx fy
        exact decEqOfIff
          (rx = ry ∧ nx = ny ∧ vx = vy ∧ argsx = argsy ∧ retx = rety ∧ sx = sy ∧
            errx = erry ∧ fx = fy ∧ permx = permy)
          (by rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
    next xs ys =>
        exact decEqOfIff (xs = ys) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next =>
        exact isTrue rfl
    next =>
        exact isTrue rfl
    next rx vx ry vy =>
        letI : Decidable (rx = ry) := StorageRef.decEq rx ry
        exact decEqOfIff (rx = ry ∧ vx = vy)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)
    next rx ry =>
        letI : Decidable (rx = ry) := StorageRef.decEq rx ry
        exact decEqOfIff (rx = ry) (by intro h; cases h; rfl) (by intro h; cases h; rfl)
    next rx ry =>
        letI : Decidable (rx = ry) := StorageRef.decEq rx ry
        exact decEqOfIff (rx = ry) (by intro h; cases h; rfl) (by intro h; cases h; rfl)

  private def Stmt.decEqList : (as bs : List Stmt) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | a :: as, b :: bs =>
        letI : Decidable (a = b) := Stmt.decEq a b
        letI : Decidable (as = bs) := Stmt.decEqList as bs
        decEqOfIff (a = b ∧ as = bs)
          (by rintro ⟨rfl, rfl⟩; rfl)
          (by intro h; cases h; exact ⟨rfl, rfl⟩)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq Stmt := Stmt.decEq

deriving instance DecidableEq for Param
deriving instance DecidableEq for StorageDecl
deriving instance DecidableEq for ConstructorDecl
deriving instance DecidableEq for StructDecl
deriving instance DecidableEq for FunctionDecl
deriving instance DecidableEq for TransitionDecl
deriving instance DecidableEq for ContractDecl

end Solm
