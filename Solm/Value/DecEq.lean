import Solm.Value.Basic

/-!
`DecidableEq Value`.

`Value` carries nested `List` payloads (`struct`, `array`, `tuple`), a shape Lean's
`deriving DecidableEq` handler cannot process, so the instance is a hand-written
structural `decEq`. Kept out of `Solm.Value.Basic` so that file reads as the type
definition alone.
-/

namespace Solm

mutual
  private def Value.decEq : (a b : Value) -> Decidable (a = b)
    | .int x, .int y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .bool x, .bool y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .address x, .address y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .struct tag fields, .struct tag' fields' =>
        match (inferInstance : Decidable (tag = tag')), Value.decEqNamedList fields fields' with
        | isTrue htag, isTrue hfields => isTrue (by subst tag'; cases hfields; rfl)
        | isFalse htag, _ => isFalse (by intro h'; cases h'; exact htag rfl)
        | _, isFalse hfields => isFalse (by intro h'; cases h'; exact hfields rfl)
    | .array xs, .array ys =>
        match Value.decEqList xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .tuple xs, .tuple ys =>
        match Value.decEqList xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .fixedBytes n bs, .fixedBytes m bs' =>
        match (inferInstance : Decidable (n = m)), (inferInstance : Decidable (bs = bs')) with
        | isTrue hn, isTrue hbytes => isTrue (by cases hn; cases hbytes; rfl)
        | isFalse hn, _ => isFalse (by intro h; cases h; exact hn rfl)
        | _, isFalse hbytes => isFalse (by intro h; cases h; exact hbytes rfl)
    | .unit, .unit => isTrue rfl
    | .bytes x, .bytes y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .storageRef rx tx, .storageRef ry ty =>
        match (inferInstance : Decidable (rx = ry)), (inferInstance : Decidable (tx = ty)) with
        | isTrue hr, isTrue ht => isTrue (by cases hr; cases ht; rfl)
        | isFalse hr, _ => isFalse (by intro h; cases h; exact hr rfl)
        | _, isFalse ht => isFalse (by intro h; cases h; exact ht rfl)
    | .int _, .bool _ => isFalse (by intro h; cases h)
    | .int _, .address _ => isFalse (by intro h; cases h)
    | .int _, .struct _ _ => isFalse (by intro h; cases h)
    | .int _, .array _ => isFalse (by intro h; cases h)
    | .int _, .tuple _ => isFalse (by intro h; cases h)
    | .int _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .int _, .unit => isFalse (by intro h; cases h)
    | .bool _, .int _ => isFalse (by intro h; cases h)
    | .bool _, .address _ => isFalse (by intro h; cases h)
    | .bool _, .struct _ _ => isFalse (by intro h; cases h)
    | .bool _, .array _ => isFalse (by intro h; cases h)
    | .bool _, .tuple _ => isFalse (by intro h; cases h)
    | .bool _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .bool _, .unit => isFalse (by intro h; cases h)
    | .address _, .int _ => isFalse (by intro h; cases h)
    | .address _, .bool _ => isFalse (by intro h; cases h)
    | .address _, .struct _ _ => isFalse (by intro h; cases h)
    | .address _, .array _ => isFalse (by intro h; cases h)
    | .address _, .tuple _ => isFalse (by intro h; cases h)
    | .address _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .address _, .unit => isFalse (by intro h; cases h)
    | .struct _ _, .int _ => isFalse (by intro h; cases h)
    | .struct _ _, .bool _ => isFalse (by intro h; cases h)
    | .struct _ _, .address _ => isFalse (by intro h; cases h)
    | .struct _ _, .array _ => isFalse (by intro h; cases h)
    | .struct _ _, .tuple _ => isFalse (by intro h; cases h)
    | .struct _ _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .struct _ _, .unit => isFalse (by intro h; cases h)
    | .array _, .int _ => isFalse (by intro h; cases h)
    | .array _, .bool _ => isFalse (by intro h; cases h)
    | .array _, .address _ => isFalse (by intro h; cases h)
    | .array _, .struct _ _ => isFalse (by intro h; cases h)
    | .array _, .tuple _ => isFalse (by intro h; cases h)
    | .array _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .array _, .unit => isFalse (by intro h; cases h)
    | .tuple _, .int _ => isFalse (by intro h; cases h)
    | .tuple _, .bool _ => isFalse (by intro h; cases h)
    | .tuple _, .address _ => isFalse (by intro h; cases h)
    | .tuple _, .struct _ _ => isFalse (by intro h; cases h)
    | .tuple _, .array _ => isFalse (by intro h; cases h)
    | .tuple _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .tuple _, .unit => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .int _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .bool _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .address _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .struct _ _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .array _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .tuple _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .unit => isFalse (by intro h; cases h)
    | .unit, .int _ => isFalse (by intro h; cases h)
    | .unit, .bool _ => isFalse (by intro h; cases h)
    | .unit, .address _ => isFalse (by intro h; cases h)
    | .unit, .struct _ _ => isFalse (by intro h; cases h)
    | .unit, .array _ => isFalse (by intro h; cases h)
    | .unit, .tuple _ => isFalse (by intro h; cases h)
    | .unit, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .int _, .bytes _ => isFalse (by intro h; cases h)
    | .bool _, .bytes _ => isFalse (by intro h; cases h)
    | .address _, .bytes _ => isFalse (by intro h; cases h)
    | .struct _ _, .bytes _ => isFalse (by intro h; cases h)
    | .array _, .bytes _ => isFalse (by intro h; cases h)
    | .tuple _, .bytes _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .bytes _ => isFalse (by intro h; cases h)
    | .unit, .bytes _ => isFalse (by intro h; cases h)
    | .bytes _, .int _ => isFalse (by intro h; cases h)
    | .bytes _, .bool _ => isFalse (by intro h; cases h)
    | .bytes _, .address _ => isFalse (by intro h; cases h)
    | .bytes _, .struct _ _ => isFalse (by intro h; cases h)
    | .bytes _, .array _ => isFalse (by intro h; cases h)
    | .bytes _, .tuple _ => isFalse (by intro h; cases h)
    | .bytes _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .bytes _, .unit => isFalse (by intro h; cases h)
    | .storageRef _ _, .int _ => isFalse (by intro h; cases h)
    | .int _, .storageRef _ _ => isFalse (by intro h; cases h)
    | .storageRef _ _, .bool _ => isFalse (by intro h; cases h)
    | .bool _, .storageRef _ _ => isFalse (by intro h; cases h)
    | .storageRef _ _, .address _ => isFalse (by intro h; cases h)
    | .address _, .storageRef _ _ => isFalse (by intro h; cases h)
    | .storageRef _ _, .struct _ _ => isFalse (by intro h; cases h)
    | .struct _ _, .storageRef _ _ => isFalse (by intro h; cases h)
    | .storageRef _ _, .array _ => isFalse (by intro h; cases h)
    | .array _, .storageRef _ _ => isFalse (by intro h; cases h)
    | .storageRef _ _, .tuple _ => isFalse (by intro h; cases h)
    | .tuple _, .storageRef _ _ => isFalse (by intro h; cases h)
    | .storageRef _ _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .storageRef _ _ => isFalse (by intro h; cases h)
    | .storageRef _ _, .bytes _ => isFalse (by intro h; cases h)
    | .bytes _, .storageRef _ _ => isFalse (by intro h; cases h)
    | .storageRef _ _, .unit => isFalse (by intro h; cases h)
    | .unit, .storageRef _ _ => isFalse (by intro h; cases h)

  private def Value.decEqList : (as bs : List Value) -> Decidable (as = bs)
    | [], [] => isTrue rfl
    | a :: as, b :: bs =>
        match Value.decEq a b, Value.decEqList as bs with
        | isTrue ha, isTrue hs => isTrue (by cases ha; cases hs; rfl)
        | isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, isFalse hs => isFalse (by intro h; cases h; exact hs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)

  private def Value.decEqNamedList :
      (as bs : List (Ident × Value)) -> Decidable (as = bs)
    | [], [] => isTrue rfl
    | (name, value) :: as, (name', value') :: bs =>
        match (inferInstance : Decidable (name = name')),
            Value.decEq value value', Value.decEqNamedList as bs with
        | isTrue hname, isTrue hvalue, isTrue hs =>
            isTrue (by subst name'; cases hvalue; cases hs; rfl)
        | isFalse hname, _, _ =>
            isFalse (by intro h; cases h; exact hname rfl)
        | _, isFalse hvalue, _ =>
            isFalse (by intro h; cases h; exact hvalue rfl)
        | _, _, isFalse hs =>
            isFalse (by intro h; cases h; exact hs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq Value :=
  Value.decEq

end Solm
