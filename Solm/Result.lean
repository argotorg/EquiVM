namespace Solm

/-- Solm evaluation errors. These indicate an ill-formed program or configuration. -/
inductive EvalError where
  | unboundVariable
  | typeError
  | storageError
  deriving DecidableEq, Repr, Inhabited

/-- A computation either returns a value, reverts like the modeled language, or gets stuck on an
    ill-formed program/configuration.  This lives below both value and storage semantics so storage
    backends can expose the same result type as the evaluator. -/
inductive EvalResult (α : Type) where
  | ok : α -> EvalResult α
  | revert : EvalResult α
  | error : EvalError -> EvalResult α
  deriving Repr, DecidableEq

namespace EvalResult

@[inline] def bind : EvalResult α -> (α -> EvalResult β) -> EvalResult β
  | .ok a,    f => f a
  | .revert,  _ => .revert
  | .error e, _ => .error e

instance : Monad EvalResult where
  pure := .ok
  bind := bind

/-- Lift an `Option`, mapping `none` to the model-level error `e`. -/
@[inline] def ofOption (e : EvalError) : Option α -> EvalResult α
  | some a => .ok a
  | none   => .error e

/-- Sequence results, short-circuiting on the first revert/error. -/
def seqList : List (EvalResult α) -> EvalResult (List α)
  | [] => .ok []
  | x :: xs => do
      let a <- x
      let as <- seqList xs
      .ok (a :: as)

end EvalResult
end Solm
