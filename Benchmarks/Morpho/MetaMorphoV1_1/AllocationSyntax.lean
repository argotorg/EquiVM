import Solm.Syntax

/-! Explicit memory-cursor accounting, expressed in the existing Solm language. -/

open Solm ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def cursorName : Ident := "__solcMemoryCursor"

def sizeName : Ident := "__solcAllocationSize"

def nextName : Ident := "__solcNextCursor"

def roundedSizeExpr : Expr :=
  .binary .mul
    (.binary .div
      (.binary .mod (.binary .add (.var sizeName) (.intLit 31))
        (.intLit (Int.ofNat (2 ^ 256))))
      (.intLit 32))
    (.intLit 32)

def nextCursorExpr : Expr :=
  .binary .mod (.binary .add (.var cursorName) roundedSizeExpr) (.intLit (Int.ofNat (2 ^ 256)))

def allocationCheckExpr : Expr :=
  .binary .and
    (.binary .lt (.var nextName) (.intLit (Int.ofNat (2 ^ 64))))
    (.binary .le (.var cursorName) (.var nextName))

/-- The compiler's allocation helper, with its memory cursor passed explicitly. -/
def allocateFunction : FunctionDecl :=
  { name := "__solcAllocateMemory"
    params :=
      [{ name := cursorName, ty := .elem (.int (.uint ⟨256, by decide⟩)) },
       { name := sizeName, ty := .elem (.int (.uint ⟨256, by decide⟩)) }]
    returnType := [.elem (.int (.uint ⟨256, by decide⟩))]
    body :=
      [.letDecl nextName none nextCursorExpr,
       .require allocationCheckExpr,
       .return [.var nextName]] }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
