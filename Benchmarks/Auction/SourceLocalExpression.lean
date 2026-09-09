import Benchmarks.Auction.Spec
import Reasoning.SolmBody

open Solm ABI Ethereum

namespace Auction

/-- LIBRARY CANDIDATE: a fragment whose evaluation depends only on the listed locals. -/
inductive SourceLocalExpression (names : List Ident) : Expr → Prop
  | intLit (n) : SourceLocalExpression names (.intLit n)
  | boolLit (b) : SourceLocalExpression names (.boolLit b)
  | bytesLit (b) : SourceLocalExpression names (.bytesLit b)
  | var {name} (h : name ∈ names) : SourceLocalExpression names (.var name)
  | length {name} (h : name ∈ names) :
      SourceLocalExpression names (.arrayLength .localVar { base := name })
  | binary {a b} (op) (ha : SourceLocalExpression names a)
      (hb : SourceLocalExpression names b) : SourceLocalExpression names (.binary op a b)
  | unary {a} (op) (ha : SourceLocalExpression names a) :
      SourceLocalExpression names (.unary op a)
  | decode {a} (ty) (ha : SourceLocalExpression names a) :
      SourceLocalExpression names (.abiDecode ty a)
  | slice {a b c} (ha : SourceLocalExpression names a)
      (hb : SourceLocalExpression names b) (hc : SourceLocalExpression names c) :
      SourceLocalExpression names (.bytesSlice a b c)

/-- LIBRARY CANDIDATE: adding unrelated locals preserves evaluation, including reverts. -/
theorem SourceLocalExpression.eval_eq {names : List Ident} {e : Expr}
    (he : SourceLocalExpression names e) (cfg : Config) (f₁ f₂ : Frame) (evm : EVM.State)
    (h : ∀ name ∈ names, f₁.locals.get? name = f₂.locals.get? name) :
    evalExpr? cfg f₁ evm e = evalExpr? cfg f₂ evm e := by
  induction he with
  | intLit | boolLit | bytesLit => simp only [evalExpr?]
  | var hn => simp only [evalExpr?, h _ hn]
  | length hn => simp only [evalExpr?, h _ hn, readLocalPath?]
  | binary op _ _ ih₁ ih₂ => cases op <;> simp only [evalExpr?, ih₁, ih₂]
  | unary _ _ ih | decode _ _ ih => simp only [evalExpr?, ih]
  | slice _ _ _ ih₁ ih₂ ih₃ => simp only [evalExpr?, ih₁, ih₂, ih₃]

end Auction
