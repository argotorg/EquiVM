import Benchmarks.Midnight.InternalCall

/-! Pure source and word computations for the tick exponential approximation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

abbrev tickSigned (x : Int) : Int := normalizeInt (.sint ⟨256, by decide⟩) x
abbrev tickUnsigned (x : Int) : Int := normalizeInt (.uint ⟨256, by decide⟩) x

def tickExpArgument (tick : Nat) : Int :=
  tickSigned (4987541511039073 * tickSigned (tickSigned (6744 / 2) - tickSigned tick))

def tickExpArgumentWord (tick : UInt256) : UInt256 :=
  UInt256.mul (UInt256.ofNat 4987541511039073) (UInt256.sub (UInt256.ofNat 3372) tick)

def wExpQ (x : Int) : Int := (tickSigned (x + 322611214989459870)).tdiv 693147180559945309
def wExpR (x : Int) : Int := tickSigned (x - tickSigned (wExpQ x * 693147180559945309))
def wExpSecond (x : Int) : Int := (tickSigned (wExpR x * wExpR x)).tdiv 2000000000000000000
def wExpThird (x : Int) : Int :=
  (tickSigned (wExpSecond x * wExpR x)).tdiv 3000000000000000000
def wExpMantissa (x : Int) : Int :=
  tickSigned (tickSigned (tickSigned (1000000000000000000 + wExpR x) + wExpSecond x) + wExpThird x)
def wExpPositiveValue (x : Int) : Int :=
  if 256 ≤ (tickUnsigned (wExpQ x)).toNat then 0
  else tickUnsigned (tickUnsigned (wExpMantissa x) *
    Int.ofNat (EVM.twoPow (tickUnsigned (wExpQ x)).toNat))

def wExpPositiveWord (x : UInt256) : UInt256 :=
  let q := UInt256.sdiv (x + UInt256.ofNat 322611214989459870) (UInt256.ofNat 693147180559945309)
  let r := UInt256.sub x (UInt256.mul q (UInt256.ofNat 693147180559945309))
  let second := UInt256.sdiv (UInt256.mul r r) (UInt256.ofNat 2000000000000000000)
  let third := UInt256.sdiv (UInt256.mul second r) (UInt256.ofNat 3000000000000000000)
  UInt256.shiftLeft (((r + second) + third) + UInt256.ofNat 1000000000000000000) q

def wExpValue (x : Int) : Int :=
  if x < 0 then 1000000000000000000000000000000000000 / wExpPositiveValue (tickSigned (0 - x))
  else wExpPositiveValue x

abbrev wExpFunction : FunctionDecl := contract.functions[24]!
def wExpPositiveBody : List Stmt :=
  match wExpFunction.body.head! with
  | .ite _ _ body => body
  | _ => []
def wExpNegativeBody : List Stmt :=
  match wExpFunction.body.head! with
  | .ite _ body _ => body
  | _ => []

theorem wExpFunction_body :
    wExpFunction.body = [.ite (.binary .lt (.var "x") (.intLit 0))
      wExpNegativeBody wExpPositiveBody] := rfl

end Benchmarks.Midnight
