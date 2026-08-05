import Ethereum.Semantics

/-!
# Pinned trusted ModExp model

The parser, functional model, fork-dependent native gas schedule, and runner in this file mirror
`EvmSemantics/EVM/Precompile.lean` at evm-semantics commit
`601183cb2d959748243d59093c144652a6f10716`, specifically its
`bytesToNatPadded`, `modPowAux`, `modPow`, `natToBytes`, and `runModexp` definitions.

The byte conversion helpers are adapted from `EvmSemantics/Data/Bytes.lean` at the same commit,
specifically `bytesToBigEndianNat`, `intToBytesAux`, and `natToBytesPadded`.

They are copied rather than imported because that revision of evm-semantics uses Lean 4.31 while
EquiVM is currently pinned to Lean 4.29.  The only substitutions in the computational definitions
through `runModexp` are replacing upstream-qualified helper names such as
`Data.Bytes.natToBytesPadded` and `MachineState.readPadded` by their source-identical local copies.
In particular, these definitions are the trusted specification and must not be adjusted to fit the
replacement bytecode.  `output` below is the sole additional proof-facing projection; it is
connected to the successful branch of `runModexp` by `runModexp_eq_success_output`.
-/

namespace Modexp.Model

/-- Decode a big-endian byte array as a natural number. Verbatim definition from
evm-semantics `Data/Bytes.lean`, commit `601183cb…`. -/
def bytesToBigEndianNat (bs : ByteArray) : Nat :=
  bs.toList.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Read exactly `n` bytes, zero-padding past the input. Verbatim definition from
evm-semantics `Machine/MachineState.lean`, commit `601183cb…`. -/
def readPadded (bs : ByteArray) (start n : Nat) : ByteArray :=
  let start' := Nat.min start bs.size
  let avail := bs.size - start'
  let take := Nat.min avail n
  let pad := n - take
  let prefix1 := bs.extract start' (start' + take)
  prefix1 ++ ByteArray.mk (Array.replicate pad 0)

/-- Read a big-endian field, treating missing trailing calldata bytes as zero. Source:
evm-semantics `EVM/Precompile.lean`, commit `601183cb…`. -/
def bytesToNatPadded (bs : ByteArray) (offset width : Nat) : Nat :=
  bytesToBigEndianNat (readPadded bs offset width)

/-- Square-and-multiply kernel. Source: evm-semantics `EVM/Precompile.lean`, commit
`601183cb…`. -/
def modPowAux (base acc modulus e : Nat) : Nat :=
  if h : e = 0 then acc
  else
    let acc' := if e % 2 = 1 then (acc * base) % modulus else acc
    modPowAux ((base * base) % modulus) acc' modulus (e / 2)
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- `b^e mod m`, with the EIP-198 conventions for moduli zero and one. Source:
evm-semantics `EVM/Precompile.lean`, commit `601183cb…`. -/
def modPow (b e modulus : Nat) : Nat :=
  if modulus = 0 then 0
  else if modulus = 1 then 0
  else modPowAux (b % modulus) 1 modulus e

/-- Inner loop for a minimal big-endian encoding. Source: evm-semantics `Data/Bytes.lean`,
commit `601183cb…`. -/
def intToBytesAux (k : Nat) (acc : List UInt8) : List UInt8 :=
  if h : k = 0 then acc
  else intToBytesAux (k / 256) (UInt8.ofNat (k % 256) :: acc)
termination_by k
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- Encode `n` as exactly `width` big-endian bytes, truncating high bytes. Source:
evm-semantics `Data/Bytes.lean`, commit `601183cb…`. -/
def natToBytesPadded (n width : Nat) : ByteArray := Id.run do
  let mut bs : Array UInt8 := Array.mkEmpty width
  let mut k := n
  let mut le : Array UInt8 := Array.mkEmpty width
  for _ in [0:width] do
    le := le.push (UInt8.ofNat (k % 256))
    k := k / 256
  for i in [0:width] do
    bs := bs.push le[width - 1 - i]!
  return ByteArray.mk bs

/-- Name used by the trusted precompile model. Verbatim wrapper from evm-semantics
`EVM/Precompile.lean`, commit `601183cb…`. -/
@[inline] def natToBytes (n width : Nat) : ByteArray :=
  natToBytesPadded n width

/-! The following result, fork, gas, validity, and runner definitions are copied from
`EvmSemantics/EVM/Precompile.lean` and `EvmSemantics/EVM/Fork.lean` at commit `601183cb…`.
Keeping them here makes the boundary between the trusted precompile semantics and the bytecode's
independently proved instruction gas explicit. -/

inductive Result where
  | success (output : ByteArray) (gasUsed : Nat)
  | outOfGas
  deriving Inhabited

inductive Fork where
  | Frontier | Homestead | TangerineWhistle | SpuriousDragon
  | Byzantium | Constantinople | Petersburg
  | Istanbul | MuirGlacier | Berlin | London
  | ArrowGlacier | GrayGlacier | Paris | Shanghai | Cancun
  | Prague | Osaka
  deriving DecidableEq, Repr, Inhabited

namespace Fork

def toOrd : Fork → Nat
  | .Frontier => 0
  | .Homestead => 1
  | .TangerineWhistle => 2
  | .SpuriousDragon => 3
  | .Byzantium => 4
  | .Constantinople => 5
  | .Petersburg => 6
  | .Istanbul => 7
  | .MuirGlacier => 8
  | .Berlin => 9
  | .London => 10
  | .ArrowGlacier => 11
  | .GrayGlacier => 12
  | .Paris => 13
  | .Shanghai => 14
  | .Cancun => 15
  | .Prague => 16
  | .Osaka => 17

instance : LE Fork := ⟨fun a b => a.toOrd ≤ b.toOrd⟩
instance : LT Fork := ⟨fun a b => a.toOrd < b.toOrd⟩
instance (a b : Fork) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toOrd ≤ b.toOrd))
instance (a b : Fork) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toOrd < b.toOrd))

end Fork

def multComplexity (x : Nat) : Nat :=
  if x ≤ 64 then x * x
  else if x ≤ 1024 then x * x / 4 + 96 * x - 3072
  else x * x / 16 + 480 * x - 199680

def adjustedExpLen (coeff esize expHead : Nat) : Nat :=
  if esize ≤ 32 then
    if expHead = 0 then 0 else Nat.log2 expHead
  else
    let base := coeff * (esize - 32)
    if expHead = 0 then base else base + Nat.log2 expHead

def modexpGasByzantium (bsize esize msize expHead : Nat) : Nat :=
  let adj := Nat.max (adjustedExpLen 8 esize expHead) 1
  multComplexity (Nat.max bsize msize) * adj / 20

def modexpGasBerlin (bsize esize msize expHead : Nat) : Nat :=
  let words := (Nat.max bsize msize + 7) / 8
  let adj := Nat.max (adjustedExpLen 8 esize expHead) 1
  Nat.max 200 (words * words * adj / 3)

def modexpGasOsaka (bsize esize msize expHead : Nat) : Nat :=
  let maxLen := Nat.max bsize msize
  let words := (maxLen + 7) / 8
  let mult := if maxLen ≤ 32 then 16 else 2 * words * words
  let iter := Nat.max (adjustedExpLen 16 esize expHead) 1
  Nat.max 500 (mult * iter)

@[inline] def modexpOsakaInputTooLarge (bsize esize msize : Nat) : Bool :=
  bsize > 1024 ∨ esize > 1024 ∨ msize > 1024

@[inline] def modexpGas (fork : Fork) (bsize esize msize expHead : Nat) : Nat :=
  if fork ≥ .Osaka then modexpGasOsaka bsize esize msize expHead
  else if fork ≥ .Berlin then modexpGasBerlin bsize esize msize expHead
  else modexpGasByzantium bsize esize msize expHead

def runModexp (fork : Fork) (input : ByteArray) (childGas : Nat) : Result :=
  let bsize := bytesToNatPadded input 0 32
  let esize := bytesToNatPadded input 32 32
  let msize := bytesToNatPadded input 64 32
  let expHead :=
    let n := Nat.min esize 32
    bytesToNatPadded input (96 + bsize) n
  if fork ≥ .Osaka ∧ modexpOsakaInputTooLarge bsize esize msize then .outOfGas
  else
    let cost := modexpGas fork bsize esize msize expHead
    if cost ≤ childGas then
      if msize = 0 then .success ByteArray.empty cost
      else
        let b := bytesToNatPadded input 96 bsize
        let e := bytesToNatPadded input (96 + bsize) esize
        let m := bytesToNatPadded input (96 + bsize + esize) msize
        let r := modPow b e m
        .success (natToBytes r msize) cost
    else .outOfGas

/-- The caller-visible output expression copied from the successful branch of evm-semantics
`runModexp`, commit `601183cb…`.  This definition is not a replacement for `runModexp`: it is the
pure value used by bytecode proofs, and the theorem below records precisely when the trusted runner
returns it. -/
def output (input : ByteArray) : ByteArray :=
  let bsize := bytesToNatPadded input 0 32
  let esize := bytesToNatPadded input 32 32
  let msize := bytesToNatPadded input 64 32
  if msize = 0 then ByteArray.empty
  else
    let b := bytesToNatPadded input 96 bsize
    let e := bytesToNatPadded input (96 + bsize) esize
    let m := bytesToNatPadded input (96 + bsize + esize) msize
    let r := modPow b e m
    natToBytes r msize

/-- The proof-facing pure value is exactly the result of the trusted precompile runner whenever
the runner passes its fork-size and native-gas checks.  The `cost` here is the native precompile
charge; it is intentionally distinct from the replacement bytecode's instruction gas. -/
theorem runModexp_eq_success_output (fork : Fork) (input : ByteArray) (childGas : Nat)
    (hsize : ¬ (fork ≥ .Osaka ∧
      modexpOsakaInputTooLarge
        (bytesToNatPadded input 0 32)
        (bytesToNatPadded input 32 32)
        (bytesToNatPadded input 64 32)))
    (hgas : modexpGas fork
      (bytesToNatPadded input 0 32)
      (bytesToNatPadded input 32 32)
      (bytesToNatPadded input 64 32)
      (bytesToNatPadded input (96 + bytesToNatPadded input 0 32)
        (Nat.min (bytesToNatPadded input 32 32) 32)) ≤ childGas) :
    runModexp fork input childGas =
      .success (output input)
        (modexpGas fork
          (bytesToNatPadded input 0 32)
          (bytesToNatPadded input 32 32)
          (bytesToNatPadded input 64 32)
          (bytesToNatPadded input (96 + bytesToNatPadded input 0 32)
            (Nat.min (bytesToNatPadded input 32 32) 32))) := by
  unfold runModexp output
  simp only [hsize, hgas, ↓reduceIte]
  split <;> rfl

end Modexp.Model
