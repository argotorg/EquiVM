import Benchmarks.CompoundIII.Comet.DiffTarget

/-!
Reproducer for the unbounded uint8 immutable values admitted by the generated proof scaffold.
Run with:
  lake env lean Benchmarks/CompoundIII/Comet/ScaffoldAudit.lean

The contract correctness goal only needs well-typed immutable stores. The original generated
valuation admitted decimals = 256 and numAssets = 256, making its runtime lemmas too strong.
The approved range constraints now exclude these values. Explicitly untyped stores below
preserve the counterexample and the adjacent valid boundary as regression evidence.
-/

namespace Benchmarks.CompoundIII.Comet.ScaffoldAudit

open Solm ABI Ethereum Ethereum.EVM Solm.DiffTest
open Benchmarks.CompoundIII.Comet Benchmarks.CompoundIII.Comet.Immutables

-- An explicitly untyped store keeps the original counterexample reproducible after the
-- valuation structure has been corrected to require the two uint8 bounds.
private def untypedStore (n : Nat) : Store :=
  ((initialImmutables contract).insert "decimals" (.int n)).insert "numAssets" (.int n)

private def target (n : Nat) : Target :=
  { fixtureTarget with
    contract := contract
    immutables := untypedStore n
    runtime := immutableLayout.deployed cometWithExtendedAssetListBytecode (untypedStore n)
    gas := 100000 }

private def run (index n : Nat) : Run :=
  let t := target n
  runCase t {
    label := "uint8 immutable range"
    σ := t.world
    I := t.env t.runtime (EVM.address 0x2000) 0
      (if index = 16 then selectorBytes 0x31 0x3c 0xe5 0x67
       else selectorBytes 0xa4 0x6f 0xe8 0x3b) true }

-- These small facts are kernel checked; the executable runs below independently check the
-- actual runtime and interpreter. Neither check uses the unfinished correctness theorems.
theorem uint8_rejects_256 :
    encodeReturnValues? [.elem (.int (.uint ⟨8, by decide⟩))] [.int 256] = none := by
  simp [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?, encodeABIValue?,
    encodeABIWord?, abiTupleHeadSize?, EVM.twoPow]

theorem uint8_mask_256 :
    UInt256.land (UInt256.ofNat 256) (UInt256.ofNat 255) = UInt256.ofNat 0 := by
  decide +kernel

theorem uint8_return_256_impossible (out : ByteArray) :
    ¬ returnEquiv out (some [.int 256]) [.elem (.int (.uint ⟨8, by decide⟩))] := by
  intro h
  cases h with
  | returned hvalues hencode =>
    cases hvalues
    rw [uint8_rejects_256] at hencode
    cases hencode
  | fallthrough hvalues _ _ => cases hvalues

#eval (show IO Unit from do
  for (name, index) in [("decimals()", 16), ("numAssets()", 47)] do
    for n in [255, 256] do
      let result := run index n
      let output := match result.evmResult with
        | .ok (.success _ out) => Ethereum.toHex out
        | other => describeEvm other
      IO.println s!"{name}, immutable={n}: {result.verdict.describe}; EVM output={output}")

#print axioms uint8_rejects_256
#print axioms uint8_mask_256
#print axioms uint8_return_256_impossible

end Benchmarks.CompoundIII.Comet.ScaffoldAudit
