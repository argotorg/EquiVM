import Benchmarks.Morpho.MetaMorphoV1_1.DiffTarget

/-!
# Byte-sized immutable boundary regression

The runtime proof scaffold currently permits arbitrary words for the two uint8 immutables.
This regression exhibits the invalid DECIMALS_OFFSET = 256 valuation: the bytecode masks the
return word to zero, whereas the specification's return value cannot be encoded as uint8.
The value 255 is a successful boundary control. The final contract refinement quantifies only
over fitting immutable stores, so the proof valuation must enforce the declared byte bounds.

Run with `lake env lean --run Benchmarks/Morpho/MetaMorphoV1_1/ImmutableTypeRegression.lean`.
-/

open Solm Solm.DiffTest Ethereum

namespace Benchmarks.Morpho.MetaMorphoV1_1.ImmutableTypeRegression

theorem uint8_return_256_unencodable :
    ABI.encodeReturnValues? [.elem (.int (.uint ⟨8, by decide⟩))] [.int 256] = none := by
  simp [ABI.encodeReturnValues?, ABI.encodeABIValues?, ABI.abiTupleHeadSize?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, EVM.twoPow]

theorem word_256_mask_uint8 :
    UInt256.land (.ofNat 256) (.ofNat 255) = .ofNat 0 := by
  decide +kernel

def checkOffset (offset : Int) (expectedWord : Nat) (expectAgreement : Bool) : IO Unit := do
  let imms := deployedImmutables.insert "DECIMALS_OFFSET" (.int offset)
  let t : Target :=
    { diffTarget with
      immutables := imms
      runtime := immutableLayout.deployed metaMorphoV1_1Bytecode imms }
  let cd := (KEC "DECIMALS_OFFSET()".toUTF8).extract 0 4
  let run := runCase t
    { label := "uint8 immutable boundary"
      σ := t.world
      I := t.env t.runtime (EVM.address 0x2000) 0 cd true }
  IO.println s!"DECIMALS_OFFSET={offset}: {run.verdict.describe}"
  let .ok (.success _ output) := run.evmResult
    | throw (IO.userError "expected a successful EVM return")
  unless output == (UInt256.ofNat expectedWord).toByteArray do
    throw (IO.userError s!"unexpected EVM return: {Ethereum.toHex output}")
  IO.println s!"EVM return word: {expectedWord}"
  if expectAgreement then
    unless run.verdict.isSuccess do
      throw (IO.userError "valid uint8 boundary did not agree successfully")
  else
    match run.verdict with
    | .disagree why =>
        unless why == "the returned values do not ABI-encode at the declared return types" do
          throw (IO.userError s!"unexpected disagreement: {why}")
    | _ => throw (IO.userError "expected the out-of-range ABI return disagreement")

def check : IO Unit := do
  checkOffset 255 255 true
  checkOffset 256 0 false

end Benchmarks.Morpho.MetaMorphoV1_1.ImmutableTypeRegression

def main : IO Unit := Benchmarks.Morpho.MetaMorphoV1_1.ImmutableTypeRegression.check
