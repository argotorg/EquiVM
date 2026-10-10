import Benchmarks.CompoundIII.Comet.AbsorbStaticDecodeWitness

open Solm ABI Solm.DiffTest Ethereum Ethereum.EVM
open Benchmarks.CompoundIII.Comet Benchmarks.CompoundIII.Comet.AbsorbStaticDecodeWitness

namespace Benchmarks.CompoundIII.Comet.Solc0815Regression

def target : Target := { zeroTarget with config := config }

def absorbData (absorber : Nat) (accounts : List Nat) : ByteArray :=
  cometWithExtendedAssetListSelBytes 38 ++ wordBytes absorber ++ wordBytes 64 ++
    wordBytes accounts.length ++ accounts.foldl (fun bytes n ↦ bytes ++ wordBytes n) ByteArray.empty

def cases : List (String × ByteArray × Bool × Nat) :=
  [ ("dirty element before static accrual", dirtyData, false, 1),
    ("dirty element after writable accrual", dirtyData, true, 1),
    ("dirty element with no accrual", dirtyData, false, 0),
    ("dirty scalar absorber", absorbData (2^160) [0], false, 1),
    ("truncated array", dirtyData.extract 0 131, false, 1),
    ("offset exceeds uint64", cometWithExtendedAssetListSelBytes 38 ++ wordBytes 0 ++
      wordBytes (2^64) ++ wordBytes 0, false, 1),
    ("length exceeds uint64", cometWithExtendedAssetListSelBytes 38 ++ wordBytes 0 ++
      wordBytes 64 ++ wordBytes (2^64), false, 1),
    ("canonical address", absorbData 0 [0], true, 0),
    ("empty array", absorbData 0 [], true, 0),
    ("empty array with static accrual", absorbData 0 [], false, 1) ]

def verdicts : List (String × Verdict) :=
  cases.map fun (label, data, perm, timestamp) ↦
    let c : Case :=
      { label := label
        σ := target.world
        I := target.env target.runtime (EVM.address 0x2000) 0 data perm timestamp }
    (label, (runCase target c).verdict)

theorem cases_agree : verdicts.all (fun entry ↦ entry.2.isAgree) = true := by native_decide

theorem dirty_calldata_decodes :
    (decodeCalldataWithMode .solc0815 (absorbTransition.params.map Param.name)
      (transitionSignature absorbTransition).paramTypes dirtyData).isSome = true := by native_decide

-- The same word still fails when used as a scalar or in returned memory data.
#guard decodeABIWord? (.elem .address) (.ofNat (2^160)) .solc0815 = none
#guard decodeReturnValueWithMode? .solc0815 (.dynamicArray (.elem .address))
  (wordBytes 32 ++ wordBytes 1 ++ wordBytes (2^160)) = none
#guard decodeReturnValueWithMode? .solc0815 (.dynamicArray (.elem .address))
  (wordBytes 32 ++ wordBytes 1 ++ wordBytes 7) =
    some (.array [.address (AccountAddress.ofNat 7)])
#guard evalIndex? (.array [Solc0815.addressArrayWord (2^160)]) (.int 0) = .revert
#guard evalIndex? (.array [Solc0815.addressArrayWord 7]) (.int 0) =
  .ok (.address (AccountAddress.ofNat 7))

#eval verdicts.map fun (label, verdict) ↦ (label, verdict.describe)

end Benchmarks.CompoundIII.Comet.Solc0815Regression
