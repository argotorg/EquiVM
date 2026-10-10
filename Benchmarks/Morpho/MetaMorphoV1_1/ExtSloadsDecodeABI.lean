import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsDecodeSource
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsCall
import Benchmarks.EAS.Attester.ReturnArrayABI

/-! Reuse the general bytes32-array decoder facts and derive bounds from the actual call. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- LIBRARY CANDIDATE: a raw call with bounded input has a gas-derived return-size bound.
theorem callViaEVM_output_bound {evm evm' : State} {target : AccountAddress}
    {value : Int} {input out : ByteArray} {ok perm : Bool}
    (hcall : callViaEVM evm target value input (ok, evm', out) perm)
    (hinput : input.size ≤ Ethereum.EVM.maxReturnDataSizeByGas) :
    out.size < 2 ^ 138 := by
  cases hcall with
  | callMade _ htheta _ _ _ =>
      obtain ⟨gas, substate, htheta⟩ := htheta
      exact Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        htheta hinput
  | callNotMade _ _ _ => decide

theorem extSloadsReturnSize {evm evm' : State} {target : AccountAddress}
    {slot : UInt256} {out : ByteArray} {ok : Bool}
    (hcall : typedCallViaEVM config evm target "extSloads" 0
      [.array [wordBytes32Value slot]] (ok, evm', out) false) :
    out.size < 2 ^ 138 := by
  obtain ⟨input, hencode, hcall⟩ := hcall
  rw [extSloadsEncode, Option.some.injEq] at hencode
  subst input
  exact callViaEVM_output_bound hcall (by rw [extSloadsCalldata_size]; decide +kernel)

abbrev extSloadsReturnChecks := Benchmarks.EAS.Attester.ReturnArrayChecks
abbrev extSloadsReturnValues := Benchmarks.EAS.Attester.returnArrayValues
abbrev extSloadsReturnOffset := Benchmarks.EAS.Attester.returnArrayOffset
abbrev extSloadsReturnCount := Benchmarks.EAS.Attester.returnArrayCount

theorem extSloadsDecodeFacts {out : ByteArray} {value : Value}
    (hout : out.size < 2 ^ 138)
    (hdecode : ABI.decodeReturnValueWithMode? config.abiDecodeMode
      (.dynamicArray (.elem (.bytes ⟨31, by decide⟩))) out = some value) :
    ∃ values, value = .array values ∧ extSloadsReturnChecks out ∧
      values.length = extSloadsReturnCount out ∧ 32 + 32 * values.length < UInt256.size := by
  obtain ⟨values, ending, hvalue, _, hcheck, hlength⟩ :=
    Benchmarks.EAS.Attester.returnArrayDecode_some_facts (by omega) hdecode
  refine ⟨values, hvalue, hcheck, hlength, ?_⟩
  have hcount := hcheck.length
  change extSloadsReturnCount out ≤ 18446744073709551615 at hcount
  rw [hlength]
  change 32 + 32 * extSloadsReturnCount out < 2 ^ 256
  omega

/-- The complete source helper is executable for every actual singleton call result.
The allocation and decoding cases are conclusions, not assumptions on the environment. -/
theorem extSloadsBodyCases {frame : Frame} {evm evm' : State}
    (ptr : UInt256) (morpho : AccountAddress) (slot : UInt256) (ok : Bool) (out : ByteArray)
    (hlookup : lookupCallable? frame.contract allocateFunction.name =
      some allocateFunction.toCallable)
    (hcall : typedCallViaEVM config evm morpho "extSloads" 0
      [.array [wordBytes32Value slot]] (ok, evm', out) false) :
    ExecFuncBody config (extSloadsFrame frame ptr morpho [wordBytes32Value slot]) evm
        extSloadsFunction.body .reverted ∨
      ∃ values, ok = true ∧ extSloadsReturnChecks out ∧
        allocationFits ptr (UInt256.ofNat out.size) ∧
        allocationFits (nextCursor ptr (UInt256.ofNat out.size)) (decodedArraySize values) ∧
        ExecFuncBody config (extSloadsFrame frame ptr morpho [wordBytes32Value slot]) evm
          extSloadsFunction.body
          (.returned (extSloadsResultFrame frame ptr morpho [wordBytes32Value slot] out values)
            evm' (some [.array values, uint256Value (extSloadsFinalCursor ptr out values)])) := by
  have hout := extSloadsReturnSize hcall
  have hword : out.size < UInt256.size := by change _ < 2 ^ 256; omega
  cases ok with
  | false => exact .inl (extSloadsBodyCallReverts ptr morpho _ out hcall)
  | true =>
      by_cases hfit : allocationFits ptr (UInt256.ofNat out.size)
      · cases hdecode : ABI.decodeReturnValueWithMode? config.abiDecodeMode
            (.dynamicArray (.elem (.bytes ⟨31, by decide⟩))) out with
        | none =>
            exact .inl (extSloadsBodyDecodeReverts ptr morpho _ out hlookup hcall hword
              hfit hdecode)
        | some value =>
            obtain ⟨values, rfl, hcheck, _, hsize⟩ := extSloadsDecodeFacts hout hdecode
            by_cases harray : allocationFits (nextCursor ptr (UInt256.ofNat out.size))
                (decodedArraySize values)
            · exact .inr ⟨values, rfl, hcheck, hfit, harray,
                extSloadsBodyReturns ptr morpho _ values out hlookup hcall hword hfit
                  hdecode hsize harray⟩
            · exact .inl (extSloadsBodyArrayReverts ptr morpho _ values out hlookup hcall
                hword hfit hdecode hsize harray)
      · exact .inl (extSloadsBodyBufferReverts ptr morpho _ out hlookup hcall hword hfit)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
