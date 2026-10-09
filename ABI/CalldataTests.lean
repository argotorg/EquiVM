import ABI.Decode
import ABI.Encode

/-! Boundary regressions for solc's direct calldata tails versus eager memory decoding.
    The independent compiler/EVM checks live in `Benchmarks/EAS/EAS/AbiCheck.lean`. -/

namespace ABI.CalldataTests

open ABI.Solc08Calldata

private def word (n : Nat) : ByteArray := (EVM.Word.ofNat n).toByteArray
private def words (ns : List Nat) : ByteArray := ns.foldl (fun b n => b ++ word n) .empty
private def call (ns : List Nat) : ByteArray := ⟨#[0, 0, 0, 0]⟩ ++ words ns
private def u256 : ABIType := .elem (.int (.uint ⟨256, by decide⟩))
private def row : ABIType := .tuple [u256, .dynamicArray u256]
private def params : List ABIType := [.dynamicArray row]
private def direct : DecodeMode := .solc08Calldata [(0, [{ materialize := [] }])]
private def copyRow : DecodeMode := .solc08Calldata [(0, [{ materialize := [[.element]] }])]
private def copyData : DecodeMode :=
  .solc08Calldata [(0, [{ materialize := [[.element, .field 1]] }])]
private def getArg (mode : DecodeMode) (ns : List Nat) : Option Solm.Value := do
  let store ← decodeCalldata ["r"] params (call ns) mode
  store.get? "r"
private def emptyRow : Solm.Value := .array [.tuple [.int 0, .array []]]

-- Canonical input and noncanonical, in-bounds aliases are distinct cases.
#guard getArg direct [32, 1, 32, 0, 64, 0] = some emptyRow
#guard getArg copyRow [32, 1, 32, 0, 64, 0] = some emptyRow
#guard getArg direct [32, 1, 64, 0, 0, 64, 0] = some emptyRow
#guard getArg direct [32, 1, 32, 0, 0] = some emptyRow
#guard getArg direct [32, 1, 64, 0, 0, 2^256 - 32] = some emptyRow
#guard getArg copyData [32, 1, 64, 0, 0, 2^256 - 32] = some emptyRow
#guard getArg copyRow [32, 1, 64, 0, 0, 2^256 - 32] = none
#guard getArg (.solc08Calldata []) [32, 1, 64, 0, 0, 2^256 - 32] = none
#guard getArg .modern [32, 1, 64, 0, 0, 2^256 - 32] = none

-- These unsigned, top-level and length checks must not be relaxed by a calldata plan.
#guard getArg direct [2^256 - 32, 1, 64, 0, 0, 0] = none
#guard getArg direct [32, 1, 64, 0, 0, 256] = none
#guard getArg direct [32, 1, 64, 0, 0, 64] = none
#guard getArg direct [32, 1, 64, 0, 0, 64, 2^64] = none

-- The boundary is strict SLT; minimum tail size is included before resolving the pointer.
#guard solcTailTarget? true (.dynamicArray u256) (List.replicate 196 0) 132 164 = some 132
#guard solcTailTarget? true (.dynamicArray u256)
  ((List.replicate 164 0) ++ (word 33).toList) 132 164 = none
#guard solcTailTarget? true (.dynamicArray u256)
  ((List.replicate 164 0) ++ (word 32).toList) 132 164 = some 164

-- The full calldata, including the selector, is the address space. The nested array length
-- aliases byte 0 (all zero here, even though the first *argument* word is 32).
#guard getArg direct [32, 1, 64, 0, 0, 2^256 - 132] = some emptyRow

-- A signed-negative absolute pointer passes the reference guard and CALLDATALOAD zero-fills.
-- Materializing the array retains the unsigned extent check and rejects it.
#guard getArg direct [32, 1, 64, 0, 0, 2^256 - 256] = some emptyRow
#guard getArg copyData [32, 1, 64, 0, 0, 2^256 - 256] = none

-- Return data and abi.decode use eager offsets even when the call's mode enables references.
#guard (decodeReturnValueWithMode? direct (.dynamicArray row)
  (words [32, 1, 32, 0, 64, 0])).isSome
#guard decodeReturnValueWithMode? direct (.dynamicArray row)
  (words [32, 1, 64, 0, 0, 2^256 - 32]) = none
#guard decodeReturnValueWithMode? direct (.elem .bool) (word 2) = none
#guard decodeReturnValueWithMode? direct (.elem .address) (word (2^160)) = none
#guard decodeReturnValueWithMode? direct (.elem (.int (.uint ⟨8, by decide⟩))) (word 256) = none

-- Preserve the existing raw bool-array representation; the new policy changes pointers only.
#guard decodeReturnValueWithMode? direct (.dynamicArray (.elem .bool)) (words [32, 2, 1, 2]) =
  decodeReturnValue? (.dynamicArray (.elem .bool)) (words [32, 2, 1, 2])

-- A later invalid request must not preempt effects from an earlier valid request.
private def deferredRows : DecodeMode := .solc08Calldata [(0, [{
  materialize := [[.element, .field 1]]
  deferErrors := [[.element]] }])]
#guard getArg deferredRows [32, 2, 64, 65536, 0, 64, 0] =
  some (.array [.tuple [.int 0, .array []], decodeFailure])
#guard getArg copyData [32, 2, 64, 65536, 0, 64, 0] = none
#guard getArg deferredRows [2^256 - 32, 1, 64, 0, 0, 0] = none
#guard decodeReturnValueWithMode? deferredRows (.dynamicArray row)
  (words [32, 2, 64, 65536, 0, 64, 0]) = none

-- Static tuple elements (such as signatures) can also fail at their individual accesses.
private def signatures : List ABIType :=
  [.dynamicArray (.tuple [.elem (.int (.uint ⟨8, by decide⟩)), u256])]
#guard (decodeCalldata ["s"] signatures (call [32, 2, 27, 0, 256, 0]) deferredRows
    >>= fun store => store.get? "s") =
  some (.array [.tuple [.int 27, .int 0], decodeFailure])

end ABI.CalldataTests
