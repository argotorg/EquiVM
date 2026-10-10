import Solm.DiffTest.Harness
import Benchmarks.UniswapV3.Pool.Spec
import Benchmarks.UniswapV3.Pool.Bytecode
import Benchmarks.UniswapV3.Pool.ImmutableCode

/-!
# UniswapV3Pool differential-test target

Registered in `Tests/DiffTest/Generated.lean`.
Run with `lake exe solm-difftest --only UniswapV3Pool`.
The two caller fixtures implement the deployer's five-word `parameters()` result and all three
callbacks. The factory implements `owner()`. Token balances can be raised by callback payments.
-/

open Solm Solm.DiffTest

namespace Benchmarks.UniswapV3.Pool

private def pushWord (n : Nat) : ByteArray := ⟨#[0x7f]⟩ ++ wordBytes n

private def returnWords (words : List Nat) : ByteArray :=
  let stores := words.zipIdx.foldl (fun code (word, i) ↦
    code ++ pushWord word ++ push2 (32 * i) ++ ⟨#[0x52]⟩) ByteArray.empty
  stores ++ push2 (32 * words.length) ++ ⟨#[0x60, 0, 0xf3]⟩

private def calleeDispatch (arms : List (Nat × ByteArray)) : ByteArray := Id.run do
  let otherwise : ByteArray := ⟨#[0x60, 0, 0x60, 0, 0xfd]⟩
  let mut offset := 6 + 11 * arms.length + 1 + otherwise.size
  let mut checks : ByteArray := ⟨#[0x60, 0, 0x35, 0x60, 0xe0, 0x1c]⟩
  let mut bodies := ByteArray.empty
  for (selector, body) in arms do
    checks := checks ++ ⟨#[0x80, 0x63]⟩ ++ (wordBytes selector).extract 28 32 ++
      ⟨#[0x14]⟩ ++ push2 offset ++ ⟨#[0x57]⟩
    bodies := bodies ++ ⟨#[0x5b, 0x50]⟩ ++ body
    offset := offset + 2 + body.size
  return checks ++ ⟨#[0x50]⟩ ++ otherwise ++ bodies

-- These payment fixtures deliberately allow arbitrary credits. transfer returns true; balanceOf
-- reports the stored credits. The callback's nested calls are replayed with their account effects.
private def tokenCode : ByteArray :=
  let balance : ByteArray := ⟨#[0x60, 0, 0x54, 0x60, 0, 0x52, 0x60, 32, 0x60, 0, 0xf3]⟩
  let credit : ByteArray :=
    ⟨#[0x60, 4, 0x35, 0x60, 0, 0x54, 0x01, 0x60, 0, 0x55]⟩ ++ returnWords [1]
  calleeDispatch [(0x70a08231, balance), (0xa9059cbb, returnWords [1]), (0x12345678, credit)]

private def payToken (token offset : Nat) (signed : Bool) : ByteArray :=
  let selector := pushWord (0x12345678 * 2 ^ 224) ++ ⟨#[0x60, 0, 0x52]⟩
  let amount := push2 offset ++ ⟨#[0x35]⟩ ++
    (if signed then ⟨#[0x80, 0x60, 0, 0x90, 0x13, 0x02]⟩ else ByteArray.empty)
  selector ++ amount ++ ⟨#[0x60, 4, 0x52, 0x60, 32, 0x60, 0, 0x60, 36,
    0x60, 0, 0x60, 0]⟩ ++ push2 token ++ ⟨#[0x5a, 0xf1, 0x50]⟩

private def callbackCode : ByteArray :=
  let payment (signed : Bool) :=
    payToken 0x5000 4 signed ++ payToken 0x5001 36 signed ++ returnWords []
  -- Unit spacing lets the generator's small signed ticks reach successful mint executions.
  calleeDispatch [
    (0x89035730, returnWords [0x4000, 0x5000, 0x5001, 500, 1]),
    (0xd3487997, payment false), (0xfa461e33, payment true),
    (0xe9cbafb0, payment false)]

def poolCallees : List (EVM.Address × ByteArray) :=
  [(EVM.address 0x2000, callbackCode), (EVM.address 0x3000, callbackCode),
    (EVM.address 0x4000, calleeDispatch [(0x8da5cb5b, returnWords [0x2000])]),
    (EVM.address 0x5000, tokenCode), (EVM.address 0x5001, tokenCode)]

def diffTarget : Target :=
  { name := "UniswapV3Pool", contract := contract, config := config,
    runtime := uniswapV3PoolBytecode,
    initcode := some uniswapV3PoolCreationBytecode,
    -- runtime cases use the store a generated constructor run leaves; the zero valuation
    -- is the fallback
    immutables := initialImmutables contract,
    runtimeCodeOf := some (immutableLayout.deployed uniswapV3PoolBytecode),
    deployedRuntime := true,
    callees := poolCallees,
    -- genInt subtracts 2^(bits-1) from its word-pool draw; these offsets produce small ticks.
    words := (List.replicate 8
      [0, 1, 10, 20, 500, 2 ^ 96, 2 ^ 23 - 10, 2 ^ 23, 2 ^ 23 + 10]).flatten ++
      [100, 1000, 10000, 1000000, 10 ^ 18, 4295128739, 4295128740,
        79267784519130042428790663799, 79188560314459151373725315960,
        1461446703485210103287273052203988822378723970341, 887270, 887272] }

end Benchmarks.UniswapV3.Pool
