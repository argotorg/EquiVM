import Benchmarks.Morpho.MetaMorphoV1_1.AddressDelegateRuntime

/-! A nested bytes offset accepted by the runtime but rejected by the source decoder.

The outer argument starts at byte 36, its one-element offset table at byte 68. The relative
offset `2^256 - 100` points to byte `2^256 - 32`. CALLDATALOAD supplies a zero length there;
adding 32 wraps the empty payload's start to zero. All compiled decoder guards pass.

The account at `codeOwner` contains STOP, while the executing environment carries the exact
patched MetaMorpho runtime. The unrestricted runtime-refinement statement permits these
inputs. Its self-DELEGATECALL succeeds, and the runtime returns `[bytes("")]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.MulticallWrappedCalldataRegression

set_option autoImplicit false
set_option maxRecDepth 2000

def valuation : MetaMorphoV1_1Immutables :=
  ⟨EVM.address 0, ⟨0⟩, ⟨0⟩, ⟨0⟩, EVM.address 0, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
    EVM.address 0, ⟨0⟩, by decide, by decide⟩

def calldata : ByteArray :=
  ByteArray.mk #[0xac, 0x96, 0x50, 0xd8] ++
    (UInt256.ofNat 32).toByteArray ++ (UInt256.ofNat 1).toByteArray ++
    (UInt256.ofNat (2 ^ 256 - 100)).toByteArray

def accounts : AccountMap :=
  (∅ : AccountMap).insert (EVM.address 0x1000)
    { (default : Account) with code := ByteArray.mk #[0] }

def environment : ExecutionEnv :=
  { (default : ExecutionEnv) with
    codeOwner := EVM.address 0x1000
    source := EVM.address 0x2000
    sender := EVM.address 0x2000
    calldata := calldata
    code := deployedRuntime valuation
    perm := true }

def output : ByteArray :=
  (UInt256.ofNat 32).toByteArray ++ (UInt256.ofNat 1).toByteArray ++
    (UInt256.ofNat 32).toByteArray ++ (UInt256.ofNat 0).toByteArray

def returnsExpectedOutput : Bool :=
  match Ethereum.EVM.Ξ accounts accounts ⟨1000000⟩ default environment with
  | .ok (.success _ out) => out == output
  | _ => false

theorem runtimeReturns : returnsExpectedOutput = true := by native_decide

theorem calldataSize : calldata.size = 100 := by decide +kernel

theorem sourceRejects :
    decodeCalldata ["data"] [.dynamicArray .bytes] calldata = none := by native_decide

end Benchmarks.Morpho.MetaMorphoV1_1.MulticallWrappedCalldataRegression
