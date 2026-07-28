import Benchmarks.WETH9.Bytecode
import Reasoning.ABI
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Dispatch
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# Shared WETH9 proof helpers

Contract-wide selector constants and the runtime dispatcher's selector word.  The selectors are
computed from the canonical ABI signatures and cross-checked against the runtime dispatch constants
in `Bytecode.lean` (see the disassembled binary-search dispatcher).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.WETH9

/-- The 4-byte function selector word the runtime dispatcher computes from calldata. -/
abbrev weth9SelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- WETH9 selectors, indexed in `contract.transitions` order. -/
def weth9SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x06, 0xfd, 0xde, 0x03]⟩  -- name()
  | 1 => ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩  -- approve(address,uint256)
  | 2 => ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩  -- totalSupply()
  | 3 => ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩  -- transferFrom(address,address,uint256)
  | 4 => ⟨#[0x2e, 0x1a, 0x7d, 0x4d]⟩  -- withdraw(uint256)
  | 5 => ⟨#[0x31, 0x3c, 0xe5, 0x67]⟩  -- decimals()
  | 6 => ⟨#[0x70, 0xa0, 0x82, 0x31]⟩  -- balanceOf(address)
  | 7 => ⟨#[0x95, 0xd8, 0x9b, 0x41]⟩  -- symbol()
  | 8 => ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩  -- transfer(address,uint256)
  | 9 => ⟨#[0xd0, 0xe3, 0x0d, 0xb0]⟩  -- deposit()
  | _ => ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩  -- allowance(address,address)

end Benchmarks.WETH9
