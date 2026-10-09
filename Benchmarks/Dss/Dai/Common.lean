import Benchmarks.Dss.Dai.Bytecode
import Reasoning.ABI
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Dispatch
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# Shared MakerDAO DSS Dai proof helpers

This file contains contract-wide proof notation and selector constants.  The selectors are computed
from the canonical ABI signatures and cross-checked against the runtime dispatch constants in
`Bytecode.lean`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Dai

/-- The 4-byte function selector word the runtime dispatcher computes from calldata. -/
abbrev daiSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Dai selectors, indexed in `contract.transitions` order. -/
def daiSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩  -- allowance(address,address)
  | 1 => ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩  -- approve(address,uint256)
  | 2 => ⟨#[0x70, 0xa0, 0x82, 0x31]⟩  -- balanceOf(address)
  | 3 => ⟨#[0x9d, 0xc2, 0x9f, 0xac]⟩  -- burn(address,uint256)
  | 4 => ⟨#[0x31, 0x3c, 0xe5, 0x67]⟩  -- decimals()
  | 5 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩  -- deny(address)
  | 6 => ⟨#[0x36, 0x44, 0xe5, 0x15]⟩  -- DOMAIN_SEPARATOR()
  | 7 => ⟨#[0x40, 0xc1, 0x0f, 0x19]⟩  -- mint(address,uint256)
  | 8 => ⟨#[0xbb, 0x35, 0x78, 0x3b]⟩  -- move(address,address,uint256)
  | 9 => ⟨#[0x06, 0xfd, 0xde, 0x03]⟩  -- name()
  | 10 => ⟨#[0x7e, 0xce, 0xbe, 0x00]⟩ -- nonces(address)
  | 11 => ⟨#[0x8f, 0xcb, 0xaf, 0x0c]⟩ -- permit(address,address,uint256,uint256,bool,uint8,bytes32,bytes32)
  | 12 => ⟨#[0x30, 0xad, 0xf8, 0x1f]⟩ -- PERMIT_TYPEHASH()
  | 13 => ⟨#[0xf2, 0xd5, 0xd5, 0x6b]⟩ -- pull(address,uint256)
  | 14 => ⟨#[0xb7, 0x53, 0xa9, 0x8c]⟩ -- push(address,uint256)
  | 15 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 16 => ⟨#[0x95, 0xd8, 0x9b, 0x41]⟩ -- symbol()
  | 17 => ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ -- totalSupply()
  | 18 => ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩ -- transfer(address,uint256)
  | 19 => ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ -- transferFrom(address,address,uint256)
  | 20 => ⟨#[0x54, 0xfd, 0x4d, 0x50]⟩ -- version()
  | _ => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩  -- wards(address)

end Benchmarks.Dss.Dai
