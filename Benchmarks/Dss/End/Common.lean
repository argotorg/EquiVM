import Benchmarks.Dss.End.Bytecode
import Reasoning.ABI
import Reasoning.Theory
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Memory
import Reasoning.Storage
import Reasoning.Dispatch
import Reasoning.Refinement
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# MakerDAO/Sky DSS End shared proof foundation

Contract-wide selector notation and the transition-body obligation shape used by the dispatcher
scaffold. Selectors are listed in `contract.transitions` order.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.End

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev endSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order. -/
def endSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩  -- wards(address)
  | 1 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩  -- vat()
  | 2 => ⟨#[0xe4, 0x88, 0x18, 0x13]⟩  -- cat()
  | 3 => ⟨#[0xc3, 0xb3, 0xad, 0x7f]⟩  -- dog()
  | 4 => ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩  -- vow()
  | 5 => ⟨#[0x4b, 0xa2, 0x36, 0x3a]⟩  -- pot()
  | 6 => ⟨#[0x6f, 0x26, 0x5b, 0x93]⟩  -- spot()
  | 7 => ⟨#[0x84, 0x07, 0x82, 0xed]⟩  -- cure()
  | 8 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩  -- live()
  | 9 => ⟨#[0xe2, 0xb0, 0xca, 0xef]⟩  -- when()
  | 10 => ⟨#[0x64, 0xbd, 0x70, 0x13]⟩ -- wait()
  | 11 => ⟨#[0x0d, 0xca, 0x59, 0xc1]⟩ -- debt()
  | 12 => ⟨#[0xee, 0x64, 0x47, 0xb5]⟩ -- tag(bytes32)
  | 13 => ⟨#[0xe6, 0xee, 0x62, 0xaa]⟩ -- gap(bytes32)
  | 14 => ⟨#[0xe1, 0x34, 0x0a, 0x3d]⟩ -- Art(bytes32)
  | 15 => ⟨#[0x63, 0xfa, 0xd8, 0x5e]⟩ -- fix(bytes32)
  | 16 => ⟨#[0x92, 0x55, 0xf8, 0x09]⟩ -- bag(address)
  | 17 => ⟨#[0xc9, 0x39, 0xeb, 0xfc]⟩ -- out(bytes32,address)
  | 18 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 19 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 20 => ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ -- file(bytes32,address)
  | 21 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file(bytes32,uint256)
  | 22 => ⟨#[0x69, 0x24, 0x50, 0x09]⟩ -- cage()
  | 23 => ⟨#[0xe2, 0x70, 0x2f, 0xdc]⟩ -- cage(bytes32)
  | 24 => ⟨#[0x38, 0xc6, 0xde, 0x40]⟩ -- snip(bytes32,uint256)
  | 25 => ⟨#[0x50, 0x3e, 0xcf, 0x06]⟩ -- skip(bytes32,uint256)
  | 26 => ⟨#[0x89, 0xea, 0x45, 0xd3]⟩ -- skim(bytes32,address)
  | 27 => ⟨#[0xc8, 0x30, 0x62, 0xc6]⟩ -- free(bytes32)
  | 28 => ⟨#[0x59, 0x20, 0x37, 0x5c]⟩ -- thaw()
  | 29 => ⟨#[0x4a, 0x10, 0xea, 0xa6]⟩ -- flow(bytes32)
  | 30 => ⟨#[0x6e, 0xa4, 0x25, 0x55]⟩ -- pack(uint256)
  | _ => ⟨#[0xfe, 0x85, 0x07, 0xc6]⟩ -- cash(bytes32,uint256)

abbrev endBodyObligation (idx : ℕ) : Prop :=
  ∀ {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256},
    I.code = endBytecode →
    I.calldata.size < UInt256.size →
    I.perm = true →
    I.weiValue = ⟨0⟩ →
    selIs I (endSelBytes idx) →
    accountMapEquiv σ_evm σ_solm →
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I

end Benchmarks.Dss.End
