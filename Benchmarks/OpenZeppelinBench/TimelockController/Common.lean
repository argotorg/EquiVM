import Benchmarks.OpenZeppelinBench.TimelockController.Bytecode
import Reasoning.ABI
import Reasoning.Theory
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Memory
import Reasoning.Storage
import Reasoning.Dispatch
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# OpenZeppelin TimelockController shared proof foundation

Contract-wide selector notation and constants for the optimized TimelockController runtime
(solc 0.8.35, optimizer on, Shanghai / PUSH0). The runtime dispatcher is a balanced depth-3
binary search over 28 selectors, so the selector machinery mirrors the fully-proved `Benchmarks/Dss/Pot`
(same compiler family, `RD.selectorSplit*Auto` + `RD.dispatchTo`).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.TimelockController

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev tlcSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order. -/
def tlcSelBytes : ℕ → ByteArray
  | 0  => ⟨#[0xb0, 0x8e, 0x51, 0xc0]⟩ -- CANCELLER_ROLE()
  | 1  => ⟨#[0xc4, 0xd2, 0x52, 0xf5]⟩ -- cancel(bytes32)
  | 2  => ⟨#[0xa2, 0x17, 0xfd, 0xdf]⟩ -- DEFAULT_ADMIN_ROLE()
  | 3  => ⟨#[0xe3, 0x83, 0x35, 0xe5]⟩ -- executeBatch(address[],uint256[],bytes[],bytes32,bytes32)
  | 4  => ⟨#[0x13, 0x40, 0x08, 0xd3]⟩ -- execute(address,uint256,bytes,bytes32,bytes32)
  | 5  => ⟨#[0x07, 0xbd, 0x02, 0x65]⟩ -- EXECUTOR_ROLE()
  | 6  => ⟨#[0xf2, 0x7a, 0x0c, 0x92]⟩ -- getMinDelay()
  | 7  => ⟨#[0x79, 0x58, 0x00, 0x4c]⟩ -- getOperationState(bytes32)
  | 8  => ⟨#[0x24, 0x8a, 0x9c, 0xa3]⟩ -- getRoleAdmin(bytes32)
  | 9  => ⟨#[0xd4, 0x5c, 0x44, 0x35]⟩ -- getTimestamp(bytes32)
  | 10 => ⟨#[0x2f, 0x2f, 0xf1, 0x5d]⟩ -- grantRole(bytes32,address)
  | 11 => ⟨#[0x91, 0xd1, 0x48, 0x54]⟩ -- hasRole(bytes32,address)
  | 12 => ⟨#[0xb1, 0xc5, 0xf4, 0x27]⟩ -- hashOperationBatch(address[],uint256[],bytes[],bytes32,bytes32)
  | 13 => ⟨#[0x80, 0x65, 0x65, 0x7f]⟩ -- hashOperation(address,uint256,bytes,bytes32,bytes32)
  | 14 => ⟨#[0x2a, 0xb0, 0xf5, 0x29]⟩ -- isOperationDone(bytes32)
  | 15 => ⟨#[0x58, 0x4b, 0x15, 0x3e]⟩ -- isOperationPending(bytes32)
  | 16 => ⟨#[0x13, 0xbc, 0x9f, 0x20]⟩ -- isOperationReady(bytes32)
  | 17 => ⟨#[0x31, 0xd5, 0x07, 0x50]⟩ -- isOperation(bytes32)
  | 18 => ⟨#[0xbc, 0x19, 0x7c, 0x81]⟩ -- onERC1155BatchReceived(address,address,uint256[],uint256[],bytes)
  | 19 => ⟨#[0xf2, 0x3a, 0x6e, 0x61]⟩ -- onERC1155Received(address,address,uint256,uint256,bytes)
  | 20 => ⟨#[0x15, 0x0b, 0x7a, 0x02]⟩ -- onERC721Received(address,address,uint256,bytes)
  | 21 => ⟨#[0x8f, 0x61, 0xf4, 0xf5]⟩ -- PROPOSER_ROLE()
  | 22 => ⟨#[0x36, 0x56, 0x8a, 0xbe]⟩ -- renounceRole(bytes32,address)
  | 23 => ⟨#[0xd5, 0x47, 0x74, 0x1f]⟩ -- revokeRole(bytes32,address)
  | 24 => ⟨#[0x8f, 0x2a, 0x0b, 0xb0]⟩ -- scheduleBatch(address[],uint256[],bytes[],bytes32,bytes32,uint256)
  | 25 => ⟨#[0x01, 0xd5, 0x06, 0x2a]⟩ -- schedule(address,uint256,bytes,bytes32,bytes32,uint256)
  | 26 => ⟨#[0x01, 0xff, 0xc9, 0xa7]⟩ -- supportsInterface(bytes4)
  | _  => ⟨#[0x64, 0xd6, 0x23, 0x53]⟩ -- updateDelay(uint256)

theorem tlcDepth_ne_1024_of_lt {d : Fin 1025} (h : d.val < 1024) : d ≠ 1024 := by
  intro hd
  have hdval : d.val = (1024 : Fin 1025).val := congrArg Fin.val hd
  have h1024 : (1024 : Fin 1025).val = 1024 := by decide
  omega

theorem tlcInitStateDepth_ne_1024_of_lt {cA gh bl σ σ₀ A I g}
    (h : I.depth.val < 1024) :
    (initState cA gh bl σ σ₀ g A I).executionEnv.depth ≠ 1024 := by
  simpa [initState] using tlcDepth_ne_1024_of_lt h

end OpenZeppelinBench.TimelockController
