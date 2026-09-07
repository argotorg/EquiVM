import Examples.UniswapV2Pair.TransferRoutines
import Examples.UniswapV2Pair.ErrorStringCopyCore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

-- LIBRARY CANDIDATE: a legacy solc Error(string) block copying a 40-byte literal,
-- parameterized by bytecode, entry PC, literal offset, and caller stack.
structure SolcErrorString40CopyWf (code : ByteArray) (pc source : UInt256) : Prop where
  d0 : decode code pc = some (.PUSH1, some (⟨64⟩, 1))
  d2 : decode code (pc + ⟨2⟩) = some (.MLOAD, .none)
  d3 : decode code (pc + ⟨3⟩) = some (.PUSH3, some (⟨4594637⟩, 3))
  d7 : decode code (pc + ⟨7⟩) = some (.PUSH1, some (⟨229⟩, 1))
  d9 : decode code (pc + ⟨9⟩) = some (.SHL, .none)
  d10 : decode code (pc + ⟨10⟩) = some (.DUP2, .none)
  d11 : decode code (pc + ⟨11⟩) = some (.MSTORE, .none)
  d12 : decode code (pc + ⟨12⟩) = some (.PUSH1, some (⟨4⟩, 1))
  d14 : decode code (pc + ⟨14⟩) = some (.ADD, .none)
  d15 : decode code (pc + ⟨15⟩) = some (.DUP1, .none)
  d16 : decode code (pc + ⟨16⟩) = some (.DUP1, .none)
  d17 : decode code (pc + ⟨17⟩) = some (.PUSH1, some (⟨32⟩, 1))
  d19 : decode code (pc + ⟨19⟩) = some (.ADD, .none)
  d20 : decode code (pc + ⟨20⟩) = some (.DUP3, .none)
  d21 : decode code (pc + ⟨21⟩) = some (.DUP2, .none)
  d22 : decode code (pc + ⟨22⟩) = some (.SUB, .none)
  d23 : decode code (pc + ⟨23⟩) = some (.DUP3, .none)
  d24 : decode code (pc + ⟨24⟩) = some (.MSTORE, .none)
  d25 : decode code (pc + ⟨25⟩) = some (.PUSH1, some (⟨40⟩, 1))
  d27 : decode code (pc + ⟨27⟩) = some (.DUP2, .none)
  d28 : decode code (pc + ⟨28⟩) = some (.MSTORE, .none)
  d29 : decode code (pc + ⟨29⟩) = some (.PUSH1, some (⟨32⟩, 1))
  d31 : decode code (pc + ⟨31⟩) = some (.ADD, .none)
  d32 : decode code (pc + ⟨32⟩) = some (.DUP1, .none)
  d33 : decode code (pc + ⟨33⟩) = some (.PUSH2, some (source, 2))
  d36 : decode code (pc + ⟨36⟩) = some (.PUSH1, some (⟨40⟩, 1))
  d38 : decode code (pc + ⟨38⟩) = some (.SWAP2, .none)
  d39 : decode code (pc + ⟨39⟩) = some (.CODECOPY, .none)
  d40 : decode code (pc + ⟨40⟩) = some (.PUSH1, some (⟨64⟩, 1))
  d42 : decode code (pc + ⟨42⟩) = some (.ADD, .none)
  d43 : decode code (pc + ⟨43⟩) = some (.SWAP2, .none)
  d44 : decode code (pc + ⟨44⟩) = some (.POP, .none)
  d45 : decode code (pc + ⟨45⟩) = some (.POP, .none)
  d46 : decode code (pc + ⟨46⟩) = some (.PUSH1, some (⟨64⟩, 1))
  d48 : decode code (pc + ⟨48⟩) = some (.MLOAD, .none)
  d49 : decode code (pc + ⟨49⟩) = some (.DUP1, .none)
  d50 : decode code (pc + ⟨50⟩) = some (.SWAP2, .none)
  d51 : decode code (pc + ⟨51⟩) = some (.SUB, .none)
  d52 : decode code (pc + ⟨52⟩) = some (.SWAP1, .none)
  d53 : decode code (pc + ⟨53⟩) = some (.REVERT, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcErrorString40CopyReverts
    {code : ByteArray} {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {pc source : UInt256} {R : List UInt256} {k C : ℕ}
    (rd : RD code I g s0 pc R mem ⟨6⟩ rdata acc k C)
    (hwf : SolcErrorString40CopyWf code pc source)
    (hsource : source.toNat + 40 ≤ code.size)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 10 ≤ 1024) : RDrev code g s0 := by
  have _ := And.intro hsource (And.intro hmem hmem64)
  apply RD.solcErrorStringCopyReverts rd (source := source) (len := ⟨40⟩) _ hov
  cases hwf
  constructor <;> assumption

end UniswapV2Pair
