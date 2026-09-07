import Examples.UniswapV2Pair.CodeCopyRevertSteps
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

-- LIBRARY CANDIDATE: legacy Error(string) construction by CODECOPY, parameterized by literal length.
structure SolcErrorStringCopyWf (code : ByteArray) (pc source len : UInt256) : Prop where
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
  d25 : decode code (pc + ⟨25⟩) = some (.PUSH1, some (len, 1))
  d27 : decode code (pc + ⟨27⟩) = some (.DUP2, .none)
  d28 : decode code (pc + ⟨28⟩) = some (.MSTORE, .none)
  d29 : decode code (pc + ⟨29⟩) = some (.PUSH1, some (⟨32⟩, 1))
  d31 : decode code (pc + ⟨31⟩) = some (.ADD, .none)
  d32 : decode code (pc + ⟨32⟩) = some (.DUP1, .none)
  d33 : decode code (pc + ⟨33⟩) = some (.PUSH2, some (source, 2))
  d36 : decode code (pc + ⟨36⟩) = some (.PUSH1, some (len, 1))
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
theorem RD.solcErrorStringCopyReverts
    {code : ByteArray} {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {pc source len aw : UInt256} {R : List UInt256} {k C : Nat}
    (rd : RD code I g s0 pc R mem aw rdata acc k C)
    (hwf : SolcErrorStringCopyWf code pc source len)
    (hov : R.length + 10 ≤ 1024) : RDrev code g s0 := by
  have rdLoad := evm_run rd with [raw push1 ⟨64⟩ hwf.d0 (by evm_ov)]
  have rdSelector := RD.mloadWord rdLoad hwf.d2 rfl (by omega)
  have rdRaw := rdSelector.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by simpa only [u256_add_assoc] using hwf.d3) (by evm_ov)
  have rdStore0 := evm_run rdRaw with [
    raw push1 ⟨229⟩ (by simpa only [u256_add_assoc] using hwf.d7) (by evm_ov),
    raw shl (by simpa only [u256_add_assoc] using hwf.d9) (by evm_ov),
    raw dup2 (by simpa only [u256_add_assoc] using hwf.d10) (by evm_ov)]
  have rdHeader := RD.mstoreWord rdStore0 (by simpa only [u256_add_assoc] using hwf.d11) (by evm_ov)
  have rdStore1 := evm_run rdHeader with [
    raw push1 ⟨4⟩ (by simpa only [u256_add_assoc] using hwf.d12) (by evm_ov),
    raw add (by simpa only [u256_add_assoc] using hwf.d14) (by evm_ov),
    raw dup1 (by simpa only [u256_add_assoc] using hwf.d15) (by evm_ov),
    raw dup1 (by simpa only [u256_add_assoc] using hwf.d16) (by evm_ov),
    raw push1 ⟨32⟩ (by simpa only [u256_add_assoc] using hwf.d17) (by evm_ov),
    raw add (by simpa only [u256_add_assoc] using hwf.d19) (by evm_ov),
    raw dup3 (by simpa only [u256_add_assoc] using hwf.d20) (by evm_ov),
    raw dup2 (by simpa only [u256_add_assoc] using hwf.d21) (by evm_ov),
    raw sub (by simpa only [u256_add_assoc] using hwf.d22) (by evm_ov),
    raw dup3 (by simpa only [u256_add_assoc] using hwf.d23) (by evm_ov)]
  have rdLength := RD.mstoreWord rdStore1 (by simpa only [u256_add_assoc] using hwf.d24) (by evm_ov)
  have rdStore2 := evm_run rdLength with [
    raw push1 len (by simpa only [u256_add_assoc] using hwf.d25) (by evm_ov),
    raw dup2 (by simpa only [u256_add_assoc] using hwf.d27) (by evm_ov)]
  have rdPayload := RD.mstoreWord rdStore2 (by simpa only [u256_add_assoc] using hwf.d28) (by evm_ov)
  have rdCopy := evm_run rdPayload with [
    raw push1 ⟨32⟩ (by simpa only [u256_add_assoc] using hwf.d29) (by evm_ov),
    raw add (by simpa only [u256_add_assoc] using hwf.d31) (by evm_ov),
    raw dup1 (by simpa only [u256_add_assoc] using hwf.d32) (by evm_ov),
    raw push2 source (by simpa only [u256_add_assoc] using hwf.d33) (by evm_ov),
    raw push1 len (by simpa only [u256_add_assoc] using hwf.d36) (by evm_ov),
    raw swap2 (by simpa only [u256_add_assoc] using hwf.d38) (by evm_ov)]
  have rdEnd := RD.codecopyAny rdCopy (by simpa only [u256_add_assoc] using hwf.d39) (by evm_ov)
  have rdLoadFinal := evm_run rdEnd with [
    raw push1 ⟨64⟩ (by simpa only [u256_add_assoc] using hwf.d40) (by evm_ov),
    raw add (by simpa only [u256_add_assoc] using hwf.d42) (by evm_ov),
    raw swap2 (by simpa only [u256_add_assoc] using hwf.d43) (by evm_ov),
    raw pop (by simpa only [u256_add_assoc] using hwf.d44) (by evm_ov),
    raw pop (by simpa only [u256_add_assoc] using hwf.d45) (by evm_ov),
    raw push1 ⟨64⟩ (by simpa only [u256_add_assoc] using hwf.d46) (by evm_ov)]
  have rdTail := RD.mloadWord rdLoadFinal (by simpa only [u256_add_assoc] using hwf.d48) rfl (by evm_ov)
  have rdRev := evm_run rdTail with [
    raw dup1 (by simpa only [u256_add_assoc] using hwf.d49) (by evm_ov),
    raw swap2 (by simpa only [u256_add_assoc] using hwf.d50) (by evm_ov),
    raw sub (by simpa only [u256_add_assoc] using hwf.d51) (by evm_ov),
    raw swap1 (by simpa only [u256_add_assoc] using hwf.d52) (by evm_ov)]
  exact RD.revAny rdRev (by simpa only [u256_add_assoc] using hwf.d53) (by evm_ov)
end UniswapV2Pair
