import Reasoning.Reach
import Reasoning.Initcode
import Examples.VyperImmutable.Bytecode
import Examples.VyperImmutable.Immutables
import Examples.VyperImmutable.ImmutableCode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace immutableBlocks

set_option maxRecDepth 10000

/-- Automatically generated RD summary for bytecode block at pc 138. -/
theorem immutable_block_138 {suffix : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD fork (Examples.VyperImmutable.immutableBytecode ++ suffix) ee g s0 (UInt256.ofNat 138) (x0 :: R) mem aw rdata σ k C)
    : RDret fork (Examples.VyperImmutable.immutableBytecode ++ suffix) g s0 σ ByteArray.empty := by
  let r0 := h
  obtain ⟨_, _, r1⟩ := RD.sload r0 (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨138⟩ : UInt256), .SLOAD, none)) (by evm_ov)
  exact r1.stop (by append_decode(Examples.VyperImmutable.immutableBytecode, suffix, (⟨139⟩ : UInt256), .STOP, none)) (by evm_ov)

/- Unsupported instruction boundary at pc 140: push32 (0x7f). No RD transition is asserted. -/

end immutableBlocks
