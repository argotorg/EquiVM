import Reasoning.Solc

/-!
# SolcDecode — experimental scalar ABI decoder routine combinators

This file keeps the bytecode/PC-parametric scalar decoder routines separate from the main
`Reasoning.Solc` library.  They are useful as a reference point for future decoder factoring, but
are intentionally not imported by the examples.
-/

namespace Reasoning.Reach

open Ethereum Ethereum.EVM Reasoning.Theory

/-! ## Solc scalar ABI decoder routines

These lemmas capture small compiler-emitted decoder subroutines independently of a particular
contract.  Concrete proofs discharge the `*Wf` bytecode-shape hypotheses with `by decide`, but the
large instruction trace is checked once here.

These are currently unused, as they did not provide significant simplifications.
-/

/-- Bytecode shape for solc's `cleanup_t_uint256` identity routine. -/
@[reducible] def solcCleanupUInt256Wf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.PUSH0, .none)
  ∧ decode code p2 = some (.DUP2, .none)
  ∧ decode code p3 = some (.SWAP1, .none)
  ∧ decode code p4 = some (.POP, .none)
  ∧ decode code p5 = some (.SWAP2, .none)
  ∧ decode code p6 = some (.SWAP1, .none)
  ∧ decode code p7 = some (.POP, .none)
  ∧ decode code p8 = some (.JUMP, .none)

/--
solc `cleanup_t_uint256`: from `[v, ret, ...]`, return `v` unchanged to the dynamic return
address.  This is the common identity cleanup used by uint256 decoders and encoders.
-/
theorem RD.solcCleanupUInt256 {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc v ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (v :: ret :: R) mem aw rdata acc k C)
    (hwf : solcCleanupUInt256Wf code pc)
    (hret : (D_J code 0).contains ret = true) (hov : R.length + 4 ≤ 1024) :
    RD code ee g s0 ret (v :: R) mem aw rdata acc (k + 9) (C + 27) := by
  rcases hwf with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8⟩
  exact h.jumpdest hd0 (by evm_ov)
    |>.push0 hd1 (by evm_ov)
    |>.dup2 hd2 (by evm_ov)
    |>.swap1 hd3 (by evm_ov)
    |>.pop hd4 (by evm_ov)
    |>.swap2 hd5 (by evm_ov)
    |>.swap1 hd6 (by evm_ov)
    |>.pop hd7 (by evm_ov)
    |>.jump hd8 hret (by evm_ov)

/-- Bytecode shape for solc's uint256 validator routine, parameterized by its inner cleanup call. -/
@[reducible] def solcValidateUInt256Wf
    (code : ByteArray) (pc cleanupPc afterCleanupPc okPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p5 := p4 + ⟨1⟩
  let p8 := p5 + UInt256.ofNat 3
  let a1 := afterCleanupPc + ⟨1⟩
  let a2 := a1 + ⟨1⟩
  let a3 := a2 + ⟨1⟩
  let a6 := a3 + UInt256.ofNat 3
  let ok1 := okPc + ⟨1⟩
  let ok2 := ok1 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH2, some (afterCleanupPc, 2))
  ∧ decode code p4 = some (.DUP2, .none)
  ∧ decode code p5 = some (.Push .PUSH2, some (cleanupPc, 2))
  ∧ decode code p8 = some (.JUMP, .none)
  ∧ decode code afterCleanupPc = some (.JUMPDEST, .none)
  ∧ decode code a1 = some (.DUP2, .none)
  ∧ decode code a2 = some (.EQ, .none)
  ∧ decode code a3 = some (.Push .PUSH2, some (okPc, 2))
  ∧ decode code a6 = some (.JUMPI, .none)
  ∧ decode code okPc = some (.JUMPDEST, .none)
  ∧ decode code ok1 = some (.POP, .none)
  ∧ decode code ok2 = some (.JUMP, .none)

/--
solc uint256 validator: call `cleanup_t_uint256`, compare the cleaned value with the original
value, and return to `ret`.  For uint256 the comparison is reflexive, so this is a pass-only
validator.
-/
theorem RD.solcValidateUInt256 {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {pc cleanupPc afterCleanupPc okPc arg ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (arg :: ret :: R) mem aw rdata acc k C)
    (hwf : solcValidateUInt256Wf code pc cleanupPc afterCleanupPc okPc)
    (hcleanup : solcCleanupUInt256Wf code cleanupPc)
    (hcleanupJd : (D_J code 0).contains cleanupPc = true)
    (hafterCleanupJd : (D_J code 0).contains afterCleanupPc = true)
    (hokJd : (D_J code 0).contains okPc = true)
    (hret : (D_J code 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    RD code ee g s0 ret R mem aw rdata acc (k + 22) (C + 76) := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12⟩
  have h1 := h.jumpdest hd0 (by evm_ov)
    |>.push2 afterCleanupPc hd1 (by evm_ov)
    |>.dup2 hd2 (by evm_ov)
    |>.push2 cleanupPc hd3 (by evm_ov)
    |>.jump hd4 hcleanupJd (by evm_ov)
  have h2 := h1.solcCleanupUInt256 hcleanup hafterCleanupJd (by evm_ov)
  exact h2.jumpdest hd5 (by evm_ov)
    |>.dup2 hd6 (by evm_ov)
    |>.eq hd7 (by evm_ov)
    |>.push2 okPc hd8 (by evm_ov)
    |>.jumpiT hd9 (by rw [u256_eq_refl]; exact one_ne_zero_uint) hokJd (by evm_ov)
    |>.jumpdest hd10 (by evm_ov)
    |>.pop hd11 (by evm_ov)
    |>.jump hd12 hret (by evm_ov)

/-- Bytecode shape for solc's `abi_decode_uint256` routine, parameterized by its validator call. -/
@[reducible] def solcDecodeUInt256Wf
    (code : ByteArray) (pc validatePc afterValidatePc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p9 := p6 + UInt256.ofNat 3
  let p10 := p9 + ⟨1⟩
  let p13 := p10 + UInt256.ofNat 3
  let a1 := afterValidatePc + ⟨1⟩
  let a2 := a1 + ⟨1⟩
  let a3 := a2 + ⟨1⟩
  let a4 := a3 + ⟨1⟩
  let a5 := a4 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.PUSH0, .none)
  ∧ decode code p2 = some (.DUP2, .none)
  ∧ decode code p3 = some (.CALLDATALOAD, .none)
  ∧ decode code p4 = some (.SWAP1, .none)
  ∧ decode code p5 = some (.POP, .none)
  ∧ decode code p6 = some (.Push .PUSH2, some (afterValidatePc, 2))
  ∧ decode code p9 = some (.DUP2, .none)
  ∧ decode code p10 = some (.Push .PUSH2, some (validatePc, 2))
  ∧ decode code p13 = some (.JUMP, .none)
  ∧ decode code afterValidatePc = some (.JUMPDEST, .none)
  ∧ decode code a1 = some (.SWAP3, .none)
  ∧ decode code a2 = some (.SWAP2, .none)
  ∧ decode code a3 = some (.POP, .none)
  ∧ decode code a4 = some (.POP, .none)
  ∧ decode code a5 = some (.JUMP, .none)

/-- Discharge concrete solc bytecode-shape predicates by splitting their opcode facts. -/
macro "solc_wf" : tactic =>
  `(tactic|
    (dsimp only [solcCleanupUInt256Wf, solcValidateUInt256Wf, solcDecodeUInt256Wf];
     repeat' first | apply And.intro | decide))

/--
solc `abi_decode_uint256`: load one calldata word at `offset`, validate it with the uint256
validator, and return the decoded word to the dynamic return address.
-/
theorem RD.solcDecodeUInt256 {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ}
    {pc validatePc afterValidatePc cleanupPc afterCleanupPc okPc offset ennd ret : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (offset :: ennd :: ret :: R) mem aw rdata acc k C)
    (hwf : solcDecodeUInt256Wf code pc validatePc afterValidatePc)
    (hvalidate : solcValidateUInt256Wf code validatePc cleanupPc afterCleanupPc okPc)
    (hcleanup : solcCleanupUInt256Wf code cleanupPc)
    (hvalidateJd : (D_J code 0).contains validatePc = true)
    (hcleanupJd : (D_J code 0).contains cleanupPc = true)
    (hafterCleanupJd : (D_J code 0).contains afterCleanupPc = true)
    (hokJd : (D_J code 0).contains okPc = true)
    (hafterValidateJd : (D_J code 0).contains afterValidatePc = true)
    (hret : (D_J code 0).contains ret = true) (hov : R.length + 10 ≤ 1024) :
    RD code ee g s0 ret
        (uInt256OfByteArray (ee.calldata.readBytes offset.toNat 32) :: R)
        mem aw rdata acc (k + 38) (C + 126) := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14, hd15⟩
  have h1 := h.jumpdest hd0 (by evm_ov)
    |>.push0 hd1 (by evm_ov)
    |>.dup2 hd2 (by evm_ov)
    |>.calldataload hd3 (by evm_ov)
    |>.swap1 hd4 (by evm_ov)
    |>.pop hd5 (by evm_ov)
    |>.push2 afterValidatePc hd6 (by evm_ov)
    |>.dup2 hd7 (by evm_ov)
    |>.push2 validatePc hd8 (by evm_ov)
    |>.jump hd9 hvalidateJd (by evm_ov)
  have h2 := h1.solcValidateUInt256 (cleanupPc := cleanupPc)
    (afterCleanupPc := afterCleanupPc) (okPc := okPc)
    hvalidate hcleanup hcleanupJd hafterCleanupJd hokJd hafterValidateJd (by evm_ov)
  exact h2.jumpdest hd10 (by evm_ov)
    |>.swap3 hd11 (by evm_ov)
    |>.swap2 hd12 (by evm_ov)
    |>.pop hd13 (by evm_ov)
    |>.pop hd14 (by evm_ov)
    |>.jump hd15 hret (by evm_ov)

end Reasoning.Reach
