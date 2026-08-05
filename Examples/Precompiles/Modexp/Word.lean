import Examples.Precompiles.Modexp.Bytecode
import Examples.Precompiles.Modexp.Model
import Reasoning.Bytecode
import Reasoning.Solc

/-!
# ModExp single-word bytecode path

The deployed contract has a stack-only path when every operand length is at most 32 bytes. This
file gives names to the exact EVM words used by that path and proves its entry/parser trace with
threshold-exact gas. The arbitrary-limb paths build on the same public model.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

/-- The word produced by `CALLDATALOAD off`. -/
def calldataWord (I : ExecutionEnv) (off : UInt256) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes off.toNat 32)

def baseSizeWord (I : ExecutionEnv) : UInt256 := calldataWord I ⟨0⟩
def exponentSizeWord (I : ExecutionEnv) : UInt256 := calldataWord I ⟨32⟩
def modulusSizeWord (I : ExecutionEnv) : UInt256 := calldataWord I ⟨64⟩

def operandShift (size : UInt256) : UInt256 :=
  UInt256.shiftLeft (⟨32⟩ - size) ⟨3⟩

def operandWord (I : ExecutionEnv) (off size : UInt256) : UInt256 :=
  UInt256.shiftRight (calldataWord I off) (operandShift size)

def baseWord (I : ExecutionEnv) : UInt256 :=
  operandWord I ⟨96⟩ (baseSizeWord I)

def exponentWord (I : ExecutionEnv) : UInt256 :=
  operandWord I (⟨96⟩ + baseSizeWord I) (exponentSizeWord I)

def modulusWord (I : ExecutionEnv) : UInt256 :=
  operandWord I ((baseSizeWord I + exponentSizeWord I) + ⟨96⟩) (modulusSizeWord I)

def modulusShift (I : ExecutionEnv) : UInt256 :=
  operandShift (modulusSizeWord I)

/-- Pure Lean result of the single-word path, expressed using the shared modular-power model. -/
def wordOutput (I : ExecutionEnv) : ByteArray :=
  let r := UInt256.ofNat
    (Model.modPow (baseWord I).toNat (exponentWord I).toNat (modulusWord I).toNat)
  r.toByteArray.extract (32 - (modulusSizeWord I).toNat) 32

/-- Inputs currently covered by the completed trace below. The operand-length restriction selects
the contract's full single-word algorithm; `modulus ≤ 1` selects its loop-free edge path. -/
def smallModulusAccepts (ctx : BytecodeContext) : Prop :=
  let I := ctx.executionEnv
  I.weiValue = ⟨0⟩ ∧
  (baseSizeWord I).toNat ≤ 32 ∧
  (exponentSizeWord I).toNat ≤ 32 ∧
  (modulusSizeWord I).toNat ≤ 32 ∧
  (modulusWord I).toNat ≤ 1

/-- Exact bytecode gas on the loop-free `modulus = 0 ∨ modulus = 1` word path. -/
def smallModulusGasCost : Nat := 349

private theorem size_gt_1024_zero {w : UInt256} (h : w.toNat ≤ 1024) :
    UInt256.gt w ⟨1024⟩ = ⟨0⟩ := by
  apply ugt_zero
  simpa using h

private theorem size_gt_32_zero {w : UInt256} (h : w.toNat ≤ 32) :
    UInt256.gt w ⟨32⟩ = ⟨0⟩ := by
  apply ugt_zero
  simpa using h

private theorem reachEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨0x0a⟩ [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 33 := by
  have rd0 := RDx.initState
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hcode
  have hd :
      decode runtimeBytecode ⟨0x00⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) ∧
      decode runtimeBytecode ⟨0x02⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) ∧
      decode runtimeBytecode ⟨0x04⟩ = some (.MSTORE, .none) ∧
      decode runtimeBytecode ⟨0x05⟩ = some (.CALLVALUE, .none) ∧
      decode runtimeBytecode ⟨0x06⟩ = some (.Push .PUSH2, some (⟨0x1b4⟩, 2)) ∧
      decode runtimeBytecode ⟨0x09⟩ = some (.JUMPI, .none) := by
    simpa only [List.cons.injEq, and_true] using entryDecodes
  rcases hd with ⟨hd0, hd2, hd4, hd5, hd6, hd9⟩
  have rd := evm_run rd0 with [
    known push1 hd0 ⟨128⟩,
    known push1 hd2 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) hd4
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    known callvalue hd5,
    known push2 hd6 ⟨0x1b4⟩,
    known jumpiNT hd9 hvalue ]
  exact ⟨_, rd⟩

private theorem reachLengths {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨0x14⟩ [exponentSizeWord I, baseSizeWord I, modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 56 := by
  obtain ⟨k, rd0⟩ := reachEntry (g := g) hcode hvalue
  have hd :
      decode runtimeBytecode ⟨0x0a⟩ = some (.PUSH0, .none) ∧
      decode runtimeBytecode ⟨0x0b⟩ = some (.CALLDATALOAD, .none) ∧
      decode runtimeBytecode ⟨0x0c⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) ∧
      decode runtimeBytecode ⟨0x0e⟩ = some (.CALLDATALOAD, .none) ∧
      decode runtimeBytecode ⟨0x0f⟩ = some (.SWAP1, .none) ∧
      decode runtimeBytecode ⟨0x10⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) ∧
      decode runtimeBytecode ⟨0x12⟩ = some (.CALLDATALOAD, .none) ∧
      decode runtimeBytecode ⟨0x13⟩ = some (.SWAP2, .none) := by
    simpa only [List.cons.injEq, and_true] using lengthDecodes
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7⟩
  have rd := evm_run rd0 with [
    known push0 hd0,
    known calldataload hd1,
    known push1 hd2 ⟨32⟩,
    known calldataload hd3,
    known swap1 hd4,
    known push1 hd5 ⟨64⟩,
    known calldataload hd6,
    known swap2 hd7 ]
  exact ⟨_, rd⟩

/-- Exact entry/length trace after the EIP-7823 checks have accepted all three lengths. -/
theorem reachBoundsPassed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb : (baseSizeWord I).toNat ≤ 1024)
    (he : (exponentSizeWord I).toNat ≤ 1024)
    (hm : (modulusSizeWord I).toNat ≤ 1024) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨0x29⟩ [exponentSizeWord I, baseSizeWord I, modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 102 := by
  obtain ⟨k, rd0⟩ := reachLengths (g := g) hcode hvalue
  have hb1024 := size_gt_1024_zero hb
  have he1024 := size_gt_1024_zero he
  have hm1024 := size_gt_1024_zero hm
  have hd :
      decode runtimeBytecode ⟨0x14⟩ = some (.Push .PUSH2, some (⟨1024⟩, 2)) ∧
      decode runtimeBytecode ⟨0x17⟩ = some (.DUP4, .none) ∧
      decode runtimeBytecode ⟨0x18⟩ = some (.GT, .none) ∧
      decode runtimeBytecode ⟨0x19⟩ = some (.Push .PUSH2, some (⟨1024⟩, 2)) ∧
      decode runtimeBytecode ⟨0x1c⟩ = some (.DUP3, .none) ∧
      decode runtimeBytecode ⟨0x1d⟩ = some (.GT, .none) ∧
      decode runtimeBytecode ⟨0x1e⟩ = some (.OR, .none) ∧
      decode runtimeBytecode ⟨0x1f⟩ = some (.Push .PUSH2, some (⟨1024⟩, 2)) ∧
      decode runtimeBytecode ⟨0x22⟩ = some (.DUP4, .none) ∧
      decode runtimeBytecode ⟨0x23⟩ = some (.GT, .none) ∧
      decode runtimeBytecode ⟨0x24⟩ = some (.OR, .none) ∧
      decode runtimeBytecode ⟨0x25⟩ = some (.Push .PUSH2, some (⟨0x1b4⟩, 2)) ∧
      decode runtimeBytecode ⟨0x28⟩ = some (.JUMPI, .none) := by
    simpa only [List.cons.injEq, and_true] using boundDecodes
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10,
    hd11, hd12⟩
  have rd := evm_run rd0 with [
    known push2 hd0 ⟨1024⟩,
    known dup4 hd1,
    known gt hd2,
    known push2 hd3 ⟨1024⟩,
    known dup3 hd4,
    known gt hd5,
    known or hd6,
    known push2 hd7 ⟨1024⟩,
    known dup4 hd8,
    known gt hd9,
    known or hd10,
    known push2 hd11 ⟨0x1b4⟩,
    known jumpiNT hd12 (by
      simp only [hb1024, he1024, hm1024]
      native_decide) ]
  exact ⟨_, rd⟩

private theorem reachBaseSizeChecked {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨0x33⟩
      [UInt256.isZero (UInt256.gt (exponentSizeWord I) ⟨32⟩),
        exponentSizeWord I, baseSizeWord I, modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 156 := by
  obtain ⟨k, rd0⟩ := reachBoundsPassed (g := g) hcode hvalue
    (le_trans hb (by decide)) (le_trans he (by decide)) (le_trans hm (by decide))
  rcases wordDispatchFacts with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8,
    hd9, hd10, hd11, hd12, hd13, hd14, _⟩
  have hb32 := size_gt_32_zero hb
  have rd := evm_run rd0 with [
    known push1 hd0 ⟨32⟩,
    known dup3 hd1,
    known gt hd2,
    known iszero hd3,
    known dup1 hd4,
    known push2 hd5 ⟨0x1a9⟩,
    known jumpiT hd6 (by rw [hb32]; native_decide) jumpDest_1a9,
    known jumpdest hd7,
    known pop hd8,
    known push1 hd9 ⟨32⟩,
    known dup2 hd10,
    known gt hd11,
    known iszero hd12,
    known push2 hd13 ⟨0x33⟩,
    known jump hd14 jumpDest_33 ]
  exact ⟨_, rd⟩

private theorem reachExponentSizeChecked {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨0x19e⟩
      [UInt256.isZero (UInt256.gt (exponentSizeWord I) ⟨32⟩),
        exponentSizeWord I, baseSizeWord I, modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 173 := by
  obtain ⟨k, rd0⟩ := reachBaseSizeChecked (g := g) hcode hvalue hb he hm
  rcases wordDispatchFacts with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd15,
    hd16, hd17, hd18, _⟩
  have he32 := size_gt_32_zero he
  have rd := evm_run rd0 with [
    known jumpdest hd15,
    known dup1 hd16,
    known push2 hd17 ⟨0x19e⟩,
    known jumpiT hd18 (by rw [he32]; native_decide) jumpDest_19e ]
  exact ⟨_, rd⟩

private theorem reachWordPathCore {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨0x12e⟩ [exponentSizeWord I, baseSizeWord I, modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 213 := by
  obtain ⟨k, rd0⟩ := reachExponentSizeChecked (g := g) hcode hvalue hb he hm
  rcases wordDispatchFacts with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hd19, hd20, hd21, hd22, hd23, hd24, hd25, hd26, hd27, hd28, hd29⟩
  have hm32 := size_gt_32_zero hm
  have rd := evm_run rd0 with [
    known jumpdest hd19,
    known pop hd20,
    known push1 hd21 ⟨32⟩,
    known dup4 hd22,
    known gt hd23,
    known iszero hd24,
    known push2 hd25 ⟨0x39⟩,
    known jump hd26 jumpDest_39,
    known jumpdest hd27,
    known push2 hd28 ⟨0x12e⟩,
    known jumpiT hd29 (by rw [hm32]; native_decide) jumpDest_12e ]
  exact ⟨_, rd⟩

/-- Exact entry and length-parser trace to the stack-only implementation at PC `0x12e`. -/
theorem reachWordPath {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hvalue : I.weiValue = ⟨0⟩)
    (hb : (baseSizeWord I).toNat ≤ 32)
    (he : (exponentSizeWord I).toNat ≤ 32)
    (hm : (modulusSizeWord I).toNat ≤ 32) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨0x12e⟩
      [exponentSizeWord I, baseSizeWord I, modulusSizeWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 213 := by
  exact reachWordPathCore hcode hvalue hb he hm
/-
  obtain ⟨k, rdHeader⟩ := reachBoundsPassed (g := g) hcode hvalue hb he hm
  have hb32 := size_gt_32_zero hb
  have he32 := size_gt_32_zero he
  have hm32 := size_gt_32_zero hm
  have hd :
      decode runtimeBytecode ⟨0x29⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) ∧
      decode runtimeBytecode ⟨0x2b⟩ = some (.DUP3, .none) ∧
      decode runtimeBytecode ⟨0x2c⟩ = some (.GT, .none) ∧
      decode runtimeBytecode ⟨0x2d⟩ = some (.ISZERO, .none) ∧
      decode runtimeBytecode ⟨0x2e⟩ = some (.DUP1, .none) ∧
      decode runtimeBytecode ⟨0x2f⟩ = some (.Push .PUSH2, some (⟨0x1a9⟩, 2)) ∧
      decode runtimeBytecode ⟨0x32⟩ = some (.JUMPI, .none) ∧
      decode runtimeBytecode ⟨0x1a9⟩ = some (.JUMPDEST, .none) ∧
      decode runtimeBytecode ⟨0x1aa⟩ = some (.POP, .none) ∧
      decode runtimeBytecode ⟨0x1ab⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) ∧
      decode runtimeBytecode ⟨0x1ad⟩ = some (.DUP2, .none) ∧
      decode runtimeBytecode ⟨0x1ae⟩ = some (.GT, .none) ∧
      decode runtimeBytecode ⟨0x1af⟩ = some (.ISZERO, .none) ∧
      decode runtimeBytecode ⟨0x1b0⟩ = some (.Push .PUSH2, some (⟨0x33⟩, 2)) ∧
      decode runtimeBytecode ⟨0x1b3⟩ = some (.JUMP, .none) ∧
      decode runtimeBytecode ⟨0x33⟩ = some (.JUMPDEST, .none) ∧
      decode runtimeBytecode ⟨0x34⟩ = some (.DUP1, .none) ∧
      decode runtimeBytecode ⟨0x35⟩ = some (.Push .PUSH2, some (⟨0x19e⟩, 2)) ∧
      decode runtimeBytecode ⟨0x38⟩ = some (.JUMPI, .none) ∧
      decode runtimeBytecode ⟨0x19e⟩ = some (.JUMPDEST, .none) ∧
      decode runtimeBytecode ⟨0x19f⟩ = some (.POP, .none) ∧
      decode runtimeBytecode ⟨0x1a0⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) ∧
      decode runtimeBytecode ⟨0x1a2⟩ = some (.DUP4, .none) ∧
      decode runtimeBytecode ⟨0x1a3⟩ = some (.GT, .none) ∧
      decode runtimeBytecode ⟨0x1a4⟩ = some (.ISZERO, .none) ∧
      decode runtimeBytecode ⟨0x1a5⟩ = some (.Push .PUSH2, some (⟨0x39⟩, 2)) ∧
      decode runtimeBytecode ⟨0x1a8⟩ = some (.JUMP, .none) ∧
      decode runtimeBytecode ⟨0x39⟩ = some (.JUMPDEST, .none) ∧
      decode runtimeBytecode ⟨0x3a⟩ = some (.Push .PUSH2, some (⟨0x12e⟩, 2)) ∧
      decode runtimeBytecode ⟨0x3d⟩ = some (.JUMPI, .none) := by
    have hdList :
        [decode runtimeBytecode ⟨0x29⟩, decode runtimeBytecode ⟨0x2b⟩,
          decode runtimeBytecode ⟨0x2c⟩, decode runtimeBytecode ⟨0x2d⟩,
          decode runtimeBytecode ⟨0x2e⟩, decode runtimeBytecode ⟨0x2f⟩,
          decode runtimeBytecode ⟨0x32⟩, decode runtimeBytecode ⟨0x1a9⟩,
          decode runtimeBytecode ⟨0x1aa⟩, decode runtimeBytecode ⟨0x1ab⟩,
          decode runtimeBytecode ⟨0x1ad⟩, decode runtimeBytecode ⟨0x1ae⟩,
          decode runtimeBytecode ⟨0x1af⟩, decode runtimeBytecode ⟨0x1b0⟩,
          decode runtimeBytecode ⟨0x1b3⟩, decode runtimeBytecode ⟨0x33⟩,
          decode runtimeBytecode ⟨0x34⟩, decode runtimeBytecode ⟨0x35⟩,
          decode runtimeBytecode ⟨0x38⟩, decode runtimeBytecode ⟨0x19e⟩,
          decode runtimeBytecode ⟨0x19f⟩, decode runtimeBytecode ⟨0x1a0⟩,
          decode runtimeBytecode ⟨0x1a2⟩, decode runtimeBytecode ⟨0x1a3⟩,
          decode runtimeBytecode ⟨0x1a4⟩, decode runtimeBytecode ⟨0x1a5⟩,
          decode runtimeBytecode ⟨0x1a8⟩, decode runtimeBytecode ⟨0x39⟩,
          decode runtimeBytecode ⟨0x3a⟩, decode runtimeBytecode ⟨0x3d⟩] =
        [some (.Push .PUSH1, some (⟨32⟩, 1)), some (.DUP3, .none), some (.GT, .none),
          some (.ISZERO, .none), some (.DUP1, .none),
          some (.Push .PUSH2, some (⟨0x1a9⟩, 2)), some (.JUMPI, .none),
          some (.JUMPDEST, .none), some (.POP, .none),
          some (.Push .PUSH1, some (⟨32⟩, 1)), some (.DUP2, .none), some (.GT, .none),
          some (.ISZERO, .none), some (.Push .PUSH2, some (⟨0x33⟩, 2)),
          some (.JUMP, .none), some (.JUMPDEST, .none), some (.DUP1, .none),
          some (.Push .PUSH2, some (⟨0x19e⟩, 2)), some (.JUMPI, .none),
          some (.JUMPDEST, .none), some (.POP, .none),
          some (.Push .PUSH1, some (⟨32⟩, 1)), some (.DUP4, .none), some (.GT, .none),
          some (.ISZERO, .none), some (.Push .PUSH2, some (⟨0x39⟩, 2)),
          some (.JUMP, .none), some (.JUMPDEST, .none),
          some (.Push .PUSH2, some (⟨0x12e⟩, 2)), some (.JUMPI, .none)] :=
      wordDispatchDecodes
    simpa only [List.cons.injEq, and_true] using hdList
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10,
    hd11, hd12, hd13, hd14, hd15, hd16, hd17, hd18, hd19, hd20, hd21, hd22,
    hd23, hd24, hd25, hd26, hd27, hd28, hd29⟩
  have rdBase := evm_run rdHeader with [
    known push1 hd0 ⟨32⟩,
    known dup3 hd1,
    known gt hd2,
    known iszero hd3,
    known dup1 hd4,
    known push2 hd5 ⟨0x1a9⟩,
    known jumpiT hd6 (by simp [hb32]) jumpDest_1a9,
    known jumpdest hd7,
    known pop hd8,
    known push1 hd9 ⟨32⟩,
    known dup2 hd10,
    known gt hd11,
    known iszero hd12,
    known push2 hd13 ⟨0x33⟩,
    known jump hd14 jumpDest_33 ]
  have rdExponent := evm_run rdBase with [
    known jumpdest hd15 ]
  have rd := evm_run rdExponent with [
    known dup1 hd16,
    known push2 hd17 ⟨0x19e⟩,
    known jumpiT hd18 (by simp [he32]) jumpDest_19e,
    known jumpdest hd19,
    known pop hd20,
    known push1 hd21 ⟨32⟩,
    known dup4 hd22,
    known gt hd23,
    known iszero hd24,
    known push2 hd25 ⟨0x39⟩,
    known jump hd26 jumpDest_39,
    known jumpdest hd27,
    known push2 hd28 ⟨0x12e⟩,
    known jumpiT hd29 (by simp [hm32]) jumpDest_12e ]
  exact ⟨_, rd⟩
-/

end Modexp
