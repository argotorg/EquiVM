import TruthClaude.Theory
import TruthClaude.Stepping
import TruthClaude.Memory
import TruthClaude.Pow

/-!
# PowCorrect — runtime equivalence for `Pow.sol`'s `pow2(uint256 n)`

Mirrors `TruthCorrect.lean`, but the contract has a function argument and a **`while` loop** over a
symbolic `n` (computing `2^n`, guarded `n < 256`).  This is the first loop example; we build it
Truth-style and factor reusable / solc-boilerplate lemmas out as they emerge.
-/

open Act ABI Ethereum Ethereum.EVM TruthClaude.Theory

set_option maxRecDepth 10000

/-- The deployed runtime bytecode of `Pow.sol` (solc 0.8.35, Shanghai, optimizer off, no metadata). -/
def powBytecode : ByteArray :=
  ⟨#[96, 128, 96, 64, 82, 52, 128, 21, 97, 0, 15, 87, 95, 95, 253, 91, 80, 96, 4, 54, 16, 97, 0, 41,
    87, 95, 53, 96, 224, 28, 128, 99, 68, 43, 127, 251, 20, 97, 0, 45, 87, 91, 95, 95, 253, 91, 97,
    0, 71, 96, 4, 128, 54, 3, 129, 1, 144, 97, 0, 66, 145, 144, 97, 0, 207, 86, 91, 97, 0, 93, 86,
    91, 96, 64, 81, 97, 0, 84, 145, 144, 97, 1, 9, 86, 91, 96, 64, 81, 128, 145, 3, 144, 243, 91,
    95, 97, 1, 0, 130, 16, 97, 0, 107, 87, 95, 95, 253, 91, 95, 96, 1, 144, 80, 95, 95, 144, 80, 91,
    131, 129, 16, 21, 97, 0, 142, 87, 96, 2, 130, 2, 145, 80, 96, 1, 129, 1, 144, 80, 97, 0, 117,
    86, 91, 129, 146, 80, 80, 80, 145, 144, 80, 86, 91, 95, 95, 253, 91, 95, 129, 144, 80, 145, 144,
    80, 86, 91, 97, 0, 174, 129, 97, 0, 156, 86, 91, 129, 20, 97, 0, 184, 87, 95, 95, 253, 91, 80,
    86, 91, 95, 129, 53, 144, 80, 97, 0, 201, 129, 97, 0, 165, 86, 91, 146, 145, 80, 80, 86, 91, 95,
    96, 32, 130, 132, 3, 18, 21, 97, 0, 228, 87, 97, 0, 227, 97, 0, 152, 86, 91, 91, 95, 97, 0, 241,
    132, 130, 133, 1, 97, 0, 187, 86, 91, 145, 80, 80, 146, 145, 80, 80, 86, 91, 97, 1, 3, 129, 97,
    0, 156, 86, 91, 130, 82, 80, 80, 86, 91, 95, 96, 32, 130, 1, 144, 80, 97, 1, 28, 95, 131, 1,
    132, 97, 0, 250, 86, 91, 146, 145, 80, 80, 86]⟩

/-- Configuration: empty storage layout, default external-call ABI (same as `truthConfig`). -/
def powConfig : Config :=
  { storage := { layout := fun _ => none }
    externalABI := defaultExternalCallABI }

/-! ## Trusted axioms (same two opaque ones as Truth; see MISSPEC.md) -/

/-- `keccak("pow2(uint256)")[0:4] = 0x442b7ffb`. -/
axiom powSelectorBytes :
    (ffi.KEC (String.toByteArray (Act.transitionSigStr Pow.powTransition))).extract 0 4
      = ⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩

/-- The `JUMPDEST` set of `powBytecode` (confirmed by `#eval`; `D_J_aux` is `partial`). -/
axiom powValidJumps :
    Ethereum.EVM.D_J powBytecode ⟨0⟩
      = #[⟨15⟩, ⟨41⟩, ⟨45⟩, ⟨66⟩, ⟨71⟩, ⟨84⟩, ⟨93⟩, ⟨107⟩, ⟨117⟩, ⟨142⟩, ⟨152⟩, ⟨156⟩, ⟨165⟩,
          ⟨174⟩, ⟨184⟩, ⟨187⟩, ⟨201⟩, ⟨207⟩, ⟨227⟩, ⟨228⟩, ⟨241⟩, ⟨250⟩, ⟨259⟩, ⟨265⟩, ⟨284⟩]

/-! ## The loop core (crux)

The `while (i < n) { r *= 2; i += 1; }` loop: header `0x75 = 117`, body `0x7e–0x8d`, exit `0x8e =
142`.  Stack at the header is `[i, r, _, n, ret]`; one iteration maps it to `[i+1, r*2, _, n, ret]`.

This is the reusable shape of a loop combinator: an invariant (`r = 2^i ∧ i ≤ n`), a variant
(`n − i`), and the OOG-or-reach-exit conclusion, anchored to `s0` with the `(k, C)` gas discipline.
Proved by induction on the variant; each iteration is a finite `stepContinue` chain.  PROOF TODO. -/
theorem powLoopCore {g : UInt256} {s0 : State} {slot n ret : UInt256} (hn : n.toNat < 256) :
    ∀ (var : ℕ) (i r : UInt256) (k C : ℕ) (s : State),
      n.toNat - i.toNat = var →
      r.toNat = 2 ^ i.toNat → i.toNat ≤ n.toNat →
      s.executionEnv.code = powBytecode →
      s.machineState.pc = ⟨117⟩ →
      s.machineState.stack = [i, r, slot, n, ret] →
      s.machineState.gasAvailable.toNat = g.toNat - C → k ≤ C → C ≤ g.toNat →
      X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J powBytecode ⟨0⟩) s →
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .error .OutOfGass
      ∨ ∃ (k' C' : ℕ) (s' : State),
          X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k') (D_J powBytecode ⟨0⟩) s'
        ∧ s'.executionEnv.code = powBytecode ∧ s'.machineState.pc = ⟨142⟩
        ∧ s'.machineState.stack = [n, ⟨2 ^ n.toNat⟩, slot, n, ret]
        ∧ s'.machineState.gasAvailable.toNat = g.toNat - C' ∧ k' ≤ C' ∧ C' ≤ g.toNat := by
  sorry
