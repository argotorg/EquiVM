import TruthClaude.Theory
import TruthClaude.Stepping
import TruthClaude.Memory
import TruthClaude.Solc
import TruthClaude.Pow
import TruthClaude.Reach

/-!
# PowCorrect — runtime equivalence for `Pow.sol`'s `pow2(uint256 n)`

Mirrors `TruthCorrect.lean`, but the contract has a function argument and a **`while` loop** over a
symbolic `n` (computing `2^n`, guarded `n < 256`).  This is the first loop example; we build it
Truth-style and factor reusable / solc-boilerplate lemmas out as they emerge.
-/

open Act ABI Ethereum Ethereum.EVM TruthClaude.Theory TruthClaude.Reach

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

/-- **Selector decode for `pow2`** (instance of the generic `evmSelectorDecode`): the EVM check
    `eq(0x442b7ffb, SHR(calldataload 0, 224))` equals the dispatcher's 4-byte compare. -/
theorem powEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨1143701499⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0x44 0x2b 0x7f 0xfb ⟨1143701499⟩ (by decide)

/-! ## The loop core (crux) — **proved**

`while (i < n) { r *= 2; i += 1; }`: header `0x75 = 117`, body `0x7e–0x8d`, exit `0x8e = 142`.
Invariant `r = 2^i ∧ i ≤ n < 256`, variant `n − i`.  Proved by induction on the variant; the base
case (`i = n`) is the 7-step guard ending in the taken `JUMPI` to the exit, and each inductive step
is the 19-step body (guard not taken → `r*=2; i+=1` → back-jump) followed by the IH.  The gas `C`
is carried *symbolically* (it grows by 67 per iteration); the OOG-absorbing disjunction means we
never need a closed-form total — confirming the symbolic-gas-under-induction story. -/

namespace TruthClaude.Reach

/-- The `pow2` loop `0x75 → 0x8e` as an **`RD` combinator**, by induction on the variant `n − i`.
    Entry invariant `RD … ⟨117⟩ (i :: r :: slot :: n :: REST)` with `r = 2^i`, `i ≤ n < 256`;
    produces `RD … ⟨142⟩ (n :: 2^n :: slot :: n :: REST)` for *some* step/gas counters (existential,
    since they grow by 19 steps / 67 gas per iteration).  The base case (`i = n`) is the 7-step guard
    ending in the taken `JUMPI` to the exit; each inductive step is the 19-step body (guard not taken →
    `r*=2; i+=1` → back-jump) feeding the IH.  This replaces the hand-written straight-line stepping
    with the `RD` combinator chain — the loop is now *inside* `Reach`. -/
theorem RD.loop {g : UInt256} {s0 : State} {ee : ExecutionEnv} {slot n : UInt256}
    {REST : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hn : n.toNat < 256) (hRov : REST.length + 20 ≤ 1024) :
    ∀ (var : ℕ) (i r : UInt256) (k C : ℕ),
      n.toNat - i.toNat = var → r.toNat = 2 ^ i.toNat → i.toNat ≤ n.toNat →
      RD powBytecode ee g s0 ⟨117⟩ (i :: r :: slot :: n :: REST) mem aw acc k C →
      ∃ (k' C' : ℕ),
        RD powBytecode ee g s0 ⟨142⟩
          (n :: UInt256.ofNat (2 ^ n.toNat) :: slot :: n :: REST) mem aw acc k' C' := by
  intro var
  induction var with
  | zero =>
    intro i r k C hvar hinv hile h
    have hin : i.toNat = n.toNat := by omega
    have hieqn : i = n := u256_inj hin
    have hreq : r = UInt256.ofNat (2 ^ n.toNat) :=
      u256_inj (by rw [hinv, hin, ofNat_pow_toNat hn])
    -- guard (7 steps): the `JUMPI` is **taken** (`i = n` ⇒ `iszero (lt i n) = 1 ≠ 0`)
    have rd := h.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.dup4 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.dup2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.lt (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.iszero (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.push2 ⟨142⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.jumpiT (by decide)
        (by rw [show UInt256.lt i n = ⟨0⟩ from ult_zero (by omega)]; decide)
        (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by first | (simp only [List.length_cons]; omega) | omega)
    rw [hieqn, hreq] at rd
    exact ⟨_, _, rd⟩
  | succ var ih =>
    intro i r k C hvar hinv hile h
    have hilt : i.toNat < n.toNat := by omega
    have hi1size : i.toNat + 1 < UInt256.size := lt_size_of_lt256 (by omega)
    have hi1 : (i + ⟨1⟩).toNat = i.toNat + 1 := add1_toNat hi1size
    have hr2size : 2 * r.toNat < UInt256.size := by
      rw [hinv, show 2 * 2 ^ i.toNat = 2 ^ (i.toNat + 1) from by rw [pow_succ]; ring]
      exact pow_lt_size (by omega)
    have hr2 : (UInt256.mul r ⟨2⟩).toNat = 2 * r.toNat := mul2_toNat hr2size
    -- guard (7 steps, `JUMPI` not taken: `i < n` ⇒ `iszero (lt i n) = 0`) then the 12-step body
    have rd := h.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.dup4 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.dup2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.lt (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.iszero (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.push2 ⟨142⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.jumpiNT (by decide)
        (by rw [show UInt256.lt i n = ⟨1⟩ from ult_one hilt]; decide)
        (by first | (simp only [List.length_cons]; omega) | omega)
      |>.push1 ⟨2⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.dup3 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.mul (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.swap2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.push1 ⟨1⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.dup2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.add (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.swap1 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.push2 ⟨117⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.jump (by decide)
        (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by first | (simp only [List.length_cons]; omega) | omega)
    exact ih (i + ⟨1⟩) (UInt256.mul r ⟨2⟩) _ _
      (by rw [hi1]; omega) (by rw [hr2, hi1, hinv, pow_succ]; ring) (by rw [hi1]; omega) rd

end TruthClaude.Reach

/-! ## The dispatcher (success path) — reaches the function body at `0x2d`

`callvalue = 0`, `calldatasize ≥ 4`, selector matches `0x442b7ffb`: 24 instructions from
`initState` to the `JUMPDEST` at `0x2d = 45`, leaving the decoded selector word on the stack and
the free-pointer memory in place.  Mirrors `truthX_cvz_*` but with PUSH2 jump targets. -/
/-- **Dispatcher prefix → the selector `EQ` (pc 37).**  Contract-agnostic of whether the selector
    matches: reaches pc 37 with `[eq(0x442b7ffb, sel), sel]` on the stack (`sel` = the decoded
    4-byte selector).  Shared by the `match` path (`powX_disp`) and the `nomatch` revert. -/
theorem powX_dispToEq {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass
      ∨ ∃ s, (X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I)
                = X (g.toNat + 1 - 22) (D_J powBytecode ⟨0⟩) s)
           ∧ s.executionEnv = I ∧ s.machineState.pc = ⟨37⟩
           ∧ s.machineState.gasAvailable.toNat = g.toNat - 83
           ∧ s.machineState.stack
               = [UInt256.eq ⟨1143701499⟩
                    (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩),
                  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
           ∧ s.machineState.activeWords = UInt256.ofNat 3
           ∧ s.machineState.memory = solcFreePtrMem ∧ 83 ≤ g.toNat
           ∧ ((s.createdAccounts, s.accountMap) = (cA, σ)) := by
  have hsztoNat : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size := by
    show (Fin.ofNat _ I.calldata.size).val = I.calldata.size
    simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hsize
  have hlt0 : UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩ = ⟨0⟩ :=
    ult_zero (by rw [hsztoNat]; exact le_trans (show (⟨4⟩ : UInt256).toNat ≤ 4 by decide) hsz)
  rcases solcGuardPrologue (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    with hoog | ⟨s6, hX6, hee6, hpc6, hgas6, hstk6raw, haw6, hmem6, hg26, hacc6⟩
  · exact Or.inl hoog
  have hcode6 : s6.executionEnv.code = powBytecode := by rw [hee6]; exact hcode
  have hstk6 : s6.machineState.stack = [⟨1⟩, ⟨0⟩] := by
    rw [hstk6raw, hwv, show UInt256.isZero ⟨0⟩ = ⟨1⟩ from by decide]
  -- steps 6–21: PUSH2·JUMPI(t)·JUMPDEST·POP·PUSH1·CALLDATASIZE·LT·PUSH2·JUMPI(nt)·PUSH0·
  --             CALLDATALOAD·PUSH1·SHR·DUP1·PUSH4·EQ, reaching the selector compare at pc 37
  rcases (RD.startWith hcode6 hpc6 hstk6 hgas6 (by omega) hg26 hX6 hmem6 haw6 hacc6 hee6
      |>.push2 ⟨15⟩ (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.jumpiT (by decide) (by decide)
        (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by simp only [List.length_cons, List.length_nil]; omega)
      |>.jumpdest (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.pop (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.push1 ⟨4⟩ (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.calldatasize (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.lt (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.push2 ⟨41⟩ (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.jumpiNT (by decide) hlt0 (by simp only [List.length_cons, List.length_nil]; omega)
      |>.push0 (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.calldataload (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.push1 ⟨224⟩ (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.shr (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.dup1 (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.push4 ⟨1143701499⟩ (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
      |>.eq (by decide) (by simp only [List.length_cons, List.length_nil]; omega)).out
    with hoog | ⟨s, hX, _hc, hp, hstk, hg, _hk, hCg, hmem, haw, hacc, hee⟩
  · exact Or.inl hoog
  · refine Or.inr ⟨s, hX, hee, hp, hg, ?_, haw, hmem, hCg, hacc⟩
    rw [hstk, show (⟨0⟩ : UInt256).toNat = 0 from by decide]




/-- **The dispatcher (match path).**  Reuses `powX_dispToEq`, then resolves the selector `EQ`
    to `1` (via `powEvmSelector` + `hmatch`) and takes the `JUMPI` to the function body at
    `0x2d = 45`.  Same statement as before the refactor; only the prefix is now shared. -/
theorem powX_disp {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass
      ∨ ∃ s, (X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I)
                = X (g.toNat + 1 - 24) (D_J powBytecode ⟨0⟩) s)
           ∧ s.executionEnv = I ∧ s.machineState.pc = ⟨45⟩
           ∧ s.machineState.gasAvailable.toNat = g.toNat - 96
           ∧ s.machineState.stack
               = [UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
           ∧ s.machineState.activeWords = UInt256.ofNat 3
           ∧ s.machineState.memory = solcFreePtrMem ∧ 96 ≤ g.toNat
           ∧ ((s.createdAccounts, s.accountMap) = (cA, σ)) := by
  rcases powX_dispToEq hcode hwv hsz hsize with
    hoog | ⟨s22, hX22, hee22, hpc22, hgas22, hstk22, haw22, hmem22, hg83, hacc22⟩
  · exact Or.inl hoog
  · set sel := UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ with hseldef
    have hcode22 : s22.executionEnv.code = powBytecode := by rw [hee22]; exact hcode
    have heq1 : UInt256.eq ⟨1143701499⟩ sel = ⟨1⟩ := by
      rw [hseldef, powEvmSelector hsz, if_pos hmatch]
    have hstk22' : s22.machineState.stack = [⟨1⟩, sel] := by rw [hstk22, heq1]
    -- PUSH2 0x2d · JUMPI (taken: selector match ⇒ eq = 1) → function body JUMPDEST at pc 45
    rcases (RD.startWith hcode22 hpc22 hstk22' hgas22 (by omega) hg83 hX22 hmem22 haw22 hacc22 hee22
        |>.push2 ⟨45⟩ (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
        |>.jumpiT (by decide) (by decide)
          (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
          (by simp only [List.length_cons, List.length_nil]; omega)).out
      with hoog | ⟨s, hX, _hc, hp, hstk, hg, _hk, hCg, hmem, haw, hacc, hee⟩
    · exact Or.inl hoog
    · exact Or.inr ⟨s, hX, hee, hp, hg, hstk, haw, hmem, hCg, hacc⟩
