import TruthClaude.PowCorrect
import TruthClaude.Reach

/-! Scratch: develop Pow decode/encode segment lemmas, then move into PowCorrect. -/

open Act ABI Ethereum Ethereum.EVM TruthClaude.Theory TruthClaude.Reach

set_option maxRecDepth 10000

namespace TruthClaude.Reach

/-- solc routine `0x9c` (`cleanup_t_uint256`-style identity) as an **`RD→RD` combinator**: from
    `[v, ret, …R]` at pc 156, returns `v` to the dynamic address `ret`, leaving `[v, …R]`.
    9 instructions / gas 27; memory, active words, accounts and env untouched.  Chains directly
    inside callers (no `out`/`startWith` glue). -/
theorem RD.routine9c {g : UInt256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {v ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨156⟩ (v :: ret :: R) mem aw acc k C)
    (hret : (D_J powBytecode ⟨0⟩).contains ret = true) (hov : R.length + 4 ≤ 1024) :
    RD powBytecode ee g s0 ret (v :: R) mem aw acc (k + 9) (C + 27) :=
  -- JUMPDEST · PUSH0 · DUP2 · SWAP1 · POP · SWAP2 · SWAP1 · POP · JUMP
  h |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push0 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.dup2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.swap1 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.swap2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.swap1 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jump (by decide) hret (by first | (simp only [List.length_cons]; omega) | omega)

end TruthClaude.Reach

/-- Old-form wrapper around `RD.routine9c` (for callers not yet migrated to the `RD` fold). -/
theorem powRoutine_9c {g : UInt256} {s0 s : State} {k C : ℕ} {v ret : UInt256} {R : List UInt256}
    (hcode : s.executionEnv.code = powBytecode) (hpc : s.machineState.pc = ⟨156⟩)
    (hstk : s.machineState.stack = v :: ret :: R)
    (hret : (D_J powBytecode ⟨0⟩).contains ret = true) (hov : R.length + 4 ≤ 1024)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J powBytecode ⟨0⟩) s) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .error .OutOfGass
      ∨ ∃ (k' C' : ℕ) (s' : State),
          X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k') (D_J powBytecode ⟨0⟩) s'
        ∧ s'.executionEnv.code = powBytecode ∧ s'.machineState.pc = ret
        ∧ s'.machineState.stack = v :: R
        ∧ s'.machineState.gasAvailable.toNat = g.toNat - C' ∧ k' ≤ C' ∧ C' ≤ g.toNat
        ∧ s'.machineState.memory = s.machineState.memory
        ∧ s'.machineState.activeWords = s.machineState.activeWords
        ∧ ((s'.createdAccounts, s'.accountMap) = (s.createdAccounts, s.accountMap)) :=
  (RD.start hcode hpc hstk hgas hk hC hX |>.routine9c hret hov).conclude

namespace TruthClaude.Reach

/-- solc routine `0xa5` (`abi_decode`'s validator) as an **`RD→RD` combinator**: entry at pc 165
    with `[arg, ret, …R]`, calls `0x9c` to clean `arg`, checks `arg == cleanup(arg)` (always true
    for uint256), returns to `ret` leaving `[…R]`.  The `0x9c` call is now a direct `.routine9c`
    chain — no `out`/`startWith` glue.  22 instructions / gas 76. -/
theorem RD.routinea5 {g : UInt256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {arg ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨165⟩ (arg :: ret :: R) mem aw acc k C)
    (hret : (D_J powBytecode ⟨0⟩).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    RD powBytecode ee g s0 ret R mem aw acc (k + 22) (C + 76) :=
  -- JUMPDEST·PUSH2 174·DUP2·PUSH2 156·JUMP → 0x9c → JUMPDEST·DUP2·EQ·PUSH2 184·JUMPI·JUMPDEST·POP·JUMP
  h |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push2 ⟨174⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.dup2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push2 ⟨156⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jump (by decide) (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by first | (simp only [List.length_cons]; omega) | omega)
    |>.routine9c (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.dup2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.eq (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push2 ⟨184⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jumpiT (by decide) (by rw [u256_eq_refl]; exact one_ne_zero_uint)
        (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jump (by decide) hret (by first | (simp only [List.length_cons]; omega) | omega)


/-- solc routine `0xbb` (`abi_decode_uint256`) as an **`RD→RD` combinator**: entry at pc 187 with
    `[offset, end, ret, …R]`, loads `calldata[offset]` (off the carried env `ee`), validates it via
    `0xa5` (a direct `.routinea5` chain), returns it to `ret` leaving `[calldata[offset], …R]`.
    38 instructions / gas 126. -/
theorem RD.routinebb {g : UInt256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {offset ennd ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨187⟩ (offset :: ennd :: ret :: R) mem aw acc k C)
    (hret : (D_J powBytecode ⟨0⟩).contains ret = true) (hov : R.length + 10 ≤ 1024) :
    RD powBytecode ee g s0 ret
        (uInt256OfByteArray (ee.calldata.readBytes offset.toNat 32) :: R) mem aw acc (k + 38) (C + 126) :=
  -- JUMPDEST·PUSH0·DUP2·CALLDATALOAD·SWAP1·POP·PUSH2 201·DUP2·PUSH2 165·JUMP → 0xa5 → JUMPDEST·SWAP3·SWAP2·POP·POP·JUMP
  h |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push0 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.dup2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.calldataload (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.swap1 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push2 ⟨201⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.dup2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push2 ⟨165⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jump (by decide) (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by first | (simp only [List.length_cons]; omega) | omega)
    |>.routinea5 (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.swap3 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.swap2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jump (by decide) hret (by first | (simp only [List.length_cons]; omega) | omega)

end TruthClaude.Reach

/-- `SUB` of `ofNat sz` and `4` is `sz - 4` (no wrap), for `4 ≤ sz < size`. -/
theorem sub4_toNat {sz : ℕ} (h4 : 4 ≤ sz) (hsz : sz < UInt256.size) :
    (UInt256.sub (UInt256.ofNat sz) ⟨4⟩).toNat = sz - 4 := by
  have h1 : (UInt256.ofNat sz).toNat = sz := by
    show (Fin.ofNat _ sz).val = sz; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hsz
  have hrw : UInt256.sub (UInt256.ofNat sz) ⟨4⟩ = UInt256.ofNat sz - UInt256.ofNat 4 := rfl
  rw [hrw, toNat_sub_ofNat (by rw [h1]; exact h4), h1]

/-- `SLT a 32 = 0` (signed) when `32 ≤ a < 2^255`. -/
theorem slt32_zero {a : UInt256} (hlo : 32 ≤ a.toNat) (hhi : a.toNat < 2 ^ 255) :
    UInt256.slt a ⟨32⟩ = ⟨0⟩ := by
  have h32 : (⟨32⟩ : UInt256).toNat = 32 := by
    show (Fin.ofNat _ 32).val = 32; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))
  have hbool : UInt256.sltBool a ⟨32⟩ = false := by
    unfold UInt256.sltBool
    rw [if_neg (show ¬ a.toNat ≥ 2 ^ 255 by omega),
        if_neg (show ¬ (⟨32⟩ : UInt256).toNat ≥ 2 ^ 255 by rw [h32]; norm_num)]
    exact decide_eq_false (show ¬ a < ⟨32⟩ by
      show ¬ a.toNat < (⟨32⟩ : UInt256).toNat; rw [h32]; omega)
  show UInt256.fromBool (UInt256.sltBool a ⟨32⟩) = ⟨0⟩
  rw [hbool]; rfl

/-- `SLT a 32 = 1` (signed) when `a < 32` (so `a` is non-negative). -/
theorem slt32_one {a : UInt256} (hlo : a.toNat < 32) :
    UInt256.slt a ⟨32⟩ = ⟨1⟩ := by
  have hhi : a.toNat < 2 ^ 255 := by omega
  have h32 : (⟨32⟩ : UInt256).toNat = 32 := by
    show (Fin.ofNat _ 32).val = 32; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))
  have hbool : UInt256.sltBool a ⟨32⟩ = true := by
    unfold UInt256.sltBool
    rw [if_neg (show ¬ a.toNat ≥ 2 ^ 255 by omega),
        if_neg (show ¬ (⟨32⟩ : UInt256).toNat ≥ 2 ^ 255 by rw [h32]; norm_num)]
    exact decide_eq_true (show a < ⟨32⟩ by
      show a.toNat < (⟨32⟩ : UInt256).toNat; rw [h32]; omega)
  show UInt256.fromBool (UInt256.sltBool a ⟨32⟩) = ⟨1⟩
  rw [hbool]; rfl

/-- `SLT a 32 = 1` (signed) when `a ≥ 2^255` (so `a` is negative two's-complement).  This is the
    *high* reason solc's decoder bounds-check reverts: a calldata so large that `calldatasize − 4`
    has its sign bit set. -/
theorem slt32_one_high {a : UInt256} (hhi : 2 ^ 255 ≤ a.toNat) :
    UInt256.slt a ⟨32⟩ = ⟨1⟩ := by
  have h32 : (⟨32⟩ : UInt256).toNat = 32 := by
    show (Fin.ofNat _ 32).val = 32; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))
  have hbool : UInt256.sltBool a ⟨32⟩ = true := by
    unfold UInt256.sltBool
    rw [if_pos (show a.toNat ≥ 2 ^ 255 by omega),
        if_neg (show ¬ (⟨32⟩ : UInt256).toNat ≥ 2 ^ 255 by rw [h32]; norm_num)]
  show UInt256.fromBool (UInt256.sltBool a ⟨32⟩) = ⟨1⟩
  rw [hbool]; rfl

/-- `ADD` of two in-range literals does not wrap. -/
theorem add_lit_toNat {a b : ℕ} (ha : a < UInt256.size) (hb : b < UInt256.size)
    (h : a + b < UInt256.size) :
    (UInt256.add (UInt256.ofNat a) (UInt256.ofNat b)).toNat = a + b := by
  have hav : (UInt256.ofNat a).toNat = a := by
    show (Fin.ofNat _ a).val = a; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt ha
  have hbv : (UInt256.ofNat b).toNat = b := by
    show (Fin.ofNat _ b).val = b; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hb
  show ((UInt256.ofNat a).val + (UInt256.ofNat b).val).val = a + b
  rw [Fin.add_def]
  show ((UInt256.ofNat a).toNat + (UInt256.ofNat b).toNat) % UInt256.size = a + b
  rw [hav, hbv, Nat.mod_eq_of_lt h]

/-- `(⟨4⟩ + ⟨0⟩).toNat = 4`. -/
theorem add40_toNat : ((⟨4⟩ : UInt256) + ⟨0⟩).toNat = 4 := by
  have : (⟨4⟩ : UInt256) + ⟨0⟩ = UInt256.add (UInt256.ofNat 4) (UInt256.ofNat 0) := rfl
  rw [this, add_lit_toNat (lt_size_of_lt256 (by norm_num)) (lt_size_of_lt256 (by norm_num))
    (lt_size_of_lt256 (by norm_num))]

namespace TruthClaude.Reach

/-- solc routine `0xcf` (`abi_decode_tuple`'s bounds-checked decoder) as an **`RD→RD` combinator**:
    entry at pc 207 with `[4, size, ret, …R']`; when `SLT(size−4, 32) = 0` (enough calldata) it sets
    up offset `4+0` and calls `0xbb` (a direct `.routinebb` chain), returning `calldata[4:36]` to
    `ret`.  66 instructions / gas 215. -/
theorem RD.routinecf {g : UInt256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {de ret : UInt256} {R' : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨207⟩ (⟨4⟩ :: de :: ret :: R') mem aw acc k C)
    (hsltval : UInt256.slt (UInt256.sub de ⟨4⟩) ⟨32⟩ = ⟨0⟩)
    (hret : (D_J powBytecode ⟨0⟩).contains ret = true) (hov : R'.length + 15 ≤ 1024) :
    RD powBytecode ee g s0 ret
        (uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨0⟩).toNat 32) :: R')
        mem aw acc (k + 66) (C + 215) :=
  -- prologue (SLT=0 ⇒ ISZERO=1 ⇒ JUMPI taken) · set up offset · JUMP → 0xbb → rearrange · JUMP ret
  h |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push0 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push1 ⟨32⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.dup3 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.dup5 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.sub (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.slt (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.iszero (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push2 ⟨228⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jumpiT (by decide) (by rw [hsltval]; decide)
        (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push0 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push2 ⟨241⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.dup5 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.dup3 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.dup6 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.add (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push2 ⟨187⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jump (by decide) (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by first | (simp only [List.length_cons]; omega) | omega)
    |>.routinebb (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.swap2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.swap3 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.swap2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jump (by decide) hret (by first | (simp only [List.length_cons]; omega) | omega)

end TruthClaude.Reach

/-- **Decoder bounds check fails (`calldatasize < 36`)**: the signed `SLT(size−4, 32)` is `1`, so
    `ISZERO` is `0`, the `JUMPI` is not taken, and execution jumps to the revert routine at `0x98`.
    Shares the `0x cf` entry with `powRoutine_cf`; only the `SLT` value and the post-`JUMPI` tail
    differ. -/
theorem powRoutine_cf_revert {g : UInt256} {s0 s : State} {I : Ethereum.ExecutionEnv} {k C : ℕ}
    {ret : UInt256} {R' : List UInt256}
    (hcode : s.executionEnv.code = powBytecode) (hee : s.executionEnv = I)
    (hpc : s.machineState.pc = ⟨207⟩)
    (hstk : s.machineState.stack = ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R')
    (hsz4 : 4 ≤ I.calldata.size) (hszsize : I.calldata.size < UInt256.size)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩)
    (hov : R'.length + 15 ≤ 1024)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J powBytecode ⟨0⟩) s) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .error .OutOfGass
      ∨ ∃ g' o, X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .ok (.revert g' o) := by
  set de := UInt256.ofNat I.calldata.size with hde
  -- 207→153: same prologue as cf, but SLT=1 ⇒ ISZERO=0 ⇒ JUMPI not taken ⇒ fall through to revert routine
  rcases (RD.startWith hcode hpc hstk hgas hk hC hX rfl rfl rfl hee
      |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.push0 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.push1 ⟨32⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.dup3 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.dup5 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.sub (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.slt (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.iszero (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.push2 ⟨228⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.jumpiNT (by decide) (by rw [hsltval]; decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.push2 ⟨227⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.push2 ⟨152⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.jump (by decide) (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
          (by first | (simp only [List.length_cons]; omega) | omega)
      |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)).out
    with hoog | ⟨s14, hX14, hc14, hp14, hstk14, hg14, hkC14, hCg14, _hm, _ha, _hacc, _hee⟩
  · exact Or.inl hoog
  exact solcRevert0 hc14 hp14 (by decide) (by decide) (by decide) hstk14
    (by first | (simp only [List.length_cons]; omega) | omega) hg14 hkC14 hCg14 hX14

/-- General `ADD` toNat (mod size). -/
theorem uadd_toNat (a b : UInt256) : (a + b).toNat = (a.toNat + b.toNat) % UInt256.size := by
  show (a.val + b.val).val = (a.val.val + b.val.val) % UInt256.size
  rw [Fin.add_def]

/-- solc recomputes `dataEnd = headStart + (calldatasize − headStart) = calldatasize`. -/
theorem add_sub4 {sz : ℕ} (h4 : 4 ≤ sz) (hsz : sz < UInt256.size) :
    (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat sz) ⟨4⟩ = UInt256.ofNat sz := by
  apply u256_inj
  have h4t : (⟨4⟩ : UInt256).toNat = 4 := by
    show (Fin.ofNat _ 4).val = 4; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))
  have hsz' : (UInt256.ofNat sz).toNat = sz := by
    show (Fin.ofNat _ sz).val = sz; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hsz
  rw [uadd_toNat, h4t, sub4_toNat h4 hsz, hsz',
      show 4 + (sz - 4) = sz from by omega, Nat.mod_eq_of_lt hsz]

namespace TruthClaude.Reach

/-- **Call-setup prefix `0x2d → decoder entry 0x cf = 207`** as an **`RD→RD` combinator**: from
    `[sel]` at pc 45, reaches pc 207 with `[4, calldatasize, 0x42, 0x47, sel]`, ready for the
    decoder's bounds check.  14 instructions / gas 44.  (The `ADD` produces the raw `4 + (size−4)`,
    rewritten to `ofNat size` here so callers get the clean form.) -/
theorem RD.routinedecodeToCf {g : UInt256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {sel : UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨45⟩ [sel] mem aw acc k C)
    (hsz4 : 4 ≤ ee.calldata.size) (hszsize : ee.calldata.size < UInt256.size) :
    RD powBytecode ee g s0 ⟨207⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ⟨66⟩ :: ⟨71⟩ :: [sel]) mem aw acc (k + 14) (C + 44) := by
  -- 45→65: JUMPDEST·PUSH2 71·PUSH1 4·DUP1·CALLDATASIZE·SUB·DUP2·ADD·SWAP1·PUSH2 66·SWAP2·SWAP1·PUSH2 207·JUMP 207
  rw [show UInt256.ofNat ee.calldata.size
        = (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩
      from (add_sub4 hsz4 hszsize).symm]
  exact h |>.jumpdest (by decide) (by first | (simp only [List.length_cons, List.length_nil]; omega) | omega)
      |>.push2 ⟨71⟩ (by decide) (by first | (simp only [List.length_cons, List.length_nil]; omega) | omega)
      |>.push1 ⟨4⟩ (by decide) (by first | (simp only [List.length_cons, List.length_nil]; omega) | omega)
      |>.dup1 (by decide) (by first | (simp only [List.length_cons, List.length_nil]; omega) | omega)
      |>.calldatasize (by decide) (by first | (simp only [List.length_cons, List.length_nil]; omega) | omega)
      |>.sub (by decide) (by first | (simp only [List.length_cons, List.length_nil]; omega) | omega)
      |>.dup2 (by decide) (by first | (simp only [List.length_cons, List.length_nil]; omega) | omega)
      |>.add (by decide) (by first | (simp only [List.length_cons, List.length_nil]; omega) | omega)
      |>.swap1 (by decide) (by first | (simp only [List.length_cons, List.length_nil]; omega) | omega)
      |>.push2 ⟨66⟩ (by decide) (by first | (simp only [List.length_cons, List.length_nil]; omega) | omega)
      |>.swap2 (by decide) (by first | (simp only [List.length_cons, List.length_nil]; omega) | omega)
      |>.swap1 (by decide) (by first | (simp only [List.length_cons, List.length_nil]; omega) | omega)
      |>.push2 ⟨207⟩ (by decide) (by first | (simp only [List.length_cons, List.length_nil]; omega) | omega)
      |>.jump (by decide) (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
          (by first | (simp only [List.length_cons, List.length_nil]; omega) | omega)

end TruthClaude.Reach

/-- Old-form wrapper around `RD.routinedecodeToCf` (still used by the short-arg revert paths in
    `PowAct`).  Exposes `s'.executionEnv = I` via `concludeE`. -/
theorem powX_decodeToCf {g : UInt256} {s0 s : State} {I : Ethereum.ExecutionEnv} {k C : ℕ}
    {sel : UInt256}
    (hcode : s.executionEnv.code = powBytecode) (hee : s.executionEnv = I)
    (hpc : s.machineState.pc = ⟨45⟩) (hstk : s.machineState.stack = [sel])
    (hsz4 : 4 ≤ I.calldata.size) (hszsize : I.calldata.size < UInt256.size)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J powBytecode ⟨0⟩) s) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .error .OutOfGass
      ∨ ∃ (k' C' : ℕ) (s' : State),
          X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k') (D_J powBytecode ⟨0⟩) s'
        ∧ s'.executionEnv.code = powBytecode ∧ s'.executionEnv = I ∧ s'.machineState.pc = ⟨207⟩
        ∧ s'.machineState.stack
            = ⟨4⟩ :: UInt256.ofNat I.calldata.size :: ⟨66⟩ :: ⟨71⟩ :: [sel]
        ∧ s'.machineState.gasAvailable.toNat = g.toNat - C' ∧ k' ≤ C' ∧ C' ≤ g.toNat
        ∧ s'.machineState.memory = s.machineState.memory
        ∧ s'.machineState.activeWords = s.machineState.activeWords
        ∧ ((s'.createdAccounts, s'.accountMap) = (s.createdAccounts, s.accountMap)) :=
  (RD.startWith hcode hpc hstk hgas hk hC hX rfl rfl rfl hee
    |>.routinedecodeToCf hsz4 hszsize).concludeE

/-- Function body `0x2d`: set up and call the ABI decoder, returning at
    `0x42 = 66` with the decoded argument `n = calldata[4:36]` on the stack (`[n, ⟨71⟩, sel]`). -/
theorem powX_decode {g : UInt256} {s0 s : State} {I : Ethereum.ExecutionEnv} {k C : ℕ}
    {sel : UInt256}
    (hcode : s.executionEnv.code = powBytecode) (hee : s.executionEnv = I)
    (hpc : s.machineState.pc = ⟨45⟩) (hstk : s.machineState.stack = [sel])
    (hsz36 : 36 ≤ I.calldata.size) (hsz255 : I.calldata.size < 2 ^ 255 + 4)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J powBytecode ⟨0⟩) s) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .error .OutOfGass
      ∨ ∃ (k' C' : ℕ) (s' : State),
          X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k') (D_J powBytecode ⟨0⟩) s'
        ∧ s'.executionEnv.code = powBytecode ∧ s'.machineState.pc = ⟨66⟩
        ∧ s'.machineState.stack = uInt256OfByteArray (I.calldata.readBytes 4 32) :: ⟨71⟩ :: [sel]
        ∧ s'.machineState.gasAvailable.toNat = g.toNat - C' ∧ k' ≤ C' ∧ C' ≤ g.toNat
        ∧ s'.machineState.memory = s.machineState.memory
        ∧ s'.machineState.activeWords = s.machineState.activeWords
        ∧ ((s'.createdAccounts, s'.accountMap) = (s.createdAccounts, s.accountMap)) := by
  have hszsize : I.calldata.size < UInt256.size := by
    have hp : (2:ℕ)^255 + 4 < UInt256.size := by
      have : (2:ℕ)^255 + 4 < 2^256 := by norm_num
      simpa [UInt256.size] using this
    omega
  have hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ := by
    apply slt32_zero
    · rw [sub4_toNat (by omega) hszsize]; omega
    · rw [sub4_toNat (by omega) hszsize]; omega
  rw [show I.calldata.readBytes 4 32
        = I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨0⟩).toNat 32 from by rw [add40_toNat]]
  -- decode prefix (0x2d → 207) then the bounds-checked decoder 0xcf, composed as one RD fold
  exact (RD.startWith hcode hpc hstk hgas hk hC hX rfl rfl rfl hee
      |>.routinedecodeToCf (by omega) hszsize
      |>.routinecf hsltval (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
          (by simp only [List.length_cons, List.length_nil]; omega)).conclude

namespace TruthClaude.Reach

/-- `require(n < 256)` check (passes) as an **`RD→RD` combinator**: `0x42 → 0x75`, leaving
    `[0, 1, 0, n, 71, sel]` (initialises the loop's `r = 1, i = 0`).  19 instructions / gas 57. -/
theorem RD.routinerequire {g : UInt256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {n sel : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨66⟩ (n :: ⟨71⟩ :: sel :: R) mem aw acc k C)
    (hltval : UInt256.lt n ⟨256⟩ = ⟨1⟩) (hov : R.length + 10 ≤ 1024) :
    RD powBytecode ee g s0 ⟨117⟩ (⟨0⟩ :: ⟨1⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R)
        mem aw acc (k + 19) (C + 57) :=
  -- JUMPDEST·PUSH2 93·JUMP·JUMPDEST·PUSH0·PUSH2 256·DUP3·LT·PUSH2 107·JUMPI(taken)·JUMPDEST·PUSH0·PUSH1 1·SWAP1·POP·PUSH0·PUSH0·SWAP1·POP
  h |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push2 ⟨93⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jump (by decide) (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push0 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push2 ⟨256⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.dup3 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.lt (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push2 ⟨107⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jumpiT (by decide) (by rw [hltval]; exact one_ne_zero_uint)
        (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push0 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push1 ⟨1⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.swap1 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push0 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push0 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.swap1 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)

end TruthClaude.Reach

/-- Old-form wrapper around `RD.routinerequire`. -/
theorem powX_require {g : UInt256} {s0 s : State} {k C : ℕ} {n sel : UInt256} {R : List UInt256}
    (hcode : s.executionEnv.code = powBytecode) (hpc : s.machineState.pc = ⟨66⟩)
    (hstk : s.machineState.stack = n :: ⟨71⟩ :: sel :: R) (hn : n.toNat < 256)
    (hov : R.length + 10 ≤ 1024)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J powBytecode ⟨0⟩) s) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .error .OutOfGass
      ∨ ∃ (k' C' : ℕ) (s' : State),
          X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k') (D_J powBytecode ⟨0⟩) s'
        ∧ s'.executionEnv.code = powBytecode ∧ s'.machineState.pc = ⟨117⟩
        ∧ s'.machineState.stack = ⟨0⟩ :: ⟨1⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R
        ∧ s'.machineState.gasAvailable.toNat = g.toNat - C' ∧ k' ≤ C' ∧ C' ≤ g.toNat
        ∧ s'.machineState.memory = s.machineState.memory
        ∧ s'.machineState.activeWords = s.machineState.activeWords
        ∧ ((s'.createdAccounts, s'.accountMap) = (s.createdAccounts, s.accountMap)) := by
  have h256 : (⟨256⟩ : UInt256).toNat = 256 := by
    show (Fin.ofNat _ 256).val = 256; simp only [Fin.ofNat]
    have : (256:ℕ) < UInt256.size := by
      have := pow_lt_size (show (8:ℕ) < 256 by norm_num); norm_num at this; exact this
    exact Nat.mod_eq_of_lt this
  have hltval : UInt256.lt n ⟨256⟩ = ⟨1⟩ := ult_one (by rw [h256]; exact hn)
  exact (RD.start hcode hpc hstk hgas hk hC hX |>.routinerequire hltval hov).conclude

/-- **`require(n < 256)` fails (`n ≥ 256`)**: same prefix as `powX_require`, but `LT n 256 = 0`,
    so the `JUMPI` is not taken and execution reverts at `0x68`.  Reused (in the assembly) after
    the already-proved `powX_disp` + `powX_decode`. -/
theorem powX_require_revert {g : UInt256} {s0 s : State} {k C : ℕ} {n sel : UInt256}
    {R : List UInt256}
    (hcode : s.executionEnv.code = powBytecode) (hpc : s.machineState.pc = ⟨66⟩)
    (hstk : s.machineState.stack = n :: ⟨71⟩ :: sel :: R) (hn : 256 ≤ n.toNat)
    (hov : R.length + 10 ≤ 1024)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J powBytecode ⟨0⟩) s) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .error .OutOfGass
      ∨ ∃ g' o, X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .ok (.revert g' o) := by
  have h256 : (⟨256⟩ : UInt256).toNat = 256 := by
    show (Fin.ofNat _ 256).val = 256; simp only [Fin.ofNat]
    have : (256:ℕ) < UInt256.size := by
      have := pow_lt_size (show (8:ℕ) < 256 by norm_num); norm_num at this; exact this
    exact Nat.mod_eq_of_lt this
  have hltval : UInt256.lt n ⟨256⟩ = ⟨0⟩ := ult_zero (by rw [h256]; exact hn)
  -- 66→104: JUMPDEST·PUSH2 93·JUMP·JUMPDEST·PUSH0·PUSH2 256·DUP3·LT(=0)·PUSH2 107·JUMPI(not taken) ⇒ revert
  rcases (RD.start hcode hpc hstk hgas hk hC hX
      |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.push2 ⟨93⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.jump (by decide) (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
          (by first | (simp only [List.length_cons]; omega) | omega)
      |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.push0 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.push2 ⟨256⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.dup3 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.lt (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.push2 ⟨107⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      |>.jumpiNT (by decide) hltval (by first | (simp only [List.length_cons]; omega) | omega)).out
    with hoog | ⟨s10, hX10, hc10, hp10, hstk10, hg10, hkC10, hCg10, _hm, _ha, _hacc, _hee⟩
  · exact Or.inl hoog
  exact solcRevert0 hc10 hp10 (by decide) (by decide) (by decide) hstk10
    (by first | (simp only [List.length_cons]; omega) | omega) hg10 hkC10 hCg10 hX10

namespace TruthClaude.Reach

/-- Loop exit `0x8e → 0x47` as an **`RD→RD` combinator**: drop the loop scratch, keep the result
    `val = 2^n`, and jump to the encoder at the saved return address `ret`.
    `[a, val, c, d, ret] ++ Rt → at ret, val :: Rt`.  10 instructions / gas 29. -/
theorem RD.routineexit {g : UInt256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {a val c d ret : UInt256} {Rt : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨142⟩ (a :: val :: c :: d :: ret :: Rt) mem aw acc k C)
    (hret : (D_J powBytecode ⟨0⟩).contains ret = true) (hov : Rt.length + 7 ≤ 1024) :
    RD powBytecode ee g s0 ret (val :: Rt) mem aw acc (k + 10) (C + 29) :=
  -- JUMPDEST · DUP2 · SWAP3 · POP · POP · POP · SWAP2 · SWAP1 · POP · JUMP ret
  h |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.dup2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.swap3 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.swap2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.swap1 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.jump (by decide) hret (by first | (simp only [List.length_cons]; omega) | omega)

end TruthClaude.Reach

/-! ## Encoder memory: the result word stored at `0x80` -/

/-- Memory after solc stores the return word `val` at `0x80` (over the free-pointer memory). -/
noncomputable def powMem2 (val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 solcFreePtrMem 128 32

theorem powMem2_eq (val : UInt256) :
    powMem2 val = (solcFreePtrMem ++ ffi.ByteArray.zeroes (USize.ofNat 32)) ++ UInt256.toByteArray val := by
  rw [powMem2, toByteArray_write_eq _ _ _ (by rw [solcFreePtrMem_size]; omega)
        (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))]
  norm_num [solcFreePtrMem_size]

theorem powMem2_size (val : UInt256) : (powMem2 val).size = 160 := by
  rw [powMem2_eq, ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
      zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem solcFreePtrMem_pad_size :
    (solcFreePtrMem ++ ffi.ByteArray.zeroes (USize.ofNat 32)).size = 128 := by
  rw [ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size _ (by norm_num)]

theorem powMem2_read64 (val : UInt256) :
    (powMem2 val).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := powMem2_size val; omega), powMem2_eq,
      extract_append_left _ _ _ _ (by have := solcFreePtrMem_pad_size; omega),
      extract_append_left _ _ _ _ (by have := solcFreePtrMem_size; omega),
      ← readWithPadding_eq_extract _ _ (by have := solcFreePtrMem_size; omega), solcFreePtrMem_read64]

theorem powMem2_read128 (val : UInt256) :
    (powMem2 val).readWithPadding 128 32 = UInt256.toByteArray val := by
  rw [readWithPadding_eq_extract _ _ (by have := powMem2_size val; omega), powMem2_eq,
      extract_append_right' _ _ _ _ (by have := solcFreePtrMem_pad_size; omega)
        (by have := solcFreePtrMem_pad_size; have := toByteArray_size val; omega)]

/-- `(ofNat c).toNat = c` for in-range `c`. -/
theorem ulit_toNat' (c : ℕ) (h : c < UInt256.size) : (UInt256.ofNat c).toNat = c := by
  show (Fin.ofNat _ c).val = c; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt h

theorem u0 : (⟨0⟩ : UInt256).toNat = 0 := by
  show (Fin.ofNat _ 0).val = 0; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))
theorem u32 : (⟨32⟩ : UInt256).toNat = 32 := by
  show (Fin.ofNat _ 32).val = 32; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))
theorem u128 : (⟨128⟩ : UInt256).toNat = 128 := by
  show (Fin.ofNat _ 128).val = 128; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))

/-- `ADD` of two literals (toNat). -/
theorem add128_0_toNat : ((⟨128⟩ : UInt256) + ⟨0⟩).toNat = 128 := by
  rw [uadd_toNat, u128, u0, Nat.add_zero, Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))]
theorem add128_32_toNat : ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 := by
  rw [uadd_toNat, u128, u32]; show (160:ℕ) % UInt256.size = 160; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))

/-- General `SUB` toNat (no wrap). -/
theorem usub_toNat {a b : UInt256} (h : b.toNat ≤ a.toNat) :
    (UInt256.sub a b).toNat = a.toNat - b.toNat := by
  show (a.val - b.val).val = a.toNat - b.toNat
  rw [Fin.coe_sub_iff_le.mpr (by rw [Fin.le_def]; exact h)]; rfl

theorem sub_ret32_toNat : (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 := by
  rw [usub_toNat (by rw [add128_32_toNat, u128]; omega), add128_32_toNat, u128]

theorem u160 : (⟨160⟩ : UInt256).toNat = 160 := by
  show (Fin.ofNat _ 160).val = 160; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))
theorem add128_0 : ((⟨128⟩ : UInt256) + ⟨0⟩) = ⟨128⟩ := u256_inj (by rw [add128_0_toNat, u128])
theorem add128_32 : ((⟨128⟩ : UInt256) + ⟨32⟩) = ⟨160⟩ := u256_inj (by rw [add128_32_toNat, u160])
theorem sub_160_128 : UInt256.sub (⟨160⟩ : UInt256) ⟨128⟩ = ⟨32⟩ :=
  u256_inj (by rw [usub_toNat (by rw [u160, u128]; omega), u160, u128, u32])

theorem ofNat128 : UInt256.ofNat 128 = ⟨128⟩ :=
  u256_inj (by rw [ulit_toNat' 128 (lt_size_of_lt256 (by norm_num)), u128])

/-! ## Encoder `0x47 → RETURN` — the ABI-encode-and-return tail (**proved**)

`pc 71` ABI-encodes the return word `val = 2^n` into `mem[0x80 .. 0xa0]` (via the internal
`abi_encode` routines at `0x109`/`0xfa`/`0x9c`) and `RETURN`s those 32 bytes.  47 instructions
plus one nested `powRoutine_9c` call.  Concludes the success result `toByteArray val`. -/
set_option maxHeartbeats 4000000 in
theorem powX_encode {g : UInt256} {s0 s : State} {k C : ℕ} {val : UInt256} {Rt : List UInt256}
    (hcode : s.executionEnv.code = powBytecode) (hpc : s.machineState.pc = ⟨71⟩)
    (hstk : s.machineState.stack = val :: Rt)
    (hmem : s.machineState.memory = solcFreePtrMem)
    (haw : s.machineState.activeWords = UInt256.ofNat 3)
    (hov : Rt.length + 11 ≤ 1024)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J powBytecode ⟨0⟩) s) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0 = .error .OutOfGass
      ∨ ∃ s', X (g.toNat + 1) (D_J powBytecode ⟨0⟩) s0
                = .ok (.success s' (UInt256.toByteArray val))
            ∧ ((s'.createdAccounts, s'.accountMap) = (s.createdAccounts, s.accountMap)) := by
  rcases (RD.startWith hcode hpc hstk hgas hk hC hX hmem haw rfl rfl
      -- 1: JUMPDEST @71
      |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 2: PUSH1 64 @72
      |>.push1 ⟨64⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 3: MLOAD @74  (free-pointer mem[64] = 128)
      |>.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
        (fun s haws hstks => by
          have h0 : s.machineState.stack[0]! = (⟨64⟩ : UInt256) := (by rw [hstks]; rfl)
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, h0]; decide)
        (by rw [if_neg (by rw [solcFreePtrMem_size]; decide),
          show (⟨64⟩ : UInt256).toNat = 64 from (by decide), solcFreePtrMem_read64,
          fromByteArrayBigEndian_toByteArray,
          show UInt256.ofNat ((⟨128⟩ : UInt256).toNat) = ⟨128⟩ from (by decide)])
        (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 4: PUSH2 84 @75
      |>.push2 ⟨84⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 5: SWAP2 @78
      |>.swap2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 6: SWAP1 @79
      |>.swap1 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 7: PUSH2 265 @80
      |>.push2 ⟨265⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 8: JUMP @83 → 265
      |>.jump (by decide) (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by first | (simp only [List.length_cons]; omega) | omega)
      -- 9: JUMPDEST @265
      |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 10: PUSH0 @266
      |>.push0 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 11: PUSH1 32 @267
      |>.push1 ⟨32⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 12: DUP3 @269
      |>.dup3 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 13: ADD @270  (128 + 32)
      |>.add (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 14: SWAP1 @271
      |>.swap1 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 15: POP @272
      |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 16: PUSH2 284 @273
      |>.push2 ⟨284⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 17: PUSH0 @276
      |>.push0 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 18: DUP4 @277
      |>.dup4 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 19: ADD @278  (128 + 0)
      |>.add (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 20: DUP5 @279
      |>.dup5 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 21: PUSH2 250 @280
      |>.push2 ⟨250⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 22: JUMP @283 → 250
      |>.jump (by decide) (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by first | (simp only [List.length_cons]; omega) | omega)
      -- 23: JUMPDEST @250
      |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 24: PUSH2 259 @251
      |>.push2 ⟨259⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 25: DUP2 @254
      |>.dup2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 26: PUSH2 156 @255
      |>.push2 ⟨156⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 27: JUMP @258 → 156
      |>.jump (by decide) (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by first | (simp only [List.length_cons]; omega) | omega)
      -- 28: routine 0x9c @156 → 259
      |>.routine9c (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by first | (simp only [List.length_cons]; omega) | omega)
      -- 29: JUMPDEST @259
      |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 30: DUP3 @260
      |>.dup3 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 31: MSTORE @261  (mem[128] := val)
      |>.mstore 6 (powMem2 val) (UInt256.ofNat 5) (by decide)
        (fun s haws hstks => by
          have h0 : s.machineState.stack[0]! = ((⟨128⟩ : UInt256) + ⟨0⟩) := (by rw [hstks]; rfl)
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, h0]; decide)
        (by rw [show ((⟨128⟩ : UInt256) + ⟨0⟩).toNat = 128 from (by decide)]; rfl)
        (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 32: POP @262
      |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 33: POP @263
      |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 34: JUMP @264 → 284
      |>.jump (by decide) (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by first | (simp only [List.length_cons]; omega) | omega)
      -- 35: JUMPDEST @284
      |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 36: SWAP3 @285
      |>.swap3 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 37: SWAP2 @286
      |>.swap2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 38: POP @287
      |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 39: POP @288
      |>.pop (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 40: JUMP @289 → 84
      |>.jump (by decide) (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by first | (simp only [List.length_cons]; omega) | omega)
      -- 41: JUMPDEST @84
      |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 42: PUSH1 64 @85
      |>.push1 ⟨64⟩ (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 43: MLOAD @87  (free-pointer mem[64] = 128, now in powMem2)
      |>.mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
        (fun s haws hstks => by
          have h0 : s.machineState.stack[0]! = (⟨64⟩ : UInt256) := (by rw [hstks]; rfl)
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, h0]; decide)
        (by rw [if_neg (by rw [powMem2_size]; decide),
          show (⟨64⟩ : UInt256).toNat = 64 from (by decide), powMem2_read64,
          fromByteArrayBigEndian_toByteArray,
          show UInt256.ofNat ((⟨128⟩ : UInt256).toNat) = ⟨128⟩ from (by decide)])
        (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 44: DUP1 @88
      |>.dup1 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 45: SWAP2 @89
      |>.swap2 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 46: SUB @90  (160 - 128 = 32, symbolic)
      |>.sub (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      -- 47: SWAP1 @91 → pc 92
      |>.swap1 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
      ).out with hoog | ⟨sR, hXR, hcR, hpR, hstkR, hgR, hkCR, hCgR, hmemR, hawR, haccR, _heeR⟩
  · exact Or.inl hoog
  -- RETURN @92: returns mem[128 .. 160] = toByteArray val
  · have h0ᵣ : sR.machineState.stack[0]! = (⟨128⟩ : UInt256) := by rw [hstkR]; rfl
    have h1ᵣ : sR.machineState.stack[1]! = UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩ := by
      rw [hstkR]; rfl
    have hmcr : memoryExpansionCost sR .RETURN = 0 := by
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawR, h0ᵣ, h1ᵣ]; decide
    have st47 := return_xstep hcR hpR (by decide) hstkR
      (by first | (simp only [List.length_cons]; omega) | omega)
    rw [hmcr,
      show sR.machineState.memory.readWithPadding (⟨128⟩ : UInt256).toNat
            (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = UInt256.toByteArray val from by
        rw [hmemR, show (⟨128⟩ : UInt256).toNat = 128 from by decide, sub_ret32_toNat,
          powMem2_read128]] at st47
    refine Or.inr ⟨stReturn sR ⟨128⟩ (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩) Rt, ?_, ?_⟩
    · exact hXR.trans (stepHaltSuccess hgR st47 (by omega) (by omega))
    · show (sR.createdAccounts, sR.accountMap) = (s.createdAccounts, s.accountMap)
      exact haccR


/-! ## Full success trace — `initState → RETURN(2^n)` (**proved**)

Composes the six forward segments (dispatcher → decode → require → loop → exit → encoder) for a
well-formed `pow2(n)` call with `callvalue = 0`, `calldatasize ≥ 36`, matching selector, and
`n < 256`.  Either the run OOGs, or it succeeds returning the 32-byte big-endian word `2^n`. -/
set_option maxHeartbeats 1000000 in
theorem powX_success {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsz255 : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hn : (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat < 256) :
    X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass
      ∨ ∃ s', (X (g.toNat + 1) (D_J powBytecode ⟨0⟩) (initState cA gh bl σ σ₀ g A I)
          = .ok (.success s'
              (UInt256.toByteArray
                (UInt256.ofNat (2 ^ (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat)))))
            ∧ ((s'.createdAccounts, s'.accountMap) = (cA, σ)) := by
  have hsize : I.calldata.size < UInt256.size := by
    have h0 : (2:ℕ)^255 + 4 < 2^256 := by norm_num
    have hp : (2:ℕ)^255 + 4 < UInt256.size := by simpa [UInt256.size] using h0
    omega
  -- the selector word and the decoded argument
  set sel := UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ with hsel
  set arg := uInt256OfByteArray (I.calldata.readBytes 4 32) with harg
  rcases powX_disp hcode hwv (by omega) hsize hmatch with
    hd | ⟨s1, hX1, hee1, hp1, hg1, hstk1, haw1, hmem1, hC1, hacc1⟩
  · exact Or.inl hd
  · rcases powX_decode (s0 := initState cA gh bl σ σ₀ g A I) (I := I) (k := 24) (C := 96)
        (by rw [hee1]; exact hcode) hee1 hp1 hstk1 hsz36 hsz255 hg1 (by norm_num) hC1 hX1 with
      hd | ⟨k2, C2, s2, hX2, hc2, hp2, hstk2, hg2, hk2, hCg2, hmem2, haw2, hacc2⟩
    · exact Or.inl hd
    · rcases powX_require (n := arg) (sel := sel) (R := []) hc2 hp2 hstk2 hn
          (by simp only [List.length_nil]; omega) hg2 hk2 hCg2 hX2 with
        hd | ⟨k3, C3, s3, hX3, hc3, hp3, hstk3, hg3, hk3, hCg3, hmem3, haw3, hacc3⟩
      · exact Or.inl hd
      · rcases powLoopCore (slot := ⟨0⟩) (n := arg) (REST := [⟨71⟩, sel])
            hn (by simp only [List.length_cons, List.length_nil]; omega)
            arg.toNat ⟨0⟩ ⟨1⟩ k3 C3 s3
            (by rw [show (⟨0⟩:UInt256).toNat = 0 from (by decide)]; omega)
            (by decide)
            (by rw [show (⟨0⟩:UInt256).toNat = 0 from (by decide)]; omega)
            hc3 hp3 hstk3 hg3 hk3 hCg3 hX3 with
          hd | ⟨k4, C4, s4, hX4, hc4, hp4, hstk4, hg4, hk4, hCg4, hmem4, haw4, hacc4⟩
        · exact Or.inl hd
        · rcases (RD.start hc4 hp4 hstk4 hg4 hk4 hCg4 hX4
              |>.routineexit (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
                (by simp only [List.length_cons, List.length_nil]; omega)).conclude with
            hd | ⟨k5, C5, s5, hX5, hc5, hp5, hstk5, hg5, hk5, hCg5, hmem5, haw5, hacc5⟩
          · exact Or.inl hd
          · have hmemS : s5.machineState.memory = solcFreePtrMem := by
              rw [hmem5, hmem4, hmem3, hmem2, hmem1]
            have hawS : s5.machineState.activeWords = UInt256.ofNat 3 := by
              rw [haw5, haw4, haw3, haw2, haw1]
            rcases powX_encode (val := UInt256.ofNat (2 ^ arg.toNat)) (Rt := [sel])
                hc5 hp5 hstk5 hmemS hawS (by simp only [List.length_cons, List.length_nil]; omega)
                hg5 hk5 hCg5 hX5 with
              hd | ⟨s6, hX6, hacc6⟩
            · exact Or.inl hd
            · exact Or.inr ⟨s6, hX6,
                hacc6.trans (hacc5.trans (hacc4.trans (hacc3.trans (hacc2.trans hacc1))))⟩

/-- Lift the success trace to `Ξ`: either out-of-gas, or success returning the 32-byte
    big-endian encoding of `2^n`, with `σ`/`createdAccounts`/substate carried by the final state. -/
theorem powXi_success {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsz255 : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hn : (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat < 256) :
    Ξ cA gh bl σ σ₀ g A I = .error .OutOfGass
      ∨ ∃ (g' : UInt256) (A' : Ethereum.Substate), Ξ cA gh bl σ σ₀ g A I
                = .ok (.success (cA, σ, g', A')
                    (UInt256.toByteArray
                      (UInt256.ofNat (2 ^ (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat)))) := by
  rcases powX_success hcode hwv hsz36 hsz255 hmatch hn with hoog | ⟨s, hX, hacc⟩
  · exact Or.inl (Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
  · have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hσ : s.accountMap = σ := congrArg Prod.snd hacc
    refine Or.inr ⟨s.machineState.gasAvailable, s.substate, ?_⟩
    have hxi := Xi_success_of_X (by rw [← hcode] at hX; exact hX)
    rw [hcA, hσ] at hxi
    exact hxi
