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

/-- Decoder bounds-check **failure** (`0xcf` revert path) as an **`RD → RDrev` combinator**: from the
    decoder Cf-entry at pc 207 with `[4, de, ret, …R']`, the signed `SLT(de − 4, 32) = 1` ⇒ `ISZERO = 0`
    ⇒ the `JUMPI` falls through to the revert routine `0x98`, which reverts (`PUSH0·PUSH0·REVERT`).
    Composes off `routinedecodeToCf` (the short-arg / huge-arg revert paths). -/
theorem RD.routinecf_revert {g : UInt256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {de ret : UInt256} {R' : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨207⟩ (⟨4⟩ :: de :: ret :: R') mem aw acc k C)
    (hsltval : UInt256.slt (UInt256.sub de ⟨4⟩) ⟨32⟩ = ⟨1⟩)
    (hov : R'.length + 15 ≤ 1024) :
    RDrev powBytecode g s0 :=
  h |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
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
    |>.jumpdest (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push0 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push0 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.rev 0 (by decide) (fun s _ hstks => memExpRevert0 s hstks)
        (by first | (simp only [List.length_cons]; omega) | omega)

end TruthClaude.Reach
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

/-- `require(n < 256)` **failure** (`n ≥ 256`) as an **`RD → RDrev` combinator**: from pc 66 with
    `[n, 71, sel, …R]`, `LT n 256 = 0` ⇒ the `JUMPI` is not taken and execution reverts at `0x68`
    (`PUSH0·PUSH0·REVERT`).  Composes off the decoder (the `n ≥ 256` revert path). -/
theorem RD.routinerequire_revert {g : UInt256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {n sel : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨66⟩ (n :: ⟨71⟩ :: sel :: R) mem aw acc k C)
    (hltval : UInt256.lt n ⟨256⟩ = ⟨0⟩) (hov : R.length + 10 ≤ 1024) :
    RDrev powBytecode g s0 :=
  -- 66→104: JUMPDEST·PUSH2 93·JUMP·JUMPDEST·PUSH0·PUSH2 256·DUP3·LT(=0)·PUSH2 107·JUMPI(nt) ⇒ revert
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
    |>.jumpiNT (by decide) hltval (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push0 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.push0 (by decide) (by first | (simp only [List.length_cons]; omega) | omega)
    |>.rev 0 (by decide) (fun s _ hstks => memExpRevert0 s hstks)
        (by first | (simp only [List.length_cons]; omega) | omega)


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
theorem add128_32_toNat : ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 := by
  rw [uadd_toNat, u128, u32]; show (160:ℕ) % UInt256.size = 160; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))

/-- General `SUB` toNat (no wrap). -/
theorem usub_toNat {a b : UInt256} (h : b.toNat ≤ a.toNat) :
    (UInt256.sub a b).toNat = a.toNat - b.toNat := by
  show (a.val - b.val).val = a.toNat - b.toNat
  rw [Fin.coe_sub_iff_le.mpr (by rw [Fin.le_def]; exact h)]; rfl

theorem sub_ret32_toNat : (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 := by
  rw [usub_toNat (by rw [add128_32_toNat, u128]; omega), add128_32_toNat, u128]

/-! ## Encoder `0x47 → RETURN` — the ABI-encode-and-return tail (**proved**)

`pc 71` ABI-encodes the return word `val = 2^n` into `mem[0x80 .. 0xa0]` (via the internal
`abi_encode` routines at `0x109`/`0xfa`/`0x9c`) and `RETURN`s those 32 bytes.  47 instructions
plus one nested `powRoutine_9c` call.  Concludes the success result `toByteArray val`. -/
namespace TruthClaude.Reach

set_option maxHeartbeats 4000000 in
/-- The encoder `0x47 → RETURN` as an **`RD → RDret` combinator**: from pc 71 with `[val, …Rt]`,
    free-pointer memory and `activeWords = 3`, ABI-encode `val` into `mem[0x80 .. 0xa0]` and `RETURN`
    those 32 bytes — halting with success returning `toByteArray val`.  47 instructions plus one
    nested `0x9c` call. -/
theorem RD.routineencode {g : UInt256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val : UInt256} {Rt : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨71⟩ (val :: Rt) solcFreePtrMem (UInt256.ofNat 3) acc k C)
    (hov : Rt.length + 11 ≤ 1024) :
    RDret powBytecode g s0 acc (UInt256.toByteArray val) :=
  h
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
      -- 48: RETURN @92 → success returning mem[128 .. 160] = toByteArray val
      |>.ret 0 (UInt256.toByteArray val) (by decide)
        (fun s haws hstks => by
          have h0 : s.machineState.stack[0]! = (⟨128⟩ : UInt256) := (by rw [hstks]; rfl)
          have h1 : s.machineState.stack[1]! = UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩ :=
            (by rw [hstks]; rfl)
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, h0, h1]; decide)
        (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, sub_ret32_toNat, powMem2_read128])
        (by first | (simp only [List.length_cons]; omega) | omega)

end TruthClaude.Reach

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
    RDret powBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
        (UInt256.toByteArray
          (UInt256.ofNat (2 ^ (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat))) := by
  have hsize : I.calldata.size < UInt256.size := by
    have h0 : (2:ℕ)^255 + 4 < 2^256 := by norm_num
    have hp : (2:ℕ)^255 + 4 < UInt256.size := by simpa [UInt256.size] using h0
    omega
  -- the selector word and the decoded argument
  set sel := UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ with hsel
  set arg := uInt256OfByteArray (I.calldata.readBytes 4 32) with harg
  -- decoder bounds check passes (size ≥ 36 ⇒ slt(size − 4, 32) = 0); require check passes (n < 256)
  have hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ := by
    apply slt32_zero <;> (rw [sub4_toNat (by omega) hsize]; omega)
  have h256 : (⟨256⟩ : UInt256).toNat = 256 := by
    show (Fin.ofNat _ 256).val = 256; simp only [Fin.ofNat]
    exact Nat.mod_eq_of_lt (by have := pow_lt_size (show (8:ℕ) < 256 by norm_num); norm_num at this; exact this)
  have hltval : UInt256.lt arg ⟨256⟩ = ⟨1⟩ := ult_one (by rw [h256]; exact hn)
  -- dispatcher → decoder → cf → require → loop → loop-exit, threaded as one `RD`; encoder is terminal
  have rdDec := powX_disp (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
        hcode hwv (by omega) hsize hmatch
      |>.routinedecodeToCf (by omega) hsize
      |>.routinecf hsltval (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
          (by simp only [List.length_cons, List.length_nil]; omega)
  rw [show ((⟨4⟩ : UInt256) + ⟨0⟩).toNat = 4 from add40_toNat, ← harg] at rdDec
  rcases RD.loop (slot := ⟨0⟩) (n := arg) (REST := [⟨71⟩, sel])
      hn (by simp only [List.length_cons, List.length_nil]; omega)
      arg.toNat ⟨0⟩ ⟨1⟩ _ _
      (by rw [show (⟨0⟩:UInt256).toNat = 0 from (by decide)]; omega)
      (by decide)
      (by rw [show (⟨0⟩:UInt256).toNat = 0 from (by decide)]; omega)
      (rdDec |>.routinerequire hltval (by simp only [List.length_cons, List.length_nil]; omega))
    with ⟨k4, C4, rd4⟩
  -- loop-exit → encoder, threaded straight to the success terminal `RDret`
  exact rd4.routineexit (by rw [powValidJumps]; exact Array.contains_eq_true_of_mem (by simp))
        (by simp only [List.length_cons, List.length_nil]; omega)
      |>.routineencode (by simp only [List.length_cons, List.length_nil]; omega)

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
