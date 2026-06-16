import Examples.Pow.Bytecode
import Examples.Pow.Spec
import Reasoning.Theory
import Reasoning.Dispatch
import Reasoning.SolmBody
import Reasoning.Stepping
import Reasoning.Memory
import Reasoning.Solc
import Reasoning.Reach

/-!
# Pow — runtime-equivalence proof for `pow2(uint256 n)`

The full EVM↔Solm equivalence: dispatcher, the `while`-loop `RD` combinator, the abi-decode/encode
segments, the success/​revert traces, the Solm-side body execution, and the final `Pow.powCorrect`.
Built on the generic `Reasoning` library; the bytecode and Solm spec live in the sibling files.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 10000

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

namespace Reasoning.Reach

/-- The `pow2` loop `0x75 → 0x8e` as an **`RD` combinator**, by induction on the variant `n − i`.
    Entry invariant `RD … ⟨117⟩ (i :: r :: slot :: n :: REST)` with `r = 2^i`, `i ≤ n < 256`;
    produces `RD … ⟨142⟩ (n :: 2^n :: slot :: n :: REST)` for *some* step/gas counters (existential,
    since they grow by 19 steps / 67 gas per iteration).  The base case (`i = n`) is the 7-step guard
    ending in the taken `JUMPI` to the exit; each inductive step is the 19-step body (guard not taken →
    `r*=2; i+=1` → back-jump) feeding the IH.  This replaces the hand-written straight-line stepping
    with the `RD` combinator chain — the loop is now *inside* `Reach`. -/
theorem RD.loop {g : Sat256} {s0 : State} {ee : ExecutionEnv} {slot n : UInt256}
    {REST : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hn : n.toNat < 256) (hRov : REST.length + 20 ≤ 1024) :
    ∀ (var : ℕ) (i r : UInt256) (k C : ℕ),
      n.toNat - i.toNat = var → r.toNat = 2 ^ i.toNat → i.toNat ≤ n.toNat →
      RD powBytecode ee g s0 ⟨117⟩ (i :: r :: slot :: n :: REST) mem aw rdata acc k C →
      ∃ (k' C' : ℕ),
        RD powBytecode ee g s0 ⟨142⟩
          (n :: UInt256.ofNat (2 ^ n.toNat) :: slot :: n :: REST) mem aw rdata acc k' C' := by
  -- An instance of the generic `RD.whileLoop`: loop state `(i, r) : UInt256 × UInt256`, invariant
  -- `r = 2^i ∧ i ≤ n` at variant `n − i`, with the `pow2` guard/body as the two trace obligations.
  intro var i r k C hvar hinv hile h
  refine RD.whileLoop (α := UInt256 × UInt256) ⟨117⟩ ⟨142⟩
    (fun m ir => n.toNat - ir.1.toNat = m ∧ ir.2.toNat = 2 ^ ir.1.toNat ∧ ir.1.toNat ≤ n.toNat)
    (fun ir => ir.1 :: ir.2 :: slot :: n :: REST)
    (n :: UInt256.ofNat (2 ^ n.toNat) :: slot :: n :: REST)
    ?hexit ?hbody var (i, r) ⟨hvar, hinv, hile⟩ k C h
  case hexit =>
    -- variant `0` (`i = n`): the guard's `JUMPI` is **taken** to the exit `0x8e`.
    rintro ⟨i, r⟩ ⟨hvar, hinv, hile⟩ k C h
    dsimp only at hvar hinv hile h
    have hin : i.toNat = n.toNat := by omega
    have hieqn : i = n := u256_inj hin
    have hreq : r = UInt256.ofNat (2 ^ n.toNat) :=
      u256_inj (by rw [hinv, hin, ofNat_pow_toNat hn])
    have rd := evm_run h with [
      jumpdest, dup4, dup2, lt, iszero, push2 ⟨142⟩,
      jumpiT (by rw [show UInt256.lt i n = ⟨0⟩ from ult_zero (by omega)]; decide)
             (by jump_dest) ]
    rw [hieqn, hreq] at rd
    exact ⟨_, _, rd⟩
  case hbody =>
    -- variant `v+1` (`i < n`): guard not taken → `r*=2; i+=1` → back-jump to `0x75`.
    rintro v ⟨i, r⟩ ⟨hvar, hinv, hile⟩ k C h
    dsimp only at hvar hinv hile h
    have hilt : i.toNat < n.toNat := by omega
    have hi1size : i.toNat + 1 < UInt256.size := lt_size_of_lt256 (by omega)
    have hi1 : (i + ⟨1⟩).toNat = i.toNat + 1 := add1_toNat hi1size
    have hr2size : 2 * r.toNat < UInt256.size := by
      rw [hinv, show 2 * 2 ^ i.toNat = 2 ^ (i.toNat + 1) from by rw [pow_succ]; ring]
      exact pow_lt_size (by omega)
    have hr2 : (UInt256.mul r ⟨2⟩).toNat = 2 * r.toNat := mul2_toNat hr2size
    have rd := evm_run h with [
      jumpdest, dup4, dup2, lt, iszero, push2 ⟨142⟩,
      jumpiNT (by rw [show UInt256.lt i n = ⟨1⟩ from ult_one hilt]; decide),
      push1 ⟨2⟩, dup3, mul, swap2, pop, push1 ⟨1⟩, dup2, add, swap1, pop, push2 ⟨117⟩,
      jump (by jump_dest) ]
    exact ⟨(i + ⟨1⟩, UInt256.mul r ⟨2⟩), _, _,
      ⟨by rw [hi1]; omega, by rw [hr2, hi1, hinv, pow_succ]; ring, by rw [hi1]; omega⟩, rd⟩

end Reasoning.Reach

/-! ## The dispatcher (success path) — reaches the function body at `0x2d`

`callvalue = 0`, `calldatasize ≥ 4`, selector matches `0x442b7ffb`: 24 instructions from
`initState` to the `JUMPDEST` at `0x2d = 45`, leaving the decoded selector word on the stack and
the free-pointer memory in place.  Mirrors `truthX_cvz_*` but with PUSH2 jump targets. -/
/-- **Dispatcher prefix → the selector `EQ` (pc 37).**  Contract-agnostic of whether the selector
    matches: reaches pc 37 with `[eq(0x442b7ffb, sel), sel]` on the stack (`sel` = the decoded
    4-byte selector).  Shared by the `match` path (`powX_disp`) and the `nomatch` revert. -/
theorem powX_dispToEq {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    RD powBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨37⟩
        [UInt256.eq ⟨1143701499⟩
            (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩),
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) 22 83 := by
  have hsztoNat : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size := by
    show (Fin.ofNat _ I.calldata.size).val = I.calldata.size
    simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hsize
  have hlt0 : UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩ = ⟨0⟩ :=
    ult_zero (by rw [hsztoNat]; exact le_trans (show (⟨4⟩ : UInt256).toNat ≤ 4 by decide) hsz)
  -- prologue → PUSH2·JUMPI(t)·JUMPDEST·POP·PUSH1·CALLDATASIZE·LT·PUSH2·JUMPI(nt)·PUSH0·
  --   CALLDATALOAD·PUSH1·SHR·DUP1·PUSH4·EQ, reaching the selector compare at pc 37, as one `RD` chain
  have rd := evm_run (solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (g := g) hcode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      with [
      push2 ⟨15⟩,
      jumpiT (by rw [hwv]; decide)
             (by jump_dest),
      jumpdest, pop, push1 ⟨4⟩, calldatasize, lt, push2 ⟨41⟩,
      jumpiNT hlt0,
      push0, calldataload, push1 ⟨224⟩, shr, dup1, push4 ⟨1143701499⟩, eq ]
  rw [show (⟨0⟩ : UInt256).toNat = 0 from by decide] at rd
  exact rd




/-- **The dispatcher (match path).**  Reuses `powX_dispToEq`, then resolves the selector `EQ`
    to `1` (via `powEvmSelector` + `hmatch`) and takes the `JUMPI` to the function body at
    `0x2d = 45`.  Same statement as before the refactor; only the prefix is now shared. -/
theorem powX_disp {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    RD powBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨45⟩
        [UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) 24 96 := by
  -- the selector compare resolves to `1` (match), then PUSH2 0x2d · JUMPI (taken) → body at pc 45
  have rd := powX_dispToEq (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsz hsize
  rw [show UInt256.eq ⟨1143701499⟩
        (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩) = ⟨1⟩
      from by rw [powEvmSelector hsz, if_pos hmatch]] at rd
  exact evm_run rd with [
      push2 ⟨45⟩,
      jumpiT (by decide) (by jump_dest) ]



set_option maxRecDepth 10000

namespace Reasoning.Reach

/-- solc routine `0x9c` (`cleanup_t_uint256`-style identity) as an **`RD→RD` combinator**: from
    `[v, ret, …R]` at pc 156, returns `v` to the dynamic address `ret`, leaving `[v, …R]`.
    9 instructions / gas 27; memory, active words, accounts and env untouched.  Chains directly
    inside callers (no `out`/`startWith` glue). -/
theorem RD.routine9c {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {v ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨156⟩ (v :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J powBytecode 0).contains ret = true) (hov : R.length + 4 ≤ 1024) :
    RD powBytecode ee g s0 ret (v :: R) mem aw rdata acc (k + 9) (C + 27) :=
  -- JUMPDEST · PUSH0 · DUP2 · SWAP1 · POP · SWAP2 · SWAP1 · POP · JUMP
  evm_run h with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop,
    jump hret ]


/-- solc routine `0xa5` (`abi_decode`'s validator) as an **`RD→RD` combinator**: entry at pc 165
    with `[arg, ret, …R]`, calls `0x9c` to clean `arg`, checks `arg == cleanup(arg)` (always true
    for uint256), returns to `ret` leaving `[…R]`.  The `0x9c` call is now a direct `.routine9c`
    chain — no `out`/`startWith` glue.  22 instructions / gas 76. -/
theorem RD.routinea5 {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {arg ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨165⟩ (arg :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J powBytecode 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    RD powBytecode ee g s0 ret R mem aw rdata acc (k + 22) (C + 76) :=
  -- JUMPDEST·PUSH2 174·DUP2·PUSH2 156·JUMP → 0x9c → JUMPDEST·DUP2·EQ·PUSH2 184·JUMPI·JUMPDEST·POP·JUMP
  evm_run h with [
    jumpdest, push2 ⟨174⟩, dup2, push2 ⟨156⟩,
    jump (by jump_dest),
    raw routine9c (by jump_dest) (by evm_ov),
    jumpdest, dup2, eq, push2 ⟨184⟩,
    jumpiT (by rw [u256_eq_refl]; exact one_ne_zero_uint)
           (by jump_dest),
    jumpdest, pop,
    jump hret ]


/-- solc routine `0xbb` (`abi_decode_uint256`) as an **`RD→RD` combinator**: entry at pc 187 with
    `[offset, end, ret, …R]`, loads `calldata[offset]` (off the carried env `ee`), validates it via
    `0xa5` (a direct `.routinea5` chain), returns it to `ret` leaving `[calldata[offset], …R]`.
    38 instructions / gas 126. -/
theorem RD.routinebb {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {offset ennd ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨187⟩ (offset :: ennd :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J powBytecode 0).contains ret = true) (hov : R.length + 10 ≤ 1024) :
    RD powBytecode ee g s0 ret
        (uInt256OfByteArray (ee.calldata.readBytes offset.toNat 32) :: R) mem aw rdata acc (k + 38) (C + 126) :=
  -- JUMPDEST·PUSH0·DUP2·CALLDATALOAD·SWAP1·POP·PUSH2 201·DUP2·PUSH2 165·JUMP → 0xa5 → JUMPDEST·SWAP3·SWAP2·POP·POP·JUMP
  evm_run h with [
    jumpdest, push0, dup2, calldataload, swap1, pop, push2 ⟨201⟩, dup2, push2 ⟨165⟩,
    jump (by jump_dest),
    raw routinea5 (by jump_dest) (by evm_ov),
    jumpdest, swap3, swap2, pop, pop,
    jump hret ]

end Reasoning.Reach

/-- `SUB` of `ofNat sz` and `4` is `sz - 4` (no wrap), for `4 ≤ sz < size`. -/
theorem sub4_toNat {sz : ℕ} (h4 : 4 ≤ sz) (hsz : sz < UInt256.size) :
    (UInt256.sub (UInt256.ofNat sz) ⟨4⟩).toNat = sz - 4 := by
  have h1 : (UInt256.ofNat sz).toNat = sz := by
    show (Fin.ofNat _ sz).val = sz; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hsz
  have hrw : UInt256.sub (UInt256.ofNat sz) ⟨4⟩ = UInt256.ofNat sz - UInt256.ofNat 4 := rfl
  rw [hrw, UInt256.toNat_sub_ofNat_of_le (by rw [h1]; exact h4), h1]

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

namespace Reasoning.Reach

/-- solc routine `0xcf` (`abi_decode_tuple`'s bounds-checked decoder) as an **`RD→RD` combinator**:
    entry at pc 207 with `[4, size, ret, …R']`; when `SLT(size−4, 32) = 0` (enough calldata) it sets
    up offset `4+0` and calls `0xbb` (a direct `.routinebb` chain), returning `calldata[4:36]` to
    `ret`.  66 instructions / gas 215. -/
theorem RD.routinecf {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {de ret : UInt256} {R' : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨207⟩ (⟨4⟩ :: de :: ret :: R') mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub de ⟨4⟩) ⟨32⟩ = ⟨0⟩)
    (hret : (D_J powBytecode 0).contains ret = true) (hov : R'.length + 15 ≤ 1024) :
    RD powBytecode ee g s0 ret
        (uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨0⟩).toNat 32) :: R')
        mem aw rdata acc (k + 66) (C + 215) :=
  -- prologue (SLT=0 ⇒ ISZERO=1 ⇒ JUMPI taken) · set up offset · JUMP → 0xbb → rearrange · JUMP ret
  evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨228⟩,
    jumpiT (by rw [hsltval]; decide)
           (by jump_dest),
    jumpdest, push0, push2 ⟨241⟩, dup5, dup3, dup6, add, push2 ⟨187⟩,
    jump (by jump_dest),
    raw routinebb (by jump_dest) (by evm_ov),
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop,
    jump hret ]

/-- Decoder bounds-check **failure** (`0xcf` revert path) as an **`RD → RDrev` combinator**: from the
    decoder Cf-entry at pc 207 with `[4, de, ret, …R']`, the signed `SLT(de − 4, 32) = 1` ⇒ `ISZERO = 0`
    ⇒ the `JUMPI` falls through to the revert routine `0x98`, which reverts (`PUSH0·PUSH0·REVERT`).
    Composes off `routinedecodeToCf` (the short-arg / huge-arg revert paths). -/
theorem RD.routinecf_revert {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {de ret : UInt256} {R' : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨207⟩ (⟨4⟩ :: de :: ret :: R') mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub de ⟨4⟩) ⟨32⟩ = ⟨1⟩)
    (hov : R'.length + 15 ≤ 1024) :
    RDrev powBytecode g s0 :=
  evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨228⟩,
    jumpiNT (by rw [hsltval]; decide),
    push2 ⟨227⟩, push2 ⟨152⟩,
    jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

end Reasoning.Reach
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

namespace Reasoning.Reach

/-- **Call-setup prefix `0x2d → decoder entry 0x cf = 207`** as an **`RD→RD` combinator**: from
    `[sel]` at pc 45, reaches pc 207 with `[4, calldatasize, 0x42, 0x47, sel]`, ready for the
    decoder's bounds check.  14 instructions / gas 44.  (The `ADD` produces the raw `4 + (size−4)`,
    rewritten to `ofNat size` here so callers get the clean form.) -/
theorem RD.routinedecodeToCf {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {sel : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨45⟩ [sel] mem aw rdata acc k C)
    (hsz4 : 4 ≤ ee.calldata.size) (hszsize : ee.calldata.size < UInt256.size) :
    RD powBytecode ee g s0 ⟨207⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ⟨66⟩ :: ⟨71⟩ :: [sel]) mem aw rdata acc (k + 14) (C + 44) := by
  -- 45→65: JUMPDEST·PUSH2 71·PUSH1 4·DUP1·CALLDATASIZE·SUB·DUP2·ADD·SWAP1·PUSH2 66·SWAP2·SWAP1·PUSH2 207·JUMP 207
  rw [show UInt256.ofNat ee.calldata.size
        = (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩
      from (add_sub4 hsz4 hszsize).symm]
  exact evm_run h with [
    jumpdest, push2 ⟨71⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨66⟩, swap2, swap1, push2 ⟨207⟩,
    jump (by jump_dest) ]


/-- `require(n < 256)` check (passes) as an **`RD→RD` combinator**: `0x42 → 0x75`, leaving
    `[0, 1, 0, n, 71, sel]` (initialises the loop's `r = 1, i = 0`).  19 instructions / gas 57. -/
theorem RD.routinerequire {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {n sel : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨66⟩ (n :: ⟨71⟩ :: sel :: R) mem aw rdata acc k C)
    (hltval : UInt256.lt n ⟨256⟩ = ⟨1⟩) (hov : R.length + 10 ≤ 1024) :
    RD powBytecode ee g s0 ⟨117⟩ (⟨0⟩ :: ⟨1⟩ :: ⟨0⟩ :: n :: ⟨71⟩ :: sel :: R)
        mem aw rdata acc (k + 19) (C + 57) :=
  -- JUMPDEST·PUSH2 93·JUMP·JUMPDEST·PUSH0·PUSH2 256·DUP3·LT·PUSH2 107·JUMPI(taken)·JUMPDEST·PUSH0·PUSH1 1·SWAP1·POP·PUSH0·PUSH0·SWAP1·POP
  evm_run h with [
    jumpdest, push2 ⟨93⟩,
    jump (by jump_dest),
    jumpdest, push0, push2 ⟨256⟩, dup3, lt, push2 ⟨107⟩,
    jumpiT (by rw [hltval]; exact one_ne_zero_uint)
           (by jump_dest),
    jumpdest, push0, push1 ⟨1⟩, swap1, pop, push0, push0, swap1, pop ]

/-- `require(n < 256)` **failure** (`n ≥ 256`) as an **`RD → RDrev` combinator**: from pc 66 with
    `[n, 71, sel, …R]`, `LT n 256 = 0` ⇒ the `JUMPI` is not taken and execution reverts at `0x68`
    (`PUSH0·PUSH0·REVERT`).  Composes off the decoder (the `n ≥ 256` revert path). -/
theorem RD.routinerequire_revert {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {n sel : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨66⟩ (n :: ⟨71⟩ :: sel :: R) mem aw rdata acc k C)
    (hltval : UInt256.lt n ⟨256⟩ = ⟨0⟩) (hov : R.length + 10 ≤ 1024) :
    RDrev powBytecode g s0 :=
  -- 66→104: JUMPDEST·PUSH2 93·JUMP·JUMPDEST·PUSH0·PUSH2 256·DUP3·LT(=0)·PUSH2 107·JUMPI(nt) ⇒ revert
  evm_run h with [
    jumpdest, push2 ⟨93⟩,
    jump (by jump_dest),
    jumpdest, push0, push2 ⟨256⟩, dup3, lt, push2 ⟨107⟩,
    jumpiNT hltval,
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]


/-- Loop exit `0x8e → 0x47` as an **`RD→RD` combinator**: drop the loop scratch, keep the result
    `val = 2^n`, and jump to the encoder at the saved return address `ret`.
    `[a, val, c, d, ret] ++ Rt → at ret, val :: Rt`.  10 instructions / gas 29. -/
theorem RD.routineexit {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {a val c d ret : UInt256} {Rt : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨142⟩ (a :: val :: c :: d :: ret :: Rt) mem aw rdata acc k C)
    (hret : (D_J powBytecode 0).contains ret = true) (hov : Rt.length + 7 ≤ 1024) :
    RD powBytecode ee g s0 ret (val :: Rt) mem aw rdata acc (k + 10) (C + 29) :=
  -- JUMPDEST · DUP2 · SWAP3 · POP · POP · POP · SWAP2 · SWAP1 · POP · JUMP ret
  evm_run h with [
    jumpdest, dup2, swap3, pop, pop, pop, swap2, swap1, pop,
    jump hret ]

end Reasoning.Reach


theorem u0 : (⟨0⟩ : UInt256).toNat = 0 := by
  show (Fin.ofNat _ 0).val = 0; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))
theorem u32 : (⟨32⟩ : UInt256).toNat = 32 := by
  show (Fin.ofNat _ 32).val = 32; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))
theorem u128 : (⟨128⟩ : UInt256).toNat = 128 := by
  show (Fin.ofNat _ 128).val = 128; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))

/-- `ADD` of two literals (toNat). -/
theorem add128_32_toNat : ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 := by
  rw [uadd_toNat, u128, u32]; show (160:ℕ) % UInt256.size = 160; exact Nat.mod_eq_of_lt (lt_size_of_lt256 (by norm_num))

theorem sub_ret32_toNat : (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 := by
  rw [usub_toNat (by rw [add128_32_toNat, u128]; omega), add128_32_toNat, u128]

/-! ## Encoder `0x47 → RETURN` — the ABI-encode-and-return tail (**proved**)

`pc 71` ABI-encodes the return word `val = 2^n` into `mem[0x80 .. 0xa0]` (via the internal
`abi_encode` routines at `0x109`/`0xfa`/`0x9c`) and `RETURN`s those 32 bytes.  47 instructions
plus one nested `RD.routine9c` call.  Concludes the success result `toByteArray val`. -/
namespace Reasoning.Reach

set_option maxHeartbeats 4000000 in
/-- The encoder `0x47 → RETURN` as an **`RD → RDret` combinator**: from pc 71 with `[val, …Rt]`,
    free-pointer memory and `activeWords = 3`, ABI-encode `val` into `mem[0x80 .. 0xa0]` and `RETURN`
    those 32 bytes — halting with success returning `toByteArray val`.  47 instructions plus one
    nested `0x9c` call. -/
theorem RD.routineencode {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {val : UInt256} {Rt : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD powBytecode ee g s0 ⟨71⟩ (val :: Rt) solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : Rt.length + 11 ≤ 1024) :
    RDret powBytecode g s0 acc (UInt256.toByteArray val) :=
  evm_run h with [
      -- 71→83: load free pointer, save return addr 84, JUMP to the abi-encode helper @265
      jumpdest, push1 ⟨64⟩,
      raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide) mem_cost
        (by rw [if_neg (by rw [solcFreePtrMem_size]; decide),
          show (⟨64⟩ : UInt256).toNat = 64 from (by decide), solcFreePtrMem_read64,
          fromByteArrayBigEndian_toByteArray,
          show UInt256.ofNat ((⟨128⟩ : UInt256).toNat) = ⟨128⟩ from (by decide)])
        (by decide) (by evm_ov),
      push2 ⟨84⟩, swap2, swap1, push2 ⟨265⟩,
      jump (by jump_dest),
      -- 265→283: tail = 128+32, head = 128+0, JUMP to the word-copy helper @250
      jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
      push2 ⟨284⟩, push0, dup4, add, dup5, push2 ⟨250⟩,
      jump (by jump_dest),
      -- 250→258: cleanup the value (0x9c), JUMP to it
      jumpdest, push2 ⟨259⟩, dup2, push2 ⟨156⟩,
      jump (by jump_dest),
      raw routine9c (by jump_dest) (by evm_ov),
      -- 259→264: MSTORE mem[128] := val, JUMP back @284
      jumpdest, dup3,
      raw mstore 6 (solcReturnMem val) (UInt256.ofNat 5) (by decide) mem_cost
        (by rw [show ((⟨128⟩ : UInt256) + ⟨0⟩).toNat = 128 from (by decide)]; rfl)
        (by decide) (by evm_ov),
      pop, pop,
      jump (by jump_dest),
      -- 284→289: rearrange, JUMP back @84
      jumpdest, swap3, swap2, pop, pop,
      jump (by jump_dest),
      -- 84→92: reload free pointer (now solcReturnMem), compute length 160−128, RETURN mem[128..160]
      jumpdest, push1 ⟨64⟩,
      raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide) mem_cost
        (by rw [if_neg (by rw [solcReturnMem_size]; decide),
          show (⟨64⟩ : UInt256).toNat = 64 from (by decide), solcReturnMem_read64,
          fromByteArrayBigEndian_toByteArray,
          show UInt256.ofNat ((⟨128⟩ : UInt256).toNat) = ⟨128⟩ from (by decide)])
        (by decide) (by evm_ov),
      dup1, swap2, sub, swap1,
      raw ret 0 (UInt256.toByteArray val) (by decide) mem_cost
        (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, sub_ret32_toNat, solcReturnMem_read128])
        (by evm_ov) ]

end Reasoning.Reach

/-! ## Full success trace — `initState → RETURN(2^n)` (**proved**)

Composes the six forward segments (dispatcher → decode → require → loop → exit → encoder) for a
well-formed `pow2(n)` call with `callvalue = 0`, `calldatasize ≥ 36`, matching selector, and
`n < 256`.  Either the run OOGs, or it succeeds returning the 32-byte big-endian word `2^n`. -/
set_option maxHeartbeats 1000000 in
theorem powX_success {cA gh bl σ σ₀ A I} {g : Sat256}
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
      |>.routinecf hsltval (by jump_dest)
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
  exact rd4.routineexit (by jump_dest)
        (by simp only [List.length_cons, List.length_nil]; omega)
      |>.routineencode (by simp only [List.length_cons, List.length_nil]; omega)



namespace Pow

set_option maxRecDepth 10000

/-- **Calldata decode for `pow2(uint256 n)`.**  With at least 36 bytes of calldata, decoding
    succeeds, binding `n` to the EVM's `CALLDATALOAD 4` value. -/
theorem powDecode_n {I : Ethereum.ExecutionEnv} (hsz : 36 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldata (Pow.powTransition.params.map Param.name)
        (transitionSignature Pow.powTransition).paramTypes I.calldata
      = some ((∅ : Solm.Store).insert "n"
          (.int (Int.ofNat (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat))) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hwlt : (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).val.val < EVM.twoPow 256 :=
    (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).val.isLt
  show decodeCalldata ["n"] [Pow.uint256] I.calldata = _
  unfold decodeCalldata decodeCalldata.decodeArgs
  rw [if_neg (by rw [htlen]; omega)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, Pow.uint256,
    decodeABIValues?, decodeABIValue?, readWord?, readBytes?, decodeABIWord?,
    bind, Option.bind, List.drop_zero, htake, hwlt, if_true,
    Bool.false_eq_true, if_false, Nat.zero_add, Nat.add_zero]
  rw [decode_word_at_eq I.calldata 4 (by omega) (by norm_num)]
  rfl

/-- **Calldata decode fails** when `4 ≤ size < 36`: the `uint256` argument can't be read. -/
theorem powDecode_none {I : Ethereum.ExecutionEnv} (hsz36 : I.calldata.size < 36) :
    decodeCalldata (Pow.powTransition.params.map Param.name)
        (transitionSignature Pow.powTransition).paramTypes I.calldata = none := by
  by_cases hsz4 : I.calldata.size < 4
  · show decodeCalldata ["n"] [Pow.uint256] I.calldata = none
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]; rfl
    unfold decodeCalldata; rw [if_pos (by rw [htlen]; omega)]
  · have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]; rfl
    have htake : ¬ (((I.calldata.toList.drop 4).take 32).length = 32) := by
      rw [List.length_take, List.length_drop, htlen]; omega
    show decodeCalldata ["n"] [Pow.uint256] I.calldata = none
    unfold decodeCalldata decodeCalldata.decodeArgs
    rw [if_neg (by rw [htlen]; omega)]
    rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
    simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, Pow.uint256,
      decodeABIValues?, decodeABIValue?, readWord?, readBytes?, bind, Option.bind,
      Nat.add_zero, Nat.zero_add, List.drop_zero, Bool.false_eq_true, if_false, htake]

/-- **Calldata decode fails** when `2^255 + 4 ≤ size`: the args region (`size − 4`) is `≥ 2^255`, so
    solc's **signed** length check `SLT(size − 4, 32) = 1` reverts.  The spec's decoder rejects the
    same calldata via the matching guard (`ABI/Decode.lean`).  Pairs with `powX_hugearg`. -/
theorem powDecode_none_huge {I : Ethereum.ExecutionEnv} (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (Pow.powTransition.params.map Param.name)
        (transitionSignature Pow.powTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  show decodeCalldata ["n"] [Pow.uint256] I.calldata = none
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega)]
  rw [if_pos (⟨rfl, by rw [List.length_drop, htlen]; omega⟩)]

/-! ## EVM revert trace: non-zero call value -/

/-- **`callvalue ≠ 0`**: the non-payable guard fails — `ISZERO` gives `0`, the `JUMPI` is not
    taken, and execution reverts at `PUSH0; PUSH0; REVERT`. -/
theorem powX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev powBytecode g (initState cA gh bl σ σ₀ g A I) := by
  -- prologue → PUSH2 0x0f · JUMPI (not taken: callvalue ≠ 0 ⇒ iszero = 0) → revert stub, one `RD`
  exact evm_run (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) with [
      push2 ⟨15⟩,
      jumpiNT (isZero_eq_zero_of_ne hwv),
      raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

/-! ## EVM revert trace: short calldata (`size < 4`) -/

/-- **`callvalue = 0`, `calldatasize < 4`**: the guard passes, but the calldata-size check
    (`lt(size, 4)`) takes the `JUMPI` to the `0x29` revert stub. -/
theorem powX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    RDrev powBytecode g (initState cA gh bl σ σ₀ g A I) := by
  -- prologue → guard JUMPI (taken, cv=0) → JUMPDEST·POP·PUSH1 4·CALLDATASIZE·LT (=1, size<4)·PUSH2 41·
  --   JUMPI (taken → 41)·JUMPDEST → revert stub at pc 42, as one `RD`
  exact evm_run (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) with [
      push2 ⟨15⟩,
      jumpiT (by rw [hwv]; decide)
             (by jump_dest),
      jumpdest, pop, push1 ⟨4⟩, calldatasize, lt, push2 ⟨41⟩,
      jumpiT (by rw [ult_one (by rw [ulit_toNat' _ (lt_size_of_lt256 (by omega)),
                show (⟨4⟩ : UInt256).toNat = 4 from by decide]; omega)]; decide)
             (by jump_dest),
      jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

/-! ## EVM revert trace: `n ≥ 256` (reuses the dispatcher + decoder) -/

/-- **`callvalue = 0`, valid selector, `calldatasize ≥ 36`, `n ≥ 256`**: dispatch and decode
    succeed (reusing the dispatcher/decoder), then `require(n < 256)` reverts. -/
theorem powX_nlarge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsz255 : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hn : 256 ≤ (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat) :
    RDrev powBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsize : I.calldata.size < UInt256.size := by
    have h0 : (2:ℕ)^255 + 4 < 2^256 := by norm_num
    have hp : (2:ℕ)^255 + 4 < UInt256.size := by simpa [UInt256.size] using h0
    omega
  set sel := UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ with hsel
  set arg := uInt256OfByteArray (I.calldata.readBytes 4 32) with harg
  have hsltval0 : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ := by
    apply slt32_zero <;> (rw [sub4_toNat (by omega) hsize]; omega)
  have h256 : (⟨256⟩ : UInt256).toNat = 256 := by
    show (Fin.ofNat _ 256).val = 256; simp only [Fin.ofNat]
    exact Nat.mod_eq_of_lt (by have := pow_lt_size (show (8:ℕ) < 256 by norm_num); norm_num at this; exact this)
  have hltval : UInt256.lt arg ⟨256⟩ = ⟨0⟩ := ult_zero (by rw [h256]; exact hn)
  -- dispatcher → decoder → cf → require-revert (n ≥ 256), threaded as one `RD` ⇒ `RDrev`
  have rdDec := powX_disp (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
        hcode hwv (by omega) hsize hmatch
      |>.routinedecodeToCf (by omega) hsize
      |>.routinecf hsltval0 (by jump_dest)
          (by simp only [List.length_cons, List.length_nil]; omega)
  rw [show ((⟨4⟩ : UInt256) + ⟨0⟩).toNat = 4 from add40_toNat, ← harg] at rdDec
  exact rdDec |>.routinerequire_revert hltval (by simp only [List.length_nil]; omega)

/-! ## EVM revert trace: wrong selector (reuses `powX_dispToEq`) -/

/-- **`callvalue = 0`, `calldatasize ≥ 4`, selector mismatch**: reuses `powX_dispToEq`, then the
    `EQ` is `0`, the dispatch `JUMPI` is not taken, and execution reverts at `0x29`. -/
theorem powX_nomatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = false) :
    RDrev powBytecode g (initState cA gh bl σ σ₀ g A I) := by
  -- selector compare resolves to `0` (mismatch); the dispatch JUMPI falls through to the revert stub
  have rd := powX_dispToEq (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsz hsize
  rw [show UInt256.eq ⟨1143701499⟩
        (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩) = ⟨0⟩
      from by rw [powEvmSelector hsz, if_neg (by rw [hmatch]; decide)]] at rd
  exact evm_run rd with [
      push2 ⟨45⟩,
      jumpiNT rfl,
      jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

/-! ## EVM revert trace: short argument (`4 ≤ size < 36`, reuses disp + decode prefixes) -/

/-- **`callvalue = 0`, valid selector, `4 ≤ calldatasize < 36`**: dispatch and the decode
    call-setup succeed (reusing `powX_disp` + `powX_decodeToCf`), then the decoder's bounds check
    (`SLT(size−4, 32) = 1`) reverts. -/
theorem powX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsz36 : I.calldata.size < 36)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    RDrev powBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsize : I.calldata.size < UInt256.size := lt_size_of_lt256 (by omega)
  have hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply slt32_one; rw [sub4_toNat (by omega) hsize]; omega
  -- dispatcher → decoder set-up → Cf-revert (SLT bounds check fails), threaded as one `RD` ⇒ `RDrev`
  exact powX_disp hcode hwv hsz4 hsize hmatch
      |>.routinedecodeToCf (by omega) hsize
      |>.routinecf_revert hsltval (by simp only [List.length_cons, List.length_nil]; omega)

/-! ## EVM revert trace: huge calldata (`calldatasize ≥ 2^255 + 4`) -/

/-- **`callvalue = 0`, valid selector, `calldatasize ≥ 2^255 + 4`**: dispatch and the decoder
    call-setup succeed, but the decoder's **signed** bounds check `SLT(size − 4, 32) = 1` reverts —
    here because `size − 4 ≥ 2^255` is a negative two's-complement word.  Mirrors `powX_shortarg`
    (same trace, `slt32_one_high` instead of `slt32_one`); the matching Solm failure is
    `powDecode_none_huge`. -/
theorem powX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    RDrev powBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply slt32_one_high; rw [sub4_toNat (by omega) hsize]; omega
  -- dispatcher → decoder set-up → Cf-revert (SLT bounds check fails), threaded as one `RD` ⇒ `RDrev`
  exact powX_disp hcode hwv (by omega) hsize hmatch
      |>.routinedecodeToCf (by omega) hsize
      |>.routinecf_revert hsltval (by simp only [List.length_cons, List.length_nil]; omega)

/-! ## Dispatch -/

/-- Dispatch reduces (via `powSelectorBytes`) to a 4-byte calldata-prefix comparison. -/
theorem powDispatch_eq (cd : ByteArray) :
    dispatchMsg Pow.powContract cd
      = if ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == cd.extract 0 4)
        then some Pow.powTransition else none :=
  dispatch_eq rfl powSelectorBytes cd

/-- `powContract` has exactly one transition, so any successful dispatch yields it. -/
theorem powDispatch_unique {cd : ByteArray} {t : TransitionDecl}
    (h : dispatchMsg Pow.powContract cd = some t) : t = Pow.powTransition :=
  dispatch_unique rfl h

/-- Short calldata (< 4 bytes) ⇒ dispatch fails. -/
theorem powDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg Pow.powContract cd = none :=
  dispatch_none_short rfl powSelectorBytes rfl h

/-- Selector mismatch ⇒ dispatch fails. -/
theorem powDispatch_none_nomatch {cd : ByteArray}
    (h : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == cd.extract 0 4) = false) :
    dispatchMsg Pow.powContract cd = none :=
  dispatch_none_nomatch rfl powSelectorBytes h

/-! ## Store / expression-evaluation helpers -/

/-- `i < n` evaluates from the locals. -/
theorem evalLt {cfg : Config} {C : ContractDecl} {L : Solm.Store} {evm : EVM.State} {a b : Int}
    (hi : L.get? "i" = some (.int a)) (hn : L.get? "n" = some (.int b)) :
    evalExpr? cfg { contract := C, locals := L } evm (.binary .lt (.var "i") (.var "n"))
      = .ok (.bool (a < b)) := by
  simp only [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, EvalResult.ofOption, hi, hn]

/-- `r * 2` evaluates from the locals. -/
theorem evalMul2 {cfg : Config} {C : ContractDecl} {L : Solm.Store} {evm : EVM.State} {a : Int}
    (hr : L.get? "r" = some (.int a)) :
    evalExpr? cfg { contract := C, locals := L } evm (.binary .mul (.var "r") (.intLit 2))
      = .ok (.int (a * 2)) := by
  simp only [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, EvalResult.ofOption, hr]

/-- `i + 1` evaluates from the locals. -/
theorem evalAdd1 {cfg : Config} {C : ContractDecl} {L : Solm.Store} {evm : EVM.State} {a : Int}
    (hi : L.get? "i" = some (.int a)) :
    evalExpr? cfg { contract := C, locals := L } evm (.binary .add (.var "i") (.intLit 1))
      = .ok (.int (a + 1)) := by
  simp only [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, EvalResult.ofOption, hi]

/-- Reading a plain variable from the locals. -/
theorem evalVar {cfg : Config} {C : ContractDecl} {L : Solm.Store} {evm : EVM.State} {name : Ident}
    {v : Value} (h : L.get? name = some v) :
    evalExpr? cfg { contract := C, locals := L } evm (.var name) = .ok v := by
  simp only [evalExpr?, EvalResult.ofOption, h]

/-! ## The Solm `while` loop computes `2^n` (by induction on the variant `n − i`) -/

/-- The loop body of `pow2`. -/
def powLoopBody : List Stmt :=
  [ .letDecl "r" (some Pow.uint256) (.binary .mul (.var "r") (.intLit 2)),
    .letDecl "i" (some Pow.uint256) (.binary .add (.var "i") (.intLit 1)) ]

/-- The loop condition of `pow2`. -/
def powLoopCond : Expr := .binary .lt (.var "i") (.var "n")

/-- **Solm-side loop core.**  With locals `i ↦ i`, `r ↦ 2^i`, `n ↦ N` and `i ≤ N`, the `while` runs
    (in unbounded `Int`) to an `.ok` state whose locals read `r ↦ 2^N`.  A direct instance of the
    generic `execWhile_var` Hoare rule (variant `N − i`, coupling invariant on the locals). -/
theorem powLoopActCore {cfg : Config} {C : ContractDecl} {evm : EVM.State} (N : ℕ) :
    ∀ (var i : ℕ) (L : Solm.Store),
      N - i = var → i ≤ N →
      L.get? "i" = some (.int (Int.ofNat i)) →
      L.get? "r" = some (.int (Int.ofNat (2 ^ i))) →
      L.get? "n" = some (.int (Int.ofNat N)) →
      ∃ L', ExecStmt cfg { contract := C, locals := L } evm (.while powLoopCond powLoopBody)
              (.ok { contract := C, locals := L' } evm)
            ∧ L'.get? "r" = some (.int (Int.ofNat (2 ^ N))) := by
  -- variant-indexed invariant: `var` iterations left ⟺ a counter `i` with `N − i = var`
  let P : ℕ → Solm.Store → Prop := fun var L =>
    ∃ i, N - i = var ∧ i ≤ N ∧ L.get? "i" = some (.int (Int.ofNat i))
      ∧ L.get? "r" = some (.int (Int.ofNat (2 ^ i))) ∧ L.get? "n" = some (.int (Int.ofNat N))
  have hfalse : ∀ L, P 0 L →
      evalExpr? cfg { contract := C, locals := L } evm powLoopCond = .ok (.bool false) := by
    rintro L ⟨i, hvar, hile, hi, _, hn⟩
    rw [powLoopCond, evalLt hi hn,
        decide_eq_false (by simp only [Int.ofNat_eq_natCast, Nat.cast_lt]; omega)]
  have htrue : ∀ v L, P (v + 1) L →
      evalExpr? cfg { contract := C, locals := L } evm powLoopCond = .ok (.bool true) := by
    rintro v L ⟨i, hvar, hile, hi, _, hn⟩
    rw [powLoopCond, evalLt hi hn,
        decide_eq_true (by simp only [Int.ofNat_eq_natCast, Nat.cast_lt]; omega)]
  have hstep : ∀ v L, P (v + 1) L →
      ∃ L', ExecBlock cfg { contract := C, locals := L } evm powLoopBody
              (.ok { contract := C, locals := L' } evm) ∧ P v L' := by
    rintro v L ⟨i, hvar, hile, hi, hr, hn⟩
    have e1 : (Int.ofNat i + 1 : Int) = Int.ofNat (i + 1) := by
      simp only [Int.ofNat_eq_natCast]; push_cast; ring
    have e2 : (Int.ofNat (2 ^ i) * 2 : Int) = Int.ofNat (2 ^ (i + 1)) := by
      simp only [Int.ofNat_eq_natCast]; push_cast [pow_succ]; ring
    set L1 := L.insert "r" (.int (Int.ofNat (2 ^ i) * 2)) with hL1
    set L2 := L1.insert "i" (.int (Int.ofNat i + 1)) with hL2
    have hL2i : L2.get? "i" = some (.int (Int.ofNat (i + 1))) := by rw [hL2, store_get_self, e1]
    have hL2r : L2.get? "r" = some (.int (Int.ofNat (2 ^ (i + 1)))) := by
      rw [hL2, store_get_ne _ _ (by decide), hL1, store_get_self, e2]
    have hL2n : L2.get? "n" = some (.int (Int.ofNat N)) := by
      rw [hL2, store_get_ne _ _ (by decide), hL1, store_get_ne _ _ (by decide), hn]
    refine ⟨L2, ?_, i + 1, by omega, by omega, hL2i, hL2r, hL2n⟩
    refine ExecBlock.consNormal (ExecStmt.letDecl ?_) (ExecBlock.consNormal (ExecStmt.letDecl ?_)
              ExecBlock.nil)
    · rw [evalMul2 hr]
    · show evalExpr? cfg { contract := C, locals := L1 } evm (.binary .add (.var "i") (.intLit 1))
          = .ok (.int (Int.ofNat i + 1))
      rw [evalAdd1 (by rw [hL1, store_get_ne _ _ (by decide), hi])]
  intro var i L hvar hile hi hr hn
  obtain ⟨L', hwhile, j, hj, hjN, _, hjr, _⟩ :=
    execWhile_var P hfalse htrue hstep var L ⟨i, hvar, hile, hi, hr, hn⟩
  exact ⟨L', hwhile, by rw [hjr, show j = N by omega]⟩

/-! ## The Solm body returns `2^n` (callvalue 0, n < 256) -/
/-- `require(n < 256)` passes when the argument is in range. -/
theorem evalReqN {cfg : Config} {C : ContractDecl} {L : Solm.Store} {evm : EVM.State} {N : ℕ}
    (hn : L.get? "n" = some (.int (Int.ofNat N))) (hN : N < 256) :
    evalExpr? cfg { contract := C, locals := L } evm
        (.binary .lt (.var "n") (.intLit 256)) = .ok (.bool true) := by
  have h : (Int.ofNat N < (256 : Int)) := by simp only [Int.ofNat_eq_natCast]; omega
  simp only [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, EvalResult.ofOption, hn]
  rw [decide_eq_true h]

/-- **The Solm body computes `2^n`.**  With zero call value, `n < 256`, and the decoded argument
    `n ↦ N` in the locals, `pow2`'s body runs to `return (2^N)` (unbounded `Int`). -/
theorem powBodyReturns (evm : EVM.State) (locals : Solm.Store) {N : ℕ}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hN : N < 256)
    (hn : locals.get? "n" = some (.int (Int.ofNat N))) :
    ∃ L', ExecContractBody powConfig Pow.powContract evm locals Pow.powTransition.body
            (.returned { contract := Pow.powContract, locals := L' } evm
              (some (.int (Int.ofNat (2 ^ N))))) := by
  -- locals after `r := 1` and `i := 0`
  set Lr := locals.insert "r" (.int 1) with hLr
  set Lri := Lr.insert "i" (.int 0) with hLri
  have hLri_i : Lri.get? "i" = some (.int (Int.ofNat 0)) := by rw [hLri, store_get_self]; rfl
  have hLri_r : Lri.get? "r" = some (.int (Int.ofNat (2 ^ 0))) := by
    rw [hLri, store_get_ne _ _ (by decide), hLr, store_get_self]; rfl
  have hLri_n : Lri.get? "n" = some (.int (Int.ofNat N)) := by
    rw [hLri, store_get_ne _ _ (by decide), hLr, store_get_ne _ _ (by decide), hn]
  -- run the loop
  obtain ⟨L', hwhile, hL'r⟩ :=
    powLoopActCore (cfg := powConfig) (C := Pow.powContract) (evm := evm) N
      N 0 Lri (by omega) (by omega) hLri_i hLri_r hLri_n
  -- the body reads forward: require · require · let r:=1 · let i:=0 · while · return r
  exact ⟨L', ExecFuncBody.execBlockRet <|
    ABlock.start
      |>.requireStep (evalCallvalueEq_true hwv)
      |>.requireStep (evalReqN hn hN)
      |>.letStep (value := .int 1) (by simp only [evalExpr?]; rfl)
      |>.letStep (value := .int 0) (by simp only [evalExpr?]; rfl)
      |>.whileStep hwhile
      |>.returns (evalVar hL'r)⟩

/-! ## The Solm body reverts (callvalue ≠ 0, or n ≥ 256) -/

/-- Non-zero call value ⇒ `require(callvalue == 0)` fails, body reverts. -/
theorem powBodyReverts_cv (evm : EVM.State) (locals : Solm.Store)
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecContractBody powConfig Pow.powContract evm locals Pow.powTransition.body .reverted :=
  bodyReverts_nonPayable h

/-- `n ≥ 256` (with zero call value) ⇒ `require(n < 256)` fails, body reverts. -/
theorem powBodyReverts_n (evm : EVM.State) (locals : Solm.Store) {N : ℕ}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hN : 256 ≤ N)
    (hn : locals.get? "n" = some (.int (Int.ofNat N))) :
    ExecContractBody powConfig Pow.powContract evm locals Pow.powTransition.body .reverted :=
  ExecFuncBody.execBlockRevert <|
    (ABlock.start.requireStep (evalCallvalueEq_true hwv)).requireRevert (by
      have h : ¬ (Int.ofNat N < (256 : Int)) := by simp only [Int.ofNat_eq_natCast]; omega
      show evalExpr? powConfig _ evm (.binary .lt (.var "n") (.intLit 256)) = .ok (.bool false)
      simp only [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, EvalResult.ofOption, hn]
      rw [decide_eq_false h])

/-! ## ABI encoding of the `uint256` return value `2^n` -/

/-- `EVM.word` and `UInt256.ofNat` agree (both are `⟨n % 2^256⟩`). -/
theorem evm_word_eq_ofNat (n : ℕ) : EVM.word n = UInt256.ofNat n := rfl

/-- The 32-byte big-endian ABI encoding of `2^N` (for `N < 256`, so it fits a word) is exactly the
    EVM `RETURN` word `UInt256.ofNat (2^N)`. -/
theorem powReturnEncoding {N : ℕ} (hN : N < 256) :
    encodeReturnValue? Pow.uint256 (.int (Int.ofNat (2 ^ N)))
      = some (UInt256.toByteArray (UInt256.ofNat (2 ^ N))) := by
  have hlt : Int.ofNat (2 ^ N) < Int.ofNat (EVM.twoPow 256) := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_lt, EVM.twoPow]
    exact Nat.pow_lt_pow_right (by norm_num) hN
  -- the single ABI value encodes to the 32 big-endian bytes of `ofNat (2^N)`
  have hval : encodeABIValue? Pow.uint256 (.int (Int.ofNat (2 ^ N)))
                = some (EVM.Word.toBytesBE (UInt256.ofNat (2 ^ N))) := by
    simp only [Pow.uint256, encodeABIValue?, encodeABIWord?]
    rw [if_neg (by decide), if_pos ⟨Int.natCast_nonneg _, hlt⟩, evm_word_eq_ofNat]; rfl
  have hdyn : isDynamicABIType Pow.uint256 = false := rfl
  have hhead : abiTupleHeadSize? [Pow.uint256] = some 32 := by
    simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, Pow.uint256, bind,
      Option.bind]
    decide
  rw [toByteArray_eq_toBytesBE,
    show encodeReturnValue? Pow.uint256 (.int (Int.ofNat (2 ^ N)))
        = encodeReturnValues? [Pow.uint256] [.int (Int.ofNat (2 ^ N))] from rfl]
  simp only [encodeReturnValues?, encodeABIValues?, hhead, encodeABIValuesFrom?, hval, hdyn,
    bind, Option.bind, if_false, Bool.false_eq_true, List.nil_append, List.append_nil]

/-! ## The runtime-equivalence assembly -/

/-- The dispatched transition's `n`-store the decoder produces. -/
private def powCallargs (I : Ethereum.ExecutionEnv) : Solm.Store :=
  (∅ : Solm.Store).insert "n"
    (.int (Int.ofNat (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat))

/-- **`callvalue = 0` case**: split on calldata size and the selector to land in one of
    `noDispatch` / `decodingFailed` / `execution`. -/
theorem powReEquiv_callvalueZero {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) :
    runtimeEquivalenceFor powConfig Pow.powContract cA gh bl σ σ₀ g.toUInt256 A I := by
  by_cases hsz4 : I.calldata.size < 4
  · -- short calldata ⇒ noDispatch
    exact (powX_short hcode hwv hsz4).reEquivNoDispatch hcode (powDispatch_none_short hsz4)
  · rw [not_lt] at hsz4
    by_cases hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true
    · have hd : dispatchMsg Pow.powContract I.calldata = some Pow.powTransition := by
        rw [powDispatch_eq, if_pos hmatch]
      by_cases hsz36 : I.calldata.size < 36
      · -- decode fails ⇒ decodingFailed
        exact (powX_shortarg hcode hwv hsz4 hsz36 hmatch).reEquivDecodingFailed hcode hd
          (powDecode_none hsz36)
      · rw [not_lt] at hsz36
        by_cases hbig : 2 ^ 255 + 4 ≤ I.calldata.size
        · -- huge calldata: solc's signed `SLT(size−4,32)` reverts (decoder), Solm decode fails too
          exact (powX_hugearg hcode hwv hbig hsize hmatch).reEquivDecodingFailed hcode hd
            (powDecode_none_huge hbig)
        · rw [not_le] at hbig
          by_cases hn : (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat < 256
          · -- success: EVM returns 2^n, Solm body returns 2^n
            obtain ⟨L', hbody⟩ := powBodyReturns (initState cA gh bl σ σ₀ g A I) (powCallargs I)
              (by simp only [initState]; exact hwv) hn (by rw [powCallargs, store_get_self])
            exact (powX_success hcode hwv hsz36 hbig hmatch hn).reEquivExecution hcode hd
              (powDecode_n hsz36 hbig) hbody (returnEquiv_of_encode (powReturnEncoding hn))
          · -- n ≥ 256 ⇒ body reverts (execution)
            rw [not_lt] at hn
            exact (powX_nlarge hcode hwv hsz36 hbig hmatch hn).reEquivExecutionRevert hcode hd
              (powDecode_n hsz36 hbig)
              (powBodyReverts_n (initState cA gh bl σ σ₀ g A I) (powCallargs I)
                (by simp only [initState]; exact hwv) hn (by rw [powCallargs, store_get_self]))
    · -- wrong selector ⇒ noDispatch
      rw [Bool.not_eq_true] at hmatch
      exact (powX_nomatch hcode hwv hsz4 hsize hmatch).reEquivNoDispatch hcode
        (powDispatch_none_nomatch hmatch)

/-! ## (Kept pending cleanup) Pow's `Ξ`-success, exposed via `RDret.xiResult`.

Built when the plan was to reuse a verified callee's behavior in a caller proof.  The external-call
proof instead treats the sub-call as opaque (the caller has no runtime guarantee that the callee is
Pow), so this is **not** used by `Caller`; retained for now. -/
theorem powXiSuccess {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = powBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsz255 : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x44, 0x2b, 0x7f, 0xfb]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hn : (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat < 256) :
    Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .OutOfGass
    ∨ ∃ (g' : UInt256) (A' : Substate),
        Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (cA, σ, g', A')
          (UInt256.toByteArray
            (UInt256.ofNat (2 ^ (uInt256OfByteArray (I.calldata.readBytes 4 32)).toNat)))) :=
  (powX_success hcode hwv hsz36 hsz255 hmatch hn).xiResult hcode

/-- **Runtime equivalence of `Pow.sol`'s `pow2` bytecode and its Solm specification.** -/
theorem powCorrect : runtimeEquivalence!?! powConfig powBytecode Pow.powContract := by
  refine ⟨fun cA gh bl σ σ₀ g A I hcode hsize _hperm => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact powReEquiv_callvalueZero (g := Sat256.ofUInt256 g) hcode hwv hsize
  · -- callvalue ≠ 0: the non-payable guard reverts; the generic helper handles the Solm coupling
    exact (powX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivNonPayable hcode rfl
      fun ca => powBodyReverts_cv _ ca (by simp only [initState]; exact hwv)

end Pow
