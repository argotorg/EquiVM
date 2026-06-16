import Examples.Caller.Bytecode
import Examples.Caller.Spec
import Reasoning.Theory
import Reasoning.Dispatch
import Reasoning.ActBody
import Reasoning.Stepping
import Reasoning.Memory
import Reasoning.Solc
import Reasoning.Reach

/-!
# Caller — runtime-equivalence proof for `run(address t, uint256 n)`

`run` makes an **external call** `t.pow2(n)` and stores the result in `stored`.  The external call
is *opaque*: nothing is assumed about the code at `t`.  The EVM `CALL` and the Act `externalCall`
invoke the identical `Θ`, so the opaque `(z, σ', o)` coincide on both sides by construction; the
success branch then stores `decode(o)` (EVM `SSTORE` ↔ Act `.assign`).  Built on `RD.call`.
-/

open Act ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 10000

namespace Caller

/-! ## Act-side dispatch facts (mirror `Truth`) -/

/-- Dispatch reduces (via `callerSelectorBytes`) to a 4-byte calldata-prefix comparison. -/
theorem callerDispatch_eq (cd : ByteArray) :
    dispatchMsg callerContract cd
      = if ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == cd.extract 0 4)
        then some runTransition else none :=
  dispatch_eq rfl callerSelectorBytes cd

theorem callerDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg callerContract cd = none :=
  dispatch_none_short rfl callerSelectorBytes rfl h

theorem callerDispatch_none_nomatch {cd : ByteArray}
    (h : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == cd.extract 0 4) = false) :
    dispatchMsg callerContract cd = none :=
  dispatch_none_nomatch rfl callerSelectorBytes h

/-- With non-zero call value, the Act body reverts: `require(callvalue == 0)` fails. -/
theorem callerBodyReverts (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecContractBody callerConfig callerContract evm locals runTransition.body .reverted :=
  bodyReverts_nonPayable h

/-! ## JUMPDEST membership facts -/

theorem callerContains15 : (D_J callerBytecode ⟨0⟩).contains ⟨15⟩ = true := by
  rw [callerValidJumps]; exact Array.contains_eq_true_of_mem (by simp)
theorem callerContains41 : (D_J callerBytecode ⟨0⟩).contains ⟨41⟩ = true := by
  rw [callerValidJumps]; exact Array.contains_eq_true_of_mem (by simp)
theorem callerContains45 : (D_J callerBytecode ⟨0⟩).contains ⟨45⟩ = true := by
  rw [callerValidJumps]; exact Array.contains_eq_true_of_mem (by simp)

/-! ## Selector decode (generic instance) -/

/-- The EVM selector check `eq(0x381fd190, SHR(calldata,224))` agrees with the dispatcher's
    4-byte compare `0x381fd190 == calldata.extract 0 4`. -/
theorem callerEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨941609360⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0x38 0x1f 0xd1 0x90 ⟨941609360⟩ (by decide)

/-! ## Decoder arithmetic helpers -/

/-- solc's `dataEnd = headStart + (calldatasize − headStart)` collapses to `calldatasize`. -/
theorem add4_sub4 {sz : ℕ} (h4 : 4 ≤ sz) (hsz : sz < UInt256.size) :
    (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat sz) ⟨4⟩ = UInt256.ofNat sz := by
  apply u256_inj
  have ho : (UInt256.ofNat sz).toNat = sz := by
    show (Fin.ofNat _ sz).val = sz; simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hsz
  have h4n : (⟨4⟩ : UInt256).toNat = 4 := by decide
  have hsub : (UInt256.sub (UInt256.ofNat sz) ⟨4⟩).toNat = sz - 4 := by
    rw [show UInt256.sub (UInt256.ofNat sz) ⟨4⟩ = UInt256.ofNat sz - UInt256.ofNat 4 from rfl,
        toNat_sub_ofNat (by rw [ho]; exact h4), ho]
  rw [uadd_toNat, h4n, hsub, ho, show 4 + (sz - 4) = sz from by omega, Nat.mod_eq_of_lt hsz]

/-- `SLT a 64 = 0` (signed) when `64 ≤ a < 2^255`. -/
theorem slt64_zero {a : UInt256} (hlo : 64 ≤ a.toNat) (hhi : a.toNat < 2 ^ 255) :
    UInt256.slt a ⟨64⟩ = ⟨0⟩ := by
  have h64 : (⟨64⟩ : UInt256).toNat = 64 := by decide
  have hbool : UInt256.sltBool a ⟨64⟩ = false := by
    unfold UInt256.sltBool
    rw [if_neg (show ¬ a.toNat ≥ 2 ^ 255 by omega),
        if_neg (show ¬ (⟨64⟩ : UInt256).toNat ≥ 2 ^ 255 by rw [h64]; norm_num)]
    exact decide_eq_false (show ¬ a < ⟨64⟩ by
      show ¬ a.toNat < (⟨64⟩ : UInt256).toNat; rw [h64]; omega)
  show UInt256.fromBool (UInt256.sltBool a ⟨64⟩) = ⟨0⟩
  rw [hbool]; rfl

/-- `(128 + n) − 128 = n` (no overflow) when `n < 2²⁵⁵` — the decoder's `dataEnd − headStart`. -/
theorem add128_sub128 {n : ℕ} (hn : n < 2 ^ 255) :
    UInt256.sub (UInt256.add ⟨128⟩ (UInt256.ofNat n)) ⟨128⟩ = UInt256.ofNat n := by
  apply u256_inj
  have hsz : (2:ℕ) ^ 255 + 128 < UInt256.size := by norm_num [UInt256.size]
  have ho : (UInt256.ofNat n).toNat = n := by
    show n % UInt256.size = n; exact Nat.mod_eq_of_lt (by omega)
  have h128 : (⟨128⟩ : UInt256).toNat = 128 := by decide
  have hadd : (UInt256.add ⟨128⟩ (UInt256.ofNat n)).toNat = 128 + n := by
    rw [show UInt256.add ⟨128⟩ (UInt256.ofNat n) = ⟨128⟩ + UInt256.ofNat n from rfl, uadd_toNat,
        h128, ho]
    exact Nat.mod_eq_of_lt (by omega)
  rw [show UInt256.sub (UInt256.add ⟨128⟩ (UInt256.ofNat n)) ⟨128⟩
        = UInt256.add ⟨128⟩ (UInt256.ofNat n) - UInt256.ofNat 128 from rfl,
      toNat_sub_ofNat (by rw [hadd]; omega), hadd, ho]
  omega

/-- `SLT (ofNat n) 32 = 0` (signed) when `32 ≤ n < 2²⁵⁵` — the decoder's `≥ 32` length check passes. -/
theorem slt32_zero {n : ℕ} (hlo : 32 ≤ n) (hhi : n < 2 ^ 255) :
    UInt256.slt (UInt256.ofNat n) ⟨32⟩ = ⟨0⟩ := by
  have hsz : (2:ℕ) ^ 255 < UInt256.size := by norm_num [UInt256.size]
  have ho : (UInt256.ofNat n).toNat = n := by
    show n % UInt256.size = n; exact Nat.mod_eq_of_lt (by omega)
  have h32 : (⟨32⟩ : UInt256).toNat = 32 := by decide
  have hbool : UInt256.sltBool (UInt256.ofNat n) ⟨32⟩ = false := by
    unfold UInt256.sltBool
    rw [if_neg (show ¬ (UInt256.ofNat n).toNat ≥ 2 ^ 255 by rw [ho]; omega),
        if_neg (show ¬ (⟨32⟩ : UInt256).toNat ≥ 2 ^ 255 by rw [h32]; norm_num)]
    exact decide_eq_false (show ¬ UInt256.ofNat n < ⟨32⟩ by
      show ¬ (UInt256.ofNat n).toNat < (⟨32⟩ : UInt256).toNat; rw [ho, h32]; omega)
  show UInt256.fromBool (UInt256.sltBool (UInt256.ofNat n) ⟨32⟩) = ⟨0⟩
  rw [hbool]; rfl

theorem callerContains491 : (D_J callerBytecode ⟨0⟩).contains ⟨491⟩ = true := by
  rw [callerValidJumps]; exact Array.contains_eq_true_of_mem (by simp)

/-! ## EVM traces (revert scenarios) -/

/-- `callvalue ≠ 0`: the non-payable guard reverts (prologue → not-taken JUMPI → revert stub). -/
theorem callerX_callvalue_ne
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) with [
      push2 ⟨15⟩,
      jumpiNT (isZero_eq_zero_of_ne hwv),
      raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

/-- The shared dispatcher prefix for `callvalue = 0`: through the non-payable guard's taken jump
    (`0x08 → 0x0f`) and on to the `0x18` (24) `JUMPI`, reaching pc 24 with stack `[41, size < 4]`. -/
theorem callerX_cvz_prefix
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩) :
    RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨24⟩
        [⟨41⟩, UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) 14 53 := by
  exact evm_run (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) with [
      push2 ⟨15⟩,
      jumpiT (by rw [hwv]; decide) callerContains15,
      jumpdest, pop, push1 ⟨4⟩, calldatasize, lt, push2 ⟨41⟩ ]

/-- `callvalue = 0 ∧ calldatasize < 4`: the prefix's `JUMPI` jumps to the `0x29` (41) revert stub. -/
theorem callerX_cvz_short
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run (callerX_cvz_prefix hcode hwv) with [
    jumpiT (lt_four_ne_zero_of_lt hsz) callerContains41,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

/-- `calldatasize ≥ 4, wrong selector`: fall through the size JUMPI, decode/compare the selector
    (`EQ = 0`), and revert at `0x29` (41). -/
theorem callerX_cvz_revertB
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = false) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run (callerX_cvz_prefix hcode hwv) with [
    jumpiNT (lt_four_eq_zero_of_ge hsz hsize),
    push0, calldataload, push1 ⟨224⟩, shr, dup1, push4 ⟨941609360⟩, eq, push2 ⟨45⟩,
    jumpiNT (by rw [show ((⟨0⟩ : UInt256).toNat) = 0 from by decide, callerEvmSelector hsz];
                simp [hmatch]),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

/-! ## Success path — the dispatcher reaches the `run` dispatch at pc 45 -/

theorem callerContains348 : (D_J callerBytecode ⟨0⟩).contains ⟨348⟩ = true := by
  rw [callerValidJumps]; exact Array.contains_eq_true_of_mem (by simp)

/-- **Dispatcher (match path).**  `callvalue = 0`, `calldatasize ≥ 4`, selector matches: reaches the
    `run` dispatch `JUMPDEST` at pc 45, leaving the decoded selector word on the stack. -/
theorem callerX_disp {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨45⟩
        [UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) 24 96 := by
  have rd := evm_run (callerX_cvz_prefix (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (g := g) hcode hwv) with [
    jumpiNT (lt_four_eq_zero_of_ge hsz hsize),
    push0, calldataload, push1 ⟨224⟩, shr, dup1, push4 ⟨941609360⟩, eq ]
  rw [show ((⟨0⟩ : UInt256).toNat) = 0 from by decide,
      show UInt256.eq ⟨941609360⟩
          (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩) = ⟨1⟩
        from by rw [callerEvmSelector hsz, if_pos hmatch]] at rd
  exact evm_run rd with [
    push2 ⟨45⟩,
    jumpiT (by decide) callerContains45 ]

/-- **run-dispatch (pc 45 → arg-decoder entry pc 348).**  Pushes the two return addresses
    (`0x42 = 66` after decode, `0x47 = 71` after body), sets up `[headStart=4, dataEnd]`, and jumps
    into solc's `abi_decode_tuple_(address,uint256)` at pc 348. -/
theorem callerX_toDecoder {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨348⟩
        [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) 38 140 := by
  have rd := evm_run (callerX_disp (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (g := g) hcode hwv hsz hsize hmatch) with [
    jumpdest, push2 ⟨71⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1, push2 ⟨66⟩,
    swap2, swap1, push2 ⟨348⟩,
    jump callerContains348 ]
  rwa [add4_sub4 hsz hsize] at rd

/-! ## The opaque-call coincidence (the conceptual crux)

The EVM `CALL` (via `RD.call`) and the Act `externalCall` (via `externalCallViaEVM`) invoke the
*identical* `Θ` with the *same* arguments, so the opaque result `(cA', σ', z, o)` coincides on both
sides by construction — no assumption about the callee's code is used.  Coupling the two `Θ`
applications needs two primitive identities (the address round-trip the `CALL` opcode performs, and
`wordOfInt 0 = ⟨0⟩`) plus the trace-supplied arg equalities (target, calldata). -/

/-- The 160-bit address round-trip the EVM `CALL` opcode performs on `msg.sender`:
    `ofUInt256 (ofNat addr) = addr`. -/
theorem accountAddress_roundtrip (a : AccountAddress) :
    AccountAddress.ofUInt256 (UInt256.ofNat a.val) = a := by
  have hsize : AccountAddress.size < UInt256.size := by decide
  have hlt : a.val < AccountAddress.size := a.isLt
  have hv : ((UInt256.ofNat a.val).val : ℕ) = a.val := by
    show ((Fin.ofNat _ a.val) : Fin UInt256.size).val = a.val
    simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt (lt_trans hlt hsize)
  apply Fin.ext
  simp only [AccountAddress.ofUInt256, Fin.ofNat, hv]
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]

/-- `wordOfInt 0 = ⟨0⟩` — the zero value word a value-free `CALL` forwards. -/
theorem wordOfInt_zero : EVM.wordOfInt 0 = (⟨0⟩ : UInt256) := by decide

/-- **Coincidence.**  Given the EVM-side `Θ`-link produced by `RD.call` (with witnesses `A_in`,
    `callGas`) and the trace couplings (the Act target `tgt` is the cleaned stack address, the Act
    encoding is the calldata the bytecode placed in memory), the Act `externalCallViaEVM` holds for
    the *same* opaque `(z, σ', o)`.  Instantiate the Act existentials with the EVM witnesses; `Θ`'s
    determinism does the rest. -/
theorem callerCallCoincides
    {evm : EVM.State} {nv : ℤ} {tgt : EVM.Address} {targetWord : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {A' A_in : Ethereum.Substate}
    {z : Bool} {o : ByteArray} {g'' callGas : UInt256}
    {mem : ByteArray} {inOff inSize : UInt256}
    (hperm : evm.executionEnv.perm = true)
    (hdepth : evm.executionEnv.depth ≠ 1024)
    (htgt : tgt = AccountAddress.ofUInt256 targetWord)
    (hcd : callerExternalABI.encode? "pow2" [.int nv]
            = some (mem.readWithPadding inOff.toNat inSize.toNat))
    (hΘ : (cA', σ', g'', A', z, o) =
        Ethereum.EVM.Θ evm.executionEnv.blobVersionedHashes evm.createdAccounts evm.genesisBlockHeader
          evm.blocks evm.accountMap evm.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat evm.executionEnv.codeOwner)) evm.executionEnv.sender
          (AccountAddress.ofUInt256 targetWord) (toExecute evm.accountMap (AccountAddress.ofUInt256 targetWord))
          callGas (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOff.toNat inSize.toNat) (evm.executionEnv.depth + 1)
          evm.executionEnv.header evm.executionEnv.perm) :
    externalCallViaEVM callerConfig evm tgt "pow2" 0 [.int nv]
      (z, { evm with accountMap := σ', substate := A', createdAccounts := cA' }, o) := by
  -- rewrite the EVM `Θ`-link into the Act form (round-trip sender, `tgt`, `perm = true`)
  have h := hΘ
  rw [accountAddress_roundtrip, ← htgt, hperm] at h
  exact @externalCallViaEVM.callMade callerConfig evm tgt "pow2" 0 [.int nv] (fun _ _ => g'')
    (mem.readWithPadding inOff.toNat inSize.toNat) ⟨0⟩ cA' σ' A' z o
    { evm with accountMap := σ', substate := A', createdAccounts := cA' }
    (by rw [show callerConfig.externalABI = callerExternalABI from rfl, hcd]; rfl)
    wordOfInt_zero.symm ⟨callGas, A_in, h⟩ rfl
    (by show (⟨0⟩ : UInt256) ≤ _; exact Fin.zero_le _) hdepth

/-! ## Decoder trace (abi_decode (address,uint256)) -/

/-- All `callerBytecode` jump targets validated by one tactic (mirrors `callerContains15`). -/
macro "caller_jd" : term => `(by rw [callerValidJumps]; exact Array.contains_eq_true_of_mem (by simp))

/-- Decoder segment: bounds-check (`datalen ≥ 64`) passes, set up arg0 offset, jump to the address
    element decoder at pc 277.  Counters existential. -/
theorem callerX_dec277 {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨277⟩
        [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨383⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
          UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have ho : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size := by
    show (Fin.ofNat _ I.calldata.size).val = I.calldata.size
    simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hsize
  have hsub : (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩).toNat = I.calldata.size - 4 := by
    rw [show UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩
          = UInt256.ofNat I.calldata.size - UInt256.ofNat 4 from rfl,
        toNat_sub_ofNat (by rw [ho]; omega), ho]
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    slt64_zero (by rw [hsub]; omega) (by rw [hsub]; omega)
  exact ⟨_, _, evm_run (callerX_toDecoder (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (g := g) hcode hwv hsz hsize hmatch) with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero, push2 ⟨370⟩,
    jumpiT (by rw [hslt]; decide) caller_jd,
    jumpdest, push0, push2 ⟨383⟩, dup6, dup3, dup7, add, push2 ⟨277⟩,
    jump caller_jd ]⟩

/-- Address-mask literal (`PUSH20 0xff…ff`). -/
def addrMask : UInt256 := ⟨1461501637330902918203684832716283019655932542975⟩

/-- Decoder segment: load + cleanup arg0 (address), reaching the clean-address check at pc 264.
    `tw` is the raw calldata word at offset 4, `tc = tw & addrMask` the cleaned address. -/
theorem callerX_dec264 {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨264⟩
        [UInt256.land (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)) addrMask,
          uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32),
          ⟨291⟩, uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32),
          ⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨383⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
          UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := callerX_dec277 hcode hwv hsz hsize hsz68 hszhi hmatch
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, dup2, calldataload, swap1, pop, push2 ⟨291⟩, dup2, push2 ⟨255⟩, jump caller_jd,
    jumpdest, push2 ⟨264⟩, dup2, push2 ⟨238⟩, jump caller_jd,
    jumpdest, push0, push2 ⟨248⟩, dup3, push2 ⟨207⟩, jump caller_jd,
    jumpdest, push0, push20 addrMask, dup3, and, swap1, pop, swap2, swap1, pop, jump caller_jd,
    jumpdest, swap1, pop, swap2, swap1, pop, jump caller_jd ]⟩

/-- The decoded calldata address word at offset 4. -/
abbrev callerArg0 (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

/-- Decoder segment: the clean-address check passes (`address` canonical), return to pc 291. -/
theorem callerX_dec291 {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨291⟩
        [callerArg0 I, ⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨383⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
          UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := callerX_dec264 hcode hwv hsz hsize hsz68 hszhi hmatch
  exact ⟨_, _, evm_run rd with [
    jumpdest, dup2, eq, push2 ⟨274⟩, jumpiT (by rw [hclean]; decide) caller_jd,
    jumpdest, pop, jump caller_jd ]⟩

theorem ueq_self (a : UInt256) : UInt256.eq a a = ⟨1⟩ := by
  have h : UInt256.eq a a = UInt256.ofNat 1 := by simp [UInt256.eq, UInt256.fromBool]
  rw [h]; rfl

/-- The decoded calldata uint256 word at offset 36. -/
abbrev callerArg1 (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

/-- Decoder final segment: decode arg1 (uint256), return to the dispatch point pc 66 with the two
    decoded values `[n, t, 71, sel]` on the stack. -/
theorem callerX_decoded {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨66⟩
        [callerArg1 I, callerArg0 I, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := callerX_dec291 hcode hwv hsz hsize hsz68 hszhi hmatch hclean
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, swap2, pop, pop, jump caller_jd,
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨400⟩, dup6, dup3, dup7, add, push2 ⟨328⟩, jump caller_jd,
    jumpdest, push0, dup2, calldataload, swap1, pop, push2 ⟨342⟩, dup2, push2 ⟨306⟩, jump caller_jd,
    jumpdest, push2 ⟨315⟩, dup2, push2 ⟨297⟩, jump caller_jd,
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump caller_jd,
    jumpdest, dup2, eq, push2 ⟨325⟩, jumpiT (by rw [ueq_self]; decide) caller_jd,
    jumpdest, pop, jump caller_jd,
    jumpdest, swap3, swap2, pop, pop, jump caller_jd,
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop, jump caller_jd ]⟩

/-! ## Body trace: encode `pow2(n)` calldata, reach the CALL -/

/-- Body segment: clean the target address, load the free pointer, build the selector word; reach
    the first `MSTORE` (selector → mem[128]) at pc 117. -/
theorem callerX_body117 {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨117⟩
        [⟨128⟩, UInt256.shiftLeft (UInt256.land ⟨4294967295⟩ ⟨1143701499⟩) ⟨224⟩, ⟨128⟩, callerArg1 I,
          ⟨1143701499⟩, UInt256.land addrMask (callerArg0 I), callerArg1 I, callerArg0 I, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := callerX_decoded hcode hwv hsz hsize hsz68 hszhi hmatch hclean
  exact ⟨_, _, evm_run rd with [
    jumpdest, push2 ⟨73⟩, jump caller_jd,
    jumpdest, dup2, push20 addrMask, and, push4 ⟨1143701499⟩, dup3, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      (fun s haws hstks => by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          Fin.isValue, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos,
          Nat.one_lt_ofNat, getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide)
      (by rw [if_neg (by rw [solcFreePtrMem_size]; decide),
          show (⟨64⟩ : UInt256).toNat = 64 from (by decide), solcFreePtrMem_read64,
          fromByteArrayBigEndian_toByteArray,
          show UInt256.ofNat ((⟨128⟩ : UInt256).toNat) = ⟨128⟩ from (by decide)])
      (by decide) (by evm_ov),
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2 ]⟩

/-- Memory after writing the (left-shifted) `pow2` selector to `mem[128]`. -/
noncomputable def callerSelMem : ByteArray :=
  (UInt256.shiftLeft (UInt256.land ⟨4294967295⟩ ⟨1143701499⟩) ⟨224⟩).toByteArray.write 0
    solcFreePtrMem 128 32

/-- Body segment: store the selector, set up the encoder call, jump to the uint256 encoder at pc 425. -/
theorem callerX_body425 {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨425⟩
        [⟨4⟩ + ⟨128⟩, callerArg1 I, ⟨130⟩, ⟨1143701499⟩, UInt256.land addrMask (callerArg0 I),
          callerArg1 I, callerArg0 I, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        callerSelMem (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := callerX_body117 hcode hwv hsz hsize hsz68 hszhi hmatch hclean
  exact ⟨_, _, evm_run rd with [
    raw mstore 6 callerSelMem (UInt256.ofNat 5) (by decide)
      (fun s haws hstks => by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          Fin.isValue, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos,
          Nat.one_lt_ofNat, getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide)
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩, add, push2 ⟨130⟩, swap2, swap1, push2 ⟨425⟩, jump caller_jd ]⟩

/-- Memory after the encoder writes `n` at mem[132] (the full `pow2(n)` calldata at mem[128..164]). -/
noncomputable def callerCalldataMem (I : ExecutionEnv) : ByteArray :=
  (callerArg1 I).toByteArray.write 0 callerSelMem 132 32

/-- The free-memory pointer the body MLOADs at offset 64 (carried symbolically; provably `⟨128⟩`). -/
noncomputable def callerOutPtr (I : ExecutionEnv) : UInt256 :=
  if (⟨64⟩ : UInt256).toNat ≥ (callerCalldataMem I).size ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩
  then ⟨0⟩
  else UInt256.ofNat (fromByteArrayBigEndian ((callerCalldataMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))

/-- `callerSelMem` is exactly the generic solc "store a word at `0x80`" memory (`solcReturnMem`)
    applied to the shifted selector, so its size / read-backs are the generic ones. -/
theorem callerSelMem_size : callerSelMem.size = 160 := solcReturnMem_size _

theorem callerSelMem_read64 : callerSelMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  solcReturnMem_read64 _

/-- The full `pow2(n)` calldata buffer is 164 bytes (`0x80 .. 0xa4`). -/
theorem callerCalldataMem_size (I : ExecutionEnv) : (callerCalldataMem I).size = 164 := by
  unfold callerCalldataMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [callerSelMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract, callerSelMem_size, toByteArray_size]
  omega

/-- The free pointer (`mem[0x40]`) is untouched by the selector/arg writes: it still reads `0x80`. -/
theorem callerCalldataMem_read64 (I : ExecutionEnv) :
    (callerCalldataMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold callerCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size]) (by rw [callerSelMem_size]; omega)
        (by omega), callerSelMem_read64]

/-- **The output pointer the `CALL` uses is `0x80`** — the byte-level coupling that ties the decoder's
    read region to the `CALL` out-region. -/
theorem callerOutPtr_eq (I : ExecutionEnv) : callerOutPtr I = ⟨128⟩ := by
  unfold callerOutPtr
  rw [if_neg (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, callerCalldataMem_size]
        rintro (h | h)
        · omega
        · exact absurd h (by decide)),
      show (⟨64⟩ : UInt256).toNat = 64 from by decide, callerCalldataMem_read64,
      fromByteArrayBigEndian_toByteArray, show UInt256.ofNat ((⟨128⟩ : UInt256).toNat) = ⟨128⟩ from by decide]

/-- Body segment: run the uint256 encoder (MSTORE `n` at mem[132]), set up and MLOAD for the CALL,
    reaching the GAS at pc 142 (just before the `CALL`). -/
theorem callerX_toCall142 {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨142⟩
        [UInt256.land addrMask (callerArg0 I), ⟨0⟩, callerOutPtr I,
          UInt256.sub ⟨164⟩ (callerOutPtr I), callerOutPtr I, ⟨32⟩, ⟨164⟩, ⟨1143701499⟩,
          UInt256.land addrMask (callerArg0 I), callerArg1 I, callerArg0 I, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        (callerCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := callerX_body425 hcode hwv hsz hsize hsz68 hszhi hmatch hclean
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨444⟩, push0, dup4, add, dup5,
    push2 ⟨410⟩, jump caller_jd,
    jumpdest, push2 ⟨419⟩, dup2, push2 ⟨297⟩, jump caller_jd,
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump caller_jd,
    jumpdest, dup3,
    raw mstore 3 (callerCalldataMem I) (UInt256.ofNat 6) (by decide)
      (fun s haws hstks => by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          Fin.isValue, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos,
          getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide)
      (by rfl) (by decide) (by evm_ov),
    pop, pop, jump caller_jd,
    jumpdest, swap3, swap2, pop, pop, jump caller_jd,
    jumpdest, push1 ⟨32⟩, push1 ⟨64⟩,
    raw mload 0 (callerOutPtr I) (UInt256.ofNat 6) (by decide)
      (fun s haws hstks => by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          Fin.isValue, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos,
          getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide)
      (by rfl) (by decide) (by evm_ov),
    dup1, dup4, sub, dup2, push0, dup8 ]⟩

/-- **The opaque CALL executes in the trace.**  GAS then `RD.call` (value 0): the result
    `(cA', σ', z, o)` is the *opaque* `Θ` output, and the run reaches the post-CALL `ISZERO` at pc 143
    with the success flag on the stack — no assumption about the callee's code. -/
theorem callerX_afterCall {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (mem' : ByteArray) (aw' : UInt256) (rdata' : ByteArray) (k' C' : ℕ),
      RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨142⟩ + ⟨1⟩ + ⟨1⟩)
        ((if z then ⟨1⟩ else ⟨0⟩) ::
          ⟨164⟩ :: ⟨1143701499⟩ :: UInt256.land addrMask (callerArg0 I) :: callerArg1 I ::
          callerArg0 I :: ⟨71⟩ ::
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ :: [])
        mem' aw' rdata' (cA', σ') k' C' := by
  obtain ⟨k, C, rd142⟩ := callerX_toCall142 hcode hwv hsz hsize hsz68 hszhi hmatch hclean
  obtain ⟨gv, rd143⟩ := rd142.gas (by decide) (by evm_ov)
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', _hΘ, rd144⟩ := rd143.call (by decide) hdepth (by evm_ov)
  exact ⟨cA', σ', z, _, _, _, k', C', rd144⟩

/-- **Post-call failure tail** (`z = false`): the `CALL` returned `0`, so the solc check
    `iszero(success)` jumps into the `RETURNDATACOPY … REVERT` bail-out — the whole run reverts,
    independent of the (opaque) return data. -/
theorem callerX_postRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ} {rest : List UInt256}
    (rd : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨142⟩ + ⟨1⟩ + ⟨1⟩)
            (⟨0⟩ :: rest) mem aw rdata acc k C)
    (hov : rest.length + 4 ≤ 1024) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  -- 144 ISZERO; 145 DUP1; 146 ISZERO; 147 PUSH2 158; 150 JUMPI (not taken, z = false)
  have rd151 : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I)
      (⟨142⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩)
      (UInt256.isZero ⟨0⟩ :: rest) mem aw rdata acc _ _ :=
    evm_run rd with [iszero, dup1, iszero, push2 ⟨158⟩, jumpiNT (by decide)]
  -- 151 RETURNDATASIZE; 152 PUSH0; 153 PUSH0; 154 RETURNDATACOPY
  obtain ⟨mem2, aw2, k2, C2, rd155⟩ :=
    RD.returndatacopyFull rd151 (by decide) (by decide) (by decide) (by decide)
      (by simp only [List.length_cons]; omega)
  -- 155 RETURNDATASIZE; 156 PUSH0; 157 REVERT
  have rd156 := RD.returndatasize rd155 (by decide) (by simp only [List.length_cons]; omega)
  have rd157 := RD.push0 rd156 (by decide) (by simp only [List.length_cons]; omega)
  exact RD.rev _ rd157 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by simp only [List.length_cons]; omega)

theorem callerContains158 : (D_J callerBytecode ⟨0⟩).contains ⟨158⟩ = true := by
  rw [callerValidJumps]; exact Array.contains_eq_true_of_mem (by simp)

/-- **Post-call success prefix** (`z = true`): the `CALL` returned `1`, so `iszero(success)` is
    false and control jumps to pc 158, the 4 dead stack words are `POP`ped, and `PUSH1 64` pushes the
    free-pointer slot address — reaching the `MLOAD` at pc 165 with stack `[64, arg1, arg0, 71, sel]`.
    (`d0 d1 d2` are the three dispatcher words above `arg1` that the `POP`s discard.) -/
theorem callerX_succ_to165 {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ}
    {d0 d1 d2 : UInt256} {tl : List UInt256}
    (rd : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨142⟩ + ⟨1⟩ + ⟨1⟩)
            (⟨1⟩ :: d0 :: d1 :: d2 :: tl) mem aw rdata acc k C)
    (hov : tl.length + 7 ≤ 1024) :
    ∃ k' C', RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨165⟩
        (⟨64⟩ :: tl) mem aw rdata acc k' C' := by
  -- 144 ISZERO; DUP1; ISZERO; PUSH2 158; JUMPI (taken, z = true) → 158; POP×4; PUSH1 64
  refine ⟨_, _, evm_run rd with [iszero, dup1, iszero, push2 ⟨158⟩,
    jumpiT (by decide) callerContains158, jumpdest, pop, pop, pop, pop, push1 ⟨64⟩]⟩

theorem callerContains470 : (D_J callerBytecode ⟨0⟩).contains ⟨470⟩ = true := by
  rw [callerValidJumps]; exact Array.contains_eq_true_of_mem (by simp)

/-- **Success decoder, straight-line part (165 → 470).**  `MLOAD` the free pointer (`fp = 128`),
    `RETURNDATASIZE` (= `|o|`), round up and bump the free pointer (`MSTORE` at `0x40`), compute
    `dataEnd = 128 + |o|`, and jump into the length-checking decoder subroutine at pc 470 — leaving
    `[128, 128+|o|, 194, …]` on the stack.  Active words stay `⟨6⟩`, so every memory op is free. -/
theorem callerX_succ_to470 {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {o : ByteArray} {k C : ℕ} {arg1 arg0 sel : UInt256}
    (rd : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨165⟩
            [⟨64⟩, arg1, arg0, ⟨71⟩, sel] mem ⟨6⟩ o acc k C)
    (hfp : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ ⟨6⟩ * ⟨32⟩ then ⟨0⟩
           else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
          = ⟨128⟩) :
    ∃ mem2 k' C', RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨470⟩
      [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨194⟩, arg1, arg0, ⟨71⟩, sel]
      mem2 ⟨6⟩ o acc k' C' := by
  refine ⟨_, _, _, evm_run rd with [
    raw mload 0 ⟨128⟩ ⟨6⟩ (by decide)
      (fun s haws hstks => by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
        Fin.isValue, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos,
        Nat.one_lt_ofNat, getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide)
      hfp (by decide) (by evm_ov),
    returndatasize,
    push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and, dup3, add, dup1, push1 ⟨64⟩,
    raw mstore 0 ((UInt256.add ⟨128⟩ (UInt256.land (UInt256.add (UInt256.ofNat o.size) ⟨31⟩)
        (UInt256.lnot ⟨31⟩))).toByteArray.write 0 mem 64 32) ⟨6⟩ (by decide)
      (fun s haws hstks => by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
        Fin.isValue, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos,
        Nat.one_lt_ofNat, getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide)
      (by rfl) (by decide) (by evm_ov),
    pop, dup2, add, swap1, push2 ⟨194⟩, swap2, swap1, push2 ⟨470⟩, jump callerContains470 ]⟩

/-- **Success decoder, length check (470 → 491).**  `slt(dataEnd − headStart, 32) = slt(|o|, 32) = 0`
    (since `|o| ≥ 32`), so `iszero` is `1` and the `JUMPI` jumps past the bail-out to pc 491. -/
theorem callerX_succ_to491 {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem2 : ByteArray} {o : ByteArray} {k C : ℕ} {arg1 arg0 sel : UInt256}
    (rd : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨470⟩
            [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨194⟩, arg1, arg0, ⟨71⟩, sel]
            mem2 ⟨6⟩ o acc k C)
    (ho32 : 32 ≤ o.size) (ho : o.size < 2 ^ 255) :
    ∃ k' C', RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨491⟩
      [⟨0⟩, ⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨194⟩, arg1, arg0, ⟨71⟩, sel]
      mem2 ⟨6⟩ o acc k' C' := by
  refine ⟨_, _, evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨491⟩,
    jumpiT (by rw [add128_sub128 ho, slt32_zero ho32 ho]; decide) callerContains491 ]⟩

/-! ## The `callvalue = 0` Act coupling -/

theorem callerReEquiv_callvalueZero
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = callerBytecode) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) :
    runtimeEquivalenceFor callerConfig callerContract cA gh bl σ σ₀ g A I := by
  by_cases hsz : I.calldata.size < 4
  · exact (callerX_cvz_short hcode hwv hsz).reEquivNoDispatch hcode (callerDispatch_none_short hsz)
  · rw [not_lt] at hsz
    by_cases hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true
    · -- matching selector → `run` executes the external call and stores the result
      sorry
    · rw [Bool.not_eq_true] at hmatch
      exact (callerX_cvz_revertB hcode hwv hsz hsize hmatch).reEquivNoDispatch hcode
        (callerDispatch_none_nomatch hmatch)

/-! ## The correctness statement -/

/-- The runtime bytecode refines the Act specification, for every initial state. -/
theorem callerCorrect :
    runtimeEquivalence!?! callerConfig callerBytecode callerContract := by
  refine ⟨fun cA gh bl σ σ₀ g A I hcode hsize _hperm => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact callerReEquiv_callvalueZero hcode hsize hwv
  · exact (callerX_callvalue_ne hcode hwv).reEquivNonPayable hcode rfl
      fun ca => callerBodyReverts _ ca (by simp only [initState]; exact hwv)

end Caller
