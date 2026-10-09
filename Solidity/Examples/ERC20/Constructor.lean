import Solidity.Examples.ERC20.Transfer
import Reasoning.Initcode

/-!
# ERC20 — the constructor refines its Solidity body

The deployed code is `erc20Creation ++ abi.encode(initialSupply)`.  The creation code copies the
argument word from its own tail to `0x80`, checks its length, stores it into `balanceOf[msg.sender]`
and `totalSupply`, emits `Transfer(address(0), msg.sender, initialSupply)`, and returns the runtime
code (`CODECOPY` of bytes `0x99 .. 0x99 + 0x55a`).  Every instruction lies in the fixed prefix, so
decodes and jump destinations transfer from `erc20Creation` to the appended code
(`decode_append_left_window`, `D_J_contains_append_left`).
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Trace

set_option maxRecDepth 2000000

namespace ERC20.Opt

/-! ## Static facts -/

theorem erc20Flat_topCtor : topCtor? erc20Flat = some fnCtor := rfl
theorem erc20Flat_immZero : immZero erc20Flat = some ∅ := rfl
theorem erc20Flat_initializers : initializers erc20Flat = [] := rfl
theorem erc20Flat_ctorAbiTys : ctorAbiTys erc20Flat = some [abiU256] := rfl
theorem erc20Creation_size : erc20Creation.size = 1523 := rfl

theorem ctorPayable_erc20 {I : ExecutionEnv} : ctorPayable erc20Flat I ↔ I.weiValue = ⟨0⟩ :=
  ctorPayable_iff_of_nonpayable erc20Flat_topCtor (by decide)

/-- Only a single in-range `uint256` deploys; the deployed code is the creation code followed by
    the argument word. -/
theorem deployment_shape {args : List Solm.Value} {dep : ByteArray}
    (h : erc20Cfg.selfDeployment erc20Creation args = some dep) :
    ∃ w : UInt256, args = [.int (Int.ofNat w.toNat)] ∧ dep = erc20Creation ++ UInt256.toByteArray w := by
  have h : (ABI.encodeABIValues? [abiU256] args).bind (fun enc => some (erc20Creation ++ enc.toByteArray)) =
      some dep := h
  rcases args with _ | ⟨arg, _ | ⟨arg2, rest⟩⟩
  · simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, ABI.abiTupleHeadSize?, abiU256] at h
  · cases arg with
    | int i =>
      simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
        ABI.isDynamicABIType, ABI.encodeABIValue?, ABI.encodeABIWord?, abiU256] at h
      split at h
      · rename_i hbounds
        simp at h
        have hlt' : i.toNat < UInt256.size := by
          have h1 : i.toNat < EVM.twoPow 256 := (Int.toNat_lt hbounds.1).mpr hbounds.2
          simpa [EVM.twoPow, UInt256.size] using h1
        have hw : (EVM.word i.toNat).toNat = i.toNat := ulit_toNat' _ hlt'
        refine ⟨EVM.word i.toNat, ?_, ?_⟩
        · rw [hw]; exact congrArg (fun x => [Solm.Value.int x]) (Int.toNat_of_nonneg hbounds.1).symm
        · rw [← h, word_toBytesBE_toByteArray_eq_toByteArray]
      · simp at h
    | _ =>
      simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
        ABI.isDynamicABIType, ABI.encodeABIValue?, ABI.encodeABIWord?, abiU256] at h
  · simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
      ABI.isDynamicABIType, ABI.encodeABIValue?, ABI.encodeABIWord?, abiU256] at h

/-! ## The creation code with its argument word -/

abbrev ctorCode (w : UInt256) : ByteArray := erc20Creation ++ UInt256.toByteArray w

theorem ctorCode_size (w : UInt256) : (ctorCode w).size = 1555 := by
  rw [ByteArray.size_append, erc20Creation_size, toByteArray_size]

theorem ctorCode_decode (w : UInt256) (pc : UInt256) (hpc : pc.toNat < 1490) :
    decode (ctorCode w) pc = decode erc20Creation pc :=
  decode_append_left_window erc20Creation _ pc (by rw [erc20Creation_size]; omega)
    (by rw [erc20Creation_size]; norm_num)

/-- `decode (ctorCode w) pc = op` for a concrete in-prefix `pc`. -/
macro "ctor_decode" : tactic => `(tactic| (rw [ctorCode_decode _ _ (by decide)]; native_decide))
/-- `(D_J (ctorCode w) 0).contains pc = true` for an in-prefix `JUMPDEST`. -/
macro "ctor_jd" : tactic => `(tactic| (apply Reasoning.Theory.D_J_contains_append_left; native_decide))

open Lean in
/-- `evm_run` with the decode obligation discharged by `ctor_decode`. -/
macro "ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) => acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by ctor_decode) $(args[0]!) $(args[1]!) (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

/-! ## Memory facts beyond the 96-byte scratch space -/

/-- `write` of a window of `src` at or past the end of `base`: a zero gap, then the window. -/
theorem write_gap_eq (src base : ByteArray) (srcAddr dest len : ℕ) (hlen : len ≠ 0)
    (hsrc : srcAddr + len ≤ src.size) (hoff : base.size ≤ dest) (_hgap : dest - base.size < USize.size) :
    src.write srcAddr base dest len =
      base ++ ByteArray.zeroes (dest - base.size) ++ src.extract srcAddr (srcAddr + len) := by
  have hsd : src.data.size = src.size := rfl
  have hpz : (ByteArray.zeroes (dest - base.size)).data.size = dest - base.size := by
    rw [show (ByteArray.zeroes (dest - base.size)).data.size = (ByteArray.zeroes (dest - base.size)).size from rfl,
      ByteArray_zeroes_size]
  have hDsz : (base.data ++ (ByteArray.zeroes (dest - base.size)).data).size = dest := by
    rw [Array.size_append, hpz]; show base.size + (dest - base.size) = dest; omega
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ (srcAddr ≥ src.size) from by omega)]
  simp only [ByteArray.data_copySlice, ByteArray.data_append, ByteArray.data_extract]
  rw [show min len (src.size - srcAddr) = len from by omega,
    show min base.size (dest + len) - (dest + len) = 0 from by omega,
    show (ByteArray.zeroes 0).data = (#[] : Array UInt8) from by rw [zeroes_zero (n := 0) (by rfl)]; rfl]
  simp only [Array.append_empty, Nat.add_zero]
  rw [Array.extract_eq_self_of_le (by rw [hDsz]),
    show min len (src.data.size - srcAddr) = len from by omega,
    Array.extract_eq_empty_of_le (as := base.data ++ (ByteArray.zeroes (dest - base.size)).data) (i := dest + len)
      (by rw [hDsz]; omega),
    Array.append_empty]

theorem twoWordHashMem_size_of_le {mem : ByteArray} (key slot : UInt256) (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  have h0 : (wordAt0Mem key mem).size = mem.size :=
    toByteArray_write32_size_of_le mem key 0 mem.size mem.size rfl (by omega) (by omega)
  unfold twoWordHashMem wordAt32Mem
  exact toByteArray_write32_size_of_le _ slot 32 mem.size mem.size h0 (by omega) (by omega)

theorem twoWordHashMem_read0_64_of_le {mem : ByteArray} (key slot : UInt256) (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 = UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  have h0 : (wordAt0Mem key mem).size = mem.size :=
    toByteArray_write32_size_of_le mem key 0 mem.size mem.size rfl (by omega) (by omega)
  have hsz : (twoWordHashMem key slot mem).size = mem.size := twoWordHashMem_size_of_le key slot hmem
  rw [show (64 : ℕ) = 32 + 32 from rfl,
    byteArray_readWithPadding_split _ 0 32 32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by omega), Nat.zero_add]
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size]) (by omega) (by omega), wordAt0Mem_read0,
    toByteArray_write32_read_back _ _ 32 (by omega)]

theorem twoWordHashMem_read64_of_le {mem : ByteArray} (key slot : UInt256) (hmem : 96 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 = mem.readWithPadding 64 32 := by
  have h0 : (wordAt0Mem key mem).size = mem.size :=
    toByteArray_write32_size_of_le mem key 0 mem.size mem.size rfl (by omega) (by omega)
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size]) (by omega) (by omega) (by omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega) (by omega) (by omega)]

theorem twoWordHashMem_slot_of_le (baseSlot key : UInt256) {mem : ByteArray} (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian (Ethereum.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_of_le key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

/-! ## The memories of the construction run -/

/-- After the argument is copied to `0x80`. -/
noncomputable abbrev cm1 (w : UInt256) : ByteArray :=
  solcFreePtrMem ++ ByteArray.zeroes 32 ++ UInt256.toByteArray w
/-- After the free pointer is set to `0xa0`. -/
noncomputable abbrev cm2 (w : UInt256) : ByteArray := (UInt256.toByteArray ⟨0xa0⟩).write 0 (cm1 w) 64 32
/-- The mapping-slot hash input `msg.sender ‖ 0`. -/
noncomputable abbrev cm4 (I : ExecutionEnv) (w : UInt256) : ByteArray := twoWordHashMem (callerW I) ⟨0⟩ (cm2 w)
/-- The log data written at the free pointer. -/
noncomputable abbrev cm5 (I : ExecutionEnv) (w : UInt256) : ByteArray :=
  (UInt256.toByteArray w).write 0 (cm4 I w) 160 32
/-- The runtime code copied to `0`. -/
noncomputable abbrev cm6 (I : ExecutionEnv) (w : UInt256) : ByteArray := (ctorCode w).write 153 (cm5 I w) 0 1370

theorem cm1_eq (w : UInt256) : (ctorCode w).write 1523 solcFreePtrMem 128 32 = cm1 w := by
  rw [write_gap_eq _ _ 1523 128 32 (by decide) (by rw [ctorCode_size]) (by rw [solcFreePtrMem_size]; omega)
    (lt_usize _ (by omega)), solcFreePtrMem_size, show (128 - 96 : ℕ) = 32 from rfl,
    extract_append_right' _ _ _ _ erc20Creation_size.symm (by rw [erc20Creation_size, toByteArray_size])]

theorem cm1_size (w : UInt256) : (cm1 w).size = 160 := by
  rw [ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size _ (by norm_num),
    toByteArray_size]

theorem cm1_read128 (w : UInt256) : (cm1 w).readWithPadding 128 32 = UInt256.toByteArray w := by
  have hX : (solcFreePtrMem ++ ByteArray.zeroes 32).size = 128 := by
    rw [ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size _ (by norm_num)]
  rw [readWithPadding_eq_extract _ 128 (by rw [cm1_size]),
    extract_append_right' _ _ _ _ hX.symm (by rw [hX, toByteArray_size])]

theorem cm2_size (w : UInt256) : (cm2 w).size = 160 :=
  toByteArray_write32_size_of_le _ _ 64 160 160 (cm1_size w) (by rw [cm1_size]; omega) (by omega)

theorem cm2_read64 (w : UInt256) : (cm2 w).readWithPadding 64 32 = UInt256.toByteArray ⟨0xa0⟩ :=
  toByteArray_write32_read_back _ _ 64 (by rw [cm1_size]; omega)

theorem cm2_read128 (w : UInt256) : (cm2 w).readWithPadding 128 32 = UInt256.toByteArray w := by
  rw [write32_read_above _ _ 64 128 (by rw [toByteArray_size]) (by rw [cm1_size]; omega) (by omega) (by rw [cm1_size])]
  exact cm1_read128 w

theorem cm4_size (I : ExecutionEnv) (w : UInt256) : (cm4 I w).size = 160 := by
  rw [twoWordHashMem_size_of_le _ _ (by rw [cm2_size]; omega), cm2_size]

theorem cm4_read64 (I : ExecutionEnv) (w : UInt256) : (cm4 I w).readWithPadding 64 32 = UInt256.toByteArray ⟨0xa0⟩ := by
  rw [twoWordHashMem_read64_of_le _ _ (by rw [cm2_size]; omega)]
  exact cm2_read64 w

theorem cm4_slot (I : ExecutionEnv) (w : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian (Ethereum.KEC ((cm4 I w).readWithPadding 0 64))) =
      solcMappingSlot ⟨0⟩ (callerW I) :=
  twoWordHashMem_slot_of_le ⟨0⟩ (callerW I) (by rw [cm2_size]; omega)

theorem cm5_size (I : ExecutionEnv) (w : UInt256) : (cm5 I w).size = 192 :=
  toByteArray_write32_size_of_ge _ _ 160 160 192 (cm4_size I w) (le_refl _) (lt_usize _ (by norm_num)) rfl

theorem cm5_read160 (I : ExecutionEnv) (w : UInt256) : (cm5 I w).readWithPadding 160 32 = UInt256.toByteArray w :=
  toByteArray_write_read_back_of_gap w _ 160 (lt_usize _ (by rw [cm4_size]; norm_num))

theorem cm5_read64 (I : ExecutionEnv) (w : UInt256) : (cm5 I w).readWithPadding 64 32 = UInt256.toByteArray ⟨0xa0⟩ := by
  rw [write32_read_below _ _ 160 64 (by rw [toByteArray_size]) (by rw [cm4_size]) (by omega)]
  exact cm4_read64 I w

theorem cm6_read (I : ExecutionEnv) (w : UInt256) : (cm6 I w).readWithPadding 0 1370 = erc20Runtime := by
  rw [write0_read_back_from_gen _ _ 153 1370 (by decide) (by rw [ctorCode_size]; omega) (by norm_num),
    extract_append_left _ _ _ _ (by rw [erc20Creation_size])]
  native_decide

/-! ## The EVM runs -/

abbrev ctorLog (I : ExecutionEnv) (w : UInt256) : LogEntry :=
  ⟨I.codeOwner, #[transferTopic, ⟨0⟩, callerW I], UInt256.toByteArray w⟩

theorem ctorGuard {σ σ₀ A I} {g : Sat256} {w : UInt256} (hcode : I.code = ctorCode w) :
    Run (ctorCode w) (initState σ σ₀ g A I)
      ⟨⟨8⟩, [UInt256.isZero I.weiValue, I.weiValue], solcFreePtrMem, UInt256.ofNat 3, ByteArray.empty,
        ⟨A.createdAccounts, σ, A.logSeries⟩⟩ 6 26 :=
  Run.solcGuardPrologue hcode (by ctor_decode) (by ctor_decode) (by ctor_decode) (by ctor_decode) (by ctor_decode)
    (by ctor_decode)

theorem ctorRunNonPayable {σ σ₀ A I} {g : Sat256} {w : UInt256} (hcode : I.code = ctorCode w)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    Reverted (ctorCode w) (initState σ σ₀ g A I) ByteArray.empty :=
  Run.solcGuardCallvalueNonzeroRevert (ctgt := ⟨0x0e⟩) (wC := 1) (opC := .PUSH1) (ctorGuard hcode) hwv (by decide)
    (by ctor_decode) (by ctor_decode) (by ctor_decode) (by ctor_decode) (by ctor_decode)

theorem ctorRunOk {σ σ₀ A I} {g : Sat256} {w : UInt256} (hcode : I.code = ctorCode w) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) :
    Returned (ctorCode w) (initState σ σ₀ g A I)
      ⟨A.createdAccounts, sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨0⟩ (callerW I)) w) ⟨2⟩ w,
        A.logSeries.push (ctorLog I w)⟩ erc20Runtime := by
  obtain ⟨_, _, h0'⟩ := Run.solcGuardCallvalueZero (ctgt := ⟨0x0e⟩) (wC := 1) (opC := .PUSH1) (ctorGuard hcode) hwv
    (by decide) (by ctor_decode) (by ctor_decode) (by ctor_decode) (by ctor_decode) (by ctor_jd)
  have h0 : Run (ctorCode w) (initState σ σ₀ g A I)
      ⟨⟨0x10⟩, [], solcFreePtrMem, UInt256.ofNat 3, ByteArray.empty, ⟨A.createdAccounts, σ, A.logSeries⟩⟩ _ _ := h0'
  -- the argument word: copied from the code tail to `0x80`, length-checked, loaded
  have h1 := ctor_run h0 with [push1 ⟨0x40⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by ctor_decode) mem_cost
      (mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) solcFreePtrMem_read64) (by decide) (by evm_ov),
    push2 ⟨0x5f3⟩, codesize, sub]
  rw [show UInt256.sub (UInt256.ofNat (ctorCode w).size) ⟨0x5f3⟩ = ⟨32⟩ from by rw [ctorCode_size]; decide] at h1
  have h2 := ctor_run h1 with [dup1, push2 ⟨0x5f3⟩, dup4,
    raw codecopy 6 (cm1 w) (UInt256.ofNat 5) (by ctor_decode) mem_cost (cm1_eq w) (by decide) (by evm_ov),
    dup2, add]
  rw [show (⟨128⟩ : UInt256) + ⟨32⟩ = ⟨0xa0⟩ from by decide] at h2
  have h3 := ctor_run h2 with [push1 ⟨0x40⟩, dup2, swap1,
    raw mstore 0 (cm2 w) (UInt256.ofNat 5) (by ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨0x2b⟩, swap2, push1 ⟨0x76⟩, jump (by ctor_jd), jumpdest, push0, push1 ⟨0x20⟩, dup3, dup5, sub]
  rw [show UInt256.sub (⟨0xa0⟩ : UInt256) ⟨128⟩ = ⟨0x20⟩ from by decide] at h3
  have h4 := ctor_run h3 with [slt]
  rw [show UInt256.slt (⟨0x20⟩ : UInt256) ⟨0x20⟩ = ⟨0⟩ from by decide] at h4
  have h5 := ctor_run h4 with [iszero]
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at h5
  have h6 := ctor_run h5 with [push1 ⟨0x85⟩, jumpiT (by decide) (by ctor_jd), jumpdest, pop,
    raw mload 0 w (UInt256.ofNat 5) (by ctor_decode) mem_cost
      (mloadWordValue_of_readWithPadding (off := ⟨128⟩) (by rw [cm2_size]; decide) (cm2_read128 w))
      (by decide) (by evm_ov),
    swap2, swap1, pop, jump (by ctor_jd)]
  -- `balanceOf[msg.sender] = initialSupply; totalSupply = initialSupply;`
  have h7 := ctor_run h6 with [jumpdest, caller, push0, dup2, dup2,
    raw mstore 0 (wordAt0Mem (callerW I) (cm2 w)) (UInt256.ofNat 5) (by ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨0x20⟩, dup2, dup2,
    raw mstore 0 (cm4 I w) (UInt256.ofNat 5) (by ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push1 ⟨0x40⟩, dup1, dup4,
    raw keccak256 0 (solcMappingSlot ⟨0⟩ (callerW I)) (UInt256.ofNat 5) (by ctor_decode) mem_cost (cm4_slot I w)
      (by decide) (by evm_ov),
    dup6, swap1]
  obtain ⟨_, _, h8'⟩ := h7.sstore hperm (by ctor_decode) (by evm_ov)
  have h8 : Run (ctorCode w) (initState σ σ₀ g A I)
      ⟨⟨0x3e⟩, ⟨0x40⟩ :: ⟨0x20⟩ :: ⟨0⟩ :: callerW I :: [w], cm4 I w, UInt256.ofNat 5, ByteArray.empty,
        ⟨A.createdAccounts, sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨0⟩ (callerW I)) w, A.logSeries⟩⟩ _ _ := h8'
  have h9 := ctor_run h8 with [push1 ⟨2⟩, dup6, swap1]
  obtain ⟨_, _, h10'⟩ := h9.sstore hperm (by ctor_decode) (by evm_ov)
  have h10 : Run (ctorCode w) (initState σ σ₀ g A I)
      ⟨⟨0x43⟩, ⟨0x40⟩ :: ⟨0x20⟩ :: ⟨0⟩ :: callerW I :: [w], cm4 I w, UInt256.ofNat 5, ByteArray.empty,
        ⟨A.createdAccounts, sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨0⟩ (callerW I)) w) ⟨2⟩ w,
          A.logSeries⟩⟩ _ _ := h10'
  -- `emit Transfer(address(0), msg.sender, initialSupply);`
  have h11 := ctor_run h10 with [
    raw mload 0 ⟨0xa0⟩ (UInt256.ofNat 5) (by ctor_decode) mem_cost
      (mloadWordValue_of_readWithPadding (off := ⟨0x40⟩) (by rw [cm4_size]; decide) (cm4_read64 I w))
      (by decide) (by evm_ov),
    dup5, dup2,
    raw mstore 3 (cm5 I w) (UInt256.ofNat 6) (by ctor_decode) mem_cost rfl (by decide) (by evm_ov)]
  have h12 := h11.pushConst (width := 32) (op := .PUSH32) transferTopic (by decide) (by ctor_decode) (by evm_ov)
  have h13 := ctor_run h12 with [swap2, add, push1 ⟨0x40⟩,
    raw mload 0 ⟨0xa0⟩ (UInt256.ofNat 6) (by ctor_decode) mem_cost
      (mloadWordValue_of_readWithPadding (off := ⟨0x40⟩) (by rw [cm5_size]; decide) (cm5_read64 I w))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1]
  rw [show UInt256.sub (⟨0x20⟩ + ⟨0xa0⟩) ⟨0xa0⟩ = ⟨0x20⟩ from by decide] at h13
  have h14 := h13.log3 0 (UInt256.ofNat 6) (by ctor_decode) hperm mem_cost (by decide) (by evm_ov)
  rw [show (⟨0xa0⟩ : UInt256).toNat = 160 from rfl, show (⟨0x20⟩ : UInt256).toNat = 32 from rfl, cm5_read160] at h14
  -- return the runtime code
  have h15 := ctor_run h14 with [pop, push1 ⟨0x8c⟩, jump (by ctor_jd), jumpdest, push2 ⟨0x55a⟩, dup1, push2 ⟨0x99⟩, push0,
    raw codecopy 114 (cm6 I w) (UInt256.ofNat 43) (by ctor_decode) mem_cost rfl (by decide) (by evm_ov),
    push0]
  have hret := h15.retVar (by ctor_decode) (by evm_ov)
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨0x55a⟩ : UInt256).toNat = 1370 from rfl, cm6_read] at hret
  exact hret

/-! ## The spec derivation -/

def ctorStmts : Block :=
  [ .exprStmt (.assign .assign (.index (.ident "balanceOf") msgSender) (.ident "initialSupply")),
    .exprStmt (.assign .assign (.ident "totalSupply") (.ident "initialSupply")),
    .emit (.ident "Transfer") (.positional
      [ .call (.typeExpr addrTy) [] (.positional [.lit (.number 0 none none)]), msgSender, .ident "initialSupply" ]) ]

/-- The (empty) immutables the constructor frame starts from. -/
abbrev imms0 : Store := immStore (initRoot erc20Flat ∅)

def ctorFrame (w : UInt256) : Frame :=
  ({ here := "ERC20", locals := imms0, retVars := [] } : Frame).bind "initialSupply" u256 (some .memory) (u256Val w.toNat)

theorem ctorEnter (m : Machine) (w : UInt256) :
    enterFn erc20Cfg erc20Flat.types "ERC20" fnCtor.decl [u256Val w.toNat] m imms0 = some (.ok (ctorFrame w, m)) := by
  simp [enterFn, declare, coerce, fnCtor, ctorFrame, fuelDefault]
  try rfl

abbrev cSlot (m : Machine) : UInt256 := balSlot m.evm.executionEnv.source
noncomputable abbrev cM1 (m : Machine) (w : UInt256) : Machine := storeU256 m (cSlot m) w
noncomputable abbrev cM2 (m : Machine) (w : UInt256) : Machine := storeU256 (cM1 m w) ⟨2⟩ w
noncomputable abbrev cLe (m : Machine) (w : UInt256) : LogEntry :=
  { address := (cM2 m w).this,
    topics := #[hashWord evTransfer.sigStr.toUTF8, UInt256.ofNat (EVM.address 0).toNat,
      UInt256.ofNat (cM2 m w).evm.executionEnv.source.toNat],
    data := UInt256.toByteArray w }
noncomputable abbrev cFinal (m : Machine) (w : UInt256) : Machine := (cM2 m w).pushLog (cLe m w)

theorem ctorBody (o : Oracle) (m : Machine) (w : UInt256) :
    ExecBlock erc20Cfg o erc20Flat (bodyFrame (ctorFrame w) ctorStmts) m ctorStmts
      (.normal (bodyFrame (ctorFrame w) ctorStmts) (cFinal m w)) := by
  refine ExecBlock.cons (ExecStmt.assignStorageU256 (w := w)
    (EvalExpr.localVal u256 (some .memory)
      (by frame_simp [bodyFrame, ctorFrame, immStore, initRoot, Std.HashMap.getElem?_filter']))
    (EvalLValue.mappingAddr (by frame_simp [bodyFrame, ctorFrame, immStore, initRoot, Std.HashMap.getElem?_filter'])
      erc20Flat_var_balanceOf rfl rfl EvalExpr.msgSender)
    (erc20Leaf_balanceOf _)) ?_
  refine ExecBlock.cons (ExecStmt.assignStorageU256 (w := w)
    (EvalExpr.localVal u256 (some .memory)
      (by frame_simp [bodyFrame, ctorFrame, immStore, initRoot, Std.HashMap.getElem?_filter']))
    (EvalLValue.stateVarTy (by frame_simp [bodyFrame, ctorFrame, immStore, initRoot, Std.HashMap.getElem?_filter'])
      erc20Flat_var_totalSupply rfl rfl)
    (erc20Leaf_totalSupply)) ?_
  exact ExecBlock.cons (ExecStmt.emitAddrAddrU256 (a := EVM.address 0) (b := (cM2 m w).evm.executionEnv.source) (n := w)
    erc20Flat_eventsNamed_Transfer rfl rfl rfl
    (EvalExprs.three (EvalExpr.convertPlain (EvalExpr.numLit 0 none) (explicitConv_lit0_address _ _))
      EvalExpr.msgSender
      (EvalExpr.localVal u256 (some .memory)
        (by frame_simp [bodyFrame, ctorFrame, immStore, initRoot, Std.HashMap.getElem?_filter'])))) ExecBlock.nil

theorem ctorSpec (o : Oracle) {σ σ₀ g A I} (w : UInt256) (hwv : I.weiValue = ⟨0⟩) :
    solidityCtorExec erc20Cfg o erc20Flat [.int (Int.ofNat w.toNat)] σ σ₀ g A I
      (.ok (cFinal (initMachine σ σ₀ g A I ∅) w)
        (immStore ((ctorFrame w).exitScope (bodyFrame (ctorFrame w) ctorStmts)))) := by
  have hargs : ofAbiList erc20Flat.types ((topCtor? erc20Flat).map (·.decl.params.map (·.ty)) |>.getD [])
      [.int (Int.ofNat w.toNat)] {} = some ([u256Val w.toNat], {}) := by
    simp [erc20Flat_topCtor, fnCtor, ofAbiList, fuelDefault]
  refine solidityCtorExec.run (frI := initRoot erc20Flat ∅) (m1 := initMachine σ σ₀ g A I ∅)
    (tbl := [("ERC20", [u256Val w.toNat])]) (m2 := initMachine σ σ₀ g A I ∅)
    (ctorPayable_erc20.mpr hwv) erc20Flat_immZero hargs ?_ ?_ ?_
  · rw [erc20Flat_initializers]; exact ExecInits.nil
  · rw [erc20Flat_ctorChain]; exact CtorArgsAll.single rfl
  · rw [erc20Flat_ctorChain]
    exact ExecCtorChain.topPlain (step := ⟨"ERC20", some 0, none⟩) (fid := 0) rfl erc20Flat_fns0 (ctorEnter _ w) rfl rfl
      (ctorBody o _ w) rfl

/-! ## The coupled result -/

theorem erc20Constructor : constructorEquivalence erc20Cfg erc20Creation erc20Flat (constCode erc20Runtime) := by
  refine constructorEquivalence.intro ?_
  intro σ σ₀ g A I args dep hdeploy hcode _hcalldata hperm
  obtain ⟨w, hargs, hdep⟩ := deployment_shape hdeploy
  subst hargs
  rw [hdep] at hcode
  by_cases hwv : I.weiValue = ⟨0⟩
  · set m0 := initMachine σ σ₀ g A I ∅ with hm0
    have hw0 : WorldEquiv ⟨A.createdAccounts, σ, A.logSeries⟩ m0 := WorldEquiv.init ∅ {}
    have hslot : cSlot m0 = solcMappingSlot ⟨0⟩ (callerW I) := by
      simp only [cSlot, balSlot_eq, hm0, initMachine_executionEnv, callerW]
    have hw1 : WorldEquiv ⟨A.createdAccounts, sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨0⟩ (callerW I)) w, A.logSeries⟩
        (cM1 m0 w) := by
      rw [← hslot]; exact hw0.sstore (owner := I.codeOwner) rfl (cSlot m0) w
    have hown1 : I.codeOwner = (cM1 m0 w).evm.executionEnv.codeOwner := by
      rw [storeU256_executionEnv, hm0, initMachine_executionEnv]
    have hw2 := hw1.sstore (owner := I.codeOwner) hown1 ⟨2⟩ w
    have hle : cLe m0 w = ctorLog I w := by
      simp only [cLe, Machine.this, storageStore_executionEnv, hm0, initMachine_executionEnv, evTransfer_topic, ctorLog,
        transferTopic, callerW]
      rfl
    have hw3 := hw2.pushLog (cLe m0 w)
    have hrun := ctorRunOk (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
      hcode hwv hperm
    rw [← hle] at hrun
    exact Returned.specCtorW default hcode hrun (ctorSpec default w hwv) hw3 rfl
  · exact Reverted.specCtorNonPayable hcode (ctorRunNonPayable hcode hwv) (fun h => hwv (ctorPayable_erc20.mp h))

end ERC20.Opt
