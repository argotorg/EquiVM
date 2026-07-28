import Benchmarks.Dss.Cat.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Cat

/-!
# Cat `bite` — the `vow.fess(dartRate)` external `CALL` (void)

This file packages the EVM-side reasoning for the `fess` external call inside `bite`, so the `bite`
trace agent can discharge it in one step.  It splits into two concerns:

* **Memory-encoding coupling** (`fessEncode_eq`): the solc calldata buffer the encoder writes at the
  free pointer `p` — selector `0x697efb78` in `mem[p..p+4)`, the single `uint256` argument in
  `mem[p+4..p+36)` — reads back (as a 36-byte window) to exactly
  `config.externalABI.encode? "fess" [.int (Int.ofNat arg.toNat)]`.  This is stated **generically**
  over the free-pointer value `p` and the pre-encoding memory `mem` (only `p.toNat ≤ mem.size`, the
  free-pointer invariant, is assumed — the writes may extend memory).

* **RD stepping** (`RD.catBiteFessCall`, `RD.catBiteFess*`): from an RD parked at the
  `EXTCODESIZE` guard (pc `2284`) with the seven CALL words on the stack and the calldata already in
  memory, step through the guard and the `CALL` to just after it (pc `2300`), emitting the `Θ`
  witness; plus the `no-code`, `depth-limit`, `call-failed` and `call-succeeded` branches.  These are
  **memory-agnostic** and **generic** over the incoming stack tail `R` and the CALL argument words
  (`target inOff inSize outOff outSize`), so the trace agent binds them to `target = vow`,
  `inOff = outOff = p`, `inSize = 36`, `outSize = 0`.

Disassembly (runtime.hex): the encoder runs `2242 → 2283`
(`MLOAD 0x40 → p`; `MSTORE p (sel<<224)`; `MSTORE (p+4) arg`; builds `argsLen = (p+36)-p = 36`,
`argsOff = p`, `value = 0`, `retOff = p`, `retLen = 0`, `addr = vow`); the guard is
`2284 EXTCODESIZE; ISZERO; DUP1; ISZERO; PUSH2 2296; JUMPI; [2296] JUMPDEST; POP; GAS`; the call is
`2299 CALL`; the success guard is `2300 ISZERO; DUP1; ISZERO; PUSH2 2316; JUMPI; [2316] JUMPDEST; POP`.
-/

/-! ## Memory-encoding coupling -/

/-- The 32-byte word solc `MSTORE`s for the `fess` selector: `(0x697efb78 & 0xffffffff) << 224`. -/
abbrev fessSelectorShifted : UInt256 :=
  UInt256.shiftLeft (UInt256.land ⟨1769929592⟩ ⟨4294967295⟩) ⟨224⟩

/-- Memory after the selector `MSTORE` at the free pointer `p` (`mem[p..p+32) := sel<<224`). -/
noncomputable def fessSelectorMem (p : UInt256) (mem : ByteArray) : ByteArray :=
  fessSelectorShifted.toByteArray.write 0 mem p.toNat 32

/-- Memory after the argument `MSTORE` at `p+4` (`mem[p+4..p+36) := arg`) — the full `fess`
    calldata buffer, whose `[p, p+36)` window is `selector ++ arg`. -/
noncomputable def fessCalldataMem (p arg : UInt256) (mem : ByteArray) : ByteArray :=
  arg.toByteArray.write 0 (fessSelectorMem p mem) (p.toNat + 4) 32

theorem fessSelectorShifted_size : fessSelectorShifted.toByteArray.size = 32 :=
  toByteArray_size _

theorem fessSelectorMem_size (p : UInt256) {mem : ByteArray} (hp : p.toNat ≤ mem.size) :
    (fessSelectorMem p mem).size = max mem.size (p.toNat + 32) := by
  unfold fessSelectorMem
  exact toByteArray_write32_size_of_le mem fessSelectorShifted p.toNat mem.size _ rfl hp rfl

theorem fessSelectorMem_ge (p : UInt256) {mem : ByteArray} (hp : p.toNat ≤ mem.size) :
    p.toNat + 32 ≤ (fessSelectorMem p mem).size := by
  rw [fessSelectorMem_size p hp]; omega

theorem fessCalldataMem_size (p arg : UInt256) {mem : ByteArray} (hp : p.toNat ≤ mem.size) :
    (fessCalldataMem p arg mem).size = max (fessSelectorMem p mem).size (p.toNat + 36) := by
  unfold fessCalldataMem
  exact toByteArray_write32_size_of_le (fessSelectorMem p mem) arg (p.toNat + 4)
    (fessSelectorMem p mem).size _ rfl
    (by have := fessSelectorMem_ge p hp; omega) (by omega)

theorem fessCalldataMem_ge (p arg : UInt256) {mem : ByteArray} (hp : p.toNat ≤ mem.size) :
    p.toNat + 36 ≤ (fessCalldataMem p arg mem).size := by
  rw [fessCalldataMem_size p arg hp]; omega

/-- The first four bytes of the selector `MSTORE` window are the `fess` selector `0x697efb78`. -/
theorem fessSelectorMem_selector (p : UInt256) {mem : ByteArray} (hp : p.toNat ≤ mem.size) :
    (fessSelectorMem p mem).extract p.toNat (p.toNat + 4) = vowFessSelector := by
  unfold fessSelectorMem
  rw [write32_eq _ _ p.toNat (by rw [toByteArray_size]) hp]
  have hAsz : (mem.extract 0 p.toNat).size = p.toNat := by
    rw [ByteArray.size_extract]; omega
  have hBsz : (fessSelectorShifted.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]; omega
  have hABsz :
      (mem.extract 0 p.toNat ++ fessSelectorShifted.toByteArray.extract 0 32).size =
        p.toNat + 32 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  rw [extract_append_left _ _ p.toNat (p.toNat + 4) (by rw [hABsz]; omega),
    extract_append_right_window _ _ p.toNat (p.toNat + 4) (by rw [hAsz]),
    hAsz, show p.toNat - p.toNat = 0 from by omega,
    show p.toNat + 4 - p.toNat = 4 from by omega,
    extract_extract_BA, show 0 + 0 = 0 from rfl, show min (0 + 4) 32 = 4 from by omega,
    toByteArray_eq_toBytesBE]
  native_decide

/-- The `[p, p+36)` window of the `fess` calldata buffer is `selector ++ arg`. -/
theorem fessCalldataMem_read_window (p arg : UInt256) {mem : ByteArray}
    (hp : p.toNat ≤ mem.size) :
    (fessCalldataMem p arg mem).readWithPadding p.toNat 36 =
      vowFessSelector ++ arg.toByteArray := by
  rw [readWithPadding_eq_extract' _ p.toNat 36 (by norm_num) (by norm_num)
      (by rw [fessCalldataMem_size p arg hp]; omega), fessCalldataMem,
    write32_eq _ (fessSelectorMem p mem) (p.toNat + 4) (by rw [toByteArray_size])
      (by have := fessSelectorMem_ge p hp; omega)]
  have hAsz : ((fessSelectorMem p mem).extract 0 (p.toNat + 4)).size = p.toNat + 4 := by
    rw [ByteArray.size_extract]; have := fessSelectorMem_ge p hp; omega
  have hBsz : (arg.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]; omega
  have hPsz :
      ((fessSelectorMem p mem).extract 0 (p.toNat + 4) ++ arg.toByteArray.extract 0 32).size =
        p.toNat + 36 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull : arg.toByteArray.extract 0 32 = arg.toByteArray := by
    have h := @ByteArray.extract_zero_size arg.toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ p.toNat (p.toNat + 36) hPsz.ge,
    extract_append_span _ _ p.toNat (p.toNat + 36) (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ (p.toNat + 4) p.toNat (p.toNat + 4) (le_refl _),
    fessSelectorMem_selector p hp]
  congr 1
  rw [show p.toNat + 36 - (p.toNat + 4) = 32 from by omega, extract_extract_BA]
  simp only [Nat.add_zero, Nat.zero_add, Nat.min_self, hBfull]

/-- **The `fess` memory-encoding coupling.**  The solc-built 36-byte calldata window equals the ABI
    encoding of `fess(arg)`. -/
theorem fessEncode_eq (p arg : UInt256) {mem : ByteArray} (hp : p.toNat ≤ mem.size) :
    config.externalABI.encode? "fess" [.int (Int.ofNat arg.toNat)] =
      some ((fessCalldataMem p arg mem).readWithPadding p.toNat 36) := by
  rw [fessCalldataMem_read_window p arg hp]
  have hlt : arg.toNat < EVM.twoPow 256 := by
    have h := arg.val.isLt
    simp only [EVM.twoPow, UInt256.toNat, UInt256.size] at h ⊢
    exact h
  have hword : EVM.word arg.toNat = arg := u256_ofNat_toNat arg
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, uint256, uint256Int, vowFessSelector,
    selectorBytes, hlt, hword, word_toBytesBE_toByteArray_eq_toByteArray]

/-! ## RD stepping through the guard + CALL

The following lemmas are memory-agnostic (they take an abstract `mem`/`rdata`/`aw`) and generic over
the incoming stack tail `R` and the CALL argument words; the trace agent binds
`target := vow`, `inOff := outOff := p`, `inSize := 36`, `outSize := 0`, and `mem := fessCalldataMem …`.
-/

/-- `fess` `EXTCODESIZE` guard + `CALL` (target has code, depth ok): from pc `2284` step through to
    pc `2300`, emitting the `Θ` witness and the post-call RD (status flag on top). -/
theorem RD.catBiteFessCall {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256} {R : List UInt256}
    {target inOff inSize outOff outSize : UInt256} {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2284⟩
      (target :: target :: ⟨0⟩ :: inOff :: inSize :: outOff :: outSize :: R)
      mem aw rdata (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 9 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl σ σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 target) (toExecute σ (AccountAddress.ofUInt256 target))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          (mem.readWithPadding inOff.toNat inSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2300⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: R)
          (o.write 0 mem outOff.toNat (min outSize (UInt256.ofNat o.size)).toNat)
          (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOff.toNat inSize.toNat)
            outOff.toNat outSize.toNat))
          o (cA', σ') k' C'
      ∧ o.size < UInt256.size := by
  obtain ⟨gasWord, k1, C1, rd2299⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2284⟩) (okPc := ⟨2296⟩) rd hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide)
      (by simp only [List.length_cons]; omega)
  obtain ⟨cA', σ', z, o, Ain, callGas, k', C', hΘ, rd2300, hout⟩ :=
    RD.call (pc := ⟨2299⟩) rd2299 (by native_decide) hdepth (by omega)
  refine ⟨cA', σ', z, o, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · exact rd2300

/-- `fess` `EXTCODESIZE` guard, target has no code: the guard reverts. -/
theorem RD.catBiteFessNoCode {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256} {R : List UInt256}
    {target inOff inSize outOff outSize : UInt256} {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2284⟩
      (target :: target :: ⟨0⟩ :: inOff :: inSize :: outOff :: outSize :: R)
      mem aw rdata (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ target = ⟨0⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨2284⟩) (okPc := ⟨2296⟩) rd hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons]; omega)

/-- `fess` `CALL` at maximum call depth (`depth = 1024`): the `CALL` yields status `0` without
    invoking `Θ`. -/
theorem RD.catBiteFessCallDepthLimit {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw gasWord : UInt256} {R : List UInt256}
    {target inOff inSize outOff outSize : UInt256} {k C : ℕ}
    (rd2299 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2299⟩
      (gasWord :: target :: ⟨0⟩ :: inOff :: inSize :: outOff :: outSize :: R)
      mem aw rdata (cA, σ) k C)
    (hdepth : I.depth = 1024)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2300⟩
      (⟨0⟩ :: R)
      (ByteArray.empty.write 0 mem outOff.toNat
        (min outSize (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOff.toNat inSize.toNat)
        outOff.toNat outSize.toNat))
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd2300⟩ :=
    RD.callDepthLimit (pc := ⟨2299⟩) rd2299 (by native_decide) hdepth (by omega)
  exact ⟨k', C', rd2300⟩

/-- `fess` success guard, `CALL` returned status `0`: the revert-data bubbling tail reverts. -/
theorem RD.catBiteFessCallFailed {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256} {R : List UInt256} {k C : ℕ}
    (rd2300 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2300⟩
      (⟨0⟩ :: R) mem aw rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨2300⟩) (okPc := ⟨2316⟩) rd2300 rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by omega)

/-- `fess` success guard, `CALL` returned nonzero status: step past the guard (void call — the
    return data is discarded), leaving pc `2318` with the tail `R`. -/
theorem RD.catBiteFessCallSucceeded {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256} {R : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (rd2300 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2300⟩
      (⟨1⟩ :: R) mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2318⟩
      R mem aw rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨2300⟩) (okPc := ⟨2316⟩) rd2300
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by omega)

end Benchmarks.Dss.Cat
