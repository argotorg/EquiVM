import TruthClaude.Memory
import TruthClaude.Stepping

/-!
# Solc — reusable boilerplate shared by every solc-compiled contract

Solidity's compiler emits the same prologue for every external function: a free-memory-pointer
store, a non-payable guard, a `calldatasize` check, and a **4-byte selector dispatch**.  The
selector dispatch is identical across contracts apart from the four selector bytes, so it is proved
here once, generically, and instantiated per contract (`truthEvmSelector`, `powEvmSelector`).

Everything in this file is contract-agnostic; the only inputs are the four selector bytes and the
matching `UInt256` constant.
-/

namespace TruthClaude.Theory

open Ethereum Ethereum.EVM

/-! ## Generic `UInt256.eq` facts -/

/-- `EQ` of equal words is `1`. -/
theorem u256_eq_refl (a : UInt256) : UInt256.eq a a = ⟨1⟩ := by
  simp only [UInt256.eq, Bool.toUInt256, decide_eq_true (rfl : a = a)]; rfl

/-- `EQ` of distinct words is `0`. -/
theorem u256_eq_of_ne {a b : UInt256} (h : a ≠ b) : UInt256.eq a b = ⟨0⟩ := by
  simp only [UInt256.eq, Bool.toUInt256, decide_eq_false h]; rfl

/-! ## Big-endian decode of the 4 selector bytes -/

/-- Evaluate `fromBytesBigEndian` on four bytes as a base-256 numeral. -/
theorem fromBytesBigEndian_four (a0 a1 a2 a3 : UInt8) :
    fromBytesBigEndian [a0, a1, a2, a3]
      = a3.toNat + 256 * (a2.toNat + 256 * (a1.toNat + 256 * a0.toNat)) := by
  simp only [fromBytesBigEndian, Function.comp, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, fromBytes', Nat.mul_zero, Nat.add_zero]
  rfl

/-- `fromBytesBigEndian` is injective on 4-byte lists (the selector decode is lossless). -/
theorem fromBytesBigEndian_inj4 {l l' : List UInt8} (hl : l.length = 4) (hl' : l'.length = 4)
    (h : fromBytesBigEndian l = fromBytesBigEndian l') : l = l' := by
  match l, hl, l', hl' with
  | [a0, a1, a2, a3], _, [b0, b1, b2, b3], _ =>
    rw [fromBytesBigEndian_four, fromBytesBigEndian_four] at h
    have ba0 : a0.toNat < 256 := a0.toFin.isLt
    have ba1 : a1.toNat < 256 := a1.toFin.isLt
    have ba2 : a2.toNat < 256 := a2.toFin.isLt
    have ba3 : a3.toNat < 256 := a3.toFin.isLt
    have bb0 : b0.toNat < 256 := b0.toFin.isLt
    have bb1 : b1.toNat < 256 := b1.toFin.isLt
    have bb2 : b2.toNat < 256 := b2.toFin.isLt
    have bb3 : b3.toNat < 256 := b3.toFin.isLt
    have e0 : a0 = b0 := UInt8.toNat_inj.mp (by omega)
    have e1 : a1 = b1 := UInt8.toNat_inj.mp (by omega)
    have e2 : a2 = b2 := UInt8.toNat_inj.mp (by omega)
    have e3 : a3 = b3 := UInt8.toNat_inj.mp (by omega)
    rw [e0, e1, e2, e3]

/-- The dispatcher's `ByteArray` selector compare `#[c0,c1,c2,c3] == calldata[0:4]` equals the
    list condition on the first four calldata bytes. -/
theorem extract4_eq_iff (cd : ByteArray) (c0 c1 c2 c3 : UInt8) (hsz : 4 ≤ cd.size) :
    ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == cd.extract 0 4) = true
      ↔ cd.data.toList.take 4 = [c0, c1, c2, c3] := by
  rw [show ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == cd.extract 0 4)
        = ((#[c0, c1, c2, c3] : Array UInt8) == (cd.extract 0 4).data) from rfl,
      beq_iff_eq, ByteArray.data_extract, ← Array.toList_inj, Array.toList_extract]
  show ([c0, c1, c2, c3] : List UInt8) = (cd.data.toList.drop 0).take (0 + 4 - 0) ↔ _
  rw [List.drop_zero]
  constructor
  · intro he; rw [← he]
  · intro he; rw [he]

/-! ## The generic selector-decode lemma -/

/-- **Selector decode** (contract-agnostic).  The EVM selector test
    `eq(sel, SHR(calldataload(0), 224))` agrees with the dispatcher's byte compare
    `#[c0,c1,c2,c3] == calldata.extract 0 4`, given `sel`'s bytes are `[c0,c1,c2,c3]`.
    Both `truthEvmSelector` and `powEvmSelector` are instances. -/
theorem evmSelectorDecode {cd : ByteArray} (hsz : 4 ≤ cd.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat) :
    UInt256.eq sel (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  have hsv : (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩).toNat
             = fromBytesBigEndian (cd.data.toList.take 4) := selector_toNat cd hsz
  by_cases hc : cd.data.toList.take 4 = [c0, c1, c2, c3]
  · have h1 : UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩ = sel :=
      u256_inj (by rw [hsv, hc, hsel])
    rw [if_pos ((extract4_eq_iff cd c0 c1 c2 c3 hsz).mpr hc), h1, u256_eq_refl]
  · rw [if_neg (fun he => hc ((extract4_eq_iff cd c0 c1 c2 c3 hsz).mp he))]
    apply u256_eq_of_ne
    intro he
    apply hc
    have hlen4 : (cd.data.toList.take 4).length = 4 := by
      rw [List.length_take]
      have : 4 ≤ cd.data.toList.length := by rw [Array.length_toList]; exact hsz
      omega
    exact fromBytesBigEndian_inj4 hlen4 rfl (by rw [← hsv, ← he]; exact hsel.symm)

/-! ## The free-memory-pointer memory

Every solc contract opens with `PUSH1 0x80; PUSH1 0x40; MSTORE`, storing the initial free pointer
`0x80` at `0x40`.  This is the resulting memory and the read-back lemma the epilogue's
`MLOAD 0x40` needs — contract-agnostic. -/

/-- Memory after solc stores the free pointer `0x80` at `0x40`. -/
noncomputable def solcFreePtrMem : ByteArray :=
  (UInt256.toByteArray ⟨128⟩).write 0 ByteArray.empty 64 32

theorem solcFreePtrMem_eq :
    solcFreePtrMem
      = (ByteArray.empty ++ ffi.ByteArray.zeroes (USize.ofNat 64)) ++ UInt256.toByteArray ⟨128⟩ := by
  rw [solcFreePtrMem, toByteArray_write_eq _ _ _ (by decide) (by exact lt_usize _ (by norm_num))]; rfl

theorem solcFreePtrMem_size : solcFreePtrMem.size = 96 := by
  rw [solcFreePtrMem_eq, ByteArray.size_append, ByteArray.size_append,
      zeroes_ofNat_size _ (by norm_num), toByteArray_size]; decide

theorem solcFreePtrMem_read64 : solcFreePtrMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := solcFreePtrMem_size; omega), solcFreePtrMem_eq,
      extract_append_right' _ _ _ _
        (by rw [ByteArray.size_append, zeroes_ofNat_size _ (by norm_num)]; rfl)
        (by rw [ByteArray.size_append, zeroes_ofNat_size _ (by norm_num), toByteArray_size]; rfl)]

/-! ## Shared bytecode-sequence lemmas

These are *trace segments* that recur byte-for-byte across solc output, factored as parameterized
lemmas (entry state / `code` / pc passed in, end state handed back through `∃ s, X … = X … s ∧ …`)
so Truth and Pow share them instead of duplicating the steps.  No combinator yet — each is threaded
by hand at the call site; the planned segment abstraction will later package exactly this shape. -/

/-- The `revert(0,0)` memory-expansion cost is `0` for any state whose top two stack words are `0`
    (offset/size `0` ⇒ `M` does not grow ⇒ cost `0`), independent of `activeWords`. -/
theorem memExpRevert0 (s : State) {t : List UInt256}
    (hstk : s.machineState.stack = ⟨0⟩ :: ⟨0⟩ :: t) :
    memoryExpansionCost s .REVERT = 0 := by
  have hlt : s.machineState.activeWords.toNat < UInt256.size := by
    simpa [UInt256.toNat] using s.machineState.activeWords.val.isLt
  have hof : UInt256.ofNat s.machineState.activeWords.toNat = s.machineState.activeWords :=
    u256_inj (by show (Fin.ofNat _ _).val = _
                 simp only [Fin.ofNat]; exact Nat.mod_eq_of_lt hlt)
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk,
    List.getElem!_cons_zero, List.getElem!_cons_succ,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, MachineState.M, hof, Nat.sub_self]

/-- **The `PUSH0; PUSH0; REVERT` stub** (`revert(0,0)`) emitted by solc for the non-payable guard,
    the dispatch fall-through, and every `require` failure.  From a state at `pc = p` part-way
    through a trace, the whole run either runs out of gas or halts with a `revert`.  Contract- and
    position-agnostic. -/
theorem solcRevert0 {g : UInt256} {s0 s : State} {code : ByteArray} {p : UInt256}
    {k C : ℕ} {rest : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = p)
    (hd0 : decode code p = some (.PUSH0, .none))
    (hd1 : decode code (p + ⟨1⟩) = some (.PUSH0, .none))
    (hd2 : decode code (p + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none))
    (hstk : s.machineState.stack = rest) (hov : rest.length + 2 ≤ 1024)
    (hgas : s.machineState.gasAvailable.toNat = g.toNat - C) (hk : k ≤ C) (hC : C ≤ g.toNat)
    (hX : X (g.toNat + 1) (D_J code ⟨0⟩) s0 = X (g.toNat + 1 - k) (D_J code ⟨0⟩) s) :
    X (g.toNat + 1) (D_J code ⟨0⟩) s0 = .error .OutOfGass
      ∨ ∃ g' o, X (g.toNat + 1) (D_J code ⟨0⟩) s0 = .ok (.revert g' o) := by
  have st0 := push0_xstep hcode hpc hd0 hstk (by omega)
  by_cases g0 : g.toNat < C + 2
  · exact Or.inl (hX.trans (stepOOG hgas st0 hk hC (by omega)))
  · set s1 := stPush0 s with hs1
    have hX1 := hX.trans (stepContinue (k := k) (C := C) hgas st0 hk (by omega))
    have hc1 : s1.executionEnv.code = code := by rw [hs1]; simp only [stPush0]; exact hcode
    have hp1 : s1.machineState.pc = p + ⟨1⟩ := by rw [hs1]; simp only [stPush0]; rw [hpc]
    have hg1 : s1.machineState.gasAvailable.toNat = g.toNat - (C + 2) := by
      rw [hs1]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
    have hk1 : s1.machineState.stack = ⟨0⟩ :: rest := by rw [hs1]; simp only [stPush0, hstk]
    have st1 := push0_xstep hc1 hp1 hd1 hk1 (by simp only [List.length_cons]; omega)
    by_cases g1 : g.toNat < C + 4
    · exact Or.inl (hX1.trans (stepOOG (k := k + 1) (C := C + 2) hg1 st1 (by omega) (by omega) (by omega)))
    · set s2 := stPush0 s1 with hs2
      have hX2 := hX1.trans (stepContinue (k := k + 1) (C := C + 2) hg1 st1 (by omega) (by omega))
      have hc2 : s2.executionEnv.code = code := by rw [hs2]; simp only [stPush0]; exact hc1
      have hp2 : s2.machineState.pc = p + ⟨1⟩ + ⟨1⟩ := by rw [hs2]; simp only [stPush0]; rw [hp1]
      have hg2 : s2.machineState.gasAvailable.toNat = g.toNat - (C + 4) := by
        rw [hs2]; simp only [stPush0]; rw [toNat_sub_ofNat (by omega)]; omega
      have hk2 : s2.machineState.stack = ⟨0⟩ :: ⟨0⟩ :: rest := by rw [hs2]; simp only [stPush0, hk1]
      have st2 := revert_xstep hc2 hp2 hd2 hk2 (by omega)
      rw [memExpRevert0 s2 hk2] at st2
      exact Or.inr ⟨_, _, hX2.trans (stepHaltRevert (k := k + 2) (C := C + 4) (cost := 0) hg2 st2
        (by omega) (by omega))⟩

/-- **The solc guard prologue** (first six instructions, byte-identical for every solc contract):
    `PUSH1 0x80; PUSH1 0x40; MSTORE; CALLVALUE; DUP1; ISZERO`.  From `initState`, reach `pc = 8`
    with the free-pointer memory installed and `[isZero(callvalue), callvalue]` on the stack, ready
    for the non-payable-guard `JUMPI`.  Used by both Truth and Pow. -/
theorem solcGuardPrologue {cA gh bl σ σ₀ A I} {g : UInt256} {code : ByteArray}
    (hcode : I.code = code)
    (hd0 : decode code ⟨0⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)))
    (hd2 : decode code ⟨2⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hd4 : decode code ⟨4⟩ = some (.MSTORE, .none))
    (hd5 : decode code ⟨5⟩ = some (.CALLVALUE, .none))
    (hd6 : decode code ⟨6⟩ = some (.DUP1, .none))
    (hd7 : decode code ⟨7⟩ = some (.ISZERO, .none)) :
    X (g.toNat + 1) (D_J code ⟨0⟩) (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass
      ∨ ∃ s, (X (g.toNat + 1) (D_J code ⟨0⟩) (initState cA gh bl σ σ₀ g A I)
                = X (g.toNat + 1 - 6) (D_J code ⟨0⟩) s)
           ∧ s.executionEnv = I ∧ s.machineState.pc = ⟨8⟩
           ∧ s.machineState.gasAvailable.toNat = g.toNat - 26
           ∧ s.machineState.stack = [UInt256.isZero I.weiValue, I.weiValue]
           ∧ s.machineState.activeWords = UInt256.ofNat 3
           ∧ s.machineState.memory = solcFreePtrMem ∧ 26 ≤ g.toNat := by
  set s0 := initState cA gh bl σ σ₀ g A I with hs0
  have hee0 : s0.executionEnv = I := by rw [hs0]; simp [initState]
  have hcode0 : s0.executionEnv.code = code := by rw [hee0]; exact hcode
  have hpc0 : s0.machineState.pc = ⟨0⟩ := by rw [hs0]; simp [initState]; rfl
  have hgas0 : s0.machineState.gasAvailable.toNat = g.toNat - 0 := by rw [hs0]; simp [initState]
  have hstk0 : s0.machineState.stack = [] := by rw [hs0]; simp [initState]; rfl
  have haw0 : s0.machineState.activeWords = UInt256.ofNat 0 := by rw [hs0]; simp [initState]; rfl
  have hmem0 : s0.machineState.memory = ByteArray.empty := by rw [hs0]; simp [initState]; rfl
  have hX0 : X (g.toNat + 1) (D_J code ⟨0⟩) s0 = X (g.toNat + 1 - 0) (D_J code ⟨0⟩) s0 := rfl
  have hstep0 := push1_xstep (argv := ⟨128⟩) hcode0 hpc0 hd0 hstk0 (by norm_num)
  by_cases h0 : g.toNat < 3
  · exact Or.inl (by rw [hX0]; exact stepOOG hgas0 hstep0 (by norm_num) (by omega) (by omega))
  · set s1 := stPush1 s0 ⟨128⟩ with hs1
    have hX1 := hX0.trans (stepContinue (k := 0) (C := 0) hgas0 hstep0 (by norm_num) (by omega))
    have hee1 : s1.executionEnv = I := by rw [hs1]; simp only [stPush1]; exact hee0
    have hcode1 : s1.executionEnv.code = code := by rw [hee1]; exact hcode
    have hpc1 : s1.machineState.pc = ⟨2⟩ := by rw [hs1]; simp only [stPush1]; rw [hpc0]; rfl
    have hgas1 : s1.machineState.gasAvailable.toNat = g.toNat - 3 := by rw [hs1]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
    have hstk1 : s1.machineState.stack = [⟨128⟩] := by rw [hs1]; simp only [stPush1, hstk0]
    have haw1 : s1.machineState.activeWords = UInt256.ofNat 0 := by rw [hs1]; simp only [stPush1]; exact haw0
    have hmem1 : s1.machineState.memory = ByteArray.empty := by rw [hs1]; simp only [stPush1]; exact hmem0
    have hstep1 := push1_xstep (argv := ⟨64⟩) hcode1 hpc1 hd2 hstk1 (by norm_num)
    by_cases h1 : g.toNat < 6
    · exact Or.inl (by rw [hX1]; exact stepOOG hgas1 hstep1 (by norm_num) (by omega) (by omega))
    · set s2 := stPush1 s1 ⟨64⟩ with hs2
      have hX2 := hX1.trans (stepContinue (k := 1) (C := 3) hgas1 hstep1 (by norm_num) (by omega))
      have hee2 : s2.executionEnv = I := by rw [hs2]; simp only [stPush1]; exact hee1
      have hcode2 : s2.executionEnv.code = code := by rw [hee2]; exact hcode
      have hpc2 : s2.machineState.pc = ⟨4⟩ := by rw [hs2]; simp only [stPush1]; rw [hpc1]; rfl
      have hgas2 : s2.machineState.gasAvailable.toNat = g.toNat - 6 := by rw [hs2]; simp only [stPush1]; rw [toNat_sub_ofNat (by omega)]; omega
      have hstk2 : s2.machineState.stack = [⟨64⟩, ⟨128⟩] := by rw [hs2]; simp only [stPush1, hstk1]
      have haw2 : s2.machineState.activeWords = UInt256.ofNat 0 := by rw [hs2]; simp only [stPush1]; exact haw1
      have hmem2 : s2.machineState.memory = ByteArray.empty := by rw [hs2]; simp only [stPush1]; exact hmem1
      have hmc2 : memoryExpansionCost s2 .MSTORE = 9 := by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw2, hstk2]; decide
      have hstep2 := mstore_xstep hcode2 hpc2 hd4 hstk2 (by norm_num)
      rw [hmc2] at hstep2
      by_cases h2 : g.toNat < 18
      · exact Or.inl (by rw [hX2]; exact stepOOG (cost := 9 + 3) hgas2 hstep2 (by norm_num) (by omega) (by omega))
      · set s3 := stMStore s2 ⟨64⟩ ⟨128⟩ [] with hs3
        have hX3 := hX2.trans (stepContinue (k := 2) (C := 6) (cost := 9 + 3) hgas2 hstep2 (by norm_num) (by omega))
        have hee3 : s3.executionEnv = I := by rw [hs3]; simp only [stMStore]; exact hee2
        have hcode3 : s3.executionEnv.code = code := by rw [hee3]; exact hcode
        have hpc3 : s3.machineState.pc = ⟨5⟩ := by rw [hs3]; simp only [stMStore]; rw [hpc2]; rfl
        have hgas3 : s3.machineState.gasAvailable.toNat = g.toNat - 18 := by rw [hs3]; simp only [stMStore, hmc2]; rw [toNat_sub_ofNat (by rw [toNat_sub_ofNat (by omega)]; omega), toNat_sub_ofNat (by omega)]; omega
        have hstk3 : s3.machineState.stack = [] := by rw [hs3]; simp [stMStore]
        have haw3 : s3.machineState.activeWords = UInt256.ofNat 3 := by rw [hs3]; simp only [stMStore, haw2]; decide
        have hmem3 : s3.machineState.memory = solcFreePtrMem := by rw [hs3]; simp only [stMStore]; rw [hmem2, show (⟨64⟩:UInt256).toNat = 64 from by decide]; rfl
        have hstep3 := callvalue_xstep hcode3 hpc3 hd5 hstk3 (by norm_num)
        by_cases h3 : g.toNat < 20
        · exact Or.inl (by rw [hX3]; exact stepOOG hgas3 hstep3 (by norm_num) (by omega) (by omega))
        · set s4 := stCallvalue s3 with hs4
          have hX4 := hX3.trans (stepContinue (k := 3) (C := 18) hgas3 hstep3 (by norm_num) (by omega))
          have hee4 : s4.executionEnv = I := by rw [hs4]; simp only [stCallvalue]; exact hee3
          have hcode4 : s4.executionEnv.code = code := by rw [hee4]; exact hcode
          have hpc4 : s4.machineState.pc = ⟨6⟩ := by rw [hs4]; simp only [stCallvalue]; rw [hpc3]; rfl
          have hgas4 : s4.machineState.gasAvailable.toNat = g.toNat - 20 := by rw [hs4]; simp only [stCallvalue]; rw [toNat_sub_ofNat (by omega)]; omega
          have hstk4 : s4.machineState.stack = [I.weiValue] := by rw [hs4]; simp only [stCallvalue, hee3, hstk3]
          have haw4 : s4.machineState.activeWords = UInt256.ofNat 3 := by rw [hs4]; simp only [stCallvalue]; exact haw3
          have hmem4 : s4.machineState.memory = solcFreePtrMem := by rw [hs4]; simp only [stCallvalue]; exact hmem3
          have hstep4 := dup1_xstep hcode4 hpc4 hd6 hstk4 (by norm_num)
          by_cases h4 : g.toNat < 23
          · exact Or.inl (by rw [hX4]; exact stepOOG hgas4 hstep4 (by norm_num) (by omega) (by omega))
          · set s5 := stDup1 s4 I.weiValue [] with hs5
            have hX5 := hX4.trans (stepContinue (k := 4) (C := 20) hgas4 hstep4 (by norm_num) (by omega))
            have hee5 : s5.executionEnv = I := by rw [hs5]; simp only [stDup1]; exact hee4
            have hcode5 : s5.executionEnv.code = code := by rw [hee5]; exact hcode
            have hpc5 : s5.machineState.pc = ⟨7⟩ := by rw [hs5]; simp only [stDup1]; rw [hpc4]; rfl
            have hgas5 : s5.machineState.gasAvailable.toNat = g.toNat - 23 := by rw [hs5]; simp only [stDup1]; rw [toNat_sub_ofNat (by omega)]; omega
            have hstk5 : s5.machineState.stack = [I.weiValue, I.weiValue] := by rw [hs5]; simp only [stDup1]
            have haw5 : s5.machineState.activeWords = UInt256.ofNat 3 := by rw [hs5]; simp only [stDup1]; exact haw4
            have hmem5 : s5.machineState.memory = solcFreePtrMem := by rw [hs5]; simp only [stDup1]; exact hmem4
            have hstep5 := iszero_xstep hcode5 hpc5 hd7 hstk5 (by norm_num)
            by_cases h5 : g.toNat < 26
            · exact Or.inl (by rw [hX5]; exact stepOOG hgas5 hstep5 (by norm_num) (by omega) (by omega))
            · set s6 := stIsZero s5 I.weiValue [I.weiValue] with hs6
              have hX6 := hX5.trans (stepContinue (k := 5) (C := 23) hgas5 hstep5 (by norm_num) (by omega))
              refine Or.inr ⟨s6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
              · have he : g.toNat + 1 - (5 + 1) = g.toNat + 1 - 6 := by omega
                rw [← he]; exact hX6
              · rw [hs6]; simp only [stIsZero]; exact hee5
              · rw [hs6]; simp only [stIsZero]; rw [hpc5]; rfl
              · rw [hs6]; simp only [stIsZero]; rw [toNat_sub_ofNat (by omega)]; omega
              · rw [hs6]; simp only [stIsZero]
              · rw [hs6]; simp only [stIsZero]; exact haw5
              · rw [hs6]; simp only [stIsZero]; exact hmem5

end TruthClaude.Theory
