import Reasoning.Memory
import Reasoning.Stepping
import Reasoning.Reach

/-!
# Solc — reusable boilerplate shared by every solc-compiled contract

Solidity's compiler emits the same prologue for every external function: a free-memory-pointer
store, a non-payable guard, a `calldatasize` check, and a **4-byte selector dispatch**.  The
selector dispatch is identical across contracts apart from the four selector bytes, so it is proved
here once, generically, and instantiated per contract (`truthEvmSelector`, `powEvmSelector`).

Everything in this file is contract-agnostic; the only inputs are the four selector bytes and the
matching `UInt256` constant.
-/

namespace Reasoning.Theory

open Ethereum Ethereum.EVM Reasoning.Reach

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

theorem solcFreePtrMem_pad_size :
    (solcFreePtrMem ++ ffi.ByteArray.zeroes (USize.ofNat 32)).size = 128 := by
  rw [ByteArray.size_append, solcFreePtrMem_size, zeroes_ofNat_size _ (by norm_num)]

/-- Memory after solc stores a 32-byte return word `val` at `0x80`, over the free-pointer memory —
    the shape every solc ABI-encoder's epilogue produces (its `RETURN`s `mem[0x80 .. 0xa0] = val`). -/
noncomputable def solcReturnMem (val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 solcFreePtrMem 128 32

theorem solcReturnMem_eq (val : UInt256) :
    solcReturnMem val = (solcFreePtrMem ++ ffi.ByteArray.zeroes (USize.ofNat 32)) ++ UInt256.toByteArray val := by
  rw [solcReturnMem, toByteArray_write_eq _ _ _ (by rw [solcFreePtrMem_size]; omega)
        (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))]
  norm_num [solcFreePtrMem_size]

theorem solcReturnMem_size (val : UInt256) : (solcReturnMem val).size = 160 := by
  rw [solcReturnMem_eq, ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
      zeroes_ofNat_size _ (by norm_num), toByteArray_size]

theorem solcReturnMem_read64 (val : UInt256) :
    (solcReturnMem val).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := solcReturnMem_size val; omega), solcReturnMem_eq,
      extract_append_left _ _ _ _ (by have := solcFreePtrMem_pad_size; omega),
      extract_append_left _ _ _ _ (by have := solcFreePtrMem_size; omega),
      ← readWithPadding_eq_extract _ _ (by have := solcFreePtrMem_size; omega), solcFreePtrMem_read64]

theorem solcReturnMem_read128 (val : UInt256) :
    (solcReturnMem val).readWithPadding 128 32 = UInt256.toByteArray val := by
  rw [readWithPadding_eq_extract _ _ (by have := solcReturnMem_size val; omega), solcReturnMem_eq,
      extract_append_right' _ _ _ _ (by have := solcFreePtrMem_pad_size; omega)
        (by have := solcFreePtrMem_pad_size; have := toByteArray_size val; omega)]

/-! ## Shared bytecode-sequence lemmas

Trace segments that recur byte-for-byte across solc output, factored once so every contract reuses
them.  The non-payable guard prologue is exposed as an `RD` producer (`solcGuardPrologueRD`) that
chains directly into an `evm_run` dispatcher fold; the rest are supporting cost/selector facts. -/

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

/-- **The solc guard prologue** (`PUSH1 0x80; PUSH1 0x40; MSTORE; CALLVALUE; DUP1; ISZERO`, byte-
    identical for every solc contract) as a **producer of the `RD` invariant** (compositional):
    `initState → RD … ⟨8⟩ [isZero(callvalue), callvalue]` so a dispatcher fold can chain straight off
    it. -/
theorem solcGuardPrologueRD {cA gh bl σ σ₀ A I} {g : UInt256} {code : ByteArray}
    (hcode : I.code = code)
    (hd0 : decode code ⟨0⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)))
    (hd2 : decode code ⟨2⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hd4 : decode code ⟨4⟩ = some (.MSTORE, .none))
    (hd5 : decode code ⟨5⟩ = some (.CALLVALUE, .none))
    (hd6 : decode code ⟨6⟩ = some (.DUP1, .none))
    (hd7 : decode code ⟨7⟩ = some (.ISZERO, .none)) :
    RD code I g (initState cA gh bl σ σ₀ g A I) ⟨8⟩
        [UInt256.isZero I.weiValue, I.weiValue] solcFreePtrMem (UInt256.ofNat 3) (cA, σ) 6 26 := by
  set s0 := initState cA gh bl σ σ₀ g A I with hs0
  have hee0 : s0.executionEnv = I := by rw [hs0]; simp [initState]
  have hcode0 : s0.executionEnv.code = code := by rw [hee0]; exact hcode
  have hpc0 : s0.machineState.pc = ⟨0⟩ := by rw [hs0]; simp [initState]; rfl
  have hgas0 : s0.machineState.gasAvailable.toNat = g.toNat - 0 := by rw [hs0]; simp [initState]
  have hstk0 : s0.machineState.stack = [] := by rw [hs0]; simp [initState]; rfl
  have haw0 : s0.machineState.activeWords = UInt256.ofNat 0 := by rw [hs0]; simp [initState]; rfl
  have hmem0 : s0.machineState.memory = ByteArray.empty := by rw [hs0]; simp [initState]; rfl
  have hacc0 : (s0.createdAccounts, s0.accountMap) = (cA, σ) := by rw [hs0]; simp [initState]
  have hX0 : X (g.toNat + 1) (D_J code ⟨0⟩) s0 = X (g.toNat + 1 - 0) (D_J code ⟨0⟩) s0 := rfl
  -- PUSH1 0x80 · PUSH1 0x40 · MSTORE (install free pointer) · CALLVALUE · DUP1 · ISZERO ⇒ pc 8
  exact RD.startWith hcode0 hpc0 hstk0 hgas0 (by omega) (by omega) hX0 hmem0 haw0 hacc0 hee0
        ⟨rfl, rfl, rfl⟩
      |>.push1 ⟨128⟩ hd0 (by decide)
      |>.push1 ⟨64⟩ hd2 (by decide)
      |>.mstore 9 solcFreePtrMem (UInt256.ofNat 3) hd4
        (fun s haws hstks => by
          simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks]; decide)
        (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
        (by decide) (by decide)
      |>.callvalue hd5 (by decide)
      |>.dup1 hd6 (by simp only [List.length_cons, List.length_nil]; omega)
      |>.iszero hd7 (by simp only [List.length_cons, List.length_nil]; omega)

end Reasoning.Theory

namespace Reasoning.Reach
open Ethereum Ethereum.EVM Reasoning.Theory

/-- The solc `revert(0,0)` stub `PUSH0·PUSH0·REVERT` as an **`RD → RDrev` combinator**: from a
    cursor at the first `PUSH0`, push the two zero words and `REVERT` (memory-expansion cost `0`).
    Recurs at the end of every revert path. -/
theorem RD.revertStub {code : ByteArray} {ee : ExecutionEnv} {g : UInt256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw acc k C)
    (hd0 : decode code pc = some (.PUSH0, .none))
    (hd1 : decode code (pc + ⟨1⟩) = some (.PUSH0, .none))
    (hd2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none))
    (hov : stk.length + 2 ≤ 1024) :
    RDrev code g s0 :=
  h.push0 hd0 (by omega)
    |>.push0 hd1 (by simp only [List.length_cons]; omega)
    |>.rev 0 hd2 (fun s _ hstks => memExpRevert0 s hstks) (by omega)

end Reasoning.Reach
