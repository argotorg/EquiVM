import Benchmarks.Dss.Clipper.Bytecode
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Initcode
import Reasoning.Memory
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.SolmBody
import Reasoning.Storage
import Mathlib.Tactic.IntervalCases

/-!
# MakerDAO/Sky DSS Clipper shared proof foundation

Contract-wide selector notation and constants for the optimized Clipper runtime.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Clipper

-- LIBRARY CANDIDATE: `Reasoning.Memory` — compute `MLOAD` expansion cost from the stack top,
-- matching `mstoreCost_of_stack`.
theorem mloadCost_of_stack {s : State} {aw off : UInt256} {t : List UInt256} {mcost : ℕ}
    (haw : s.machineState.activeWords = aw)
    (hstk : s.machineState.stack = off :: t)
    (hcost : Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) - Cₘ aw = mcost) :
    memoryExpansionCost s .MLOAD = mcost := by
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ']
  have htop : s.machineState.stack[0]! = off := by
    rw [hstk]
    rfl
  rw [htop, haw]
  exact hcost

-- LIBRARY CANDIDATE: `Reasoning.Memory` — compute `RETURN` expansion cost from the
-- stack offset/length, matching `mstoreCost_of_stack`.
theorem returnCost_of_stack {s : State} {aw off len : UInt256} {t : List UInt256}
    {mcost : ℕ}
    (haw : s.machineState.activeWords = aw)
    (hstk : s.machineState.stack = off :: len :: t)
    (hcost : Cₘ (UInt256.ofNat (MachineState.M aw.toNat off.toNat len.toNat)) - Cₘ aw =
      mcost) :
    memoryExpansionCost s .RETURN = mcost := by
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ']
  have h0 : s.machineState.stack[0]! = off := by
    rw [hstk]
    rfl
  have h1 : s.machineState.stack[1]! = len := by
    rw [hstk]
    rfl
  rw [h0, h1, haw]
  exact hcost

/-- Clipper storage states in which the public `list()` getter's byte-level memory arithmetic for
the `active` array cannot overflow the EVM word size.

The constant covers the largest pointer/length expression used by the generated getter and ABI
return code: a 128-byte base, 32-byte array length word, 64-byte ABI prefix, and two `32 * len`
byte spans. -/
def clipperStorageWF (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  224 + 64 * (solcSlotWord σ I ⟨11⟩).toNat < UInt256.size

theorem clipperStorageWF_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    clipperStorageWF σ I ↔ clipperStorageWF τ I := by
  have hword : solcSlotWord σ I ⟨11⟩ = solcSlotWord τ I ⟨11⟩ :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
  constructor <;> intro h <;> simpa [clipperStorageWF, hword] using h

theorem clipperStorageWF_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (hwf : clipperStorageWF σ I) :
    clipperStorageWF τ I :=
  (clipperStorageWF_accountMapEquiv hAccounts).mp hwf

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev clipperSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `(contract v).transitions` order. -/
def clipperSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x80, 0x33, 0xd5, 0x81]⟩  -- active(uint256)
  | 1 => ⟨#[0x15, 0x23, 0x25, 0x15]⟩  -- buf()
  | 2 => ⟨#[0x96, 0xf1, 0xb6, 0xbe]⟩  -- calc()
  | 3 => ⟨#[0xb6, 0x15, 0x00, 0xe4]⟩  -- chip()
  | 4 => ⟨#[0xba, 0x2c, 0xdc, 0x75]⟩  -- chost()
  | 5 => ⟨#[0x06, 0x66, 0x1a, 0xbd]⟩  -- count()
  | 6 => ⟨#[0x49, 0xed, 0x59, 0x31]⟩  -- cusp()
  | 7 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩  -- deny(address)
  | 8 => ⟨#[0xc3, 0xb3, 0xad, 0x7f]⟩  -- dog()
  | 9 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩  -- file(bytes32,uint256)
  | 10 => ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ -- file(bytes32,address)
  | 11 => ⟨#[0x5c, 0x62, 0x2a, 0x0e]⟩ -- getStatus(uint256)
  | 12 => ⟨#[0xc5, 0xce, 0x28, 0x1e]⟩ -- ilk()
  | 13 => ⟨#[0x89, 0x8e, 0xb2, 0x67]⟩ -- kick(uint256,uint256,address,address)
  | 14 => ⟨#[0xcf, 0xdd, 0x33, 0x02]⟩ -- kicks()
  | 15 => ⟨#[0x0f, 0x56, 0x0c, 0xd7]⟩ -- list()
  | 16 => ⟨#[0xd8, 0x43, 0x41, 0x6d]⟩ -- redo(uint256,address)
  | 17 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 18 => ⟨#[0xb5, 0xf5, 0x22, 0xf7]⟩ -- sales(uint256)
  | 19 => ⟨#[0x2e, 0x77, 0x46, 0x8d]⟩ -- spotter()
  | 20 => ⟨#[0x75, 0xf1, 0x2b, 0x21]⟩ -- stopped()
  | 21 => ⟨#[0x13, 0xd8, 0xc8, 0x40]⟩ -- tail()
  | 22 => ⟨#[0x81, 0xa7, 0x94, 0xcb]⟩ -- take(uint256,uint256,uint256,address,bytes)
  | 23 => ⟨#[0x27, 0x55, 0xcd, 0x2d]⟩ -- tip()
  | 24 => ⟨#[0x0c, 0xbb, 0x58, 0x62]⟩ -- upchost()
  | 25 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | 26 => ⟨#[0x62, 0x6c, 0xb3, 0xc5]⟩ -- vow()
  | 27 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)
  | _ => ⟨#[0x26, 0xe0, 0x27, 0xf1]⟩  -- yank(uint256)

/-- Function selectors as EVM words, in `(contract v).transitions` order. -/
def clipperSelNat : ℕ → UInt256
  | 0 => ⟨0x8033d581⟩  -- active(uint256)
  | 1 => ⟨0x15232515⟩  -- buf()
  | 2 => ⟨0x96f1b6be⟩  -- calc()
  | 3 => ⟨0xb61500e4⟩  -- chip()
  | 4 => ⟨0xba2cdc75⟩  -- chost()
  | 5 => ⟨0x06661abd⟩  -- count()
  | 6 => ⟨0x49ed5931⟩  -- cusp()
  | 7 => ⟨0x9c52a7f1⟩  -- deny(address)
  | 8 => ⟨0xc3b3ad7f⟩  -- dog()
  | 9 => ⟨0x29ae8114⟩  -- file(bytes32,uint256)
  | 10 => ⟨0xd4e8be83⟩ -- file(bytes32,address)
  | 11 => ⟨0x5c622a0e⟩ -- getStatus(uint256)
  | 12 => ⟨0xc5ce281e⟩ -- ilk()
  | 13 => ⟨0x898eb267⟩ -- kick(uint256,uint256,address,address)
  | 14 => ⟨0xcfdd3302⟩ -- kicks()
  | 15 => ⟨0x0f560cd7⟩ -- list()
  | 16 => ⟨0xd843416d⟩ -- redo(uint256,address)
  | 17 => ⟨0x65fae35e⟩ -- rely(address)
  | 18 => ⟨0xb5f522f7⟩ -- sales(uint256)
  | 19 => ⟨0x2e77468d⟩ -- spotter()
  | 20 => ⟨0x75f12b21⟩ -- stopped()
  | 21 => ⟨0x13d8c840⟩ -- tail()
  | 22 => ⟨0x81a794cb⟩ -- take(uint256,uint256,uint256,address,bytes)
  | 23 => ⟨0x2755cd2d⟩ -- tip()
  | 24 => ⟨0x0cbb5862⟩ -- upchost()
  | 25 => ⟨0x36569e77⟩ -- vat()
  | 26 => ⟨0x626cb3c5⟩ -- vow()
  | 27 => ⟨0xbf353dbb⟩ -- wards(address)
  | _ => ⟨0x26e027f1⟩  -- yank(uint256)

theorem clipperSelectorEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (i : ℕ) (hi : i < 29) :
    UInt256.eq (clipperSelNat i) (clipperSelWord I) =
      if (clipperSelBytes i == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases i <;> exact evmSelectorDecode hsz _ _ _ _ _ (by decide)

def PatchesStartAt (n : Nat) (ps : List (Nat × ByteArray)) : Prop :=
  ∀ p ∈ ps, n ≤ p.1

def PatchWindowDisjoint (lo hi : Nat) (p : Nat × ByteArray) : Prop :=
  p.1 + p.2.size ≤ lo ∨ hi ≤ p.1

def PatchWindowDisjoint32 (lo hi : Nat) (p : Nat × ByteArray) : Prop :=
  p.1 + 32 ≤ lo ∨ hi ≤ p.1

def PatchesWindowDisjoint32 (lo hi : Nat) (ps : List (Nat × ByteArray)) : Prop :=
  ∀ p ∈ ps, PatchWindowDisjoint32 lo hi p

-- LIBRARY CANDIDATE: executable offset-only check for 32-byte patch disjointness.
def patchOffsetDisjoint32Bool (lo hi off : Nat) : Bool :=
  decide (off + 32 ≤ lo) || decide (hi ≤ off)

-- LIBRARY CANDIDATE: executable offset-only check for 32-byte patch-list disjointness.
def patchOffsetsWindowDisjoint32Bool (lo hi : Nat) : List Nat → Bool
  | [] => true
  | off :: offs =>
      patchOffsetDisjoint32Bool lo hi off && patchOffsetsWindowDisjoint32Bool lo hi offs

-- LIBRARY CANDIDATE: boolean offset disjointness implies the existing patch-window Prop.
theorem patchWindowDisjoint32_of_offset_bool {lo hi : Nat} {p : Nat × ByteArray}
    (h : patchOffsetDisjoint32Bool lo hi p.1 = true) :
    PatchWindowDisjoint32 lo hi p := by
  simp [patchOffsetDisjoint32Bool] at h
  exact h

-- LIBRARY CANDIDATE: boolean offset-list disjointness implies the existing patch-list Prop.
theorem patchesWindowDisjoint32_of_offsets_bool {lo hi : Nat} {ps : List (Nat × ByteArray)}
    (h : patchOffsetsWindowDisjoint32Bool lo hi (ps.map Prod.fst) = true) :
    PatchesWindowDisjoint32 lo hi ps := by
  induction ps with
  | nil =>
      intro p hp
      cases hp
  | cons p ps ih =>
      simp [patchOffsetsWindowDisjoint32Bool] at h
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact patchWindowDisjoint32_of_offset_bool h.1
      · exact ih h.2 q hq

-- LIBRARY CANDIDATE: executable template scan to a target `JUMPDEST`, checking only opcode
-- bytes touched by the `D_J_aux` scanner and only against concrete patch offsets.
def patchScanReaches (fuel : Nat) (template : ByteArray) (offs : List Nat)
    (i target : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
      match template.get? i >>= parseInstr with
      | none => false
      | some op =>
          patchOffsetsWindowDisjoint32Bool i (i + 1) offs &&
            if i = target ∧ op = .JUMPDEST then
              true
            else
              patchScanReaches fuel template offs (N i op) target

-- LIBRARY CANDIDATE: generic ByteArray prefix get? fact.
theorem byteArray_get?_extract_prefix (b : ByteArray) {n i : Nat}
    (hi : i < n) (hn : n ≤ b.size) :
    (b.extract 0 n).get? i = b.get? i := by
  unfold ByteArray.get?
  have hleft : i < (b.extract 0 n).size := by
    rw [ByteArray.size_extract]
    omega
  have hright : i < b.size := by omega
  simp only [dif_pos hleft, dif_pos hright]
  apply congrArg some
  change (b.extract 0 n)[i] = b[i]
  simp only [ByteArray.get_extract, Nat.zero_add]

-- LIBRARY CANDIDATE: generic splice prefix get? preservation for immutable patching.
theorem spliceBytes_get?_left {template value out : ByteArray} {off i : Nat}
    (hsp : spliceBytes? template off value = some out) (hi : i < off) :
    out.get? i = template.get? i := by
  unfold spliceBytes? at hsp
  split at hsp
  · rename_i hle
    cases hsp
    rw [Reasoning.Theory.byteArray_get?_append_left (template.extract 0 off ++ value)
      (template.extract (off + value.size) template.size)]
    · rw [Reasoning.Theory.byteArray_get?_append_left (template.extract 0 off) value]
      · exact byteArray_get?_extract_prefix template hi (by omega)
      · rw [ByteArray.size_extract]
        omega
    · rw [ByteArray.size_append, ByteArray.size_extract]
      omega
  · cases hsp

-- LIBRARY CANDIDATE: generic splice prefix extraction preservation for immutable patching.
theorem spliceBytes_extract_left {template value out : ByteArray} {off i j : Nat}
    (hsp : spliceBytes? template off value = some out) (hj : j ≤ off) :
    out.extract i j = template.extract i j := by
  unfold spliceBytes? at hsp
  split at hsp
  · rename_i hle
    cases hsp
    rw [Reasoning.Theory.extract_append_left (template.extract 0 off ++ value)
      (template.extract (off + value.size) template.size) i j]
    · rw [Reasoning.Theory.extract_append_left (template.extract 0 off) value i j]
      · exact Reasoning.Theory.extract_prefix template off i j hj
      · rw [ByteArray.size_extract]
        omega
    · rw [ByteArray.size_append, ByteArray.size_extract]
      omega
  · cases hsp

-- LIBRARY CANDIDATE: generic splice prefix extraction preservation for immutable patching.
theorem spliceBytes_extract'_left {template value out : ByteArray} {off i j : Nat}
    (hsp : spliceBytes? template off value = some out)
    (hi64 : i < 2 ^ 64) (hj64 : j < 2 ^ 64) (hj : j ≤ off) :
    out.extract' i j = template.extract' i j := by
  unfold ByteArray.extract'
  have hguard : (decide (i < 2 ^ 64) && decide (j < 2 ^ 64)) = true := by
    rw [decide_eq_true hi64, decide_eq_true hj64]
    rfl
  rw [if_pos hguard, if_pos hguard]
  exact spliceBytes_extract_left hsp hj

-- LIBRARY CANDIDATE: a successful splice exposes the inserted payload at its window.
theorem spliceBytes_extract_middle {template value out : ByteArray} {off : Nat}
    (hsp : spliceBytes? template off value = some out) :
    out.extract off (off + value.size) = value := by
  unfold spliceBytes? at hsp
  split at hsp
  · rename_i hle
    cases hsp
    have hprefix : (template.extract 0 off).size = off := by
      rw [ByteArray.size_extract]
      omega
    rw [Reasoning.Theory.extract_append_left (template.extract 0 off ++ value)
      (template.extract (off + value.size) template.size) off (off + value.size)]
    · rw [Reasoning.Theory.extract_append_right' (template.extract 0 off) value off
        (off + value.size) (by rw [hprefix]) (by rw [hprefix])]
    · rw [ByteArray.size_append, hprefix]
  · cases hsp

-- LIBRARY CANDIDATE: generic patchRuntime prefix get? preservation for immutable patching.
theorem patchRuntime_get?_left {template out : ByteArray} {ps : List (Nat × ByteArray)}
    {n i : Nat} (hpatch : patchRuntime template ps = some out)
    (hps : PatchesStartAt n ps) (hi : i < n) :
    out.get? i = template.get? i := by
  induction ps generalizing template with
  | nil =>
      simp [patchRuntime] at hpatch
      cases hpatch
      rfl
  | cons p ps ih =>
      have hp : n ≤ p.1 := hps p (by simp)
      have hrest : PatchesStartAt n ps := by
        intro q hq
        exact hps q (by simp [hq])
      unfold patchRuntime at hpatch
      simp only [List.foldlM_cons, Option.bind_eq_bind] at hpatch
      by_cases hsz : p.2.size = 32
      · rw [if_pos hsz] at hpatch
        cases hsp : spliceBytes? template p.1 p.2 with
        | none => simp [hsp] at hpatch
        | some mid =>
            simp [hsp] at hpatch
            calc
              out.get? i = mid.get? i := ih hpatch hrest
              _ = template.get? i := spliceBytes_get?_left hsp (by omega)
      · rw [if_neg hsz] at hpatch
        simp at hpatch

-- LIBRARY CANDIDATE: generic patchRuntime prefix extraction preservation for immutable patching.
theorem patchRuntime_extract_left {template out : ByteArray} {ps : List (Nat × ByteArray)}
    {n i j : Nat} (hpatch : patchRuntime template ps = some out)
    (hps : PatchesStartAt n ps) (hj : j ≤ n) :
    out.extract i j = template.extract i j := by
  induction ps generalizing template with
  | nil =>
      simp [patchRuntime] at hpatch
      cases hpatch
      rfl
  | cons p ps ih =>
      have hp : n ≤ p.1 := hps p (by simp)
      have hrest : PatchesStartAt n ps := by
        intro q hq
        exact hps q (by simp [hq])
      unfold patchRuntime at hpatch
      simp only [List.foldlM_cons, Option.bind_eq_bind] at hpatch
      by_cases hsz : p.2.size = 32
      · rw [if_pos hsz] at hpatch
        cases hsp : spliceBytes? template p.1 p.2 with
        | none => simp [hsp] at hpatch
        | some mid =>
            simp [hsp] at hpatch
            calc
              out.extract i j = mid.extract i j := ih hpatch hrest
              _ = template.extract i j := spliceBytes_extract_left hsp (le_trans hj hp)
      · rw [if_neg hsz] at hpatch
        simp at hpatch

-- LIBRARY CANDIDATE: generic patchRuntime prefix extraction preservation for immutable patching.
theorem patchRuntime_extract'_left {template out : ByteArray} {ps : List (Nat × ByteArray)}
    {n i j : Nat} (hpatch : patchRuntime template ps = some out)
    (hps : PatchesStartAt n ps) (hi64 : i < 2 ^ 64) (hj64 : j < 2 ^ 64)
    (hj : j ≤ n) :
    out.extract' i j = template.extract' i j := by
  induction ps generalizing template with
  | nil =>
      simp [patchRuntime] at hpatch
      cases hpatch
      rfl
  | cons p ps ih =>
      have hp : n ≤ p.1 := hps p (by simp)
      have hrest : PatchesStartAt n ps := by
        intro q hq
        exact hps q (by simp [hq])
      unfold patchRuntime at hpatch
      simp only [List.foldlM_cons, Option.bind_eq_bind] at hpatch
      by_cases hsz : p.2.size = 32
      · rw [if_pos hsz] at hpatch
        cases hsp : spliceBytes? template p.1 p.2 with
        | none => simp [hsp] at hpatch
        | some mid =>
            simp [hsp] at hpatch
            calc
              out.extract' i j = mid.extract' i j := ih hpatch hrest
              _ = template.extract' i j :=
                spliceBytes_extract'_left hsp hi64 hj64 (le_trans hj hp)
      · rw [if_neg hsz] at hpatch
        simp at hpatch

-- LIBRARY CANDIDATE: generic patchRuntime decode preservation before immutable writes.
theorem patchRuntime_decode_left {template out : ByteArray} {ps : List (Nat × ByteArray)}
    {n : Nat} (hpatch : patchRuntime template ps = some out)
    (hps : PatchesStartAt n ps) (pc : UInt256) (hwin : pc.toNat + 33 ≤ n)
    (hn64 : n < 2 ^ 64) :
    decode out pc = decode template pc := by
  unfold decode
  rw [patchRuntime_get?_left hpatch hps (by omega : pc.toNat < n)]
  cases hget : template.get? pc.toNat with
  | none => rfl
  | some byte =>
      cases hinstr : parseInstr byte with
      | none => simp [hinstr]
      | some instr =>
          simp [hinstr]
          by_cases harg : argOnNBytesOfInstr instr = 0
          · simp [harg]
          · simp [harg]
            have hargle := argOnNBytesOfInstr_le_32 instr
            have hi64 : pc.toNat + 1 < 2 ^ 64 := by omega
            have hj64 : pc.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 64 := by omega
            have hjn : pc.toNat + 1 + argOnNBytesOfInstr instr ≤ n := by omega
            rw [patchRuntime_extract'_left (n := n) hpatch hps hi64 hj64 hjn]

-- LIBRARY CANDIDATE: precise variant of `patchRuntime_decode_left` for instructions near a patch.
theorem patchRuntime_decode_left_precise {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {n : Nat}
    (hpatch : patchRuntime template ps = some out) (hps : PatchesStartAt n ps)
    (pc : UInt256) (hpc : pc.toNat < n)
    (hwin : ∀ byte instr, template.get? pc.toNat = some byte →
      parseInstr byte = some instr → pc.toNat + 1 + argOnNBytesOfInstr instr ≤ n)
    (hn64 : n < 2 ^ 64) :
    decode out pc = decode template pc := by
  unfold decode
  rw [patchRuntime_get?_left hpatch hps hpc]
  cases hget : template.get? pc.toNat with
  | none => rfl
  | some byte =>
      cases hinstr : parseInstr byte with
      | none => simp [hinstr]
      | some instr =>
          simp [hinstr]
          by_cases harg : argOnNBytesOfInstr instr = 0
          · simp [harg]
          · simp [harg]
            have hi64 : pc.toNat + 1 < 2 ^ 64 := by omega
            have hj64 : pc.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 64 := by
              have := hwin byte instr hget hinstr
              omega
            have hjn : pc.toNat + 1 + argOnNBytesOfInstr instr ≤ n :=
              hwin byte instr hget hinstr
            rw [patchRuntime_extract'_left (n := n) hpatch hps hi64 hj64 hjn]

-- LIBRARY CANDIDATE: decode preservation from a concrete original decode result.
theorem patchRuntime_decode_left_of_decode {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {n : Nat}
    (hpatch : patchRuntime template ps = some out) (hps : PatchesStartAt n ps)
    (pc : UInt256) (res : Operation × Option (UInt256 × Nat))
    (hdec : decode template pc = some res) (hpc : pc.toNat < n)
    (hwin : pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) ≤ n)
    (hn64 : n < 2 ^ 64) :
    decode out pc = some res := by
  unfold decode at hdec ⊢
  rw [patchRuntime_get?_left hpatch hps hpc]
  cases hget : template.get? pc.toNat with
  | none => simp [hget] at hdec
  | some byte =>
      simp [hget] at hdec
      cases hinstr : parseInstr byte with
      | none => simp [hinstr] at hdec
      | some instr =>
          by_cases harg : argOnNBytesOfInstr instr = 0
          · simp [hinstr, harg] at hdec ⊢
            exact hdec
          · simp [hinstr, harg] at hdec
            cases hdec
            have hjn : pc.toNat + 1 + argOnNBytesOfInstr instr ≤ n := by
              simpa using hwin
            have hi64 : pc.toNat + 1 < 2 ^ 64 := by omega
            have hj64 : pc.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 64 := by omega
            simp [hinstr, harg]
            rw [patchRuntime_extract'_left (n := n) hpatch hps hi64 hj64 hjn]

@[simp] theorem clipperWordBytes_address (a : EVM.Address) :
    wordBytes? (.address a) = some { data := (EVM.Word.ofNat ↑a).toBytesBE.toArray } := by
  rfl

-- LIBRARY CANDIDATE: decoding a 32-byte big-endian word bytearray recovers the word.
theorem uInt256OfByteArray_word_toBytesBE (w : UInt256) :
    uInt256OfByteArray ({ data := (EVM.Word.toBytesBE w).toArray } : ByteArray) = w := by
  apply word_toBytesBE_inj
  rw [toBytesBE_uInt256OfByteArray_of_size]
  · rw [byteArray_toList_eq]
  · simpa using word_toBytesBE_toByteArray_size w

-- LIBRARY CANDIDATE: decode a `PUSH32` from local opcode/payload facts without reducing the
-- surrounding generated bytecode by definitional equality.
theorem decode_push32_of_get?_extract' {code : ByteArray} {pc w : UInt256}
    (hget : code.get? pc.toNat = some 0x7f)
    (hpayload : code.extract' (pc.toNat + 1) (pc.toNat + 33)
        = ({ data := (EVM.Word.toBytesBE w).toArray } : ByteArray)) :
    decode code pc = some (.Push .PUSH32, some (w, 32)) := by
  unfold decode
  rw [hget]
  have hparse : parseInstr 0x7f = some (.Push .PUSH32) := by native_decide
  simp [hparse, argOnNBytesOfInstr]
  rw [show pc.toNat + 1 + 32 = pc.toNat + 33 by omega]
  rw [hpayload]
  rw [uInt256OfByteArray_word_toBytesBE]

theorem clipperPatchesStartAt (v : ClipperImmutables) :
    PatchesStartAt 1463 (patches v) := by
  unfold PatchesStartAt patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none => simp [hIlk]
  | some bs => simp [hIlk]

theorem clipperDecodeBeforeFirstPatch (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) (pc : UInt256)
    (hwin : pc.toNat + 33 ≤ 1463) :
    decode code pc = decode clipperBytecode pc :=
  patchRuntime_decode_left hpatch (clipperPatchesStartAt v) pc hwin (by norm_num)

theorem clipperDecodeBeforeFirstPatchPrecise (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) (pc : UInt256)
    (hpc : pc.toNat < 1463)
    (hwin : ∀ byte instr, clipperBytecode.get? pc.toNat = some byte →
      parseInstr byte = some instr → pc.toNat + 1 + argOnNBytesOfInstr instr ≤ 1463) :
    decode code pc = decode clipperBytecode pc :=
  patchRuntime_decode_left_precise hpatch (clipperPatchesStartAt v) pc hpc hwin
    (by norm_num)

theorem clipperDecodeBeforeFirstPatchOfDecode (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) (pc : UInt256)
    (res : Operation × Option (UInt256 × Nat))
    (hdec : decode clipperBytecode pc = some res) (hpc : pc.toNat < 1463)
    (hwin : pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) ≤ 1463) :
    decode code pc = some res :=
  patchRuntime_decode_left_of_decode hpatch (clipperPatchesStartAt v) pc res hdec hpc hwin
    (by norm_num)

-- LIBRARY CANDIDATE: split a bytearray into a fixed prefix and suffix.
theorem byteArray_eq_extract_prefix_suffix (b : ByteArray) (n : Nat) (hn : n ≤ b.size) :
    b = b.extract 0 n ++ b.extract n b.size := by
  calc
    b = b.extract 0 b.size := (Reasoning.Theory.byteArray_extract_self b).symm
    _ = b.extract 0 n ++ b.extract n b.size :=
      ByteArray.extract_eq_extract_append_extract (a := b) (i := 0) (k := b.size)
        n (Nat.zero_le _) hn

-- LIBRARY CANDIDATE: generic ByteArray append-tail `get?`.
theorem byteArray_get?_append_right (A B : ByteArray) {i : Nat} (h : A.size ≤ i) :
    (A ++ B).get? i = B.get? (i - A.size) := by
  unfold ByteArray.get?
  by_cases hab : i < (A ++ B).size
  · have hb : i - A.size < B.size := by
      rw [ByteArray.size_append] at hab
      omega
    simp only [dif_pos hab, dif_pos hb]
    apply congrArg some
    change (A ++ B)[i] = B[i - A.size]
    rw [ByteArray.get_append_right h]
  · have hb : ¬ i - A.size < B.size := by
      rw [ByteArray.size_append] at hab
      omega
    simp only [dif_neg hab, dif_neg hb]

-- LIBRARY CANDIDATE: generic splice suffix get? preservation for immutable patching.
theorem spliceBytes_get?_right {template value out : ByteArray} {off i : Nat}
    (hsp : spliceBytes? template off value = some out) (hi : off + value.size ≤ i) :
    out.get? i = template.get? i := by
  unfold spliceBytes? at hsp
  split at hsp
  · rename_i hle
    cases hsp
    have hprefix : (template.extract 0 off ++ value).size = off + value.size := by
      rw [ByteArray.size_append, ByteArray.size_extract]
      omega
    rw [byteArray_get?_append_right (template.extract 0 off ++ value)
      (template.extract (off + value.size) template.size) (by omega)]
    unfold ByteArray.get?
    by_cases hsuf : i - (template.extract 0 off ++ value).size <
        (template.extract (off + value.size) template.size).size
    · have htemp : i < template.size := by
        rw [hprefix, ByteArray.size_extract] at hsuf
        omega
      simp only [dif_pos hsuf, dif_pos htemp]
      apply congrArg some
      let suffix := template.extract (off + value.size) template.size
      change suffix[i - (template.extract 0 off ++ value).size] = template[i]
      rw [ByteArray.get_extract hsuf]
      have hoff : min off template.size = off := by omega
      have hidx : off + value.size + (i - (off + value.size)) = i := by omega
      simp [hoff, hidx]
    · have htemp : ¬ i < template.size := by
        rw [hprefix, ByteArray.size_extract] at hsuf
        omega
      simp only [dif_neg hsuf, dif_neg htemp]
  · cases hsp

-- LIBRARY CANDIDATE: generic splice suffix extraction preservation for immutable patching.
theorem spliceBytes_extract_right {template value out : ByteArray} {off i j : Nat}
    (hsp : spliceBytes? template off value = some out) (hi : off + value.size ≤ i) :
    out.extract i j = template.extract i j := by
  unfold spliceBytes? at hsp
  split at hsp
  · rename_i hle
    cases hsp
    have hprefix : (template.extract 0 off ++ value).size = off + value.size := by
      rw [ByteArray.size_append, ByteArray.size_extract]
      omega
    have htprefix : (template.extract 0 (off + value.size)).size = off + value.size := by
      rw [ByteArray.size_extract]
      omega
    have hsplit := byteArray_eq_extract_prefix_suffix template (off + value.size) hle
    conv_rhs => rw [hsplit]
    rw [Reasoning.Theory.extract_append_right_window (template.extract 0 off ++ value)
      (template.extract (off + value.size) template.size) i j (by omega)]
    rw [Reasoning.Theory.extract_append_right_window (template.extract 0 (off + value.size))
      (template.extract (off + value.size) template.size) i j (by omega)]
    rw [hprefix, htprefix]
  · cases hsp

-- LIBRARY CANDIDATE: generic splice suffix `extract'` preservation for immutable patching.
theorem spliceBytes_extract'_right {template value out : ByteArray} {off i j : Nat}
    (hsp : spliceBytes? template off value = some out)
    (hi64 : i < 2 ^ 64) (hj64 : j < 2 ^ 64) (hi : off + value.size ≤ i) :
    out.extract' i j = template.extract' i j := by
  unfold ByteArray.extract'
  have hguard : (decide (i < 2 ^ 64) && decide (j < 2 ^ 64)) = true := by
    rw [decide_eq_true hi64, decide_eq_true hj64]
    rfl
  rw [if_pos hguard, if_pos hguard]
  exact spliceBytes_extract_right hsp hi

theorem spliceBytes_get?_disjoint {template value out : ByteArray} {off i : Nat}
    (hsp : spliceBytes? template off value = some out)
    (hdisj : PatchWindowDisjoint i (i + 1) (off, value)) :
    out.get? i = template.get? i := by
  rcases hdisj with hright | hleft
  · exact spliceBytes_get?_right hsp hright
  · exact spliceBytes_get?_left hsp (by omega)

theorem spliceBytes_extract_disjoint {template value out : ByteArray} {off i j : Nat}
    (hsp : spliceBytes? template off value = some out)
    (hdisj : PatchWindowDisjoint i j (off, value)) :
    out.extract i j = template.extract i j := by
  rcases hdisj with hright | hleft
  · exact spliceBytes_extract_right hsp hright
  · exact spliceBytes_extract_left hsp hleft

theorem spliceBytes_extract'_disjoint {template value out : ByteArray} {off i j : Nat}
    (hsp : spliceBytes? template off value = some out)
    (hi64 : i < 2 ^ 64) (hj64 : j < 2 ^ 64)
    (hdisj : PatchWindowDisjoint i j (off, value)) :
    out.extract' i j = template.extract' i j := by
  rcases hdisj with hright | hleft
  · exact spliceBytes_extract'_right hsp hi64 hj64 hright
  · exact spliceBytes_extract'_left hsp hi64 hj64 hleft

-- LIBRARY CANDIDATE: generic patchRuntime byte preservation outside 32-byte patch windows.
theorem patchRuntime_get?_disjoint {template out : ByteArray} {ps : List (Nat × ByteArray)}
    {i : Nat} (hpatch : patchRuntime template ps = some out)
    (hps : PatchesWindowDisjoint32 i (i + 1) ps) :
    out.get? i = template.get? i := by
  induction ps generalizing template with
  | nil =>
      simp [patchRuntime] at hpatch
      cases hpatch
      rfl
  | cons p ps ih =>
      have hp32 : PatchWindowDisjoint32 i (i + 1) p := hps p (by simp)
      have hrest : PatchesWindowDisjoint32 i (i + 1) ps := by
        intro q hq
        exact hps q (by simp [hq])
      unfold patchRuntime at hpatch
      simp only [List.foldlM_cons, Option.bind_eq_bind] at hpatch
      by_cases hsz : p.2.size = 32
      · rw [if_pos hsz] at hpatch
        cases hsp : spliceBytes? template p.1 p.2 with
        | none => simp [hsp] at hpatch
        | some mid =>
            simp [hsp] at hpatch
            have hp : PatchWindowDisjoint i (i + 1) p := by
              rcases hp32 with hright | hleft
              · exact Or.inl (by simpa [hsz] using hright)
              · exact Or.inr hleft
            calc
              out.get? i = mid.get? i := ih hpatch hrest
              _ = template.get? i := spliceBytes_get?_disjoint hsp hp
      · rw [if_neg hsz] at hpatch
        simp at hpatch

-- LIBRARY CANDIDATE: generic `D_J_aux` preservation for immutable patching while scanning
-- outside all 32-byte patch windows.
theorem patchRuntime_D_J_aux_contains_of_patchScanReaches
    {template out : ByteArray} {ps : List (Nat × ByteArray)}
    {fuel i target : Nat} (acc : Array UInt256)
    (hpatch : patchRuntime template ps = some out)
    (hscan : patchScanReaches fuel template (ps.map Prod.fst) i target = true) :
    (D_J_aux out i acc).contains (UInt256.ofNat target) = true := by
  induction fuel generalizing i acc with
  | zero =>
      simp [patchScanReaches] at hscan
  | succ fuel ih =>
      unfold patchScanReaches at hscan
      cases hdecode : template.get? i >>= parseInstr with
      | none =>
          simp [hdecode] at hscan
      | some op =>
          simp [hdecode] at hscan
          cases hdisjBool :
              patchOffsetsWindowDisjoint32Bool i (i + 1) (ps.map Prod.fst) with
          | false =>
              simp [hdisjBool] at hscan
          | true =>
              simp [hdisjBool] at hscan
              have hdisj : PatchesWindowDisjoint32 i (i + 1) ps :=
                patchesWindowDisjoint32_of_offsets_bool hdisjBool
              have hout : out.get? i >>= parseInstr = some op := by
                rw [patchRuntime_get?_disjoint hpatch hdisj]
                exact hdecode
              rw [D_J_aux_eq_some out i acc op hout]
              by_cases hhit : i = target ∧ op = .JUMPDEST
              · rw [D_J_aux_acc]
                simp [hhit.1, hhit.2]
              · have hnext :
                    patchScanReaches fuel template (ps.map Prod.fst) (N i op) target = true := by
                  simpa [hhit] using hscan
                exact ih (i := N i op)
                  (acc := if op = .JUMPDEST then acc.push (UInt256.ofNat i) else acc) hnext

-- LIBRARY CANDIDATE: generic `D_J` preservation for immutable patching while scanning
-- outside all 32-byte patch windows.
theorem patchRuntime_D_J_contains_of_patchScanReaches
    {template out : ByteArray} {ps : List (Nat × ByteArray)}
    {fuel target : Nat}
    (hpatch : patchRuntime template ps = some out)
    (hscan : patchScanReaches fuel template (ps.map Prod.fst) 0 target = true) :
    (D_J out 0).contains (UInt256.ofNat target) = true := by
  simpa [D_J] using
    patchRuntime_D_J_aux_contains_of_patchScanReaches (acc := #[]) hpatch hscan

-- LIBRARY CANDIDATE: generic patchRuntime extraction preservation outside 32-byte patch windows.
theorem patchRuntime_extract_disjoint {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {i j : Nat}
    (hpatch : patchRuntime template ps = some out)
    (hps : PatchesWindowDisjoint32 i j ps) :
    out.extract i j = template.extract i j := by
  induction ps generalizing template with
  | nil =>
      simp [patchRuntime] at hpatch
      cases hpatch
      rfl
  | cons p ps ih =>
      have hp32 : PatchWindowDisjoint32 i j p := hps p (by simp)
      have hrest : PatchesWindowDisjoint32 i j ps := by
        intro q hq
        exact hps q (by simp [hq])
      unfold patchRuntime at hpatch
      simp only [List.foldlM_cons, Option.bind_eq_bind] at hpatch
      by_cases hsz : p.2.size = 32
      · rw [if_pos hsz] at hpatch
        cases hsp : spliceBytes? template p.1 p.2 with
        | none => simp [hsp] at hpatch
        | some mid =>
            simp [hsp] at hpatch
            have hp : PatchWindowDisjoint i j p := by
              rcases hp32 with hright | hleft
              · exact Or.inl (by simpa [hsz] using hright)
              · exact Or.inr hleft
            calc
              out.extract i j = mid.extract i j := ih hpatch hrest
              _ = template.extract i j := spliceBytes_extract_disjoint hsp hp
      · rw [if_neg hsz] at hpatch
        simp at hpatch

-- LIBRARY CANDIDATE: after a target 32-byte splice, later disjoint patches preserve it.
theorem patchRuntime_extract_exact_cons {template out value : ByteArray}
    {ps : List (Nat × ByteArray)} {off : Nat}
    (hpatch : patchRuntime template ((off, value) :: ps) = some out)
    (hsize : value.size = 32)
    (hps : PatchesWindowDisjoint32 off (off + 32) ps) :
    out.extract off (off + 32) = value := by
  unfold patchRuntime at hpatch
  simp only [List.foldlM_cons, Option.bind_eq_bind] at hpatch
  rw [if_pos hsize] at hpatch
  cases hsp : spliceBytes? template off value with
  | none =>
      simp [hsp] at hpatch
  | some mid =>
      simp [hsp] at hpatch
      calc
        out.extract off (off + 32) = mid.extract off (off + 32) :=
          patchRuntime_extract_disjoint hpatch hps
        _ = value := by
          rw [← hsize]
          exact spliceBytes_extract_middle hsp

-- LIBRARY CANDIDATE: locate a target 32-byte splice after an arbitrary prefix.
theorem patchRuntime_extract_exact_split {template out value : ByteArray}
    {pre post : List (Nat × ByteArray)} {off : Nat}
    (hpatch : patchRuntime template (pre ++ (off, value) :: post) = some out)
    (hsize : value.size = 32)
    (hpost : PatchesWindowDisjoint32 off (off + 32) post) :
    out.extract off (off + 32) = value := by
  induction pre generalizing template with
  | nil =>
      simpa using patchRuntime_extract_exact_cons hpatch hsize hpost
  | cons p pre ih =>
      change patchRuntime template (p :: (pre ++ (off, value) :: post)) = some out at hpatch
      unfold patchRuntime at hpatch
      simp only [List.foldlM_cons, Option.bind_eq_bind] at hpatch
      by_cases hpsz : p.2.size = 32
      · rw [if_pos hpsz] at hpatch
        cases hsp : spliceBytes? template p.1 p.2 with
        | none =>
            simp [hsp] at hpatch
        | some mid =>
            simp [hsp] at hpatch
            change ((List.foldlM
              (fun acc p => if p.2.size = 32 then spliceBytes? acc p.1 p.2 else none)
              mid pre).bind fun init =>
                List.foldlM
                  (fun acc p => if p.2.size = 32 then spliceBytes? acc p.1 p.2 else none)
                  init ((off, value) :: post)) = some out at hpatch
            have hpatch' : patchRuntime mid (pre ++ (off, value) :: post) = some out := by
              unfold patchRuntime
              rw [List.foldlM_append]
              exact hpatch
            exact ih hpatch'
      · rw [if_neg hpsz] at hpatch
        simp at hpatch

-- LIBRARY CANDIDATE: `extract'` form of `patchRuntime_extract_exact_split`.
theorem patchRuntime_extract'_exact_split {template out value : ByteArray}
    {pre post : List (Nat × ByteArray)} {off : Nat}
    (hpatch : patchRuntime template (pre ++ (off, value) :: post) = some out)
    (hsize : value.size = 32)
    (hpost : PatchesWindowDisjoint32 off (off + 32) post)
    (hi64 : off < 2 ^ 64) (hj64 : off + 32 < 2 ^ 64) :
    out.extract' off (off + 32) = value := by
  unfold ByteArray.extract'
  have hguard : (decide (off < 2 ^ 64) && decide (off + 32 < 2 ^ 64)) = true := by
    rw [decide_eq_true hi64, decide_eq_true hj64]
    rfl
  rw [if_pos hguard]
  exact patchRuntime_extract_exact_split hpatch hsize hpost

-- LIBRARY CANDIDATE: generic patchRuntime `extract'` preservation outside patch windows.
theorem patchRuntime_extract'_disjoint {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {i j : Nat}
    (hpatch : patchRuntime template ps = some out)
    (hps : PatchesWindowDisjoint32 i j ps) (hi64 : i < 2 ^ 64) (hj64 : j < 2 ^ 64) :
    out.extract' i j = template.extract' i j := by
  unfold ByteArray.extract'
  have hguard : (decide (i < 2 ^ 64) && decide (j < 2 ^ 64)) = true := by
    rw [decide_eq_true hi64, decide_eq_true hj64]
    rfl
  rw [if_pos hguard, if_pos hguard]
  exact patchRuntime_extract_disjoint hpatch hps

-- LIBRARY CANDIDATE: decode preservation outside immutable patch windows.
theorem patchRuntime_decode_disjoint_of_decode {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {pc : UInt256}
    {res : Operation × Option (UInt256 × Nat)}
    (hpatch : patchRuntime template ps = some out)
    (hbyte : PatchesWindowDisjoint32 pc.toNat (pc.toNat + 1) ps)
    (hargs : ∀ byte instr, template.get? pc.toNat = some byte →
      parseInstr byte = some instr →
      PatchesWindowDisjoint32 (pc.toNat + 1)
        (pc.toNat + 1 + argOnNBytesOfInstr instr) ps)
    (hdec : decode template pc = some res)
    (hi64 : pc.toNat + 1 < 2 ^ 64)
    (harg64 : ∀ byte instr, template.get? pc.toNat = some byte →
      parseInstr byte = some instr → pc.toNat + 1 + argOnNBytesOfInstr instr < 2 ^ 64) :
    decode out pc = some res := by
  unfold decode at hdec ⊢
  rw [patchRuntime_get?_disjoint hpatch hbyte]
  cases hget : template.get? pc.toNat with
  | none => simp [hget] at hdec
  | some byte =>
      simp [hget] at hdec
      cases hinstr : parseInstr byte with
      | none => simp [hinstr] at hdec
      | some instr =>
          by_cases harg : argOnNBytesOfInstr instr = 0
          · simp [hinstr, harg] at hdec ⊢
            exact hdec
          · simp [hinstr, harg] at hdec
            cases hdec
            have hps := hargs byte instr hget hinstr
            have hj64 := harg64 byte instr hget hinstr
            simp [hinstr, harg]
            rw [patchRuntime_extract'_disjoint hpatch hps hi64 hj64]

-- LIBRARY CANDIDATE: result-width variant of decode preservation outside patch windows.
theorem patchRuntime_decode_disjoint_of_decode_res {template out : ByteArray}
    {ps : List (Nat × ByteArray)} {pc : UInt256}
    {res : Operation × Option (UInt256 × Nat)}
    (hpatch : patchRuntime template ps = some out)
    (hbyte : PatchesWindowDisjoint32 pc.toNat (pc.toNat + 1) ps)
    (hargs : PatchesWindowDisjoint32 (pc.toNat + 1)
      (pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2)) ps)
    (hdec : decode template pc = some res)
    (hi64 : pc.toNat + 1 < 2 ^ 64)
    (harg64 :
      pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) < 2 ^ 64) :
    decode out pc = some res := by
  unfold decode at hdec ⊢
  rw [patchRuntime_get?_disjoint hpatch hbyte]
  cases hget : template.get? pc.toNat with
  | none => simp [hget] at hdec
  | some byte =>
      simp [hget] at hdec
      cases hinstr : parseInstr byte with
      | none => simp [hinstr] at hdec
      | some instr =>
          by_cases harg : argOnNBytesOfInstr instr = 0
          · simp [hinstr, harg] at hdec ⊢
            exact hdec
          · simp [hinstr, harg] at hdec
            cases hdec
            simp [hinstr, harg]
            rw [patchRuntime_extract'_disjoint hpatch hargs hi64 (by simpa using harg64)]

theorem clipperPrefixBeforeFirstPatch (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    code.extract 0 1463 = clipperBytecode.extract 0 1463 :=
  patchRuntime_extract_left hpatch (clipperPatchesStartAt v) (by rfl)

theorem clipperCodeSize_ge_firstPatch (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    1463 ≤ code.size := by
  have hprefix := clipperPrefixBeforeFirstPatch v hpatch
  have hsz : (code.extract 0 1463).size = 1463 := by
    rw [hprefix]
    native_decide
  rw [ByteArray.size_extract] at hsz
  omega

theorem clipperJumpDestBeforeFirstPatch (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) (pc : UInt256)
    (hpc : (D_J (clipperBytecode.extract 0 1463) 0).contains pc = true) :
    (D_J code 0).contains pc = true := by
  have hprefix := clipperPrefixBeforeFirstPatch v hpatch
  have hsplit := byteArray_eq_extract_prefix_suffix code 1463
    (clipperCodeSize_ge_firstPatch v hpatch)
  rw [hsplit, hprefix]
  exact Reasoning.Theory.D_J_contains_append_left
    (clipperBytecode.extract 0 1463) (code.extract 1463 code.size) pc hpc

theorem clipperStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc] using storageLocLoad_uint256 evm slot

theorem clipperStorageLocLoad_address (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (addrLoc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  simpa [addrLoc, addressOffset0Loc] using
    storageLocLoad_address_offset0 evm slot

theorem clipperStorageLocLoad_uint64 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint64Loc slot ⟨0, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        (UInt256.ofNat (2 ^ 64 - 1))).toNat) := by
  simpa [uint64Loc, uint64Int] using
    storageLocLoad_uint_offset0 (evm := evm) (slot := slot)
      (size := ⟨8, by decide⟩) (width := ⟨64, by decide⟩)
      (hbound := by decide) (by decide)

theorem clipperStorageLocLoad_uint192 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint192Loc slot ⟨8, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨192⟩) ⟨1⟩)).toNat) := by
  have h := storageLocLoad_uint_offset (evm := evm) (slot := slot)
    (offset := ⟨8, by decide⟩) (size := ⟨24, by decide⟩)
    (width := ⟨192, by decide⟩) (hbound := by decide) (by decide) (by decide)
  simpa [uint192Loc, uint192Int] using h

-- LIBRARY CANDIDATE: ABI-encoding any unsigned integer width whose value is in range.
theorem uintReturnEncoding (width : ABI.BitWidth) (v : UInt256)
    (hlt : v.toNat < EVM.twoPow width.val) :
    encodeReturnValue? (.elem (.int (.uint width))) (.int (Int.ofNat v.toNat)) =
      some (UInt256.toByteArray v) := by
  have hword : EVM.word v.toNat = v := by
    show UInt256.ofNat v.toNat = v
    exact u256_ofNat_toNat v
  refine scalarReturnEncoding (t := (.int (.uint width))) (w := v) rfl ?_ ?_
  · simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
    cases width with
    | mk bits hbits => rfl
  · cases width with
    | mk bits hbits =>
        change v.toNat < EVM.twoPow bits at hlt
        simp only [encodeABIValue?, encodeABIWord?]
        have hcond : 0 ≤ Int.ofNat v.toNat ∧
            Int.ofNat v.toNat < Int.ofNat (EVM.twoPow bits) :=
          ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hlt⟩
        rw [if_pos hcond]
        rw [if_neg (Nat.ne_of_gt hbits.1)]
        simp [hword]

-- LIBRARY CANDIDATE: ABI encoding a `uint256` value is its big-endian EVM word.
theorem clipperEncodeABIValue_uint256 (v : UInt256) :
    encodeABIValue? uint256 (.int (Int.ofNat v.toNat)) =
      some (EVM.Word.toBytesBE v) := by
  have hword : EVM.word v.toNat = v := by
    show UInt256.ofNat v.toNat = v
    exact u256_ofNat_toNat v
  have hlt : v.toNat < EVM.twoPow 256 := by
    change v.val.val < EVM.twoPow 256
    exact v.val.isLt
  simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hlt]

noncomputable abbrev clipperActiveHashMem : ByteArray :=
  wordAt0Mem (⟨11⟩ : UInt256) solcFreePtrMem

theorem clipperActiveHashMem_size : clipperActiveHashMem.size = 96 := by
  simpa [clipperActiveHashMem] using
    wordAt0Mem_size_96 (mem := solcFreePtrMem) (⟨11⟩ : UInt256) solcFreePtrMem_size

-- LIBRARY CANDIDATE: writing a word at scratch offset 0 preserves the solc free-pointer word.
theorem wordAt0Mem_read64 {mem : ByteArray} (word : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (wordAt0Mem word mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
    (by omega) (by rw [hmem])]
  exact hread64

theorem clipperActiveHashMem_read64 :
    clipperActiveHashMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  simpa [clipperActiveHashMem] using
    wordAt0Mem_read64 (⟨11⟩ : UInt256) solcFreePtrMem_size solcFreePtrMem_read64

theorem clipperActiveHashMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ clipperActiveHashMem.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        (clipperActiveHashMem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact mloadFreePtrValue
    (mem := clipperActiveHashMem) (aw := UInt256.ofNat 3)
    (by rw [clipperActiveHashMem_size]; norm_num)
    (by decide)
    clipperActiveHashMem_read64

theorem clipperActiveHashMem_keccak_slot :
    UInt256.ofNat
        (fromByteArrayBigEndian
          (ffi.KEC (clipperActiveHashMem.readWithPadding (⟨0⟩ : UInt256).toNat
            (⟨32⟩ : UInt256).toNat))) =
      activeDataSlot := by
  simpa [clipperActiveHashMem, activeDataSlot,
    show (⟨0⟩ : UInt256).toNat = 0 from by decide,
    show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
    (wordAt0Mem_keccak_word (⟨11⟩ : UInt256) solcFreePtrMem).trans
      (keccakSlot_eq (UInt256.toByteArray (⟨11⟩ : UInt256)))

-- LIBRARY CANDIDATE: a word masked by `2^bits - 1` is in the corresponding uint range.
theorem u256LandMaskToNatLtOfToNat {bits : Nat} (w mask : UInt256)
    (hmask : mask.toNat = 2 ^ bits - 1) :
    (UInt256.land w mask).toNat < EVM.twoPow bits := by
  rw [uland_toNat, hmask]
  have hle : w.toNat &&& (2 ^ bits - 1) ≤ 2 ^ bits - 1 := nat_land_le_right _ _
  have hpos : 0 < 2 ^ bits := Nat.pow_pos (a := 2) (n := bits) (by decide)
  simpa [EVM.twoPow] using lt_of_le_of_lt hle (Nat.sub_lt hpos Nat.one_pos)

-- LIBRARY CANDIDATE: masking an already-canonical uint subword is value-preserving.
theorem u256LandMaskCleanOfToNat {bits : Nat} (w mask : UInt256)
    (hmask : mask.toNat = 2 ^ bits - 1) (hcanon : w.toNat < EVM.twoPow bits) :
    UInt256.land w mask = w := by
  apply u256_inj
  rw [uland_toNat, hmask]
  change Nat.land w.toNat (2 ^ bits - 1) = w.toNat
  rw [nat_land_mask_eq_mod]
  exact Nat.mod_eq_of_lt (by simpa [EVM.twoPow] using hcanon)

theorem clipperReturnWord476Wf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcReturnWordFromMemWf code (⟨476⟩ : UInt256) := by
  unfold solcReturnWordFromMemWf
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]
    native_decide

theorem clipperReturnAddress716Wf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcReturnAddressFromMemWf code (⟨716⟩ : UInt256) := by
  unfold solcReturnAddressFromMemWf
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]
    native_decide

-- GENERALIZES Reasoning.Solc.solcWordSlotGetterWf: packed uint getters mask the loaded word
-- before jumping back to the ABI return block.
@[reducible] def clipperPackedUintSlotGetterWf
    (code : ByteArray) (pc slot mask : UInt256) (width : Nat) (op : Operation.POp) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let pMaskOut := p4 + UInt256.ofNat width.succ
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ op ≠ .PUSH0
  ∧ decode code p4 = some (.Push op, some (mask, width))
  ∧ decode code pMaskOut = some (.AND, .none)
  ∧ decode code (pMaskOut + ⟨1⟩) = some (.DUP2, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩) = some (.JUMP, .none)

-- GENERALIZES Reasoning.Solc.RD.solcWordSlotGetter: packed uint getters use
-- `SLOAD; PUSHn mask; AND; DUP2; JUMP`.
theorem clipperPackedUintSlotGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc slot mask ret : UInt256} {width : Nat}
    {op : Operation.POp} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem aw rdata (cA, σ) k C)
    (hwf : clipperPackedUintSlotGetterWf code pc slot mask width op)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (UInt256.land (solcSlotWord σ ee slot) mask :: ret :: R) mem aw rdata (cA, σ) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hop, hd4, hdMaskOut, hdAndOut, hdJump⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 slot hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by simp only [List.length_cons]; omega)
  have rdMask := rd4.pushConst mask (width := width) (op := op) hop hd4
    (by simp only [List.length_cons]; omega)
  have rdAndOut := rdMask.and hdMaskOut (by simp only [List.length_cons]; omega)
  have rdJump := rdAndOut.dup2 hdAndOut (by omega)
  have rdRet := rdJump.jump hdJump hret (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa [solcSlotWord, u256_land_comm mask
      (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩))] using rdRet⟩

-- GENERALIZES Reasoning.Solc.solcReturnUint8FromMemWf: return a scalar after applying an
-- arbitrary literal uint mask.
@[reducible] def clipperReturnMaskedFromMemWf
    (code : ByteArray) (pc mask : UInt256) (width : Nat) (op : Operation.POp) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let pMaskOut := p5 + UInt256.ofNat width.succ
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p3 = some (.DUP1, .none)
  ∧ decode code p4 = some (.MLOAD, .none)
  ∧ op ≠ .PUSH0
  ∧ decode code p5 = some (.Push op, some (mask, width))
  ∧ decode code pMaskOut = some (.SWAP1, .none)
  ∧ decode code (pMaskOut + ⟨1⟩) = some (.SWAP3, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩) = some (.AND, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.DUP3, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.MSTORE, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.MLOAD, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.DUP2, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
      ⟨1⟩) = some (.SWAP1, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
      ⟨1⟩ + ⟨1⟩) = some (.SUB, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
      ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
      ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) = some (.ADD, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
      ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.SWAP1, .none)
  ∧ decode code (pMaskOut + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
      ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.RETURN, .none)

-- GENERALIZES Reasoning.Solc.RD.solcReturnUint8FromMem: the same return block works for
-- any literal uint mask width.
theorem clipperReturnMaskedFromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc val ret mask : UInt256} {width : Nat}
    {op : Operation.POp} {R : List UInt256} {mem memout rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (val :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : clipperReturnMaskedFromMemWf code pc mask width op)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout :
      (UInt256.toByteArray (UInt256.land val mask)).write 0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 :
      memout.readWithPadding 128 32 = UInt256.toByteArray (UInt256.land val mask))
    (hov : R.length + 9 ≤ 1024) :
    RDret code g s0 acc (UInt256.toByteArray (UInt256.land val mask)) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hop, hd5, hdMaskOut, hdSwap3, hdAnd, hdDup3, hdMstore,
      hdMload, hdSwap1, hdDup2, hdSwap1b, hdSub, hdPush32, hdAdd, hdSwap1c, hdRet⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨64⟩ hd1 (by simp only [List.length_cons]; omega)
  have rd4 := rd3.dup1 hd3 (by simp only [List.length_cons]; omega)
  have rd5 := rd4.mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64
    (by decide) (by simp only [List.length_cons]; omega)
  have rdMask := rd5.pushConst mask (width := width) (op := op) hop hd5
    (by simp only [List.length_cons]; omega)
  exact evm_run rdMask with [
    raw swap1 hdMaskOut (by evm_ov),
    raw swap3 hdSwap3 (by evm_ov),
    raw and hdAnd (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw mstore 6 memout (UInt256.ofNat 5) hdMstore mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hdMload mem_cost hmemoutLoad64 (by decide)
      (by evm_ov),
    raw swap1 hdSwap1 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap1b (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨32⟩ hdPush32 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw swap1 hdSwap1c (by evm_ov),
    raw ret 0 (UInt256.toByteArray (UInt256.land val mask)) hdRet mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov)]

theorem clipperPackedUintGetterExternal {code : ByteArray} {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel entry routine slot returnPc mask : UInt256} {bits width : Nat}
    {op : Operation.POp}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : clipperPackedUintSlotGetterWf code routine slot mask width op)
    (hmask : mask.toNat = 2 ^ bits - 1)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : clipperReturnMaskedFromMemWf code returnPc mask width op) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land (solcSlotWord σ I slot) mask)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := clipperPackedUintSlotGetter (slot := slot) (mask := mask)
    (width := width) (op := op) (R := [sel]) rdRoutine hgetter hret
    (by simp only [List.length_singleton]; omega)
  have hrd := clipperReturnMaskedFromMem (mask := mask) (width := width) (op := op)
    rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (UInt256.land (UInt256.land (solcSlotWord σ I slot) mask) mask))
    (solcReturnMem_read128 (UInt256.land (UInt256.land (solcSlotWord σ I slot) mask) mask))
    (by simp only [List.length_singleton]; omega)
  have hclean :
      UInt256.land (UInt256.land (solcSlotWord σ I slot) mask) mask =
        UInt256.land (solcSlotWord σ I slot) mask :=
    u256LandMaskCleanOfToNat (UInt256.land (solcSlotWord σ I slot) mask) mask hmask
      (u256LandMaskToNatLtOfToNat (solcSlotWord σ I slot) mask hmask)
  simpa [hclean] using hrd

-- GENERALIZES Reasoning.Solc.solcWordSlotGetterWf: packed uint getters with nonzero
-- byte offset divide the loaded slot by a computed power-of-two divisor before masking.
@[reducible] def clipperPackedUintOffsetSlotGetterWf
    (code : ByteArray) (pc slot shiftBits bits : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p8 := p6 + UInt256.ofNat 2
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p15 := p13 + UInt256.ofNat 2
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p6 = some (.Push .PUSH1, some (shiftBits, 1))
  ∧ decode code p8 = some (.SHL, .none)
  ∧ decode code p9 = some (.SWAP1, .none)
  ∧ decode code p10 = some (.DIV, .none)
  ∧ decode code p11 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p15 = some (.Push .PUSH1, some (bits, 1))
  ∧ decode code p17 = some (.SHL, .none)
  ∧ decode code p18 = some (.SUB, .none)
  ∧ decode code p19 = some (.AND, .none)
  ∧ decode code p20 = some (.DUP2, .none)
  ∧ decode code p21 = some (.JUMP, .none)

-- GENERALIZES Reasoning.Solc.RD.solcWordSlotGetter: packed offset uint getters use
-- `SLOAD; SHL; DIV; SHL; SUB; AND; DUP2; JUMP`.
set_option maxHeartbeats 1000000 in
theorem clipperPackedUintOffsetSlotGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc slot shiftBits bits ret : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem aw rdata (cA, σ) k C)
    (hwf : clipperPackedUintOffsetSlotGetterWf code pc slot shiftBits bits)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (UInt256.land
        (UInt256.div (solcSlotWord σ ee slot)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) shiftBits))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩) ::
        ret :: R) mem aw rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd6, hd8, hd9, hd10, hd11, hd13, hd15, hd17, hd18,
      hd19, hd20, hd21⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 slot hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by simp only [List.length_cons]; omega)
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by simp only [List.length_cons]; omega)
  have rd8 := rd6.push1 shiftBits hd6 (by simp only [List.length_cons]; omega)
  have rd9 := rd8.shl hd8 (by simp only [List.length_cons]; omega)
  have rd10 := rd9.swap1 hd9 (by simp only [List.length_cons]; omega)
  have rd11 := rd10.div hd10 (by simp only [List.length_cons]; omega)
  have rd13 := rd11.push1 ⟨1⟩ hd11 (by simp only [List.length_cons]; omega)
  have rd15 := rd13.push1 ⟨1⟩ hd13 (by simp only [List.length_cons]; omega)
  have rd17 := rd15.push1 bits hd15 (by simp only [List.length_cons]; omega)
  have rd18 := rd17.shl hd17 (by simp only [List.length_cons]; omega)
  have rd19 := rd18.sub hd18 (by simp only [List.length_cons]; omega)
  have rd20 := rd19.and hd19 (by simp only [List.length_cons]; omega)
  have rd21 := rd20.dup2 hd20 (by omega)
  have rdRet := rd21.jump hd21 hret (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa [solcSlotWord, u256_land_comm
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩)
      (UInt256.div
        (σ.find? ee.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩))
        (UInt256.shiftLeft (⟨1⟩ : UInt256) shiftBits))] using rdRet⟩

-- GENERALIZES Reasoning.Solc.solcReturnAddressFromMemWf: return a scalar after applying
-- a computed `(1 << bits) - 1` uint mask.
@[reducible] def clipperReturnComputedMaskFromMemWf
    (code : ByteArray) (pc bits : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p7 := p5 + UInt256.ofNat 2
  let p9 := p7 + UInt256.ofNat 2
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p25 := p23 + UInt256.ofNat 2
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p3 = some (.DUP1, .none)
  ∧ decode code p4 = some (.MLOAD, .none)
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p7 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p9 = some (.Push .PUSH1, some (bits, 1))
  ∧ decode code p11 = some (.SHL, .none)
  ∧ decode code p12 = some (.SUB, .none)
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.SWAP3, .none)
  ∧ decode code p15 = some (.AND, .none)
  ∧ decode code p16 = some (.DUP3, .none)
  ∧ decode code p17 = some (.MSTORE, .none)
  ∧ decode code p18 = some (.MLOAD, .none)
  ∧ decode code p19 = some (.SWAP1, .none)
  ∧ decode code p20 = some (.DUP2, .none)
  ∧ decode code p21 = some (.SWAP1, .none)
  ∧ decode code p22 = some (.SUB, .none)
  ∧ decode code p23 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p25 = some (.ADD, .none)
  ∧ decode code p26 = some (.SWAP1, .none)
  ∧ decode code p27 = some (.RETURN, .none)

-- GENERALIZES Reasoning.Solc.RD.solcReturnAddressFromMem: the same computed-mask return
-- block works for any uint bit width emitted as `PUSH1 bits`.
set_option maxHeartbeats 1000000 in
theorem clipperReturnComputedMaskFromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc val ret bits : UInt256}
    {R : List UInt256} {mem memout rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (val :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : clipperReturnComputedMaskFromMemWf code pc bits)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout :
      (UInt256.toByteArray (UInt256.land val
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩))).write
          0 mem 128 32 = memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 :
      memout.readWithPadding 128 32 = UInt256.toByteArray (UInt256.land val
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩)))
    (hov : R.length + 9 ≤ 1024) :
    RDret code g s0 acc (UInt256.toByteArray (UInt256.land val
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩))) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd7, hd9, hd11, hd12, hd13, hd14, hd15, hd16, hd17,
      hd18, hd19, hd20, hd21, hd22, hd23, hd25, hd26, hd27⟩
  exact evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64 (by decide) (by evm_ov),
    raw push1 ⟨1⟩ hd5 (by evm_ov),
    raw push1 ⟨1⟩ hd7 (by evm_ov),
    raw push1 bits hd9 (by evm_ov),
    raw shl hd11 (by evm_ov),
    raw sub hd12 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw swap3 hd14 (by evm_ov),
    raw and hd15 (by evm_ov),
    raw dup3 hd16 (by evm_ov),
    raw mstore 6 memout (UInt256.ofNat 5) hd17 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd18 mem_cost hmemoutLoad64 (by decide)
      (by evm_ov),
    raw swap1 hd19 (by evm_ov),
    raw dup2 hd20 (by evm_ov),
    raw swap1 hd21 (by evm_ov),
    raw sub hd22 (by evm_ov),
    raw push1 ⟨32⟩ hd23 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw swap1 hd26 (by evm_ov),
    raw ret 0 (UInt256.toByteArray (UInt256.land val
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩))) hd27 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov)]

theorem clipperPackedUintOffsetGetterExternal {code : ByteArray} {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel entry routine slot returnPc shiftBits bits : UInt256} {bitNat : Nat}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : clipperPackedUintOffsetSlotGetterWf code routine slot shiftBits bits)
    (hmask :
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩).toNat =
        2 ^ bitNat - 1)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : clipperReturnComputedMaskFromMemWf code returnPc bits) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land
        (UInt256.div (solcSlotWord σ I slot)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) shiftBits))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩))) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := clipperPackedUintOffsetSlotGetter
    (slot := slot) (shiftBits := shiftBits) (bits := bits) (R := [sel])
    rdRoutine hgetter hret (by simp only [List.length_singleton]; omega)
  have hrd := clipperReturnComputedMaskFromMem (bits := bits) rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (UInt256.land
      (UInt256.land
        (UInt256.div (solcSlotWord σ I slot)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) shiftBits))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩))
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩)))
    (solcReturnMem_read128 (UInt256.land
      (UInt256.land
        (UInt256.div (solcSlotWord σ I slot)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) shiftBits))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩))
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩)))
    (by simp only [List.length_singleton]; omega)
  have hclean :
      UInt256.land
          (UInt256.land
            (UInt256.div (solcSlotWord σ I slot)
              (UInt256.shiftLeft (⟨1⟩ : UInt256) shiftBits))
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩) =
        UInt256.land
          (UInt256.div (solcSlotWord σ I slot)
            (UInt256.shiftLeft (⟨1⟩ : UInt256) shiftBits))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩) :=
    u256LandMaskCleanOfToNat
      (UInt256.land
        (UInt256.div (solcSlotWord σ I slot)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) shiftBits))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩))
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩) hmask
      (u256LandMaskToNatLtOfToNat
        (UInt256.div (solcSlotWord σ I slot)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) shiftBits))
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) bits) ⟨1⟩) hmask)
  simpa [hclean] using hrd

-- GENERALIZES Benchmarks.Dss.Dai.Storage.daiZeroSlotSingleMappingGetterWf and
-- Reasoning.Solc.solcSingleMappingGetterWf: zero-base mapping getters can emit
-- `PUSH1 0; PUSH1 32; DUP2; SWAP1; MSTORE` instead of the ordinary base-slot store.
@[reducible] def solcZeroSlotSingleMappingGetterWf (code : ByteArray) (pc : UInt256) :
    Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p5 = some (.DUP2, .none)
  ∧ decode code p6 = some (.SWAP1, .none)
  ∧ decode code p7 = some (.MSTORE, .none)
  ∧ decode code p8 = some (.SWAP1, .none)
  ∧ decode code p9 = some (.DUP2, .none)
  ∧ decode code p10 = some (.MSTORE, .none)
  ∧ decode code p11 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.KECCAK256, .none)
  ∧ decode code p15 = some (.SLOAD, .none)
  ∧ decode code p16 = some (.DUP2, .none)
  ∧ decode code p17 = some (.JUMP, .none)

-- GENERALIZES Benchmarks.Dss.Dai.Storage.RD.daiZeroSlotSingleMappingGetter and
-- Reasoning.Solc.RD.solcSingleMappingGetter: the variant above computes slot
-- `keccak(key, 0)`, loads it, and jumps back to the caller.
set_option maxHeartbeats 1000000 in
theorem solcZeroSlotSingleMappingGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcZeroSlotSingleMappingGetterWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot ⟨0⟩ key) :: ret :: R)
      (solcMappingHashMem ⟨0⟩ key) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd13, hd14, hd15,
      hd16, hd17⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨0⟩ hd1 (by evm_ov)
  have rd5 := rd3.push1 ⟨32⟩ hd3 (by evm_ov)
  have rd6 := rd5.dup2 hd5 (by simp only [List.length_cons]; omega)
  have rd7 := rd6.swap1 hd6 (by simp only [List.length_cons]; omega)
  have rd8 := rd7.mstore 0 (solcMappingBaseSlotMem ⟨0⟩)
    (UInt256.ofNat 3) hd7 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd9 := rd8.swap1 hd8 (by evm_ov)
  have rd10 := rd9.dup2 hd9 (by evm_ov)
  have rd11 := rd10.mstore 0 (solcMappingHashMem ⟨0⟩ key)
    (UInt256.ofNat 3) hd10 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd13 := rd11.push1 ⟨64⟩ hd11 (by evm_ov)
  have rd14 := rd13.swap1 hd13 (by evm_ov)
  have hslot := solcMappingKeccakSlot ⟨0⟩ key
  have rd15 := rd14.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) hd14 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  obtain ⟨k16, C16, rd16⟩ := rd15.sload hd15 (by evm_ov)
  have rd17 := rd16.dup2 hd16 (by evm_ov)
  have rd18 := rd17.jump hd17 hret (by evm_ov)
  exact ⟨k16 + 1 + 1, C16 + 3 + 8, by simpa [solcSlotWord] using rd18⟩

-- GENERALIZES Benchmarks.Dss.Dai.Storage.daiOneAddressExternalEntryWf: a reusable
-- one-address ABI entry wrapper whose decoded block immediately masks and jumps.
@[reducible] def solcOneAddressExternalDecodedPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p17 := p14 + UInt256.ofNat 3
  let p18 := p17 + ⟨1⟩
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  p21 + ⟨1⟩

@[reducible] def solcOneAddressExternalEntryWf
    (code : ByteArray) (pc ret routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p17 := p14 + UInt256.ofNat 3
  let p18 := p17 + ⟨1⟩
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  let p22 := solcOneAddressExternalDecodedPc pc
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p27 := p25 + UInt256.ofNat 2
  let p29 := p27 + UInt256.ofNat 2
  let p31 := p29 + UInt256.ofNat 2
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p37 := p34 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH2, some (ret, 2))
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p6 = some (.DUP1, .none)
  ∧ decode code p7 = some (.CALLDATASIZE, .none)
  ∧ decode code p8 = some (.SUB, .none)
  ∧ decode code p9 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p11 = some (.DUP2, .none)
  ∧ decode code p12 = some (.LT, .none)
  ∧ decode code p13 = some (.ISZERO, .none)
  ∧ decode code p14 = some (.Push .PUSH2, some (p22, 2))
  ∧ decode code p17 = some (.JUMPI, .none)
  ∧ decode code p18 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p20 = some (.DUP1, .none)
  ∧ decode code p21 = some (.REVERT, .none)
  ∧ decode code p22 = some (.JUMPDEST, .none)
  ∧ decode code p23 = some (.POP, .none)
  ∧ decode code p24 = some (.CALLDATALOAD, .none)
  ∧ decode code p25 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p27 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p29 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p31 = some (.SHL, .none)
  ∧ decode code p32 = some (.SUB, .none)
  ∧ decode code p33 = some (.AND, .none)
  ∧ decode code p34 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p37 = some (.JUMP, .none)

-- GENERALIZES Benchmarks.Dss.Dai.Storage.RD.daiOneAddressExternalLenOk.
set_option maxHeartbeats 1000000 in
theorem solcOneAddressExternalLenOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {code : ByteArray} {entry ret routine : UInt256}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : solcOneAddressExternalEntryWf code entry ret routine)
    (hdecoded : (D_J code 0).contains (solcOneAddressExternalDecodedPc entry) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      (solcOneAddressExternalDecodedPc entry)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, _hd22, _hd23, _hd24, _hd25, _hd27, _hd29, _hd31, _hd32,
      _hd33, _hd34, _hd37⟩
  exact RD.solcOneAddressExternalLenOk hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9 hd11
    hd12 hd13 hd14 hd17 hdecoded hsz36 hsize

-- GENERALIZES Benchmarks.Dss.Dai.Storage.RD.daiOneAddressExternalMaskAndJumpMasked.
set_option maxHeartbeats 1000000 in
theorem solcOneAddressExternalMaskAndJumpMasked {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {entry ret routine de : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (solcOneAddressExternalDecodedPc entry)
      (de :: ⟨4⟩ :: ret :: R) solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcOneAddressExternalEntryWf code entry ret routine)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine
      (UInt256.land solcAddrMask (calldataWord ee.calldata 4) :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd25, hd27, hd29, hd31,
      hd32, hd33, hd34, hd37⟩
  exact RD.solcOneAddressExternalMaskAndJumpMasked h hd22 hd23 hd24 hd25 hd27 hd29
    hd31 hd32 hd33 hd34 hd37 hroutine hov

-- GENERALIZES Benchmarks.Dss.Dai.Storage.RD.daiOneAddressExternalShort.
set_option maxHeartbeats 1000000 in
theorem solcOneAddressExternalShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel entry ret routine : UInt256} {code : ByteArray}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : solcOneAddressExternalEntryWf code entry ret routine)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd25, _hd27, _hd29, _hd31, _hd32,
      _hd33, _hd34, _hd37⟩
  exact RD.solcExternalStaticArgsShortReverts hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9
    hd11 hd12 hd13 hd14 hd17 hd18 hd20 hd21 hlt

-- LIBRARY CANDIDATE: constant getter returning via solc's address ABI return block.
theorem solcAddressConstGetterExternal {code : ByteArray} {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel entry routine returnPc val : UInt256} {width : Nat}
    {op : Operation.POp}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcConstGetterWf code routine val width op)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturn : solcReturnAddressFromMemWf code returnPc) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land val solcAddrMask)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ := RD.solcConstGetter (val := val) (width := width)
    (op := op) (R := [sel]) rdRoutine hgetter hret
    (by simp only [List.length_singleton]; omega)
  exact RD.solcReturnAddressFromMem rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 (UInt256.land val solcAddrMask))
    (solcReturnMem_read128 (UInt256.land val solcAddrMask))
    (by simp only [List.length_singleton]; omega)

theorem clipperUint256GetterBodyCore (v : ClipperImmutables) {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot returnPc : UInt256}
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcWordSlotGetterWf code routine slot)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturnWf : solcReturnWordFromMemWf code returnPc)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (solcSlotWord σ_solm I slot).toNat))]))) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : solcSlotWord σ_evm I slot = solcSlotWord σ_solm I slot :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (solcSlotWord σ_solm I slot).toNat)] =
        some [Value.int (Int.ofNat (solcSlotWord σ_evm I slot).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (solcSlotWord σ_evm I slot))
        (some [(.int (Int.ofNat (solcSlotWord σ_evm I slot).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (solcSlotWord σ_evm I slot))
  have hrd := RD.solcWordGetterExternal (code := code) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hret hreturnWf
  exact hrd.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem clipperAddressGetterBodyCore (v : ClipperImmutables) {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot returnPc : UInt256}
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcAddressSlotGetterWf code routine slot)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturnWf : solcReturnAddressFromMemWf code returnPc)
    (hreturn : transition.returnType = [addr])
    (hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (UInt256.land (solcSlotWord σ_solm I slot) solcAddrMask).toNat))]))) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : solcSlotWord σ_evm I slot = solcSlotWord σ_solm I slot :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.address (AccountAddress.ofNat
          (UInt256.land (solcSlotWord σ_solm I slot) solcAddrMask).toNat)] =
        some [Value.address (AccountAddress.ofNat
          (UInt256.land (solcSlotWord σ_evm I slot) solcAddrMask).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray
          (UInt256.land (solcSlotWord σ_evm I slot) solcAddrMask))
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (solcSlotWord σ_evm I slot) solcAddrMask).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [addr] using solcAddressReturnEncoding rfl (solcSlotWord σ_evm I slot))
  have hrd := RD.solcAddressGetterExternal (code := code) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hret hreturnWf
  exact hrd.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem clipperAddressConstGetterBodyCore (v : ClipperImmutables) {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine returnPc val : UInt256} {width : Nat}
    {op : Operation.POp}
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcConstGetterWf code routine val width op)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturnWf : solcReturnAddressFromMemWf code returnPc)
    (hreturn : transition.returnType = [addr])
    (hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat val.toNat))]))) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have henc :
      returnEquiv (UInt256.toByteArray (UInt256.land val solcAddrMask))
        (some [(.address (AccountAddress.ofNat val.toNat))]) transition.returnType := by
    rw [hreturn]
    have hmasked :
        Value.address (AccountAddress.ofNat val.toNat) =
          .address (AccountAddress.ofNat (UInt256.land val solcAddrMask).toNat) := by
      rw [solcAddressValue_masked val]
      rw [u256_land_comm solcAddrMask val]
    exact returnEquiv_of_encode
      (by simpa [addr, hmasked] using solcAddressReturnEncoding rfl val)
  have hrd := solcAddressConstGetterExternal (code := code) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (val := val)
    (width := width) (op := op) hreach hentry hgetter hroutine hret hreturnWf
  exact hrd.reEquivExecutionTransport hcode hdispatch hdecode hbody rfl hAccounts henc

theorem clipperBytes32ConstGetterBodyCore (v : ClipperImmutables) {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine returnPc val : UInt256} {width : Nat}
    {op : Operation.POp}
    (hcode : I.code = code)
    (hdispatch : dispatchMsg (contract v) I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : solcConstGetterWf code routine val width op)
    (hroutine : (D_J code 0).contains routine = true)
    (hret : (D_J code 0).contains returnPc = true)
    (hreturnWf : solcReturnWordFromMemWf code returnPc)
    (hreturn : transition.returnType = [bytes32])
    (hbody :
      ExecTransitionBody (config v) (contract v)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract v, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE val))]))) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have henc :
      returnEquiv (UInt256.toByteArray val)
        (some [(.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE val))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [bytes32] using bytes32ReturnEncoding val)
  have hrd := RD.solcWordConstGetterExternal (code := code) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (val := val)
    (width := width) (op := op) hreach hentry hgetter hroutine hret hreturnWf
  exact hrd.reEquivExecutionTransport hcode hdispatch hdecode hbody rfl hAccounts henc

end Benchmarks.Dss.Clipper
