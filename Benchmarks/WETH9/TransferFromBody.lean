import Benchmarks.WETH9.Storage

/-!
# WETH9 shared internal `transferFrom` body EVM trace (pc 1087 → return jump)

Both public `transferFrom(src,dst,wad)` (dispatched at pc 420) and public `transfer(dst,wad)`
(dispatched at pc 644, which pushes `msg.sender` for `src`) converge on the shared internal body at
pc 1087.  This file proves that body once, generic over the abstract `src`/`dst`/`wad` stack words,
the return address `ret`, and the stack tail `S`, in the three branch cases (`src == caller`;
`src ≠ caller ∧ allowance == uint(-1)`; `src ≠ caller ∧ allowance ≠ uint(-1)`) plus the two require
reverts (`balanceOf[src] < wad`; inner `allowance < wad`).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.WETH9

/-- `balanceOf[s]` storage slot in the EVM (keccak(s ‖ 3)). -/
abbrev wtfBalSlot (s : UInt256) : UInt256 := solcMappingSlot ⟨3⟩ s

/-- `allowance[owner][caller]` storage slot in the EVM (keccak(caller ‖ keccak(owner ‖ 4))). -/
abbrev wtfAllowSlot (ee : ExecutionEnv) (owner : UInt256) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨4⟩ owner) (solcSourceWord ee)

/-- The scratch memory after building the `balanceOf[src]` key (`src ‖ 3` at `0x00`). -/
noncomputable abbrev wtfBalHashMem (s : UInt256) : ByteArray := twoWordHashMem s ⟨3⟩ solcFreePtrMem

/-- Mask literal helper: `src ∧ ((1<<160)-1) = src` for a canonical (address-sized) `src`. -/
private theorem wtf_maskLiteral {src : UInt256} (hsrc : src.toNat < EVM.addressModulus) :
    UInt256.land src (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) = src := by
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask from by decide]
  exact solcAddrMask_clean hsrc

/-- The `balanceOf[src] ≥ wad` require prologue (pc 1087 → 1124): mask src, hash `keccak(src‖3)`,
    `SLOAD`, `GT wad; ISZERO; JUMPI` past the revert. -/
theorem weth9TFReqBalanceOk {ee g s0 rdata cA σ k C} {src dst wad ret : UInt256} {S : List UInt256}
    (h : RD weth9Bytecode ee g s0 ⟨1087⟩ (wad :: dst :: src :: ret :: S)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hsrc : src.toNat < EVM.addressModulus)
    (henough : wad.toNat ≤ (solcSlotWord σ ee (wtfBalSlot src)).toNat)
    (hov : S.length + 8 ≤ 1024) :
    ∃ k' C', RD weth9Bytecode ee g s0 ⟨1124⟩ (⟨0⟩ :: wad :: dst :: src :: ret :: S)
      (wtfBalHashMem src) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have hmaskLiteral : UInt256.land src (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
      = src := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask from by decide]
    exact solcAddrMask_clean hsrc
  have hkecval : UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((wtfBalHashMem src).readWithPadding 0 64))) = wtfBalSlot src :=
    twoWordHashMem_solcMappingSlot ⟨3⟩ src solcFreePtrMem_size
  have rdMasked := h.jumpdest (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨1⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨1⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨160⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.shl (by decide +native) (by simp only [List.length_cons]; omega)
    |>.sub (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup4 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.and (by decide +native) (by simp only [List.length_cons]; omega)
  rw [hmaskLiteral] at rdMasked
  have rdKey := rdMasked.push1 ⟨0⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.swap1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup2 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.mstore 0 (wordAt0Mem src solcFreePtrMem) (UInt256.ofNat 3) (by decide +native) mem_cost
        (by rfl) (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨3⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨32⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.mstore 0 (wtfBalHashMem src) (UInt256.ofNat 3) (by decide +native) mem_cost
        (by rw [show (⟨32⟩ : UInt256).toNat = 32 from rfl]; rfl)
        (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨64⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup2 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.keccak256 0 (wtfBalSlot src) (UInt256.ofNat 3) (by decide +native) mem_cost hkecval
        (by decide +native) (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdLoaded⟩ := rdKey.sload (by decide +native) (by simp only [List.length_cons]; omega)
  have rdChecked := rdLoaded.dup3 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.gt (by decide +native) (by simp only [List.length_cons]; omega)
    |>.iszero (by decide +native) (by simp only [List.length_cons]; omega)
    |>.pushConst (⟨1124⟩ : UInt256) (op := .PUSH2) (width := 2) (by decide) (by decide +native)
        (by simp only [List.length_cons]; omega)
  refine ⟨_, _, rdChecked.jumpiT (by decide +native) ?_ (by jump_dest)
    (by simp only [List.length_cons]; omega)⟩
  rw [ugt_zero henough]; decide

/-- The `balanceOf[src] ≥ wad` require, revert case (pc 1087 → `PUSH1 0; DUP1; REVERT`). -/
theorem weth9TFReqBalanceRev {ee g s0 rdata cA σ k C} {src dst wad ret : UInt256} {S : List UInt256}
    (h : RD weth9Bytecode ee g s0 ⟨1087⟩ (wad :: dst :: src :: ret :: S)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hsrc : src.toNat < EVM.addressModulus)
    (hlt : (solcSlotWord σ ee (wtfBalSlot src)).toNat < wad.toNat)
    (hov : S.length + 8 ≤ 1024) :
    RDrev weth9Bytecode g s0 := by
  have hkecval : UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((wtfBalHashMem src).readWithPadding 0 64))) = wtfBalSlot src :=
    twoWordHashMem_solcMappingSlot ⟨3⟩ src solcFreePtrMem_size
  have rdMasked := h.jumpdest (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨1⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨1⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨160⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.shl (by decide +native) (by simp only [List.length_cons]; omega)
    |>.sub (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup4 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.and (by decide +native) (by simp only [List.length_cons]; omega)
  rw [wtf_maskLiteral hsrc] at rdMasked
  have rdKey := rdMasked.push1 ⟨0⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.swap1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup2 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.mstore 0 (wordAt0Mem src solcFreePtrMem) (UInt256.ofNat 3) (by decide +native) mem_cost
        (by rfl) (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨3⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨32⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.mstore 0 (wtfBalHashMem src) (UInt256.ofNat 3) (by decide +native) mem_cost
        (by rw [show (⟨32⟩ : UInt256).toNat = 32 from rfl]; rfl)
        (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨64⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup2 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.keccak256 0 (wtfBalSlot src) (UInt256.ofNat 3) (by decide +native) mem_cost hkecval
        (by decide +native) (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rdLoaded⟩ := rdKey.sload (by decide +native) (by simp only [List.length_cons]; omega)
  exact rdLoaded.dup3 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.gt (by decide +native) (by simp only [List.length_cons]; omega)
    |>.iszero (by decide +native) (by simp only [List.length_cons]; omega)
    |>.pushConst (⟨1124⟩ : UInt256) (op := .PUSH2) (width := 2) (by decide) (by decide +native)
        (by simp only [List.length_cons]; omega)
    |>.jumpiNT (by decide +native) (by rw [ugt_one hlt]; decide) (by simp only [List.length_cons]; omega)
    |>.solcPush1Dup1Revert0 (by decide +native) (by decide +native) (by decide +native)
        (by simp only [List.length_cons]; omega)

/-- Branch, case `src == msg.sender` (pc 1124 → 1282): the `EQ msg.sender` short-circuits the
    `&&`, skipping the allowance spend (no store). -/
theorem weth9TFBranchSkipSender {ee g s0 rdata cA σ k C} {src dst wad ret : UInt256}
    {S : List UInt256}
    (h : RD weth9Bytecode ee g s0 ⟨1124⟩ (⟨0⟩ :: wad :: dst :: src :: ret :: S)
      (wtfBalHashMem src) (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hsrc : src.toNat < EVM.addressModulus)
    (heq : src = solcSourceWord ee)
    (hov : S.length + 8 ≤ 1024) :
    ∃ k' C', RD weth9Bytecode ee g s0 ⟨1282⟩ (⟨0⟩ :: wad :: dst :: src :: ret :: S)
      (wtfBalHashMem src) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have rdMasked := h.jumpdest (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨1⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨1⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨160⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.shl (by decide +native) (by simp only [List.length_cons]; omega)
    |>.sub (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup5 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.and (by decide +native) (by simp only [List.length_cons]; omega)
  rw [wtf_maskLiteral hsrc] at rdMasked
  have rdEq := rdMasked.caller (by decide +native) (by simp only [List.length_cons]; omega)
    |>.eq (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.iszero (by decide +native) (by simp only [List.length_cons]; omega)
    |>.swap1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.pushConst (⟨1186⟩ : UInt256) (op := .PUSH2) (width := 2) (by decide) (by decide +native)
        (by simp only [List.length_cons]; omega)
  have rdJoin := rdEq.jumpiT (by decide +native)
      (by rw [heq, u256_eq_refl]; decide) (by jump_dest) (by simp only [List.length_cons]; omega)
    |>.jumpdest (by decide +native) (by simp only [List.length_cons]; omega)
    |>.iszero (by decide +native) (by simp only [List.length_cons]; omega)
    |>.pushConst (⟨1282⟩ : UInt256) (op := .PUSH2) (width := 2) (by decide) (by decide +native)
        (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rdJoin.jumpiT (by decide +native)
    (by rw [heq, u256_eq_refl]; decide) (by jump_dest) (by simp only [List.length_cons]; omega)⟩

/-- The allowance scratch memory (nested `keccak(caller ‖ keccak(src ‖ 4))`). -/
noncomputable abbrev wtfAllowHashMem (ee : ExecutionEnv) (src : UInt256) : ByteArray :=
  solcNestedMappingCallerHashMem ⟨4⟩ src ee (wtfBalHashMem src)

/-- Branch, case `src ≠ msg.sender` (pc 1124 → 1186): fall through the `EQ`, `POP`, then load
    `allowance[src][msg.sender]` (nested keccak) and push `allowance ≠ uint(-1)` onto the stack at
    the join `JUMPDEST` (pc 1186). -/
theorem weth9TFAllowLoaded {ee g s0 rdata cA σ k C} {src dst wad ret : UInt256} {S : List UInt256}
    (h : RD weth9Bytecode ee g s0 ⟨1124⟩ (⟨0⟩ :: wad :: dst :: src :: ret :: S)
      (wtfBalHashMem src) (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hsrc : src.toNat < EVM.addressModulus)
    (hne : solcSourceWord ee ≠ src)
    (hov : S.length + 16 ≤ 1024) :
    ∃ k' C', RD weth9Bytecode ee g s0 ⟨1186⟩
      (UInt256.isZero (UInt256.eq (UInt256.lnot ⟨0⟩)
          (solcSlotWord σ ee (wtfAllowSlot ee src))) :: ⟨0⟩ :: wad :: dst :: src :: ret :: S)
      (wtfAllowHashMem ee src) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have hmem : (wtfBalHashMem src).size = 96 := twoWordHashMem_size_96 src ⟨3⟩ solcFreePtrMem_size
  have hinnerSize : (twoWordHashMem src ⟨4⟩ (wtfBalHashMem src)).size = 96 :=
    twoWordHashMem_size_96 src ⟨4⟩ hmem
  have hinner : UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((twoWordHashMem src ⟨4⟩ (wtfBalHashMem src)).readWithPadding 0 64)))
        = solcMappingSlot ⟨4⟩ src :=
    twoWordHashMem_solcMappingSlot ⟨4⟩ src hmem
  have houter : UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((wtfAllowHashMem ee src).readWithPadding 0 64))) = wtfAllowSlot ee src := by
    unfold wtfAllowHashMem solcNestedMappingCallerHashMem
    exact twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨4⟩ src) (solcSourceWord ee) hinnerSize
  -- pc 1124 → 1144: `src == caller` test fails, pop the flag
  have rd1144 := h.jumpdest (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨1⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨1⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨160⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.shl (by decide +native) (by simp only [List.length_cons]; omega)
    |>.sub (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup5 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.and (by decide +native) (by simp only [List.length_cons]; omega)
  rw [wtf_maskLiteral hsrc] at rd1144
  have rd1144b := rd1144.caller (by decide +native) (by simp only [List.length_cons]; omega)
    |>.eq (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.iszero (by decide +native) (by simp only [List.length_cons]; omega)
    |>.swap1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.pushConst (⟨1186⟩ : UInt256) (op := .PUSH2) (width := 2) (by decide) (by decide +native)
        (by simp only [List.length_cons]; omega)
    |>.jumpiNT (by decide +native) (u256_eq_of_ne hne) (by simp only [List.length_cons]; omega)
    |>.pop (by decide +native) (by simp only [List.length_cons]; omega)
  -- pc 1145 → 1171: build inner key `keccak(src ‖ 4)`
  have rd1171 := rd1144b.push1 ⟨1⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨1⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨160⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.shl (by decide +native) (by simp only [List.length_cons]; omega)
    |>.sub (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup5 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.and (by decide +native) (by simp only [List.length_cons]; omega)
  rw [wtf_maskLiteral hsrc] at rd1171
  have rd1171b := rd1171.push1 ⟨0⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.swap1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup2 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.mstore 0 (wordAt0Mem src (wtfBalHashMem src)) (UInt256.ofNat 3) (by decide +native) mem_cost
        (by rfl) (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨4⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨32⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.swap1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup2 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.mstore 0 (twoWordHashMem src ⟨4⟩ (wtfBalHashMem src)) (UInt256.ofNat 3) (by decide +native)
        mem_cost (by rw [show (⟨32⟩ : UInt256).toNat = 32 from rfl]; rfl) (by decide +native)
        (by simp only [List.length_cons]; omega)
    |>.push1 ⟨64⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup4 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.keccak256 0 (solcMappingSlot ⟨4⟩ src) (UInt256.ofNat 3) (by decide +native) mem_cost hinner
        (by decide +native) (by simp only [List.length_cons]; omega)
  -- pc 1172 → 1180: build outer key `keccak(caller ‖ innerSlot)`, SLOAD
  have rd1180 := rd1171b.caller (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup5 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.mstore 0 (wordAt0Mem (solcSourceWord ee) (twoWordHashMem src ⟨4⟩ (wtfBalHashMem src)))
        (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native)
        (by simp only [List.length_cons]; omega)
    |>.swap1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.swap2 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.mstore 0 (wtfAllowHashMem ee src) (UInt256.ofNat 3) (by decide +native) mem_cost
        (by rw [show (⟨32⟩ : UInt256).toNat = 32 from rfl]
            unfold wtfAllowHashMem solcNestedMappingCallerHashMem twoWordHashMem wordAt32Mem
            rfl)
        (by decide +native) (by simp only [List.length_cons]; omega)
    |>.swap1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.keccak256 0 (wtfAllowSlot ee src) (UInt256.ofNat 3) (by decide +native) mem_cost houter
        (by decide +native) (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd1180b⟩ := rd1180.sload (by decide +native) (by simp only [List.length_cons]; omega)
  -- pc 1181 → 1186: compute `allowance ≠ uint(-1)`, reach the join JUMPDEST
  exact ⟨_, _, rd1180b.push1 ⟨0⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.not (by decide +native) (by simp only [List.length_cons]; omega)
    |>.eq (by decide +native) (by simp only [List.length_cons]; omega)
    |>.iszero (by decide +native) (by simp only [List.length_cons]; omega)⟩

theorem wtfBalHashMem_read64 (s : UInt256) :
    (wtfBalHashMem s).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 s ⟨3⟩ solcFreePtrMem_size solcFreePtrMem_read64

theorem wtfAllowHashMem_size (ee : ExecutionEnv) (src : UInt256) :
    (wtfAllowHashMem ee src).size = 96 := by
  unfold wtfAllowHashMem solcNestedMappingCallerHashMem
  exact twoWordHashMem_size_96 _ _
    (twoWordHashMem_size_96 src ⟨4⟩ (twoWordHashMem_size_96 src ⟨3⟩ solcFreePtrMem_size))

theorem wtfAllowHashMem_read64 (ee : ExecutionEnv) (src : UInt256) :
    (wtfAllowHashMem ee src).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold wtfAllowHashMem solcNestedMappingCallerHashMem
  exact twoWordHashMem_read64 _ _
    (twoWordHashMem_size_96 src ⟨4⟩ (twoWordHashMem_size_96 src ⟨3⟩ solcFreePtrMem_size))
    (twoWordHashMem_read64 src ⟨4⟩ (twoWordHashMem_size_96 src ⟨3⟩ solcFreePtrMem_size)
      (wtfBalHashMem_read64 src))

theorem wtf_lnot0_toNat : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
  unfold UInt256.lnot; decide

/-- Branch join, case `allowance == uint(-1)` (pc 1186 → 1282): the `&&` is false, skip the spend. -/
theorem weth9TFBranchSkipMax {ee g s0 rdata cA σ k C} {src dst wad ret : UInt256}
    {S : List UInt256} {mem : ByteArray}
    (h : RD weth9Bytecode ee g s0 ⟨1186⟩
      (UInt256.isZero (UInt256.eq (UInt256.lnot ⟨0⟩)
          (solcSlotWord σ ee (wtfAllowSlot ee src))) :: ⟨0⟩ :: wad :: dst :: src :: ret :: S)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmax : (solcSlotWord σ ee (wtfAllowSlot ee src)).toNat = UInt256.size - 1)
    (hov : S.length + 8 ≤ 1024) :
    ∃ k' C', RD weth9Bytecode ee g s0 ⟨1282⟩ (⟨0⟩ :: wad :: dst :: src :: ret :: S)
      mem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have hallow : solcSlotWord σ ee (wtfAllowSlot ee src) = UInt256.lnot ⟨0⟩ :=
    u256_inj (by rw [hmax, wtf_lnot0_toNat])
  exact ⟨_, _, h.jumpdest (by decide +native) (by simp only [List.length_cons]; omega)
    |>.iszero (by decide +native) (by simp only [List.length_cons]; omega)
    |>.pushConst (⟨1282⟩ : UInt256) (op := .PUSH2) (width := 2) (by decide) (by decide +native)
        (by simp only [List.length_cons]; omega)
    |>.jumpiT (by decide +native) (by rw [hallow, u256_eq_refl]; decide) (by jump_dest)
        (by simp only [List.length_cons]; omega)⟩

/-- Rebuild the nested `allowance[src][caller]` keccak slot from `[0, wad, dst, src, ret, S]` with a
    size-96 scratch memory `mem`, `SLOAD`ing the current allowance.  Shared by the `require` check
    (pc 1192) and the decrement (pc 1239) — this variant is the `require` entry (pc 1192 → 1228). -/
theorem weth9TFRequireAllowance {ee g s0 rdata cA σ k C} {src dst wad ret : UInt256}
    {S : List UInt256} {mem : ByteArray}
    (h : RD weth9Bytecode ee g s0 ⟨1192⟩ (⟨0⟩ :: wad :: dst :: src :: ret :: S)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hsrc : src.toNat < EVM.addressModulus) (hmemsize : mem.size = 96)
    (hov : S.length + 16 ≤ 1024) :
    ∃ k' C', RD weth9Bytecode ee g s0 ⟨1228⟩
      (solcSlotWord σ ee (wtfAllowSlot ee src) :: ⟨0⟩ :: wad :: dst :: src :: ret :: S)
      (solcNestedMappingCallerHashMem ⟨4⟩ src ee mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have hinner : UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((twoWordHashMem src ⟨4⟩ mem).readWithPadding 0 64))) = solcMappingSlot ⟨4⟩ src :=
    twoWordHashMem_solcMappingSlot ⟨4⟩ src hmemsize
  have houter : UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((solcNestedMappingCallerHashMem ⟨4⟩ src ee mem).readWithPadding 0 64)))
        = wtfAllowSlot ee src := by
    unfold solcNestedMappingCallerHashMem
    exact twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨4⟩ src) (solcSourceWord ee)
      (twoWordHashMem_size_96 src ⟨4⟩ hmemsize)
  have rd := h.push1 ⟨1⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨1⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨160⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.shl (by decide +native) (by simp only [List.length_cons]; omega)
    |>.sub (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup5 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.and (by decide +native) (by simp only [List.length_cons]; omega)
  rw [wtf_maskLiteral hsrc] at rd
  have rd2 := rd.push1 ⟨0⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.swap1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup2 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.mstore 0 (wordAt0Mem src mem) (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl)
        (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨4⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨32⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.swap1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup2 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.mstore 0 (twoWordHashMem src ⟨4⟩ mem) (UInt256.ofNat 3) (by decide +native) mem_cost
        (by rw [show (⟨32⟩ : UInt256).toNat = 32 from rfl]; rfl) (by decide +native)
        (by simp only [List.length_cons]; omega)
    |>.push1 ⟨64⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup4 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.keccak256 0 (solcMappingSlot ⟨4⟩ src) (UInt256.ofNat 3) (by decide +native) mem_cost hinner
        (by decide +native) (by simp only [List.length_cons]; omega)
  have rd3 := rd2.caller (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup5 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.mstore 0 (wordAt0Mem (solcSourceWord ee) (twoWordHashMem src ⟨4⟩ mem)) (UInt256.ofNat 3)
        (by decide +native) mem_cost (by rfl) (by decide +native)
        (by simp only [List.length_cons]; omega)
    |>.swap1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.swap2 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.mstore 0 (solcNestedMappingCallerHashMem ⟨4⟩ src ee mem) (UInt256.ofNat 3) (by decide +native)
        mem_cost
        (by rw [show (⟨32⟩ : UInt256).toNat = 32 from rfl]
            unfold solcNestedMappingCallerHashMem twoWordHashMem wordAt32Mem
            rfl)
        (by decide +native) (by simp only [List.length_cons]; omega)
    |>.swap1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.keccak256 0 (wtfAllowSlot ee src) (UInt256.ofNat 3) (by decide +native) mem_cost houter
        (by decide +native) (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload (by decide +native) (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd4⟩

/-- Decrement `allowance[src][caller] -= wad` (pc 1239 → 1282): rebuild the slot, `SLOAD`, `SUB`,
    `SSTORE`. -/
theorem weth9TFDecrementAllowance {ee g s0 rdata cA σ k C} {src dst wad ret : UInt256}
    {S : List UInt256} {mem : ByteArray}
    (h : RD weth9Bytecode ee g s0 ⟨1239⟩ (⟨0⟩ :: wad :: dst :: src :: ret :: S)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true) (hsrc : src.toNat < EVM.addressModulus) (hmemsize : mem.size = 96)
    (hov : S.length + 16 ≤ 1024) :
    ∃ k' C', RD weth9Bytecode ee g s0 ⟨1282⟩ (⟨0⟩ :: wad :: dst :: src :: ret :: S)
      (solcNestedMappingCallerHashMem ⟨4⟩ src ee mem) (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (wtfAllowSlot ee src)
        (UInt256.sub (solcSlotWord σ ee (wtfAllowSlot ee src)) wad)) k' C' := by
  have hinner : UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((twoWordHashMem src ⟨4⟩ mem).readWithPadding 0 64))) = solcMappingSlot ⟨4⟩ src :=
    twoWordHashMem_solcMappingSlot ⟨4⟩ src hmemsize
  have houter : UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((solcNestedMappingCallerHashMem ⟨4⟩ src ee mem).readWithPadding 0 64)))
        = wtfAllowSlot ee src := by
    unfold solcNestedMappingCallerHashMem
    exact twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨4⟩ src) (solcSourceWord ee)
      (twoWordHashMem_size_96 src ⟨4⟩ hmemsize)
  have rd := h.jumpdest (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨1⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨1⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨160⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.shl (by decide +native) (by simp only [List.length_cons]; omega)
    |>.sub (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup5 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.and (by decide +native) (by simp only [List.length_cons]; omega)
  rw [wtf_maskLiteral hsrc] at rd
  have rd2 := rd.push1 ⟨0⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.swap1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup2 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.mstore 0 (wordAt0Mem src mem) (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl)
        (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨4⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.push1 ⟨32⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.swap1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup2 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.mstore 0 (twoWordHashMem src ⟨4⟩ mem) (UInt256.ofNat 3) (by decide +native) mem_cost
        (by rw [show (⟨32⟩ : UInt256).toNat = 32 from rfl]; rfl) (by decide +native)
        (by simp only [List.length_cons]; omega)
    |>.push1 ⟨64⟩ (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup4 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.keccak256 0 (solcMappingSlot ⟨4⟩ src) (UInt256.ofNat 3) (by decide +native) mem_cost hinner
        (by decide +native) (by simp only [List.length_cons]; omega)
  have rd3 := rd2.caller (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup5 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.mstore 0 (wordAt0Mem (solcSourceWord ee) (twoWordHashMem src ⟨4⟩ mem)) (UInt256.ofNat 3)
        (by decide +native) mem_cost (by rfl) (by decide +native)
        (by simp only [List.length_cons]; omega)
    |>.swap1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.swap2 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.mstore 0 (solcNestedMappingCallerHashMem ⟨4⟩ src ee mem) (UInt256.ofNat 3) (by decide +native)
        mem_cost
        (by rw [show (⟨32⟩ : UInt256).toNat = 32 from rfl]
            unfold solcNestedMappingCallerHashMem twoWordHashMem wordAt32Mem
            rfl)
        (by decide +native) (by simp only [List.length_cons]; omega)
    |>.swap1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.keccak256 0 (wtfAllowSlot ee src) (UInt256.ofNat 3) (by decide +native) mem_cost houter
        (by decide +native) (by simp only [List.length_cons]; omega)
    |>.dup1 (by decide +native) (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload (by decide +native) (by simp only [List.length_cons]; omega)
  have rd5 := rd4.dup4 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.swap1 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.sub (by decide +native) (by simp only [List.length_cons]; omega)
    |>.swap1 (by decide +native) (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd6⟩ := rd5.sstore hperm (by decide +native) (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd6⟩

theorem wtf_nestedHashMem_size (baseSlot owner : UInt256) (ee : ExecutionEnv) (mem : ByteArray)
    (h : mem.size = 96) : (solcNestedMappingCallerHashMem baseSlot owner ee mem).size = 96 := by
  unfold solcNestedMappingCallerHashMem
  exact twoWordHashMem_size_96 _ _ (twoWordHashMem_size_96 owner baseSlot h)

theorem wtf_nestedHashMem_read64 (baseSlot owner : UInt256) (ee : ExecutionEnv) (mem : ByteArray)
    (hsize : mem.size = 96) (hr : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcNestedMappingCallerHashMem baseSlot owner ee mem).readWithPadding 64 32
      = UInt256.toByteArray ⟨128⟩ := by
  unfold solcNestedMappingCallerHashMem
  exact twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 owner baseSlot hsize)
    (twoWordHashMem_read64 owner baseSlot hsize hr)

/-- Branch join, case `src ≠ caller ∧ allowance ≠ uint(-1) ∧ allowance ≥ wad` (pc 1186 → 1282):
    require the allowance, decrement it. -/
theorem weth9TFBranchSpendOk {ee g s0 rdata cA σ k C} {src dst wad ret : UInt256}
    {S : List UInt256}
    (h : RD weth9Bytecode ee g s0 ⟨1186⟩
      (UInt256.isZero (UInt256.eq (UInt256.lnot ⟨0⟩)
          (solcSlotWord σ ee (wtfAllowSlot ee src))) :: ⟨0⟩ :: wad :: dst :: src :: ret :: S)
      (wtfAllowHashMem ee src) (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true) (hsrc : src.toNat < EVM.addressModulus)
    (hnotMax : solcSlotWord σ ee (wtfAllowSlot ee src) ≠ UInt256.lnot ⟨0⟩)
    (hallowEnough : wad.toNat ≤ (solcSlotWord σ ee (wtfAllowSlot ee src)).toNat)
    (hov : S.length + 16 ≤ 1024) :
    ∃ k' C', RD weth9Bytecode ee g s0 ⟨1282⟩ (⟨0⟩ :: wad :: dst :: src :: ret :: S)
      (solcNestedMappingCallerHashMem ⟨4⟩ src ee
        (solcNestedMappingCallerHashMem ⟨4⟩ src ee (wtfAllowHashMem ee src)))
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (wtfAllowSlot ee src)
        (UInt256.sub (solcSlotWord σ ee (wtfAllowSlot ee src)) wad)) k' C' := by
  have rd1192 := h.jumpdest (by decide +native) (by simp only [List.length_cons]; omega)
    |>.iszero (by decide +native) (by simp only [List.length_cons]; omega)
    |>.pushConst (⟨1282⟩ : UInt256) (op := .PUSH2) (width := 2) (by decide) (by decide +native)
        (by simp only [List.length_cons]; omega)
    |>.jumpiNT (by decide +native) (by rw [u256_eq_of_ne (Ne.symm hnotMax)]; decide)
        (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd1228⟩ := weth9TFRequireAllowance rd1192 hsrc (wtfAllowHashMem_size ee src) hov
  have rd1239 := rd1228.dup3 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.gt (by decide +native) (by simp only [List.length_cons]; omega)
    |>.iszero (by decide +native) (by simp only [List.length_cons]; omega)
    |>.pushConst (⟨1239⟩ : UInt256) (op := .PUSH2) (width := 2) (by decide) (by decide +native)
        (by simp only [List.length_cons]; omega)
    |>.jumpiT (by decide +native) (by rw [ugt_zero hallowEnough]; decide) (by jump_dest)
        (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd1282⟩ := weth9TFDecrementAllowance rd1239 hperm hsrc
    (wtf_nestedHashMem_size ⟨4⟩ src ee (wtfAllowHashMem ee src) (wtfAllowHashMem_size ee src)) hov
  exact ⟨_, _, rd1282⟩

/-- Branch join, revert case `src ≠ caller ∧ allowance ≠ uint(-1) ∧ allowance < wad` (pc 1186 → the
    `PUSH1 0; DUP1; REVERT` stub). -/
theorem weth9TFBranchSpendRev {ee g s0 rdata cA σ k C} {src dst wad ret : UInt256}
    {S : List UInt256}
    (h : RD weth9Bytecode ee g s0 ⟨1186⟩
      (UInt256.isZero (UInt256.eq (UInt256.lnot ⟨0⟩)
          (solcSlotWord σ ee (wtfAllowSlot ee src))) :: ⟨0⟩ :: wad :: dst :: src :: ret :: S)
      (wtfAllowHashMem ee src) (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hsrc : src.toNat < EVM.addressModulus)
    (hnotMax : solcSlotWord σ ee (wtfAllowSlot ee src) ≠ UInt256.lnot ⟨0⟩)
    (hlt : (solcSlotWord σ ee (wtfAllowSlot ee src)).toNat < wad.toNat)
    (hov : S.length + 16 ≤ 1024) :
    RDrev weth9Bytecode g s0 := by
  have rd1192 := h.jumpdest (by decide +native) (by simp only [List.length_cons]; omega)
    |>.iszero (by decide +native) (by simp only [List.length_cons]; omega)
    |>.pushConst (⟨1282⟩ : UInt256) (op := .PUSH2) (width := 2) (by decide) (by decide +native)
        (by simp only [List.length_cons]; omega)
    |>.jumpiNT (by decide +native) (by rw [u256_eq_of_ne (Ne.symm hnotMax)]; decide)
        (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd1228⟩ := weth9TFRequireAllowance rd1192 hsrc (wtfAllowHashMem_size ee src) hov
  exact rd1228.dup3 (by decide +native) (by simp only [List.length_cons]; omega)
    |>.gt (by decide +native) (by simp only [List.length_cons]; omega)
    |>.iszero (by decide +native) (by simp only [List.length_cons]; omega)
    |>.pushConst (⟨1239⟩ : UInt256) (op := .PUSH2) (width := 2) (by decide) (by decide +native)
        (by simp only [List.length_cons]; omega)
    |>.jumpiNT (by decide +native) (by rw [ugt_one hlt]; decide) (by simp only [List.length_cons]; omega)
    |>.solcPush1Dup1Revert0 (by decide +native) (by decide +native) (by decide +native)
        (by simp only [List.length_cons]; omega)

/-- `balanceOf[src]` after the debit `-= wad` (wrapping). -/
def wtfSrcDebitedMap (ee : ExecutionEnv) (σ : AccountMap) (src wad : UInt256) : AccountMap :=
  sstoreAccountMap ee.codeOwner σ (wtfBalSlot src)
    (UInt256.sub (solcSlotWord σ ee (wtfBalSlot src)) wad)

/-- Full post-state after `balanceOf[src] -= wad; balanceOf[dst] += wad` (wrapping). -/
def wtfPostMap (ee : ExecutionEnv) (σ : AccountMap) (src dst wad : UInt256) : AccountMap :=
  sstoreAccountMap ee.codeOwner (wtfSrcDebitedMap ee σ src wad) (wtfBalSlot dst)
    (UInt256.add wad (solcSlotWord (wtfSrcDebitedMap ee σ src wad) ee (wtfBalSlot dst)))

/-- `wordAt0Mem` leaves the free-pointer slot (bytes 64–95) untouched. -/
private theorem wtfTail_wordAt0Mem_read64 {m : ByteArray} (word : UInt256) (hm : m.size = 96) :
    (wordAt0Mem word m).readWithPadding 64 32 = m.readWithPadding 64 32 := by
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hm]; omega) (by omega)
    (by rw [hm])]

/-- Overwriting `mem[0]` with `key` (leaving `slot` at `mem[32]`) makes the first 64 scratch bytes
    hash to the mapping slot `keccak(key ‖ slot)`. -/
private theorem wtfTail_wordAt0Mem_keccak {m : ByteArray} (key slot : UInt256) (hm : m.size = 96)
    (hread32 : m.readWithPadding 32 32 = UInt256.toByteArray slot) :
    UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC ((wordAt0Mem key m).readWithPadding 0 64))) =
      solcMappingSlot slot key := by
  have hread0 : (wordAt0Mem key m).readWithPadding 0 32 = UInt256.toByteArray key :=
    wordAt0Mem_read0 key m
  have hread32' : (wordAt0Mem key m).readWithPadding 32 32 = UInt256.toByteArray slot := by
    unfold wordAt0Mem
    rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size]) (by rw [hm]; omega) (by omega)
      (by rw [hm]; omega)]
    exact hread32
  have hread0_64 : (wordAt0Mem key m).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
    rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [wordAt0Mem_size_96 key hm]; omega)]
    have hleft : (wordAt0Mem key m).extract 0 32 = UInt256.toByteArray key := by
      rw [← readWithPadding_eq_extract _ 0 (by rw [wordAt0Mem_size_96 key hm]; omega), hread0]
    have hright : (wordAt0Mem key m).extract 32 64 = UInt256.toByteArray slot := by
      rw [← readWithPadding_eq_extract _ 32 (by rw [wordAt0Mem_size_96 key hm]; omega), hread32']
    rw [show (wordAt0Mem key m).extract 0 64 =
        (wordAt0Mem key m).extract 0 32 ++ (wordAt0Mem key m).extract 32 64 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [hleft, hright]
  rw [hread0_64]
  unfold solcMappingSlot
  exact mappingSlot_single key slot

/-- The shared tail (pc 1282 → JUMP `ret`): `balanceOf[src] -= wad`, `balanceOf[dst] += wad`,
    emit the `Transfer` LOG3, push the boolean `1`, and JUMP back to the caller's return address,
    leaving `[1, S]` on the stack with the wad written to the scratch return buffer. -/
theorem weth9TFTail {ee g s0 rdata cA σ k C} {src dst wad ret : UInt256} {S : List UInt256}
    {mem : ByteArray}
    (h : RD weth9Bytecode ee g s0 ⟨1282⟩ (⟨0⟩ :: wad :: dst :: src :: ret :: S)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true) (hsrc : src.toNat < EVM.addressModulus)
    (hdst : dst.toNat < EVM.addressModulus)
    (hmemsize : mem.size = 96) (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hretDest : (D_J weth9Bytecode 0).contains ret = true)
    (hov : S.length + 16 ≤ 1024) :
    ∃ k' C', RD weth9Bytecode ee g s0 ret (⟨1⟩ :: S)
      (solcScratchReturnMem (wordAt0Mem dst (twoWordHashMem src ⟨3⟩ mem)) wad) (UInt256.ofNat 5)
      rdata (cA, wtfPostMap ee σ src dst wad) k' C' := by
  have hmem0size : (twoWordHashMem src ⟨3⟩ mem).size = 96 :=
    twoWordHashMem_size_96 src ⟨3⟩ hmemsize
  have hM0size : (wordAt0Mem dst (twoWordHashMem src ⟨3⟩ mem)).size = 96 :=
    wordAt0Mem_size_96 dst hmem0size
  have hM0read64 : (wordAt0Mem dst (twoWordHashMem src ⟨3⟩ mem)).readWithPadding 64 32
      = UInt256.toByteArray ⟨128⟩ := by
    rw [wtfTail_wordAt0Mem_read64 dst hmem0size, twoWordHashMem_read64 src ⟨3⟩ hmemsize hread64]
  have hkecSrc : UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((twoWordHashMem src ⟨3⟩ mem).readWithPadding 0 64))) = wtfBalSlot src :=
    twoWordHashMem_solcMappingSlot ⟨3⟩ src hmemsize
  have hkecDst : UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((wordAt0Mem dst (twoWordHashMem src ⟨3⟩ mem)).readWithPadding 0 64)))
        = wtfBalSlot dst :=
    wtfTail_wordAt0Mem_keccak dst ⟨3⟩ hmem0size (twoWordHashMem_read32 src ⟨3⟩ hmemsize)
  -- pc 1282 → 1293: build the address mask, mask `src`
  have rdA := evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup1, dup6, and]
  rw [wtf_maskLiteral hsrc] at rdA
  -- pc 1294 → 1311: scratch `src ‖ 3`, keccak `balanceOf[src]` slot, DUP1 for the store
  have rdB := evm_run rdA with [
    push1 ⟨0⟩, dup2, dup2,
    raw mstore 0 (wordAt0Mem src mem) (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov),
    push1 ⟨3⟩, push1 ⟨32⟩, swap1, dup2,
    raw mstore 0 (twoWordHashMem src ⟨3⟩ mem) (UInt256.ofNat 3) (by decide +native) mem_cost
      (by rw [show (⟨32⟩ : UInt256).toNat = 32 from rfl]; rfl) (by decide +native) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (wtfBalSlot src) (UInt256.ofNat 3) (by decide +native) mem_cost hkecSrc
      (by decide +native) (by evm_ov),
    dup1]
  obtain ⟨_, _, rdB2⟩ := rdB.sload (by decide +native) (by evm_ov)
  -- pc 1313 → 1316: `balanceOf[src] - wad`, arrange slot/value for the SSTORE
  have rdC := evm_run rdB2 with [dup9, swap1, sub, swap1]
  obtain ⟨_, _, rdC2⟩ := rdC.sstore hperm (by decide +native) (by evm_ov)
  -- pc 1318 → 1320: mask `dst`
  have rdD := evm_run rdC2 with [swap4, dup8, and]
  rw [wtf_maskLiteral hdst] at rdD
  -- pc 1321 → 1328: scratch `dst ‖ 3`, keccak `balanceOf[dst]` slot, DUP1 for the store
  have rdE := evm_run rdD with [
    dup1, dup4,
    raw mstore 0 (wordAt0Mem dst (twoWordHashMem src ⟨3⟩ mem)) (UInt256.ofNat 3) (by decide +native)
      mem_cost (by rfl) (by decide +native) (by evm_ov),
    swap2, dup5, swap1,
    raw keccak256 0 (wtfBalSlot dst) (UInt256.ofNat 3) (by decide +native) mem_cost hkecDst
      (by decide +native) (by evm_ov),
    dup1]
  obtain ⟨_, _, rdE2⟩ := rdE.sload (by decide +native) (by evm_ov)
  -- pc 1330 → 1332: `wad + balanceOf[dst]`, arrange for the SSTORE
  have rdF := evm_run rdE2 with [dup8, add, swap1]
  obtain ⟨_, _, rdF2⟩ := rdF.sstore hperm (by decide +native) (by evm_ov)
  -- pc 1334 → 1342: MLOAD free ptr, MSTORE wad into the log-data slot, reload the free ptr
  have rdG := evm_run rdF2 with [
    dup4,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native) mem_cost
      (mloadFreePtrValue (by rw [hM0size]; decide) (by decide) hM0read64) (by decide +native)
      (by evm_ov),
    dup7, dup2,
    raw mstore 6 (solcScratchReturnMem (wordAt0Mem dst (twoWordHashMem src ⟨3⟩ mem)) wad)
      (UInt256.ofNat 5) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov),
    swap4,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide +native) mem_cost
      (solcScratchReturnMem_mload64 wad hM0size hM0read64) (by decide +native) (by evm_ov),
    swap2, swap4]
  -- pc 1343: PUSH32 the `Transfer(address,address,uint256)` topic
  have rdG2 := rdG.pushConst
      (⟨100389287136786176327247604509743168900146139575972864366142685224231313322991⟩ : UInt256)
      (op := .PUSH32) (width := 32) (by decide) (by decide +native) (by evm_ov)
  -- pc 1376 → 1394: arrange `[offset, len, t0, t1, t2]`, LOG3, push `1`, JUMP `ret`
  have rdRet := evm_run rdG2 with [
    swap3, swap1, dup2, swap1, sub, swap1, swap2, add, swap1,
    raw log3 0 (UInt256.ofNat 5) (by decide +native) hperm mem_cost (by decide) (by evm_ov),
    pop, push1 ⟨1⟩, swap4, swap3, pop, pop, pop,
    jump hretDest]
  exact ⟨_, _, rdRet⟩

end Benchmarks.WETH9
