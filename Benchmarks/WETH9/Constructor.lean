import Benchmarks.WETH9.Bytecode
import Benchmarks.WETH9.StringLayout
import Benchmarks.WETH9.ConstructorStore
import Benchmarks.WETH9.ConstructorSolm
import Reasoning.Initcode
import Reasoning.Memory
import Reasoning.Stepping
import Reasoning.SolmBody
import Reasoning.Constructor
import Solm.Equiv

/-!
# WETH9 constructor correctness

`weth9ConstructorCorrect : constructorEquivalence config weth9CreationBytecode contract weth9Bytecode`.

The solc-0.5.16 creation bytecode writes the two compact short strings `name` = "Wrapped Ether"
(slot 0) and `symbol` = "WETH" (slot 1) and `decimals` = 18 (slot 2), then (after a non-payable
callvalue guard) `CODECOPY`s the 1763-byte runtime window and `RETURN`s it.  The Solm constructor body
is `nonpayable ++ [assign name, assign symbol, assign decimals]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.WETH9

set_option maxRecDepth 4000000

/-! ## Size and runtime-window facts -/

theorem weth9CreationBytecode_size : weth9CreationBytecode.size = 2055 := by native_decide

theorem weth9Bytecode_size : weth9Bytecode.size = 1763 := by native_decide

/-- The runtime window CODECOPY'd + RETURN'd by the creation code (`PUSH2 0x6e3 DUP1 PUSH2 0x124`:
    offset `292`, length `1763`) is exactly the deployed runtime. -/
theorem weth9CreationBytecode_runtime_window :
    weth9CreationBytecode.extract 292 (292 + 1763) = weth9Bytecode := by native_decide

/-! ## Deployment shape (empty constructor) -/

theorem weth9_selfDeployment_eq :
    config.selfDeployment = genSolidityConstructorDeployment contract.ctor.params := rfl

theorem weth9_ctor_params_nil : contract.ctor.params = [] := rfl

/-! ## Constructor initcode words and memory states -/

/-- `"Wrapped Ether"` left-aligned in a 32-byte word (creation.hex pc 12–28: `PUSH13 … PUSH1 153 SHL`). -/
def weth9NameWord : UInt256 :=
  UInt256.shiftLeft ⟨3464124613321760372568404275897⟩ ⟨153⟩

/-- `"WETH"` left-aligned (creation.hex pc 63–70: `PUSH4 … PUSH1 227 SHL`). -/
def weth9SymWord : UInt256 :=
  UInt256.shiftLeft ⟨183020169⟩ ⟨227⟩

def weth9CtorMemPrologue : ByteArray :=
  (⟨192⟩ : UInt256).toByteArray.write 0 ByteArray.empty 64 32

def weth9CtorMemNameLen : ByteArray :=
  (⟨13⟩ : UInt256).toByteArray.write 0 weth9CtorMemPrologue 128 32

def weth9CtorMemName : ByteArray :=
  weth9NameWord.toByteArray.write 0 weth9CtorMemNameLen 160 32

theorem weth9CtorMemPrologue_size : weth9CtorMemPrologue.size = 96 :=
  toByteArray_write32_size_of_ge ByteArray.empty ⟨192⟩ 64 0 96 rfl (by decide)
    (lt_usize _ (by norm_num)) rfl

theorem weth9CtorMemNameLen_size : weth9CtorMemNameLen.size = 160 :=
  toByteArray_write32_size_of_ge weth9CtorMemPrologue ⟨13⟩ 128 96 160
    weth9CtorMemPrologue_size (by decide) (lt_usize _ (by norm_num)) rfl

theorem weth9CtorMemName_size : weth9CtorMemName.size = 192 :=
  toByteArray_write32_size_of_ge weth9CtorMemNameLen weth9NameWord 160 160 192
    weth9CtorMemNameLen_size (by decide) (lt_usize _ (by norm_num)) rfl

theorem weth9CtorMemName_read160 :
    weth9CtorMemName.readWithPadding 160 32 = weth9NameWord.toByteArray := by
  rw [weth9CtorMemName, write32_read_back weth9NameWord.toByteArray weth9CtorMemNameLen 160
    (by rw [toByteArray_size]) (by rw [weth9CtorMemNameLen_size]), toByteArray_extract_all]

/-! ## Segment 1: prologue + `name` setup, reaching the store subroutine at pc 122 -/

set_option maxHeartbeats 2000000 in
theorem weth9CtorReachName {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9CreationBytecode) :
    ∃ k C, RD weth9CreationBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨122⟩
      [⟨13⟩, ⟨160⟩, ⟨0⟩, ⟨46⟩]
      weth9CtorMemName (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
  have rd0 : RD weth9CreationBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨0⟩ []
      ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (cA, σ) 0 0 := RD.initState hcode
  have rd4 := evm_run rd0 with [
    push1 ⟨192⟩, push1 ⟨64⟩,
    raw mstore 9 weth9CtorMemPrologue (UInt256.ofNat 3) (by native_decide) mem_cost rfl
      (by native_decide) (by evm_ov)]
  have rd11 := evm_run rd4 with [
    push1 ⟨13⟩, push1 ⟨128⟩, dup2, swap1,
    raw mstore 6 weth9CtorMemNameLen (UInt256.ofNat 5) (by native_decide) mem_cost rfl
      (by native_decide) (by evm_ov)]
  have rd28 := rd11.pushConst (⟨3464124613321760372568404275897⟩ : UInt256)
    (width := 13) (op := .PUSH13) (by native_decide) (by native_decide) (by evm_ov)
    |>.push1 ⟨153⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
  have rd33 := evm_run rd28 with [
    push1 ⟨160⟩, swap1, dup2,
    raw mstore 3 weth9CtorMemName (UInt256.ofNat 6) (by native_decide) mem_cost rfl
      (by native_decide) (by evm_ov)]
  exact ⟨_, _, evm_run rd33 with [
    push2 ⟨46⟩, swap2, push1 ⟨0⟩, swap2, swap1, push2 ⟨122⟩, jump (by native_decide)]⟩

/-! ## Memory states for the `symbol` setup -/

def weth9CtorMemNameSub : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 weth9CtorMemName 0 32

def weth9CtorMemFreeBump : ByteArray :=
  (⟨256⟩ : UInt256).toByteArray.write 0 weth9CtorMemNameSub 64 32

def weth9CtorMemSymLen : ByteArray :=
  (⟨4⟩ : UInt256).toByteArray.write 0 weth9CtorMemFreeBump 192 32

def weth9CtorMemSym : ByteArray :=
  weth9SymWord.toByteArray.write 0 weth9CtorMemSymLen 224 32

theorem weth9CtorMemNameSub_size : weth9CtorMemNameSub.size = 192 :=
  toByteArray_write32_size_of_le weth9CtorMemName ⟨0⟩ 0 192 192 weth9CtorMemName_size
    (by rw [weth9CtorMemName_size]; omega) (by decide)

theorem weth9CtorMemFreeBump_size : weth9CtorMemFreeBump.size = 192 :=
  toByteArray_write32_size_of_le weth9CtorMemNameSub ⟨256⟩ 64 192 192 weth9CtorMemNameSub_size
    (by rw [weth9CtorMemNameSub_size]; omega) (by decide)

theorem weth9CtorMemSymLen_size : weth9CtorMemSymLen.size = 224 :=
  toByteArray_write32_size_of_le weth9CtorMemFreeBump ⟨4⟩ 192 192 224 weth9CtorMemFreeBump_size
    (by rw [weth9CtorMemFreeBump_size]) (by decide)

theorem weth9CtorMemSym_size : weth9CtorMemSym.size = 256 :=
  toByteArray_write32_size_of_le weth9CtorMemSymLen weth9SymWord 224 224 256 weth9CtorMemSymLen_size
    (by rw [weth9CtorMemSymLen_size]) (by decide)

theorem weth9CtorMemNameSub_read64 :
    weth9CtorMemNameSub.readWithPadding 64 32 = (⟨192⟩ : UInt256).toByteArray := by
  rw [weth9CtorMemNameSub,
    write32_read_above (⟨0⟩ : UInt256).toByteArray weth9CtorMemName 0 64
      (by rw [toByteArray_size]) (by omega) (by omega)
      (by rw [weth9CtorMemName_size]; omega),
    weth9CtorMemName,
    toByteArray_write_read_below_of_gap weth9NameWord weth9CtorMemNameLen 160 64
      (by rw [weth9CtorMemNameLen_size]; omega) (by omega)
      (by rw [weth9CtorMemNameLen_size]; exact lt_usize _ (by norm_num)),
    weth9CtorMemNameLen,
    toByteArray_write_read_below_of_gap ⟨13⟩ weth9CtorMemPrologue 128 64
      (by rw [weth9CtorMemPrologue_size]) (by omega)
      (by rw [weth9CtorMemPrologue_size]; exact lt_usize _ (by norm_num)),
    weth9CtorMemPrologue,
    toByteArray_write_read_back_of_gap ⟨192⟩ ByteArray.empty 64
      (by simp only [ByteArray.size_empty]; exact lt_usize _ (by norm_num))]

theorem weth9CtorMemSym_read224 :
    weth9CtorMemSym.readWithPadding 224 32 = weth9SymWord.toByteArray := by
  rw [weth9CtorMemSym,
    toByteArray_write_read_back_of_gap weth9SymWord weth9CtorMemSymLen 224
      (by rw [weth9CtorMemSymLen_size]; exact lt_usize _ (by norm_num))]

/-! ## Storage after each subroutine (EVM side) -/

/-- The `keccak(slot)` and short-word abbreviations used by the two string writes. -/
def weth9StoreV (len : UInt256) (dataword : UInt256) : UInt256 :=
  UInt256.lor (len + len) (UInt256.land (UInt256.lnot ⟨255⟩) dataword)

noncomputable def weth9OldWordsOf (σ : AccountMap) (cO : AccountAddress) (slot : UInt256) : Nat :=
  solidityBytesDataWordCount
    (weth9DecodeLenWord (σ.find? cO |>.option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩))).toNat

noncomputable def weth9EvmNameMap (σ : AccountMap) (cO : AccountAddress) : AccountMap :=
  clearDataWordsForwardFrom cO
    (sstoreAccountMap cO σ ⟨0⟩ (weth9StoreV ⟨13⟩ weth9NameWord))
    (Solm.solidityBytesDataBaseSlot ⟨0⟩) ⟨0⟩ (weth9OldWordsOf σ cO ⟨0⟩)

noncomputable def weth9EvmSymMap (σ : AccountMap) (cO : AccountAddress) : AccountMap :=
  clearDataWordsForwardFrom cO
    (sstoreAccountMap cO (weth9EvmNameMap σ cO) ⟨1⟩ (weth9StoreV ⟨4⟩ weth9SymWord))
    (Solm.solidityBytesDataBaseSlot ⟨1⟩) ⟨0⟩ (weth9OldWordsOf (weth9EvmNameMap σ cO) cO ⟨1⟩)

noncomputable def weth9EvmFinalMap (σ : AccountMap) (cO : AccountAddress) : AccountMap :=
  sstoreAccountMap cO (weth9EvmSymMap σ cO) ⟨2⟩
    (UInt256.lor ⟨18⟩ (UInt256.land (UInt256.lnot ⟨255⟩)
      ((weth9EvmSymMap σ cO).find? cO |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨2⟩ ⟨0⟩))))

def weth9CtorMemSymSub : ByteArray :=
  (⟨1⟩ : UInt256).toByteArray.write 0 weth9CtorMemSym 0 32

/-! ## The EVM initcode trace: reach the callvalue guard at pc 105 -/

set_option maxHeartbeats 4000000 in
theorem weth9CtorReachGuard {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9CreationBytecode) (hperm : I.perm = true) :
    ∃ k C, RD weth9CreationBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨105⟩
      [] weth9CtorMemSymSub (UInt256.ofNat 8) ByteArray.empty
      (cA, weth9EvmFinalMap σ I.codeOwner) k C := by
  -- Reach the name subroutine at pc 122, run it, reach pc 46.
  obtain ⟨_, _, rdName⟩ := weth9CtorReachName (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode
  obtain ⟨_, _, rd46⟩ := weth9StringStoreSubroutine ⟨13⟩ ⟨160⟩ ⟨0⟩ ⟨46⟩ weth9NameWord
    (Or.inl rfl) (by decide) hperm (by native_decide) (by decide)
    (by rw [weth9CtorMemName_size]; decide) (by decide) (by decide) (by decide)
    (by rw [show (⟨160⟩ : UInt256).toNat = 160 from rfl]; exact weth9CtorMemName_read160) rdName
  -- Segment 2: POP; symbol setup; reach pc 122.
  have rd51 := evm_run rd46 with [
    jumpdest, pop, push1 ⟨64⟩, dup1]
  have rd52 := rd51.mload 0 ⟨192⟩ (UInt256.ofNat 6) (by native_decide)
    (fun s h1 h2 => by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', h1, h2,
      List.getElem!_cons_zero]; native_decide)
    (mloadWordValue_of_readWithPadding (mem := weth9CtorMemNameSub) (aw := UInt256.ofNat 6)
      (off := ⟨64⟩) (v := ⟨192⟩)
      (by rw [weth9CtorMemNameSub_size]; decide) (by decide)
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from rfl]; exact weth9CtorMemNameSub_read64))
    (by native_decide) (by evm_ov)
  have rd57 := evm_run rd52 with [
    dup1, dup3, add, swap1, swap2,
    raw mstore 0 weth9CtorMemFreeBump (UInt256.ofNat 6) (by native_decide)
      (fun s h1 h2 => by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', h1, h2,
        List.getElem!_cons_zero]; native_decide)
      rfl (by native_decide) (by evm_ov)]
  have rd62 := evm_run rd57 with [
    push1 ⟨4⟩, dup1, dup3,
    raw mstore 3 weth9CtorMemSymLen (UInt256.ofNat 7) (by native_decide)
      (fun s h1 h2 => by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', h1, h2,
        List.getElem!_cons_zero]; native_decide)
      rfl (by native_decide) (by evm_ov)]
  have rd70 := rd62.pushConst (⟨183020169⟩ : UInt256) (width := 4) (op := .PUSH4)
    (by native_decide) (by native_decide) (by evm_ov)
    |>.push1 ⟨227⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
  have rd78 := evm_run rd70 with [
    push1 ⟨32⟩, swap1, swap3, add, swap2, dup3,
    raw mstore 3 weth9CtorMemSym (UInt256.ofNat 8) (by native_decide)
      (fun s h1 h2 => by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', h1, h2,
        List.getElem!_cons_zero]; native_decide)
      rfl (by native_decide) (by evm_ov)]
  have rd122 := evm_run rd78 with [
    push2 ⟨90⟩, swap2, push1 ⟨1⟩, swap2, push2 ⟨122⟩, jump (by native_decide)]
  -- Run the symbol subroutine, reach pc 90.
  obtain ⟨_, _, rd90⟩ := weth9StringStoreSubroutine ⟨4⟩ ⟨224⟩ ⟨1⟩ ⟨90⟩ weth9SymWord
    (Or.inr rfl) (by decide) hperm (by native_decide) (by decide)
    (by rw [weth9CtorMemSym_size]; decide) (by decide) (by decide) (by decide)
    (by rw [show (⟨224⟩ : UInt256).toNat = 224 from rfl]; exact weth9CtorMemSym_read224) rd122
  -- Segment 3a: POP; decimals RMW; reach pc 105.
  have rd91 := evm_run rd90 with [jumpdest, pop, push1 ⟨2⟩, dup1]
  obtain ⟨_, _, rd96⟩ := rd91.sload (by native_decide) (by evm_ov)
  have rd104 := evm_run rd96 with [push1 ⟨255⟩, not, and, push1 ⟨18⟩, lor, swap1]
  obtain ⟨_, _, rd105⟩ := rd104.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, rd105⟩

/-! ## Codecopy/return and the two terminal traces -/

def weth9CtorReturnMem : ByteArray :=
  weth9CreationBytecode.write 292 weth9CtorMemSymSub 0 1763

theorem weth9CtorReturnMem_read : weth9CtorReturnMem.readWithPadding 0 1763 = weth9Bytecode := by
  unfold weth9CtorReturnMem
  rw [write0_read_back_from_gen weth9CreationBytecode weth9CtorMemSymSub 292 1763
    (by decide) (by rw [weth9CreationBytecode_size]) (by decide)]
  exact weth9CreationBytecode_runtime_window

set_option maxHeartbeats 4000000 in
theorem weth9CtorInitcodeSuccess {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9CreationBytecode) (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩) :
    RDret weth9CreationBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, weth9EvmFinalMap σ I.codeOwner) weth9Bytecode := by
  obtain ⟨_, _, rd105⟩ := weth9CtorReachGuard (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hperm
  have rd287 := evm_run rd105 with [
    callvalue, dup1, iszero, push2 ⟨116⟩,
    jumpiT (by rw [hwv]; decide) (by native_decide),
    jumpdest, pop, push2 ⟨277⟩, jump (by native_decide),
    jumpdest, push2 ⟨1763⟩, dup1, push2 ⟨292⟩, push1 ⟨0⟩,
    raw codecopy 150 weth9CtorReturnMem (UInt256.ofNat 56) (by native_decide) mem_cost rfl
      (by native_decide) (by evm_ov),
    push1 ⟨0⟩]
  exact rd287.ret 0 weth9Bytecode (by native_decide) mem_cost weth9CtorReturnMem_read (by evm_ov)

set_option maxHeartbeats 4000000 in
theorem weth9CtorInitcodeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9CreationBytecode) (hperm : I.perm = true) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev weth9CreationBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd105⟩ := weth9CtorReachGuard (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hperm
  have rd114 := evm_run rd105 with [
    callvalue, dup1, iszero, push2 ⟨116⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push1 ⟨0⟩, dup1]
  exact rd114.rev 0 (by native_decide) mem_cost (by evm_ov)

/-! ## Reconciling the EVM store-then-clear with the Solm clear-then-store, per write -/

theorem ulor_comm (a b : UInt256) : UInt256.lor a b = UInt256.lor b a := by
  apply u256_inj; rw [u256_lor_toNat, u256_lor_toNat, nat_lor_comm]

/-- A single compact-string write reconciles up to `accountMapEquiv`. -/
theorem weth9WriteReconcile (cO : AccountAddress) (τ_evm τ_solm : AccountMap)
    (slot len dataword sw : UInt256) (hslot : slot = ⟨0⟩ ∨ slot = ⟨1⟩)
    (hsw : weth9StoreV len dataword = sw) (hτ : accountMapEquiv τ_evm τ_solm) :
    accountMapEquiv
      (clearDataWordsForwardFrom cO (sstoreAccountMap cO τ_evm slot (weth9StoreV len dataword))
        (Solm.solidityBytesDataBaseSlot slot) ⟨0⟩ (weth9OldWordsOf τ_evm cO slot))
      (sstoreAccountMap cO
        (clearDataWordsForwardFrom cO τ_solm (Solm.solidityBytesDataBaseSlot slot) ⟨0⟩
          (weth9OldWordsOf τ_solm cO slot)) slot sw) := by
  have hload : (τ_evm.find? cO |>.option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩)) =
      (τ_solm.find? cO |>.option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩)) :=
    accountMapEquiv_storage_findD hτ cO slot ⟨0⟩
  have how : weth9OldWordsOf τ_evm cO slot = weth9OldWordsOf τ_solm cO slot := by
    unfold weth9OldWordsOf; rw [hload]
  rw [how, ← hsw]
  refine accountMapEquiv.trans
    (weth9ClearStoreCommEquiv cO τ_evm slot (weth9StoreV len dataword) hslot
      (weth9OldWordsOf τ_solm cO slot) (weth9NoOverflow slot hslot _)) ?_
  exact accountMapEquiv_sstoreAccountMap cO slot (weth9StoreV len dataword)
    (accountMapEquiv_clearDataWordsForwardFrom cO (Solm.solidityBytesDataBaseSlot slot) ⟨0⟩ _ hτ)

/-! ## The Solm final state's account map, unfolded to the clear/store form -/

theorem weth9SolmNameState_map (evm : EVM.State) :
    (weth9SolmNameState evm).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner
        (clearDataWordsForwardFrom evm.executionEnv.codeOwner evm.accountMap
          (Solm.solidityBytesDataBaseSlot ⟨0⟩) ⟨0⟩ (weth9OldWordsOf evm.accountMap evm.executionEnv.codeOwner ⟨0⟩))
        ⟨0⟩ (solidityShortBytesWord (String.toByteArray "Wrapped Ether")) := by
  rw [weth9SolmNameState, storageStore_accountMap, clearSolidityBytesDataWordsFrom_accountMap]
  rfl

theorem weth9SolmNameState_executionEnv (evm : EVM.State) :
    (weth9SolmNameState evm).executionEnv = evm.executionEnv := by
  rw [weth9SolmNameState, storageStore_executionEnv, clearSolidityBytesDataWordsFrom_executionEnv]

theorem weth9SolmSymbolState_map (evm : EVM.State) :
    (weth9SolmSymbolState evm).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner
        (clearDataWordsForwardFrom evm.executionEnv.codeOwner (weth9SolmNameState evm).accountMap
          (Solm.solidityBytesDataBaseSlot ⟨1⟩) ⟨0⟩
          (weth9OldWordsOf (weth9SolmNameState evm).accountMap evm.executionEnv.codeOwner ⟨1⟩))
        ⟨1⟩ (solidityShortBytesWord (String.toByteArray "WETH")) := by
  rw [weth9SolmSymbolState, storageStore_accountMap, clearSolidityBytesDataWordsFrom_accountMap,
    weth9SolmNameState_executionEnv]
  rfl

theorem weth9SolmSymbolState_executionEnv (evm : EVM.State) :
    (weth9SolmSymbolState evm).executionEnv = evm.executionEnv := by
  rw [weth9SolmSymbolState, storageStore_executionEnv, clearSolidityBytesDataWordsFrom_executionEnv,
    weth9SolmNameState_executionEnv]

theorem weth9SolmFinalState_createdAccounts (evm : EVM.State) :
    (weth9SolmFinalState evm).createdAccounts = evm.createdAccounts := by
  rw [weth9SolmFinalState, storageStore_createdAccounts, weth9SolmSymbolState,
    storageStore_createdAccounts, clearSolidityBytesDataWordsFrom_createdAccounts,
    weth9SolmNameState, storageStore_createdAccounts,
    clearSolidityBytesDataWordsFrom_createdAccounts]

theorem weth9DecimalsWordComm (X : UInt256) :
    UInt256.lor ⟨18⟩ (UInt256.land (UInt256.lnot ⟨255⟩) X) =
      UInt256.lor (UInt256.land X (UInt256.lnot ⟨255⟩)) ⟨18⟩ := by
  rw [uland_comm (UInt256.lnot ⟨255⟩) X, ulor_comm ⟨18⟩ (UInt256.land X (UInt256.lnot ⟨255⟩))]

/-- The full three-write storage reconciliation between EVM and Solm final states. -/
theorem weth9FinalReconcile (cO : AccountAddress) (evm0 : EVM.State) (σ_evm : AccountMap)
    (hcO : evm0.executionEnv.codeOwner = cO) (hmap : accountMapEquiv σ_evm evm0.accountMap) :
    accountMapEquiv (weth9EvmFinalMap σ_evm cO) (weth9SolmFinalState evm0).accountMap := by
  have hName : accountMapEquiv (weth9EvmNameMap σ_evm cO)
      (weth9SolmNameState evm0).accountMap := by
    rw [weth9SolmNameState_map, hcO]
    exact weth9WriteReconcile cO σ_evm evm0.accountMap ⟨0⟩ ⟨13⟩ weth9NameWord
      (solidityShortBytesWord (String.toByteArray "Wrapped Ether")) (Or.inl rfl)
      (by native_decide) hmap
  have hSym : accountMapEquiv (weth9EvmSymMap σ_evm cO)
      (weth9SolmSymbolState evm0).accountMap := by
    rw [weth9SolmSymbolState_map, hcO]
    exact weth9WriteReconcile cO (weth9EvmNameMap σ_evm cO) (weth9SolmNameState evm0).accountMap
      ⟨1⟩ ⟨4⟩ weth9SymWord (solidityShortBytesWord (String.toByteArray "WETH")) (Or.inr rfl)
      (by native_decide) hName
  have hload2 :
      ((weth9EvmSymMap σ_evm cO).find? cO |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨2⟩ ⟨0⟩)) =
        ((weth9SolmSymbolState evm0).accountMap.find? cO |>.option ⟨0⟩
          (fun ac => ac.storage.findD ⟨2⟩ ⟨0⟩)) :=
    accountMapEquiv_storage_findD hSym cO ⟨2⟩ ⟨0⟩
  rw [weth9EvmFinalMap, weth9SolmFinalState, storageStore_accountMap,
    weth9SolmSymbolState_executionEnv, hcO,
    show Solm.EVM.storageLoad (weth9SolmSymbolState evm0) cO ⟨2⟩ =
      ((weth9SolmSymbolState evm0).accountMap.find? cO |>.option ⟨0⟩
        (fun ac => ac.storage.findD ⟨2⟩ ⟨0⟩)) from rfl,
    ← hload2, weth9DecimalsWordComm]
  exact accountMapEquiv_sstoreAccountMap cO ⟨2⟩ _ hSym

/-! ## Final assembly -/

set_option maxHeartbeats 1000000 in
theorem weth9ConstructorCorrect :
    constructorEquivalence config weth9CreationBytecode contract weth9Bytecode := by
  refine constructorEquivalence.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I args deployedInitcode hdeploy hcode _hcalldata hperm hσ
  have hdeployed := emptyCtorDeployment_eq_initcode weth9_selfDeployment_eq weth9_ctor_params_nil
    hdeploy
  rw [hdeployed] at hcode
  obtain rfl : args = [] := by
    have := emptyCtorDeployment_args_length weth9_selfDeployment_eq weth9_ctor_params_nil hdeploy
    rw [weth9_ctor_params_nil] at this
    exact List.eq_nil_of_length_eq_zero this
  by_cases hwv : I.weiValue = ⟨0⟩
  · -- Success: EVM returns runtime; reconcile the final storage.
    have hrd := weth9CtorInitcodeSuccess (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hperm hwv
    rcases hrd with hoog | ⟨s, hX, hacc⟩
    · exact constructorEquivalenceFor.outOfGas (Xi_error_of_X (g := g) (by
        rw [← hcode] at hoog; simpa [Sat256.ofUInt256] using hoog))
    · have hsuccess := Xi_success_of_X (g := g) (by
        rw [← hcode] at hX; simpa [Sat256.ofUInt256] using hX)
      have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
      have hσ' : s.accountMap = weth9EvmFinalMap σ_evm I.codeOwner := congrArg Prod.snd hacc
      rw [hcA, hσ'] at hsuccess
      refine constructorEquivalenceFor.execution hsuccess
        (weth9SolmCtorExecSuccess (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
          (g := g) (A := A) (I := I) hwv) ?_
      refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
      · rw [weth9SolmFinalState_createdAccounts]; rfl
      · exact weth9FinalReconcile I.codeOwner
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) σ_evm (by simp [initState])
          (by simpa [initState] using hσ)
  · -- Revert.
    have hrd := weth9CtorInitcodeRevert (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hperm hwv
    rcases hrd.xiResult hcode with hoog | ⟨g', o, hrev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hoog)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
        (weth9SolmCtorExecReverts (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
          (g := g) (A := A) (I := I) hwv) ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.WETH9
