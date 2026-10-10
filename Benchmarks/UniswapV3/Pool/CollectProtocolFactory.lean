import Benchmarks.UniswapV3.Pool.CollectProtocolSource
import Benchmarks.UniswapV3.Pool.Dispatch
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem collectProtocolFactoryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw junk : UInt256} {rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨8899⟩
      (junk :: EVM.word v.factory.val :: ⟨128⟩ :: ⟨4⟩ :: ⟨128⟩ :: ⟨32⟩ ::
        ⟨132⟩ :: UInt256.ofNat 2376452955 :: EVM.word v.factory.val :: R)
      factoryOwnerInputMem aw rdata σ k C)
    (hacc : evm.accountMap = σ) (hσ₀ : evm.σ₀ = s0.σ₀) (henv : evm.executionEnv = ee)
    (hcode : extCodeSizeWord evm.accountMap (EVM.word v.factory.val) ≠ ⟨0⟩)
    (ha : ActiveWords aw) (hov : R.length + 9 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config { contract := contract, locals := ∅, immutables := immStore v }
        evm factoryOwnerFunction.body .reverted) ∨
    ∃ (out : ByteArray) (σ' : AccountMap) (A' : Substate) (aw' : UInt256) (k' C' : Nat),
      32 ≤ out.size ∧ out.size < UInt256.size ∧ ActiveWords aw' ∧
      ExecFuncBody config { contract := contract, locals := ∅, immutables := immStore v }
        evm factoryOwnerFunction.body
        (.returned (factoryOwnerCallFrame v true out) { evm with accountMap := σ', substate := A' }
          (some [.address (AccountAddress.ofNat (fromByteArrayBigEndian (out.extract 0 32)))])) ∧
      RD (deployedRuntime v) ee g s0 ⟨8941⟩ (UInt256.ofNat out.size :: ⟨128⟩ :: R)
        (factoryOwnerOutputMem out) aw' out σ' k' C' := by
  have rdCall := uniswapV3Pool_block_8899 (immWords := wordsOf (immStore v)) (by evm_ov) rd
  simp only [uniswapV3Pool_block_8899_stack] at rdCall
  obtain ⟨ok, out, σ', A', k', C', hcall, rdAfter, hsize⟩ :=
    RD.staticcallSource (evm := evm) rdCall
      (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8902⟩ : UInt256), (UInt8.ofNat 250), .STATICCALL, none,
        immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov) hacc hσ₀ henv
  change callViaEVM evm (AccountAddress.ofUInt256 (EVM.word v.factory.val)) 0
    (factoryOwnerInputMem.readWithPadding 128 4)
    (ok, {evm with accountMap := σ', substate := A'}, out) false at hcall
  rw [show AccountAddress.ofUInt256 (EVM.word v.factory.val) = v.factory from
    accountAddress_roundtrip v.factory, factoryOwnerInputMem_read] at hcall
  change RD (deployedRuntime v) ee g s0 ⟨8903⟩
    ((if ok then ⟨1⟩ else ⟨0⟩) :: ⟨132⟩ :: UInt256.ofNat 2376452955 :: EVM.word v.factory.val :: R)
    (factoryOwnerOutputMem out) _ out σ' k' C' at rdAfter
  cases ok with
  | false =>
      have rdFail := uniswapV3Pool_block_8903_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide) rdAfter
      simp only [uniswapV3Pool_block_8903_fallthrough_stack] at rdFail
      exact Or.inl ⟨uniswapV3Pool_block_8910 (immWords := wordsOf (immStore v)) (by evm_ov) rdFail,
        factoryOwnerRevertsCall v evm _ out hcode hcall⟩
  | true =>
      have rdSize := uniswapV3Pool_block_8903_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdAfter
      simp only [uniswapV3Pool_block_8903_taken_stack] at rdSize
      by_cases hlen : 32 ≤ out.size
      · have rdOwner := uniswapV3Pool_block_8919_taken (immWords := wordsOf (immStore v))
          (by evm_ov)
          (by rw [ult_zero (by rw [UInt256.toNat_ofNat_of_lt hsize]; exact hlen)]; decide)
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdSize
        have hload : memLoad (UInt256.ofNat 64) (factoryOwnerOutputMem out) = ⟨128⟩ :=
          factoryOwnerOutputMem_mload64 out hsize
        simp only [uniswapV3Pool_block_8919_taken_stack, hload] at rdOwner
        exact Or.inr ⟨out, σ', A', _, _, _, hlen, hsize,
          activeWords_expand32 (callActiveWords_active ha (by decide) (by decide)) (by decide),
          factoryOwnerReturns v evm _ out hcode hcall hlen, rdOwner⟩
      · have hshort : out.size < 32 := by omega
        have rdShort := uniswapV3Pool_block_8919_fallthrough (immWords := wordsOf (immStore v))
          (by evm_ov)
          (by rw [ult_one (by rw [UInt256.toNat_ofNat_of_lt hsize]; exact hshort)]; decide) rdSize
        simp only [uniswapV3Pool_block_8919_fallthrough_stack] at rdShort
        exact Or.inl ⟨uniswapV3Pool_block_8937 (immWords := wordsOf (immStore v)) (by evm_ov) rdShort,
          factoryOwnerRevertsShort v evm _ out hcode hcall hshort⟩

theorem collectProtocolOwnerX {g : Sat256} {s0 evm : EVM.State} {k C : Nat}
    {aw : UInt256} {rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨8790⟩ R
      solcFreePtrMem aw rdata evm.accountMap k C)
    (hσ₀ : evm.σ₀ = s0.σ₀) (hperm : evm.executionEnv.perm = true)
    (ha : ActiveWords aw) (hov : R.length + 11 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config { contract := contract, locals := ∅, immutables := immStore v }
        (storeSlot0Unlocked evm false) factoryOwnerFunction.body .reverted) ∨
    ∃ (out : ByteArray) (σ' : AccountMap) (A' : Substate) (aw' : UInt256) (k' C' : Nat),
      32 ≤ out.size ∧ out.size < UInt256.size ∧ ActiveWords aw' ∧
      ExecFuncBody config { contract := contract, locals := ∅, immutables := immStore v }
        (storeSlot0Unlocked evm false) factoryOwnerFunction.body
        (.returned (factoryOwnerCallFrame v true out)
          { (storeSlot0Unlocked evm false) with accountMap := σ', substate := A' }
          (some [.address (AccountAddress.ofNat (fromByteArrayBigEndian (out.extract 0 32)))])) ∧
      RD (deployedRuntime v) evm.executionEnv g s0 ⟨8941⟩
        (UInt256.ofNat out.size :: ⟨128⟩ :: R) (factoryOwnerOutputMem out) aw' out σ' k' C' := by
  have hmap := storeSlot0Unlocked_accountMap evm false
  rw [slot0UnlockedWord_false] at hmap
  change (storeSlot0Unlocked evm false).accountMap =
    sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap (UInt256.ofNat 0)
      (UInt256.land (UInt256.lnot
        (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 240)))
        (evm.accountMap.get? evm.executionEnv.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256)))) at hmap
  have hfactory : UInt256.land (wordsOf (immStore v) "factory")
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = EVM.word v.factory.val := by
    rw [wordsOf_immStore_factory]
    change UInt256.land (EVM.word v.factory.val) solcAddrMask = _
    exact addressWord_val_clean _
  have hfree : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := solcFreePtrMem_mload64
  have hmem : (UInt256.shiftLeft (UInt256.ofNat 2376452955) (UInt256.ofNat 224)).toByteArray.write
      0 solcFreePtrMem 128 32 = factoryOwnerInputMem := rfl
  have hload : memLoad (UInt256.ofNat 64) factoryOwnerInputMem = ⟨128⟩ :=
    factoryOwnerInputMem_mload64
  by_cases hcode : extCodeSizeWord (storeSlot0Unlocked evm false).accountMap
      (EVM.word v.factory.val) = ⟨0⟩
  · obtain ⟨_, _, rdFail⟩ := uniswapV3Pool_block_8790_fallthrough
      (immWords := wordsOf (immStore v)) hov hperm
      (by rw [hfactory, ← hmap, hcode]; decide) rd
    simp only [uniswapV3Pool_block_8790_fallthrough_stack] at rdFail
    exact Or.inl ⟨uniswapV3Pool_block_8895 (immWords := wordsOf (immStore v)) (by evm_ov) rdFail,
      factoryOwnerRevertsNoCode v _ hcode⟩
  · obtain ⟨_, _, rdReady⟩ := uniswapV3Pool_block_8790_taken
      (immWords := wordsOf (immStore v)) hov hperm
      (by rw [hfactory, ← hmap, isZero_eq_zero_of_ne hcode]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_8790_taken_stack, uniswapV3Pool_block_8790_taken_memory,
      hfactory, hfree, show (⟨128⟩ : UInt256).toNat = 128 from rfl, hmem, hload,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 4 = ⟨4⟩ by native_decide,
      show (⟨128⟩ : UInt256) + UInt256.ofNat 4 = ⟨132⟩ by native_decide,
      ← hmap] at rdReady
    exact collectProtocolFactoryX (v := v) (evm := storeSlot0Unlocked evm false) rdReady rfl
      ((storeSlot0Unlocked_originalAccounts evm false).trans hσ₀)
      (storeSlot0Unlocked_executionEnv evm false) hcode
      (activeWords_expand32 (activeWords_expand32 (activeWords_expand32 ha (by decide))
        (by decide)) (by decide)) (by omega)

theorem collectProtocolLockStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨8790⟩ R mem aw rdata σ k C)
    (hperm : ee.perm = false) (hov : R.length + 4 ≤ 1024) :
    RDstatic (deployedRuntime v) g s0 := by
  have rdLoad := evm_run rd with [
    raw jumpdest (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8790⟩ : UInt256), (UInt8.ofNat 91), .JUMPDEST, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw push1 (UInt256.ofNat 0) (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8791⟩ : UInt256), (UInt8.ofNat 96), .Push .PUSH1, some ((UInt256.ofNat 0), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw dup1 (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8793⟩ : UInt256), (UInt8.ofNat 128), .DUP1, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)]
  obtain ⟨_, _, rdLoaded⟩ :=
    RD.sload rdLoad (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8794⟩ : UInt256), (UInt8.ofNat 84), .SLOAD, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rdStore := evm_run rdLoaded with [
    raw push1 (UInt256.ofNat 255) (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8795⟩ : UInt256), (UInt8.ofNat 96), .Push .PUSH1, some ((UInt256.ofNat 255), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw push1 (UInt256.ofNat 240) (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8797⟩ : UInt256), (UInt8.ofNat 96), .Push .PUSH1, some ((UInt256.ofNat 240), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw shl (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8799⟩ : UInt256), (UInt8.ofNat 27), .SHL, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw not (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8800⟩ : UInt256), (UInt8.ofNat 25), .NOT, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw and (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8801⟩ : UInt256), (UInt8.ofNat 22), .AND, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw swap1 (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8802⟩ : UInt256), (UInt8.ofNat 144), .SWAP1, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)]
  exact rdStore.sstoreStatic hperm (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8803⟩ : UInt256), (UInt8.ofNat 85), .SSTORE, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)


theorem collectProtocolReadLockX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨8719⟩ R mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ slot0FieldWord 30 1 σ ee = ⟨0⟩) ∨
      (slot0FieldWord 30 1 σ ee ≠ ⟨0⟩ ∧
        ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨8790⟩ (⟨0⟩ :: ⟨0⟩ :: R) mem aw rdata σ k' C') := by
  have hfield : UInt256.land (UInt256.ofNat 255)
      (UInt256.div
        (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256)))
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240))) =
      slot0FieldWord 30 1 σ ee := (slot0FieldWord_unlocked_evm σ ee).symm
  by_cases hlocked : slot0FieldWord 30 1 σ ee = ⟨0⟩
  · obtain ⟨_, _, rdFail⟩ := uniswapV3Pool_block_8719_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) (by rw [hfield]; exact hlocked) rd
    simp only [uniswapV3Pool_block_8719_fallthrough_stack] at rdFail
    exact Or.inl ⟨uniswapV3Pool_block_8740 (immWords := wordsOf (immStore v)) (by evm_ov) rdFail, hlocked⟩
  · exact Or.inr ⟨hlocked, uniswapV3Pool_block_8719_taken (immWords := wordsOf (immStore v))
      (by omega) (by rw [hfield]; exact hlocked)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩


theorem factoryOwnerOutputMem_heap (out : ByteArray) (aw : UInt256)
    (hb : out.size < UInt256.size) (ha : ActiveWords aw) :
    HeapMemory (factoryOwnerOutputMem out) aw ⟨128⟩ := by
  exact ⟨by rw [factoryOwnerOutputMem_size out hb]; decide,
    factoryOwnerOutputMem_read64 out hb, by decide,
    by rw [factoryOwnerOutputMem_size out hb]; decide, ha⟩

theorem factoryOwnerInputMem_read96 :
    factoryOwnerInputMem.readWithPadding 96 32 = (⟨0⟩ : UInt256).toByteArray := by native_decide

theorem factoryOwnerOutputMem_zero (out : ByteArray) (hb : out.size < UInt256.size) :
    memLoad (UInt256.ofNat 96) (factoryOwnerOutputMem out) = ⟨0⟩ := by
  apply mloadWordValue_of_readWithPadding
  · change 96 < (factoryOwnerOutputMem out).size
    rw [factoryOwnerOutputMem_size out hb]; decide
  · rw [factoryOwnerOutputMem, callOutput32_read_below _ _ _ _ hb
      (by rw [factoryOwnerInputMem_size]; decide) (by decide)]
    exact factoryOwnerInputMem_read96

theorem collectProtocolOwnerGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {out : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨8941⟩ (UInt256.ofNat out.size :: ⟨128⟩ :: R)
      (factoryOwnerOutputMem out) aw out σ k C)
    (hlen : 32 ≤ out.size) (hsize : out.size < UInt256.size) (ha : ActiveWords aw) (hov : R.length + 4 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ee.source ≠ AccountAddress.ofNat (fromByteArrayBigEndian (out.extract 0 32))) ∨
    (ee.source = AccountAddress.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ∧
      ∃ aw' k' C', ActiveWords aw' ∧ RD (deployedRuntime v) ee g s0 ⟨8963⟩ R
        (factoryOwnerOutputMem out) aw' out σ k' C') := by
  have hmask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (memLoad (⟨128⟩ : UInt256) (factoryOwnerOutputMem out)) =
      EVM.word (AccountAddress.ofNat (fromByteArrayBigEndian (out.extract 0 32))).val := by
    rw [factoryOwnerOutputMem_mload128 out hsize hlen]
    change UInt256.land solcAddrMask (calldataWord out 0) = _
    exact (factoryOwnerWord out hlen).symm
  by_cases howner : ee.source = AccountAddress.ofNat (fromByteArrayBigEndian (out.extract 0 32))
  · have rdValid := uniswapV3Pool_block_8941_taken (immWords := wordsOf (immStore v))
      hov (by rw [hmask]; change UInt256.eq (EVM.word ee.source.val) _ ≠ ⟨0⟩
              rw [howner, uInt256_eq_self]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact Or.inr ⟨howner, _, _, _, activeWords_expand32 ha (by decide), rdValid⟩
  · have hne : EVM.word ee.source.val ≠
        EVM.word (AccountAddress.ofNat (fromByteArrayBigEndian (out.extract 0 32))).val := by
      intro heq
      apply howner
      have ha := congrArg (fun word : UInt256 => AccountAddress.ofNat word.toNat) heq
      simpa only [accountAddress_of_word_val] using ha
    have rdInvalid := uniswapV3Pool_block_8941_fallthrough (immWords := wordsOf (immStore v))
      hov (by rw [hmask]; exact u256_eq_of_ne hne) rd
    simp only [uniswapV3Pool_block_8941_fallthrough_stack] at rdInvalid
    exact Or.inl ⟨uniswapV3Pool_block_8959 (immWords := wordsOf (immStore v))
      (by evm_ov) rdInvalid, howner⟩


end Benchmarks.UniswapV3.Pool
