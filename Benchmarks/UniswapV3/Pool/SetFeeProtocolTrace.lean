import Benchmarks.UniswapV3.Pool.SetFeeProtocolSource
import Benchmarks.UniswapV3.Pool.Calldata
import Benchmarks.UniswapV3.Pool.Slot0Storage
import Benchmarks.UniswapV3.Pool.FactoryOwner
import Benchmarks.UniswapV3.Pool.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks

namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem setFeeProtocolFactoryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw junk : UInt256} {rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨8385⟩
      (junk :: EVM.word v.factory.val :: ⟨128⟩ :: ⟨4⟩ :: ⟨128⟩ :: ⟨32⟩ ::
        ⟨132⟩ :: UInt256.ofNat 2376452955 :: EVM.word v.factory.val :: R)
      factoryOwnerInputMem aw rdata σ k C)
    (hacc : evm.accountMap = σ) (hσ₀ : evm.σ₀ = s0.σ₀) (henv : evm.executionEnv = ee)
    (hcode : extCodeSizeWord evm.accountMap (EVM.word v.factory.val) ≠ ⟨0⟩)
    (hov : R.length + 9 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config { contract := contract, locals := ∅, immutables := immStore v }
        evm factoryOwnerFunction.body .reverted) ∨
    ∃ (out : ByteArray) (σ' : AccountMap) (A' : Substate) (aw' : UInt256) (k' C' : Nat),
      32 ≤ out.size ∧ out.size < UInt256.size ∧
      ExecFuncBody config { contract := contract, locals := ∅, immutables := immStore v }
        evm factoryOwnerFunction.body
        (.returned (factoryOwnerCallFrame v true out) { evm with accountMap := σ', substate := A' }
          (some [.address (AccountAddress.ofNat (fromByteArrayBigEndian (out.extract 0 32)))])) ∧
      RD (deployedRuntime v) ee g s0 ⟨8427⟩ (UInt256.ofNat out.size :: ⟨128⟩ :: R)
        (factoryOwnerOutputMem out) aw' out σ' k' C' := by
  have rdCall := uniswapV3Pool_block_8385 (immWords := wordsOf (immStore v)) (by evm_ov) rd
  simp only [uniswapV3Pool_block_8385_stack] at rdCall
  obtain ⟨ok, out, σ', A', k', C', hcall, rdAfter, hsize⟩ :=
    RD.staticcallSource (evm := evm) rdCall
      (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8388⟩ : UInt256), (UInt8.ofNat 250), .STATICCALL, none,
        immutableLayout_inBounds, immutableTemplate_size64))
      (by evm_ov) hacc hσ₀ henv
  change callViaEVM evm (AccountAddress.ofUInt256 (EVM.word v.factory.val)) 0
    (factoryOwnerInputMem.readWithPadding 128 4)
    (ok, {evm with accountMap := σ', substate := A'}, out) false at hcall
  rw [show AccountAddress.ofUInt256 (EVM.word v.factory.val) = v.factory from
    accountAddress_roundtrip v.factory, factoryOwnerInputMem_read] at hcall
  change RD (deployedRuntime v) ee g s0 ⟨8389⟩
    ((if ok then ⟨1⟩ else ⟨0⟩) :: ⟨132⟩ :: UInt256.ofNat 2376452955 :: EVM.word v.factory.val :: R)
    (factoryOwnerOutputMem out) _ out σ' k' C' at rdAfter
  cases ok with
  | false =>
      have rdFail := uniswapV3Pool_block_8389_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide) rdAfter
      simp only [uniswapV3Pool_block_8389_fallthrough_stack] at rdFail
      exact Or.inl ⟨uniswapV3Pool_block_8396 (immWords := wordsOf (immStore v)) (by evm_ov) rdFail,
        factoryOwnerRevertsCall v evm _ out hcode hcall⟩
  | true =>
      have rdSize := uniswapV3Pool_block_8389_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdAfter
      simp only [uniswapV3Pool_block_8389_taken_stack] at rdSize
      by_cases hlen : 32 ≤ out.size
      · have rdOwner := uniswapV3Pool_block_8405_taken (immWords := wordsOf (immStore v))
          (by evm_ov)
          (by rw [ult_zero (by rw [UInt256.toNat_ofNat_of_lt hsize]; exact hlen)]; decide)
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdSize
        have hload : memLoad (UInt256.ofNat 64) (factoryOwnerOutputMem out) = ⟨128⟩ :=
          factoryOwnerOutputMem_mload64 out hsize
        simp only [uniswapV3Pool_block_8405_taken_stack, hload] at rdOwner
        exact Or.inr ⟨out, σ', A', _, _, _, hlen, hsize,
          factoryOwnerReturns v evm _ out hcode hcall hlen, rdOwner⟩
      · have hshort : out.size < 32 := by omega
        have rdShort := uniswapV3Pool_block_8405_fallthrough (immWords := wordsOf (immStore v))
          (by evm_ov)
          (by rw [ult_one (by rw [UInt256.toNat_ofNat_of_lt hsize]; exact hshort)]; decide) rdSize
        simp only [uniswapV3Pool_block_8405_fallthrough_stack] at rdShort
        exact Or.inl ⟨uniswapV3Pool_block_8423 (immWords := wordsOf (immStore v)) (by evm_ov) rdShort,
          factoryOwnerRevertsShort v evm _ out hcode hcall hshort⟩

theorem setFeeProtocolOwnerX {g : Sat256} {s0 evm : EVM.State} {k C : Nat}
    {aw : UInt256} {rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨8276⟩ R
      solcFreePtrMem aw rdata evm.accountMap k C)
    (hσ₀ : evm.σ₀ = s0.σ₀) (hperm : evm.executionEnv.perm = true)
    (hov : R.length + 11 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config { contract := contract, locals := ∅, immutables := immStore v }
        (storeSlot0Unlocked evm false) factoryOwnerFunction.body .reverted) ∨
    ∃ (out : ByteArray) (σ' : AccountMap) (A' : Substate) (aw' : UInt256) (k' C' : Nat),
      32 ≤ out.size ∧ out.size < UInt256.size ∧
      ExecFuncBody config { contract := contract, locals := ∅, immutables := immStore v }
        (storeSlot0Unlocked evm false) factoryOwnerFunction.body
        (.returned (factoryOwnerCallFrame v true out)
          { (storeSlot0Unlocked evm false) with accountMap := σ', substate := A' }
          (some [.address (AccountAddress.ofNat (fromByteArrayBigEndian (out.extract 0 32)))])) ∧
      RD (deployedRuntime v) evm.executionEnv g s0 ⟨8427⟩
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
  · obtain ⟨_, _, rdFail⟩ := uniswapV3Pool_block_8276_fallthrough
      (immWords := wordsOf (immStore v)) hov hperm
      (by rw [hfactory, ← hmap, hcode]; decide) rd
    simp only [uniswapV3Pool_block_8276_fallthrough_stack] at rdFail
    exact Or.inl ⟨uniswapV3Pool_block_8381 (immWords := wordsOf (immStore v)) (by evm_ov) rdFail,
      factoryOwnerRevertsNoCode v _ hcode⟩
  · obtain ⟨_, _, rdReady⟩ := uniswapV3Pool_block_8276_taken
      (immWords := wordsOf (immStore v)) hov hperm
      (by rw [hfactory, ← hmap, isZero_eq_zero_of_ne hcode]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_8276_taken_stack, uniswapV3Pool_block_8276_taken_memory,
      hfactory, hfree, show (⟨128⟩ : UInt256).toNat = 128 from rfl, hmem, hload,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 4 = ⟨4⟩ by native_decide,
      show (⟨128⟩ : UInt256) + UInt256.ofNat 4 = ⟨132⟩ by native_decide,
      ← hmap] at rdReady
    exact setFeeProtocolFactoryX (v := v) (evm := storeSlot0Unlocked evm false) rdReady rfl
      ((storeSlot0Unlocked_originalAccounts evm false).trans hσ₀)
      (storeSlot0Unlocked_executionEnv evm false) hcode (by omega)

theorem setFeeProtocolLockStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨8276⟩ R mem aw rdata σ k C)
    (hperm : ee.perm = false) (hov : R.length + 4 ≤ 1024) :
    RDstatic (deployedRuntime v) g s0 := by
  have rdLoad := evm_run rd with [
    raw jumpdest (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8276⟩ : UInt256), (UInt8.ofNat 91), .JUMPDEST, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw push1 (UInt256.ofNat 0) (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8277⟩ : UInt256), (UInt8.ofNat 96), .Push .PUSH1, some ((UInt256.ofNat 0), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw dup1 (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8279⟩ : UInt256), (UInt8.ofNat 128), .DUP1, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)]
  obtain ⟨_, _, rdLoaded⟩ :=
    RD.sload rdLoad (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8280⟩ : UInt256), (UInt8.ofNat 84), .SLOAD, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have rdStore := evm_run rdLoaded with [
    raw push1 (UInt256.ofNat 255) (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8281⟩ : UInt256), (UInt8.ofNat 96), .Push .PUSH1, some ((UInt256.ofNat 255), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw push1 (UInt256.ofNat 240) (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8283⟩ : UInt256), (UInt8.ofNat 96), .Push .PUSH1, some ((UInt256.ofNat 240), 1),
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw shl (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8285⟩ : UInt256), (UInt8.ofNat 27), .SHL, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw not (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8286⟩ : UInt256), (UInt8.ofNat 25), .NOT, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw and (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8287⟩ : UInt256), (UInt8.ofNat 22), .AND, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov),
    raw swap1 (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8288⟩ : UInt256), (UInt8.ofNat 144), .SWAP1, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)]
  exact rdStore.sstoreStatic hperm (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨8289⟩ : UInt256), (UInt8.ofNat 85), .SSTORE, none,
        immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

theorem setFeeProtocolReadLockX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨8208⟩ R mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ slot0FieldWord 30 1 σ ee = ⟨0⟩) ∨
      (slot0FieldWord 30 1 σ ee ≠ ⟨0⟩ ∧
        ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨8276⟩ R mem aw rdata σ k' C') := by
  have hfield : UInt256.land (UInt256.ofNat 255)
      (UInt256.div
        (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256)))
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240))) =
      slot0FieldWord 30 1 σ ee := (slot0FieldWord_unlocked_evm σ ee).symm
  by_cases hlocked : slot0FieldWord 30 1 σ ee = ⟨0⟩
  · obtain ⟨_, _, rdFail⟩ := uniswapV3Pool_block_8208_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) (by rw [hfield]; exact hlocked) rd
    exact Or.inl ⟨uniswapV3Pool_block_8226 (immWords := wordsOf (immStore v)) hov rdFail, hlocked⟩
  · exact Or.inr ⟨hlocked, uniswapV3Pool_block_8208_taken (immWords := wordsOf (immStore v))
      (by omega) (by rw [hfield]; exact hlocked)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩

theorem uniswapV3PoolSetFeeProtocolDecodedX {σ σ₀ A I} {g : Sat256}
    (v : UniswapV3PoolImmutables) (hcode : I.code = deployedRuntime v)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (uniswapV3PoolSelBytes 14))
    (hlen : 68 ≤ I.calldata.size) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨8208⟩
      [UInt256.land (calldataWord I.calldata 36) (UInt256.ofNat 255),
       UInt256.land (calldataWord I.calldata 4) (UInt256.ofNat 255),
       UInt256.ofNat 857, solcSelectorWord I] solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C := by
  obtain ⟨k, C, rdEntry⟩ := uniswapV3PoolReachSetFeeProtocolBody
    (g := g) (σ := σ) (σ₀ := σ₀) (A := A) v hcode hwv hsz hsize hsel
  have rdDecode := uniswapV3Pool_block_1486_taken (immWords := wordsOf (immStore v))
    (by simp) (by rw [solcDecodeLenCheckOkUnsigned (by exact hlen) hsize]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEntry
  simp only [uniswapV3Pool_block_1486_taken_stack] at rdDecode
  have rdRead := uniswapV3Pool_block_1508 (immWords := wordsOf (immStore v)) (by simp)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdDecode
  simp only [uniswapV3Pool_block_1508_stack] at rdRead
  change RD (deployedRuntime v) I g (initState σ σ₀ g A I) ⟨8208⟩
      [UInt256.land (calldataWord I.calldata 36) (UInt256.ofNat 255),
       UInt256.land (UInt256.ofNat 255) (calldataWord I.calldata 4),
       UInt256.ofNat 857, solcSelectorWord I] solcFreePtrMem ⟨3⟩ ByteArray.empty σ _ _ at rdRead
  rw [u256_land_comm (UInt256.ofNat 255)] at rdRead
  exact ⟨_, _, rdRead⟩

theorem uniswapV3PoolSetFeeProtocolShortX {σ σ₀ A I} {g : Sat256}
    (v : UniswapV3PoolImmutables) (hcode : I.code = deployedRuntime v)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (uniswapV3PoolSelBytes 14))
    (hshort : I.calldata.size < 68) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rdEntry⟩ := uniswapV3PoolReachSetFeeProtocolBody
    (g := g) (σ := σ) (σ₀ := σ₀) (A := A) v hcode hwv hsz hsize hsel
  have rdShort := uniswapV3Pool_block_1486_fallthrough (immWords := wordsOf (immStore v))
    (by simp)
    (by rw [solcDecodeLenCheckShortUnsigned (by exact hsz) (by exact hshort) hsize]; decide) rdEntry
  simp only [uniswapV3Pool_block_1486_fallthrough_stack] at rdShort
  exact uniswapV3Pool_block_1504 (immWords := wordsOf (immStore v)) (by simp) rdShort

theorem setFeeProtocolOwnerGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {out : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨8427⟩ (UInt256.ofNat out.size :: ⟨128⟩ :: R)
      (factoryOwnerOutputMem out) aw out σ k C)
    (hlen : 32 ≤ out.size) (hsize : out.size < UInt256.size) (hov : R.length + 4 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ee.source ≠ AccountAddress.ofNat (fromByteArrayBigEndian (out.extract 0 32))) ∨
    (ee.source = AccountAddress.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ∧
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨8449⟩ R
        (factoryOwnerOutputMem out) aw' out σ k' C') := by
  have hmask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (memLoad (⟨128⟩ : UInt256) (factoryOwnerOutputMem out)) =
      EVM.word (AccountAddress.ofNat (fromByteArrayBigEndian (out.extract 0 32))).val := by
    rw [factoryOwnerOutputMem_mload128 out hsize hlen]
    change UInt256.land solcAddrMask (calldataWord out 0) = _
    exact (factoryOwnerWord out hlen).symm
  by_cases howner : ee.source = AccountAddress.ofNat (fromByteArrayBigEndian (out.extract 0 32))
  · have rdValid := uniswapV3Pool_block_8427_taken (immWords := wordsOf (immStore v))
      hov (by rw [hmask]; change UInt256.eq (EVM.word ee.source.val) _ ≠ ⟨0⟩
              rw [howner, uInt256_eq_self]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    exact Or.inr ⟨howner, _, _, _, rdValid⟩
  · have hne : EVM.word ee.source.val ≠
        EVM.word (AccountAddress.ofNat (fromByteArrayBigEndian (out.extract 0 32))).val := by
      intro heq
      apply howner
      have ha := congrArg (fun word : UInt256 => AccountAddress.ofNat word.toNat) heq
      simpa only [accountAddress_of_word_val] using ha
    have rdInvalid := uniswapV3Pool_block_8427_fallthrough (immWords := wordsOf (immStore v))
      hov (by rw [hmask]; exact u256_eq_of_ne hne) rd
    simp only [uniswapV3Pool_block_8427_fallthrough_stack] at rdInvalid
    exact Or.inl ⟨uniswapV3Pool_block_8445 (immWords := wordsOf (immStore v))
      (by evm_ov) rdInvalid, howner⟩

theorem setFeeProtocolValue_evm (fp0 fp1 : UInt256)
    (h0 : fp0.toNat ≤ 10) (h1 : fp1.toNat ≤ 10) :
    fp0 + UInt256.land (UInt256.shiftLeft fp1 (UInt256.ofNat 4)) (UInt256.ofNat 4080) =
      setFeeProtocolValue fp0 fp1 := by
  rw [show (4080 : Nat) = (2 ^ 8 - 1) * 2 ^ 4 by decide,
    shiftLeft_land_mask fp1 8 4 (by decide) (by decide) (by change fp1.toNat < 256; omega)]
  apply u256_inj
  rw [setFeeProtocolValue_toNat fp0 fp1 h0 h1, uadd_toNat,
    shiftLeft_toNat_of_noOverflow fp1 (UInt256.ofNat 4) (by decide)
      (by change fp1.toNat * 16 < 2 ^ 256; omega)]
  change (fp0.toNat + fp1.toNat * 16) % (2 ^ 256) = fp0.toNat + 16 * fp1.toNat
  rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm fp1.toNat]

theorem setFeeProtocolStoreX {g : Sat256} {s0 evm : EVM.State} {k C : Nat}
    {aw fp0 fp1 : UInt256} {mem rdata : ByteArray} {R : List UInt256}
    {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨8535⟩
      (fp1 :: fp0 :: ⟨857⟩ :: R) mem aw rdata evm.accountMap k C)
    (hperm : evm.executionEnv.perm = true)
    (h0 : fp0.toNat ≤ 10) (h1 : fp1.toNat ≤ 10) (hov : R.length + 11 ≤ 1024) :
    RDret (deployedRuntime v) g s0
      (storeSlot0Unlocked (storeSlot0FeeProtocol evm (setFeeProtocolValue fp0 fp1)) true).accountMap
      ByteArray.empty := by
  obtain ⟨k', C', rdStored⟩ := uniswapV3Pool_block_8535 (immWords := wordsOf (immStore v))
    (by evm_ov) hperm rd
  rw [setFeeProtocolValue_evm fp0 fp1 h0 h1] at rdStored
  have hmap := storeSlot0FeeProtocol_accountMap evm (setFeeProtocolValue fp0 fp1)
  change (storeSlot0FeeProtocol evm (setFeeProtocolValue fp0 fp1)).accountMap =
    sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap (UInt256.ofNat 0)
      (slot0FeeProtocolWord
        (evm.accountMap.get? evm.executionEnv.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac => ac.storage.getD (UInt256.ofNat 0) ⟨0⟩)) (setFeeProtocolValue fp0 fp1)) at hmap
  simp only [slot0FeeProtocolWord] at hmap
  rw [← hmap] at rdStored
  simp only [uniswapV3Pool_block_8535_stack] at rdStored
  obtain ⟨k'', C'', rdStop⟩ := uniswapV3Pool_block_8676 (immWords := wordsOf (immStore v))
    (by evm_ov) hperm
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdStored
  have hmap' := storeSlot0Unlocked_accountMap
    (storeSlot0FeeProtocol evm (setFeeProtocolValue fp0 fp1)) true
  rw [storeSlot0FeeProtocol_executionEnv, slot0UnlockedWord_true] at hmap'
  change (storeSlot0Unlocked (storeSlot0FeeProtocol evm (setFeeProtocolValue fp0 fp1)) true).accountMap =
    sstoreAccountMap evm.executionEnv.codeOwner
      (storeSlot0FeeProtocol evm (setFeeProtocolValue fp0 fp1)).accountMap (UInt256.ofNat 0)
      (UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240))
        (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 240)))
          ((storeSlot0FeeProtocol evm (setFeeProtocolValue fp0 fp1)).accountMap.get?
            evm.executionEnv.codeOwner |>.option (⟨0⟩ : UInt256)
              (fun ac => ac.storage.getD (UInt256.ofNat 0) ⟨0⟩)))) at hmap'
  rw [← hmap'] at rdStop
  simp only [uniswapV3Pool_block_8676_stack] at rdStop
  exact uniswapV3Pool_block_857 (immWords := wordsOf (immStore v)) (by evm_ov) rdStop

theorem feeProtocolEvmCases (word : UInt256) :
    (word = ⟨0⟩ ∧ feeProtocolValid word = true) ∨
    (word ≠ ⟨0⟩ ∧ UInt256.lt word (UInt256.ofNat 4) = ⟨1⟩ ∧ feeProtocolValid word = false) ∨
    (word ≠ ⟨0⟩ ∧ UInt256.lt word (UInt256.ofNat 4) = ⟨0⟩ ∧
      UInt256.isZero (UInt256.gt word (UInt256.ofNat 10)) = (feeProtocolValid word).toUInt256) := by
  by_cases hz : word = ⟨0⟩
  · exact Or.inl ⟨hz, by rw [hz]; decide⟩
  have hnz : word.toNat ≠ 0 := fun h => hz (uint256_toNat_eq_zero h)
  by_cases hlo : word.toNat < 4
  · refine Or.inr (Or.inl ⟨hz, ult_one hlo, ?_⟩)
    simp only [feeProtocolValid, decide_eq_false_iff_not]
    omega
  · refine Or.inr (Or.inr ⟨hz, ult_zero (by change 4 ≤ word.toNat; omega), ?_⟩)
    by_cases hhi : word.toNat ≤ 10
    · rw [ugt_zero hhi]
      have hv : feeProtocolValid word = true := by
        simp only [feeProtocolValid, decide_eq_true_eq]; omega
      rw [hv]; rfl
    · rw [ugt_one (by change 10 < word.toNat; omega)]
      have hv : feeProtocolValid word = false := by
        simp only [feeProtocolValid, decide_eq_false_iff_not]; omega
      rw [hv]; rfl

theorem setFeeProtocolFirstFeeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw fp0 fp1 : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨8449⟩ (fp1 :: fp0 :: R) mem aw rdata σ k C)
    (hclean : UInt256.land fp0 (UInt256.ofNat 255) = fp0) (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨8484⟩
      ((feeProtocolValid fp0).toUInt256 :: fp1 :: fp0 :: R) mem aw rdata σ k' C' := by
  have hclean' : UInt256.land (UInt256.ofNat 255) fp0 = fp0 := by
    rw [u256_land_comm]; exact hclean
  rcases feeProtocolEvmCases fp0 with ⟨hz, hv⟩ | ⟨hnz, hlo, hv⟩ | ⟨hnz, hlo, hflag⟩
  · have rdZero := uniswapV3Pool_block_8449_taken (immWords := wordsOf (immStore v)) hov
      (by rw [hclean, hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_8449_taken_stack, hclean] at rdZero
    rw [hv]
    rw [hz] at rdZero ⊢
    exact ⟨_, _, rdZero⟩
  · have rdLower := uniswapV3Pool_block_8449_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [hclean, isZero_eq_zero_of_ne hnz]; rfl) rd
    simp only [uniswapV3Pool_block_8449_fallthrough_stack] at rdLower
    have rdBad := uniswapV3Pool_block_8460_taken (immWords := wordsOf (immStore v)) hov
      (by rw [hclean', hlo]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdLower
    simp only [uniswapV3Pool_block_8460_taken_stack, hclean', hlo] at rdBad
    rw [hv]
    exact ⟨_, _, rdBad⟩
  · have rdLower := uniswapV3Pool_block_8449_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [hclean, isZero_eq_zero_of_ne hnz]; rfl) rd
    simp only [uniswapV3Pool_block_8449_fallthrough_stack] at rdLower
    have rdUpper := uniswapV3Pool_block_8460_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [hclean', hlo]; decide) rdLower
    simp only [uniswapV3Pool_block_8460_fallthrough_stack] at rdUpper
    have rdFlag := uniswapV3Pool_block_8475 (immWords := wordsOf (immStore v)) hov rdUpper
    simp only [uniswapV3Pool_block_8475_stack, hclean', hflag] at rdFlag
    exact ⟨_, _, rdFlag⟩

theorem setFeeProtocolSecondFeeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw flag fp1 : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨8491⟩ (flag :: fp1 :: R) mem aw rdata σ k C)
    (hclean : UInt256.land fp1 (UInt256.ofNat 255) = fp1) (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨8526⟩
      ((feeProtocolValid fp1).toUInt256 :: fp1 :: R) mem aw rdata σ k' C' := by
  have hclean' : UInt256.land (UInt256.ofNat 255) fp1 = fp1 := by
    rw [u256_land_comm]; exact hclean
  rcases feeProtocolEvmCases fp1 with ⟨hz, hv⟩ | ⟨hnz, hlo, hv⟩ | ⟨hnz, hlo, hflag⟩
  · have rdZero := uniswapV3Pool_block_8491_taken (immWords := wordsOf (immStore v)) hov
      (by rw [hclean, hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_8491_taken_stack, hclean] at rdZero
    rw [hv]
    rw [hz] at rdZero ⊢
    exact ⟨_, _, rdZero⟩
  · have rdLower := uniswapV3Pool_block_8491_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [hclean, isZero_eq_zero_of_ne hnz]; rfl) rd
    simp only [uniswapV3Pool_block_8491_fallthrough_stack] at rdLower
    have rdBad := uniswapV3Pool_block_8502_taken (immWords := wordsOf (immStore v)) hov
      (by rw [hclean', hlo]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdLower
    simp only [uniswapV3Pool_block_8502_taken_stack, hclean', hlo] at rdBad
    rw [hv]
    exact ⟨_, _, rdBad⟩
  · have rdLower := uniswapV3Pool_block_8491_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [hclean, isZero_eq_zero_of_ne hnz]; rfl) rd
    simp only [uniswapV3Pool_block_8491_fallthrough_stack] at rdLower
    have rdUpper := uniswapV3Pool_block_8502_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [hclean', hlo]; decide) rdLower
    simp only [uniswapV3Pool_block_8502_fallthrough_stack] at rdUpper
    have rdFlag := uniswapV3Pool_block_8517 (immWords := wordsOf (immStore v)) hov rdUpper
    simp only [uniswapV3Pool_block_8517_stack, hclean', hflag] at rdFlag
    exact ⟨_, _, rdFlag⟩

theorem setFeeProtocolValidX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw fp0 fp1 : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨8449⟩ (fp1 :: fp0 :: R) mem aw rdata σ k C)
    (hclean0 : UInt256.land fp0 (UInt256.ofNat 255) = fp0)
    (hclean1 : UInt256.land fp1 (UInt256.ofNat 255) = fp1) (hov : R.length + 5 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ (feeProtocolValid fp0 && feeProtocolValid fp1) = false) ∨
    ((feeProtocolValid fp0 && feeProtocolValid fp1) = true ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨8535⟩ (fp1 :: fp0 :: R)
        mem aw rdata σ k' C') := by
  obtain ⟨k0, C0, rdFirst⟩ := setFeeProtocolFirstFeeX (v := v) rd hclean0 hov
  have rdBoth : ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨8526⟩
      ((feeProtocolValid fp0 && feeProtocolValid fp1).toUInt256 :: fp1 :: fp0 :: R)
      mem aw rdata σ k' C' := by
    cases hvalid0 : feeProtocolValid fp0 with
    | false =>
        rw [hvalid0] at rdFirst
        have rdBad := uniswapV3Pool_block_8484_taken (immWords := wordsOf (immStore v))
          (by evm_ov) (by decide)
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdFirst
        exact ⟨_, _, rdBad⟩
    | true =>
        rw [hvalid0] at rdFirst
        have rdSecond := uniswapV3Pool_block_8484_fallthrough (immWords := wordsOf (immStore v))
          (by evm_ov) (by decide) rdFirst
        exact setFeeProtocolSecondFeeX (v := v) rdSecond hclean1 (by evm_ov)
  obtain ⟨kb, Cb, rdFlag⟩ := rdBoth
  cases hvalid : (feeProtocolValid fp0 && feeProtocolValid fp1) with
  | false =>
      rw [hvalid] at rdFlag
      have rdRevert := uniswapV3Pool_block_8526_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide) rdFlag
      simp only [uniswapV3Pool_block_8526_fallthrough_stack] at rdRevert
      exact Or.inl ⟨uniswapV3Pool_block_8531 (immWords := wordsOf (immStore v))
        (by evm_ov) rdRevert, rfl⟩
  | true =>
      rw [hvalid] at rdFlag
      have rdSuccess := uniswapV3Pool_block_8526_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdFlag
      exact Or.inr ⟨rfl, _, _, rdSuccess⟩

end Benchmarks.UniswapV3.Pool
