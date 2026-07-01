import Examples.VyperERC20.TotalSupply
import Examples.VyperERC20.Storage
import Examples.ERC20.Common
import Reasoning.Refinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

abbrev balanceOfOwnerWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev balanceOfOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (balanceOfOwnerWord I).toNat)

abbrev balanceOfStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "owner" (balanceOfOwnerValue I)

def balanceOfSlot (I : ExecutionEnv) : UInt256 :=
  erc20BalanceOfSlot (.address (AccountAddress.ofNat (balanceOfOwnerWord I).toNat))

def balanceOfWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (balanceOfSlot I) ⟨0⟩)

def balanceOfSelectorWord : UInt256 :=
  ⟨0x70a08231⟩

theorem balanceOfOwnerWord_eq_readBytes (I : ExecutionEnv) :
    uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32) =
      balanceOfOwnerWord I := by
  rfl

theorem u256_shiftRight160_zero_of_lt (w : UInt256)
    (h : w.toNat < EVM.addressModulus) :
    UInt256.shiftRight w ⟨160⟩ = ⟨0⟩ := by
  apply u256_inj
  cases w with
  | mk val =>
    unfold UInt256.shiftRight
    simp
    change (val >>> 160).val = 0
    rw [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow]
    apply Nat.div_eq_of_lt
    simpa [EVM.addressModulus] using h

theorem erc20Decode_balanceOf_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper (ERC20.balanceOfTransition.params.map Param.name)
      (transitionSignature ERC20.balanceOfTransition).paramTypes I.calldata =
        some (balanceOfStore I) := by
  show decodeCalldataWithMode DecodeMode.vyper ["owner"] [addr] I.calldata = _
  simpa [balanceOfStore, balanceOfOwnerValue, balanceOfOwnerWord, addr]
    using decodeCalldataWithMode_vyper_address_ok (cd := I.calldata) (x := "owner")
      hsz36 hcanon

theorem erc20Decode_balanceOf_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode DecodeMode.vyper (ERC20.balanceOfTransition.params.map Param.name)
      (transitionSignature ERC20.balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.vyper ["owner"] [addr] I.calldata = none
  simpa [addr]
    using decodeCalldataWithMode_vyper_address_none_short
      (cd := I.calldata) (x := "owner") hsz4 hshort

theorem erc20Decode_balanceOf_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hnc : ¬ (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode DecodeMode.vyper (ERC20.balanceOfTransition.params.map Param.name)
      (transitionSignature ERC20.balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.vyper ["owner"] [addr] I.calldata = none
  simpa [addr, balanceOfOwnerWord, calldataWord]
    using decodeCalldataWithMode_vyper_address_none_noncanon
      (cd := I.calldata) (x := "owner") hsz36 hnc

theorem erc20BalanceOfBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody vyperERC20Config erc20Contract evm (balanceOfStore I)
      ERC20.balanceOfTransition.body
      (.returned { contract := erc20Contract, locals := balanceOfStore I } evm
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (balanceOfSlot I)).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (hbase := by simp [balanceOfStore, balanceOfRef, ERC20.balanceOfRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, balanceOfRef, ERC20.balanceOfRef,
            balanceOfStore, balanceOfOwnerValue, valueToKey?, EvalResult.seqList,
            EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?])
        (hty := by simp [storageTypeAt?, erc20Contract, ERC20.erc20Contract,
          ERC20.erc20StorageDecls, uint256Storage, ERC20.uint256Storage, storageTypeStep?])
        (hloc := vyperERC20Config_storage_balanceOf
          (.address (AccountAddress.ofNat (balanceOfOwnerWord I).toNat)))]
      rw [show erc20BalanceOfSlot
            (KeyValue.address (AccountAddress.ofNat (balanceOfOwnerWord I).toNat)) =
          balanceOfSlot I from rfl]
      rw [vyperERC20StorageLocLoad_uint256])

def balanceOfDispatchMem : ByteArray :=
  vyperERC20Bytecode.write 805 ByteArray.empty 30 2

theorem balanceOfDispatchMem_size : balanceOfDispatchMem.size = 32 := by
  native_decide

def balanceOfOwnerArgMem (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray owner).write 0 balanceOfDispatchMem 64 32

noncomputable def balanceOfKeyMem (owner : UInt256) : ByteArray :=
  wordAt32Mem owner (balanceOfOwnerArgMem owner)

noncomputable def balanceOfHashMem (owner : UInt256) : ByteArray :=
  wordAt0Mem ⟨0⟩ (balanceOfKeyMem owner)

noncomputable def balanceOfReturnMem (owner val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 (balanceOfHashMem owner) 96 32

theorem balanceOfOwnerArgMem_size (owner : UInt256) :
    (balanceOfOwnerArgMem owner).size = 96 := by
  unfold balanceOfOwnerArgMem
  rw [toByteArray_write_eq _ _ _ (by rw [balanceOfDispatchMem_size]; omega)
      (by rw [balanceOfDispatchMem_size]; exact lt_usize 32 (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, balanceOfDispatchMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (64 - 32)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem balanceOfKeyMem_size (owner : UInt256) :
    (balanceOfKeyMem owner).size = 96 := by
  unfold balanceOfKeyMem
  exact wordAt32Mem_size_96 owner (balanceOfOwnerArgMem_size owner)

theorem balanceOfHashMem_size (owner : UInt256) :
    (balanceOfHashMem owner).size = 96 := by
  unfold balanceOfHashMem
  exact wordAt0Mem_size_96 ⟨0⟩ (balanceOfKeyMem_size owner)

theorem balanceOfKeyMem_read32 (owner : UInt256) :
    (balanceOfKeyMem owner).readWithPadding 32 32 = UInt256.toByteArray owner := by
  unfold balanceOfKeyMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [balanceOfOwnerArgMem_size owner]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray owner).size ≤ 32
    rw [toByteArray_size])

theorem balanceOfHashMem_read0 (owner : UInt256) :
    (balanceOfHashMem owner).readWithPadding 0 32 = UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold balanceOfHashMem
  exact wordAt0Mem_read0 ⟨0⟩ (balanceOfKeyMem owner)

theorem balanceOfHashMem_read32 (owner : UInt256) :
    (balanceOfHashMem owner).readWithPadding 32 32 = UInt256.toByteArray owner := by
  unfold balanceOfHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
    (by rw [balanceOfKeyMem_size owner]; omega)
    (by omega)
    (by rw [balanceOfKeyMem_size owner]; omega)]
  exact balanceOfKeyMem_read32 owner

theorem balanceOfHashMem_read0_64 (owner : UInt256) :
    (balanceOfHashMem owner).readWithPadding 0 64 =
      UInt256.toByteArray (⟨0⟩ : UInt256) ++ UInt256.toByteArray owner := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [balanceOfHashMem_size owner]; omega)]
  have hleft :
      (balanceOfHashMem owner).extract 0 32 = UInt256.toByteArray (⟨0⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [balanceOfHashMem_size owner]; omega),
      balanceOfHashMem_read0 owner]
  have hright :
      (balanceOfHashMem owner).extract 32 64 = UInt256.toByteArray owner := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [balanceOfHashMem_size owner]; omega),
      balanceOfHashMem_read32 owner]
  rw [show (balanceOfHashMem owner).extract 0 64 =
      (balanceOfHashMem owner).extract 0 32 ++
        (balanceOfHashMem owner).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem balanceOfKeccakSlot (I : ExecutionEnv)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((balanceOfHashMem (balanceOfOwnerWord I)).readWithPadding 0 64)))
      = balanceOfSlot I := by
  rw [balanceOfHashMem_read0_64]
  unfold balanceOfSlot erc20BalanceOfSlot vyperMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]
  exact keccakSlot_eq _

theorem balanceOfReturnMem_size (owner val : UInt256) :
    (balanceOfReturnMem owner val).size = 128 := by
  unfold balanceOfReturnMem
  simpa [balanceOfHashMem_size] using
    write_end_size_from (UInt256.toByteArray val) (balanceOfHashMem owner) 0 32
      (by decide)
      (by rw [toByteArray_size])

theorem balanceOfReturnMem_read96 (owner val : UInt256) :
    (balanceOfReturnMem owner val).readWithPadding 96 32 = UInt256.toByteArray val := by
  unfold balanceOfReturnMem
  exact toByteArray_write_read_back_of_gap val (balanceOfHashMem owner) 96
    (by rw [balanceOfHashMem_size]; exact lt_usize 0 (by norm_num))

macro "vyper_erc20_balance_decode" : tactic =>
  `(tactic| native_decide)

theorem erc20X_balanceOfFromEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨623⟩
      [balanceOfSelectorWord] balanceOfDispatchMem (UInt256.ofNat 1) ByteArray.empty (cA, σ) k C) :
    RDret vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (balanceOfWord σ I)) := by
  obtain ⟨k, C, rd623⟩ := hreach
  have hslot := balanceOfKeccakSlot I hcanon
  have hsizeGuard : UInt256.lt (UInt256.ofNat I.calldata.size) ⟨36⟩ = ⟨0⟩ := by
    have hnot : ¬ (UInt256.ofNat I.calldata.size < (⟨36⟩ : UInt256)) := by
      intro hlt
      have hltNat :
          (UInt256.ofNat I.calldata.size).toNat < (⟨36⟩ : UInt256).toNat := hlt
      have hn : (UInt256.ofNat I.calldata.size).toNat = I.calldata.size := by
        unfold UInt256.toNat UInt256.ofNat
        simp only [Id.run]
        exact Nat.mod_eq_of_lt hsize
      rw [hn] at hltNat
      change I.calldata.size < 36 at hltNat
      omega
    unfold UInt256.lt UInt256.fromBool Bool.toUInt256
    rw [show decide (UInt256.ofNat I.calldata.size < (⟨36⟩ : UInt256)) = false from by
      exact decide_eq_false hnot]
    native_decide
  have hcanonGuard : UInt256.shiftRight (balanceOfOwnerWord I) ⟨160⟩ = ⟨0⟩ :=
    u256_shiftRight160_zero_of_lt (balanceOfOwnerWord I) hcanon
  have rdBeforeLoad := evm_run rd623 with [
    jumpdest,
    raw push4 balanceOfSelectorWord (by vyper_erc20_balance_decode) (by evm_ov),
    dup2,
    xor,
    push2 ⟨797⟩,
    jumpiNT (by native_decide),
    push1 ⟨36⟩,
    calldatasize,
    lt,
    callvalue,
    lor,
    push2 ⟨801⟩,
    jumpiNT (by rw [hsizeGuard, hwv]; decide),
    push1 ⟨4⟩,
    calldataload,
    dup1,
    push1 ⟨160⟩,
    shr,
    push2 ⟨801⟩,
    jumpiNT (by simpa [balanceOfOwnerWord, calldataWord] using hcanonGuard),
    push1 ⟨64⟩,
    raw mstore 6 (balanceOfOwnerArgMem (balanceOfOwnerWord I)) (UInt256.ofNat 3)
      (by vyper_erc20_balance_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    push1 ⟨64⟩,
    raw mload 0 (balanceOfOwnerWord I) (UInt256.ofNat 3)
      (by vyper_erc20_balance_decode)
      mem_cost
      (by
        exact mloadWordValue_of_readWithPadding
          (mem := balanceOfOwnerArgMem (balanceOfOwnerWord I)) (aw := UInt256.ofNat 3)
          (off := ⟨64⟩) (v := balanceOfOwnerWord I)
          (by rw [balanceOfOwnerArgMem_size]; decide)
          (by decide)
          (by
            unfold balanceOfOwnerArgMem
            exact toByteArray_write_read_back_of_gap (balanceOfOwnerWord I) balanceOfDispatchMem 64
              (by rw [balanceOfDispatchMem_size]; exact lt_usize 32 (by norm_num))))
      (by decide) (by evm_ov),
    push1 ⟨32⟩,
    raw mstore 0 (balanceOfKeyMem (balanceOfOwnerWord I)) (UInt256.ofNat 3)
      (by vyper_erc20_balance_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    raw mstore 0 (balanceOfHashMem (balanceOfOwnerWord I)) (UInt256.ofNat 3)
      (by vyper_erc20_balance_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push1 ⟨64⟩,
    push0,
    raw keccak256 0 (balanceOfSlot I) (UInt256.ofNat 3)
      (by vyper_erc20_balance_decode)
      mem_cost
      hslot
      (by decide) (by evm_ov)]
  obtain ⟨k1, C1, rdAfterLoad⟩ :=
    rdBeforeLoad.sload (by vyper_erc20_balance_decode) (by evm_ov)
  have rdBeforeReturn := evm_run rdAfterLoad with [
    push1 ⟨96⟩,
    raw mstore 3 (balanceOfReturnMem (balanceOfOwnerWord I) (balanceOfWord σ I)) (UInt256.ofNat 4)
      (by vyper_erc20_balance_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push1 ⟨32⟩,
    push1 ⟨96⟩]
  exact rdBeforeReturn.ret 0 (UInt256.toByteArray (balanceOfWord σ I))
    (by vyper_erc20_balance_decode)
    mem_cost
    (balanceOfReturnMem_read96 (balanceOfOwnerWord I) (balanceOfWord σ I))
    (by evm_ov)

theorem erc20BalanceOfSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem balanceOfSelectorWord_of_calldata {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size)
    (hsel : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ =
      balanceOfSelectorWord := by
  have h := evmSelectorDecode hsz 0x70 0xa0 0x82 0x31 balanceOfSelectorWord (by native_decide)
  rw [hsel] at h
  unfold UInt256.eq at h
  by_cases heq :
      balanceOfSelectorWord =
        UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩
  · exact heq.symm
  · simp [heq] at h
    have hne : UInt256.ofNat 0 ≠ (⟨1⟩ : UInt256) := by decide
    exact False.elim (hne h)

theorem balanceOfDispatchMem_mload0 :
    (if (⟨0⟩ : UInt256).toNat ≥ balanceOfDispatchMem.size ∨
        (⟨0⟩ : UInt256) ≥ (UInt256.ofNat 1) * ⟨32⟩
      then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (balanceOfDispatchMem.readWithPadding (⟨0⟩ : UInt256).toNat 32)))
      = (⟨623⟩ : UInt256) := by
  native_decide

theorem erc20X_balanceOfReach {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vyperERC20Bytecode)
    (hsel : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨623⟩
      [balanceOfSelectorWord] balanceOfDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C := by
  have hsz := erc20BalanceOfSelector_size hsel
  have hword := balanceOfSelectorWord_of_calldata (I := I) hsz hsel
  have rd0 := RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
  have rdBeforeCopy0 := evm_run rd0 with [
    push0,
    calldataload,
    push1 ⟨224⟩,
    shr,
    push1 ⟨2⟩,
    push1 ⟨7⟩,
    dup3,
    mod,
    push1 ⟨1⟩,
    shl,
    push2 ⟨805⟩,
    add,
    push1 ⟨30⟩]
  have rdBeforeCopy := by
    simpa [hword, balanceOfSelectorWord] using rdBeforeCopy0
  have rdAfterCopy := rdBeforeCopy.codecopy 3 balanceOfDispatchMem (UInt256.ofNat 1)
    (by vyper_erc20_balance_decode)
    mem_cost
    (by native_decide)
    (by decide)
    (by evm_ov)
  have rdBeforeJump := evm_run rdAfterCopy with [
    push0,
    raw mload 0 ⟨623⟩ (UInt256.ofNat 1)
      (by vyper_erc20_balance_decode)
      mem_cost
      balanceOfDispatchMem_mload0
      (by decide) (by evm_ov)]
  exact ⟨_, _, rdBeforeJump.jump (by vyper_erc20_balance_decode) (by native_decide) (by evm_ov)⟩

theorem erc20BalanceOfX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨623⟩
      [balanceOfSelectorWord] balanceOfDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd623⟩ := hreach
  have hsizeGuard := calldataSizeGuardShort (n := I.calldata.size) (m := 36)
    hsize (by norm_num [UInt256.size]) hshort
  have hsizeGuard36 : UInt256.lt (UInt256.ofNat I.calldata.size) ⟨36⟩ = ⟨1⟩ := by
    simpa using hsizeGuard
  have rd801 := evm_run rd623 with [
    jumpdest,
    raw push4 balanceOfSelectorWord (by vyper_erc20_balance_decode) (by evm_ov),
    dup2,
    xor,
    push2 ⟨797⟩,
    jumpiNT (by native_decide),
    push1 ⟨36⟩,
    calldatasize,
    lt,
    callvalue,
    lor,
    push2 ⟨801⟩,
    jumpiT (by rw [hwv, hsizeGuard36]; decide) (by vyper_erc20_balance_decode)]
  exact vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) rd801 rfl (by norm_num)

theorem erc20BalanceOfX_noncanon_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hnc : ¬ (balanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨623⟩
      [balanceOfSelectorWord] balanceOfDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ) k C) :
    RDrev vyperERC20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd623⟩ := hreach
  have hsizeGuard := calldataSizeGuardOk (n := I.calldata.size) (m := 36) hsz36 hsize
  have hsizeGuard36 : UInt256.lt (UInt256.ofNat I.calldata.size) ⟨36⟩ = ⟨0⟩ := by
    simpa using hsizeGuard
  have hcanonGuard : UInt256.shiftRight (balanceOfOwnerWord I) ⟨160⟩ ≠ ⟨0⟩ := by
    intro hzero
    exact hnc (u256_lt_addressModulus_of_shiftRight160_zero (balanceOfOwnerWord I) hzero)
  have rd801 := evm_run rd623 with [
    jumpdest,
    raw push4 balanceOfSelectorWord (by vyper_erc20_balance_decode) (by evm_ov),
    dup2,
    xor,
    push2 ⟨797⟩,
    jumpiNT (by native_decide),
    push1 ⟨36⟩,
    calldatasize,
    lt,
    callvalue,
    lor,
    push2 ⟨801⟩,
    jumpiNT (by rw [hwv, hsizeGuard36]; decide),
    push1 ⟨4⟩,
    calldataload,
    dup1,
    push1 ⟨160⟩,
    shr,
    push2 ⟨801⟩,
    jumpiT (by
      simp [balanceOfOwnerWord, calldataWord]
      exact hcanonGuard) (by vyper_erc20_balance_decode)]
  exact vyperRuntimeRevert801 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) rd801 rfl (by simp only [List.length_cons, List.length_nil]; omega)

theorem erc20Dispatch_balanceOf {cd : ByteArray}
    (hsel : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg erc20Contract cd = some ERC20.balanceOfTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split (contract := erc20Contract)
    (pre := [ERC20.approveTransition, ERC20.totalSupplyTransition, ERC20.transferFromTransition])
    (post := [ERC20.transferTransition, ERC20.allowanceTransition])
    (hfallback := rfl) (htr := rfl) ?_
    (by rw [selectorOf, vyperERC20BalanceOfSelectorBytes]; exact hsel)
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · rw [selectorOf, vyperERC20ApproveSelectorBytes, hcd]; decide
    · rw [selectorOf, vyperERC20TotalSupplySelectorBytes, hcd]; decide
    · rw [selectorOf, vyperERC20TransferFromSelectorBytes, hcd]; decide

theorem erc20BalanceOfBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD vyperERC20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨623⟩
      [balanceOfSelectorWord] balanceOfDispatchMem (UInt256.ofNat 1) ByteArray.empty
      (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor vyperERC20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := erc20Dispatch_balanceOf (cd := I.calldata) hsel
  have hword : balanceOfWord σ_evm I = balanceOfWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (balanceOfSlot I) ⟨0⟩
  have hbody :
      ExecTransitionBody vyperERC20Config erc20Contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (balanceOfStore I)
        ERC20.balanceOfTransition.body
        (.returned { contract := erc20Contract, locals := balanceOfStore I }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.int (Int.ofNat (balanceOfWord σ_solm I).toNat)))) := by
    simpa [balanceOfWord, balanceOfSlot, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using erc20BalanceOfBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
        (by simp only [initState]; exact hwv)
  have hsz4 := erc20BalanceOfSelector_size hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus
    · have hdec0 := erc20Decode_balanceOf_ok (I := I) hsz36 hcanon
      have hdec :
          decodeCalldataWithMode vyperERC20Config.abiDecodeMode
            (ERC20.balanceOfTransition.params.map Param.name)
            (transitionSignature ERC20.balanceOfTransition).paramTypes I.calldata =
              some (balanceOfStore I) := by
        simpa [vyperERC20Config] using hdec0
      exact (erc20X_balanceOfFromEntry (g := Sat256.ofUInt256 g) hwv hsz36 hsize hcanon hreach)
        |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword]) hAccounts
          (returnEquiv_of_encode (ERC20.erc20Uint256ReturnEncoding (balanceOfWord σ_evm I)))
    · have hdec0 := erc20Decode_balanceOf_none_noncanon (I := I) hsz36 hcanon
      have hdec :
          decodeCalldataWithMode vyperERC20Config.abiDecodeMode
            (ERC20.balanceOfTransition.params.map Param.name)
            (transitionSignature ERC20.balanceOfTransition).paramTypes I.calldata = none := by
        simpa [vyperERC20Config] using hdec0
      exact (erc20BalanceOfX_noncanon_owner (g := Sat256.ofUInt256 g)
          hwv hsz36 hsize hcanon hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 36 := by omega
    have hdec0 := erc20Decode_balanceOf_none_short (I := I) hsz4 hshort
    have hdec :
        decodeCalldataWithMode vyperERC20Config.abiDecodeMode
          (ERC20.balanceOfTransition.params.map Param.name)
          (transitionSignature ERC20.balanceOfTransition).paramTypes I.calldata = none := by
      simpa [vyperERC20Config] using hdec0
    exact (erc20BalanceOfX_shortarg (g := Sat256.ofUInt256 g) hwv hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

theorem erc20BalanceOfRuntimeSuccess
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vyperERC20Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor vyperERC20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact erc20BalanceOfBodyCore hcode hwv hsize hsel
    (erc20X_balanceOfReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsel)
    hAccounts

end VyperERC20
