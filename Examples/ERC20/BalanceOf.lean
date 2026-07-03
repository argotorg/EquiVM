import Examples.ERC20.Common
import Reasoning.Refinement
import Reasoning.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace ERC20

/-! ## ABI decode and source-level body for `balanceOf(address)` -/

/-- The raw ABI word for `balanceOf`'s `owner` argument. -/
abbrev balanceOfOwnerWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

abbrev balanceOfOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (balanceOfOwnerWord I).toNat)

abbrev balanceOfStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "owner" (balanceOfOwnerValue I)

def balanceOfSlot (I : ExecutionEnv) : UInt256 :=
  erc20BalanceOfSlot (.address (AccountAddress.ofNat (balanceOfOwnerWord I).toNat))

def balanceOfWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (balanceOfSlot I) ⟨0⟩)

theorem erc20Decode_balanceOf_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = some (balanceOfStore I) := by
  show decodeCalldata ["owner"] [addr] I.calldata = _
  simpa [balanceOfStore, balanceOfOwnerValue, balanceOfOwnerWord, calldataWord]
    using decodeCalldata_address_ok (cd := I.calldata) (x := "owner") hsz36 hbig hcanon

theorem erc20Decode_balanceOf_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_short (cd := I.calldata) (x := "owner") hsz4 hshort

theorem erc20Decode_balanceOf_none_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner"] [addr] I.calldata = none
  simpa [addr, balanceOfOwnerWord, calldataWord]
    using decodeCalldata_address_none_noncanon (cd := I.calldata) (x := "owner") hsz36 hbig hnc

theorem erc20Decode_balanceOf_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner"] [addr] I.calldata = none
  simpa [addr] using decodeCalldata_address_none_huge (cd := I.calldata) (x := "owner") hbig

theorem balanceOfStore_owner (I : ExecutionEnv) :
    (balanceOfStore I).get? "owner" = some (balanceOfOwnerValue I) := by
  simp [balanceOfStore, balanceOfOwnerValue]

theorem erc20BalanceOfBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody erc20Config erc20Contract evm (balanceOfStore I) balanceOfTransition.body
      (.returned { contract := erc20Contract, locals := balanceOfStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (balanceOfSlot I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (hbase := by simp [balanceOfStore, balanceOfRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, balanceOfRef, balanceOfStore,
            balanceOfOwnerValue, valueToKey?, EvalResult.seqList, EvalResult.bind,
            EvalResult.ofOption, bind, pure, evalExpr?])
        (hty := by simp [storageTypeAt?, erc20Contract, erc20StorageDecls, uint256Storage,
          storageTypeStep?])
        (hloc := erc20Config_storage_balanceOf
          (.address (AccountAddress.ofNat (balanceOfOwnerWord I).toNat)))]
      simp [balanceOfSlot, erc20StorageLocLoad_uint256])

/-! ## EVM scratch memory for the `balanceOf` mapping access -/

/-- Memory after `balanceOf` stores base slot `0` at scratch offset `0x20`. -/
noncomputable def balanceOfBaseSlotMem : ByteArray :=
  (UInt256.toByteArray (⟨0⟩ : UInt256)).write 0 solcFreePtrMem 32 32

/-- Memory after `balanceOf` stores the owner key at scratch offset `0x00`. -/
noncomputable def balanceOfHashMem (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray owner).write 0 balanceOfBaseSlotMem 0 32

theorem balanceOfBaseSlotMem_size : balanceOfBaseSlotMem.size = 96 := by
  unfold balanceOfBaseSlotMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, solcFreePtrMem_size, toByteArray_size]
  omega

theorem balanceOfHashMem_size (owner : UInt256) : (balanceOfHashMem owner).size = 96 := by
  unfold balanceOfHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [balanceOfBaseSlotMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, balanceOfBaseSlotMem_size, toByteArray_size]
  omega

theorem balanceOfBaseSlotMem_read32 :
    balanceOfBaseSlotMem.readWithPadding 32 32 = UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold balanceOfBaseSlotMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [solcFreePtrMem_size]; omega),
    show (UInt256.toByteArray (⟨0⟩ : UInt256)).extract 0 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray (⟨0⟩ : UInt256)).size ≤ 32
          rw [toByteArray_size])]

theorem balanceOfBaseSlotMem_read64 :
    balanceOfBaseSlotMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfBaseSlotMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega) (by omega)
      (by rw [solcFreePtrMem_size]),
    solcFreePtrMem_read64]

theorem balanceOfHashMem_read0 (owner : UInt256) :
    (balanceOfHashMem owner).readWithPadding 0 32 = UInt256.toByteArray owner := by
  unfold balanceOfHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega),
    show (UInt256.toByteArray owner).extract 0 32 = UInt256.toByteArray owner from by
      apply ByteArray.ext
      rw [ByteArray.data_extract]
      exact Array.extract_eq_self_of_le (by
        change (UInt256.toByteArray owner).size ≤ 32
        rw [toByteArray_size])]

theorem balanceOfHashMem_read32 (owner : UInt256) :
    (balanceOfHashMem owner).readWithPadding 32 32 = UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold balanceOfHashMem
  rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size]) (by omega)
      (by omega) (by rw [balanceOfBaseSlotMem_size]; omega),
    balanceOfBaseSlotMem_read32]

theorem balanceOfHashMem_read64 (owner : UInt256) :
    (balanceOfHashMem owner).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfHashMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega)
      (by omega) (by rw [balanceOfBaseSlotMem_size]),
    balanceOfBaseSlotMem_read64]

theorem balanceOfHashMem_mload64 (owner : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (balanceOfHashMem owner).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian ((balanceOfHashMem owner).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [balanceOfHashMem_size]; decide) (by decide)
    (balanceOfHashMem_read64 owner)

theorem balanceOfHashMem_read0_64 (owner : UInt256) :
    (balanceOfHashMem owner).readWithPadding 0 64 =
      UInt256.toByteArray owner ++ UInt256.toByteArray (⟨0⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [balanceOfHashMem_size]; omega)]
  unfold balanceOfHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  have hownerFull :
      (UInt256.toByteArray owner).extract 0 32 = UInt256.toByteArray owner := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray owner).size ≤ 32
      rw [toByteArray_size])
  have hbase32 :
      (balanceOfBaseSlotMem.extract 32 (balanceOfBaseSlotMem.size)).extract 0 32 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    rw [extract_extract_BA, show 32 + 0 = 32 from rfl,
      show min (32 + 32) balanceOfBaseSlotMem.size = 64 from by
        rw [balanceOfBaseSlotMem_size]; rfl]
    have hread := balanceOfBaseSlotMem_read32
    rw [readWithPadding_eq_extract _ 32 (by rw [balanceOfBaseSlotMem_size]; omega)] at hread
    exact hread
  have hleft0 : balanceOfBaseSlotMem.extract 0 0 = ByteArray.empty := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    show balanceOfBaseSlotMem.data.extract 0 0 = #[]
    exact Array.extract_eq_empty_of_le (by omega)
  rw [hleft0, ByteArray.empty_append, hownerFull]
  rw [extract_append_span (UInt256.toByteArray owner)
      (balanceOfBaseSlotMem.extract 32 balanceOfBaseSlotMem.size) 0 64
      (by omega) (by rw [toByteArray_size]; omega)]
  rw [show (UInt256.toByteArray owner).size = 32 from toByteArray_size owner]
  rw [show 64 - 32 = 32 from rfl]
  rw [hownerFull, hbase32]

theorem balanceOfKeccakSlot (I : ExecutionEnv)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((balanceOfHashMem (balanceOfOwnerWord I)).readWithPadding 0 64)))
      = balanceOfSlot I := by
  rw [balanceOfHashMem_read0_64]
  unfold balanceOfSlot erc20BalanceOfSlot erc20MappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]
  exact mappingSlot_single (balanceOfOwnerWord I) ⟨0⟩

/-- Memory after the shared uint256 encoder writes the `balanceOf` return word at `0x80`. -/
noncomputable def balanceOfReturnMem (owner val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 (balanceOfHashMem owner) 128 32

theorem balanceOfReturnMem_size (owner val : UInt256) :
    (balanceOfReturnMem owner val).size = 160 := by
  unfold balanceOfReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [balanceOfHashMem_size]; omega)
      (by rw [balanceOfHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, balanceOfHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem balanceOfReturnMem_read64 (owner val : UInt256) :
    (balanceOfReturnMem owner val).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [balanceOfHashMem_size]; omega)
      (by rw [balanceOfHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, balanceOfHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, balanceOfHashMem_size, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [balanceOfHashMem_size]),
    ← readWithPadding_eq_extract _ 64 (by rw [balanceOfHashMem_size]),
    balanceOfHashMem_read64]

theorem balanceOfReturnMem_mload64 (owner val : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (balanceOfReturnMem owner val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((balanceOfReturnMem owner val).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [balanceOfReturnMem_size]; decide) (by decide)
    (balanceOfReturnMem_read64 owner val)

theorem balanceOfReturnMem_read128 (owner val : UInt256) :
    (balanceOfReturnMem owner val).readWithPadding 128 32 = UInt256.toByteArray val := by
  unfold balanceOfReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [balanceOfHashMem_size]; omega)
      (by rw [balanceOfHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 128 (by
      rw [ByteArray.size_append, ByteArray.size_append, balanceOfHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      )]
  rw [extract_append_right_window
      (balanceOfHashMem owner ++ ffi.ByteArray.zeroes (USize.ofNat (128 - (balanceOfHashMem owner).size)))
      (UInt256.toByteArray val) 128 160 (by
        rw [ByteArray.size_append, balanceOfHashMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (128 - 96)).toNat = 32 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
        )]
  rw [ByteArray.size_append, balanceOfHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  norm_num
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray val).size ≤ 32
    rw [toByteArray_size])

/-! ## EVM trace for `balanceOf(address)` -/

/-- Wrapper pc 226 sets up calldata bounds for `balanceOf(address)` and jumps to the
    one-address tuple decoder at pc 2178. -/
theorem erc20BalanceOfX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨226⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2178⟩
        [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨247⟩, ⟨252⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨252⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨247⟩, swap2, swap1, push2 ⟨2178⟩, jump erc20_jd ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

/-- The one-address tuple decoder accepts calldata with at least one static word and jumps to the
    address element decoder at pc 1874. -/
theorem erc20BalanceOfX_dec1874 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨226⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1874⟩
        [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨2212⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
          UInt256.ofNat I.calldata.size, ⟨247⟩, ⟨252⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hszhi hsize
  obtain ⟨k, C, rd⟩ := erc20BalanceOfX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨2199⟩,
    jumpiT (by rw [hslt]; decide) erc20_jd,
    jumpdest, push0, push2 ⟨2212⟩, dup5, dup3, dup6, add, push2 ⟨1874⟩,
    jump erc20_jd ]⟩

/-- The `owner` address decode (success): one application of the shared `RD.erc20DecodeAddrOk`
    routine, replacing the former `dec1852`/`dec1835`/`dec1861`/`dec2212` chain. -/
theorem erc20BalanceOfX_dec2212 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨226⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2212⟩
        [balanceOfOwnerWord I, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
          ⟨247⟩, ⟨252⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc20BalanceOfX_dec1874 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz36 hsize hszhi hreach
  exact RD.erc20DecodeAddrOk rd hcanon (by jump_dest) (by evm_ov)

/-- The one-address tuple decoder returns to the external wrapper, which jumps to the internal
    `balanceOf` body at pc 1345. -/
theorem erc20BalanceOfX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨226⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1345⟩
        [balanceOfOwnerWord I, ⟨252⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc20BalanceOfX_dec2212 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz36 hsize hszhi hcanon hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop, jump erc20_jd,
    jumpdest, push2 ⟨1345⟩, jump erc20_jd ]⟩

/-- The EVM `balanceOf(address)` path loads the explicit mapping slot and returns it as a single
    ABI word. -/
theorem erc20X_balanceOf {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨226⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc20Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (balanceOfWord σ I)) := by
  obtain ⟨k, C, rd1345⟩ := erc20BalanceOfX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz36 hsize hszhi hcanon hreach
  have hslot := balanceOfKeccakSlot I hcanon
  have rd1362 := evm_run rd1345 with [
    jumpdest, push0, push1 ⟨32⟩,
    raw mstore 0 balanceOfBaseSlotMem (UInt256.ofNat 3) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    dup1, push0,
    raw mstore 0 (balanceOfHashMem (balanceOfOwnerWord I)) (UInt256.ofNat 3) (by decide)
      mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (balanceOfSlot I) (UInt256.ofNat 3) (by decide)
      mem_cost hslot (by decide) (by evm_ov),
    push0, swap2, pop, swap1, pop ]
  obtain ⟨k1, C1, rd1363⟩ := rd1362.sload (by decide) (by evm_ov)
  have rd252 := evm_run rd1363 with [
    dup2, jump erc20_jd ]
  have rd2073 := evm_run rd252 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (balanceOfHashMem_mload64 (balanceOfOwnerWord I))
      (by decide) (by evm_ov),
    push2 ⟨265⟩, swap2, swap1, push2 ⟨2073⟩, jump erc20_jd ]
  obtain ⟨k2, C2, rd265⟩ := erc20RoutineEncodeUint256FromMem
    (val := balanceOfWord σ I) (ret := ⟨265⟩) (R := [⟨252⟩, sel])
    rd2073 (by rfl) erc20_jd (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd265 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (balanceOfReturnMem_mload64 (balanceOfOwnerWord I) (balanceOfWord σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (balanceOfWord σ I)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, erc20SubRet32_toNat]
        change (balanceOfReturnMem (balanceOfOwnerWord I) (balanceOfWord σ I)).readWithPadding 128 32 =
          UInt256.toByteArray (balanceOfWord σ I)
        exact balanceOfReturnMem_read128 (balanceOfOwnerWord I) (balanceOfWord σ I))
      (by evm_ov) ]

/-! ## Decode-failure traces and top-level body theorem -/

theorem erc20BalanceOfX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨226⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz4 hshort hsize
  obtain ⟨k, C, rd⟩ := erc20BalanceOfX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨2199⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨2198⟩, push2 ⟨1800⟩, jump erc20_jd,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc20BalanceOfX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨226⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  obtain ⟨k, C, rd⟩ := erc20BalanceOfX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨2199⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨2198⟩, push2 ⟨1800⟩, jump erc20_jd,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc20BalanceOfX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (balanceOfOwnerWord I)
      (UInt256.land (balanceOfOwnerWord I) erc20AddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc20Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨226⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc20Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := erc20BalanceOfX_dec1874 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz36 hsize hszhi hreach
  exact RD.erc20DecodeAddrRevert rd hnc (by evm_ov)

theorem erc20BalanceOfSelector_size {I : ExecutionEnv}
    (hsel : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc20Dispatch_balanceOf {cd : ByteArray}
    (hsel : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg erc20Contract cd = some balanceOfTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [approveTransition, totalSupplyTransition, transferFromTransition])
    (post := [transferTransition, allowanceTransition])
    rfl rfl ?_ (by rw [selectorOf, erc20BalanceOfSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · rw [selectorOf, erc20ApproveSelectorBytes, hcd]; decide
  · rw [selectorOf, erc20TotalSupplySelectorBytes, hcd]; decide
  · rw [selectorOf, erc20TransferFromSelectorBytes, hcd]; decide

theorem erc20BalanceOfBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = erc20Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x70, 0xa0, 0x82, 0x31]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hreach : ∃ k C, RD erc20Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨226⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor erc20Config erc20Contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := erc20BalanceOfSelector_size hsel
  have hd := erc20Dispatch_balanceOf (cd := I.calldata) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (balanceOfOwnerWord I).toNat < EVM.addressModulus
      · have hdec := erc20Decode_balanceOf_ok (I := I) hsz36 hbig hcanon
        have hword : balanceOfWord σ_evm I = balanceOfWord σ_solm I :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner (balanceOfSlot I) ⟨0⟩
        have hbody :
            ExecTransitionBody erc20Config erc20Contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (balanceOfStore I)
              balanceOfTransition.body
              (.returned { contract := erc20Contract, locals := balanceOfStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (some [(.int (Int.ofNat (balanceOfWord σ_solm I).toNat))])) := by
          simpa [balanceOfWord, balanceOfSlot, initState, Solm.EVM.storageLoad,
            State.lookupAccount] using erc20BalanceOfBodyReturns
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv)
        exact (erc20X_balanceOf (g := Sat256.ofUInt256 g) hsz36 hsize hbig hcanon hreach)
          |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword])
            hAccounts
            (returnEquiv_of_encode (erc20Uint256ReturnEncoding (balanceOfWord σ_evm I)))
      · have hdec := erc20Decode_balanceOf_none_noncanon (I := I) hsz36 hbig hcanon
        have hnc : UInt256.eq (balanceOfOwnerWord I)
            (UInt256.land (balanceOfOwnerWord I) erc20AddrMask) = ⟨0⟩ :=
          erc20Ueq_zero_of_ne (fun he => hcanon (erc20Word_canonical_of_clean he))
        exact (erc20BalanceOfX_noncanon (g := Sat256.ofUInt256 g) hsz36 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := erc20Decode_balanceOf_none_huge (I := I) hbigge
      exact (erc20BalanceOfX_hugearg (g := Sat256.ofUInt256 g) hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := erc20Decode_balanceOf_none_short (I := I) hsz4 hshort
    exact (erc20BalanceOfX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end ERC20
