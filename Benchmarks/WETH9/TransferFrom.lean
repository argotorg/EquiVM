import Reasoning.MemoryShapes
import Benchmarks.WETH9.TransferFromSolm

/-! # WETH9 `transferFrom(address,address,uint256)` refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.WETH9

/-! ## Reach the shared body from the public `transferFrom` dispatch entry (pc 420) -/

/-- Peel the callvalue guard, pass the 3-word length check, decode `(src, dst, wad)`, and jump to the
    shared internal body (pc 1087) with `[wad, dstMasked, srcMasked, 361, sel]`. -/
theorem weth9TFReachBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 3)) :
    ∃ k C, RD weth9Bytecode I g (initState σ σ₀ g A I) ⟨1087⟩
      (tfWadWord I :: tfDstMasked I :: tfSrcMasked I :: ⟨361⟩ :: [weth9SelWord I])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h420⟩ := weth9ReachTransferFrom (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h434⟩ := solcFunctionGuardPeelOk (gt := ⟨432⟩) h420 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
  have hlt : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize
  have h455 := h434.pushConst (⟨361⟩ : UInt256) (op := .PUSH2) (width := 2) (by decide)
      (by native_decide) (by simp)
    |>.push1 ⟨4⟩ (by native_decide) (by simp)
    |>.dup1 (by native_decide) (by simp)
    |>.calldatasize (by native_decide) (by simp)
    |>.sub (by native_decide) (by simp)
    |>.push1 ⟨96⟩ (by native_decide) (by simp)
    |>.dup2 (by native_decide) (by simp)
    |>.lt (by native_decide) (by simp)
    |>.iszero (by native_decide) (by simp)
    |>.pushConst (⟨455⟩ : UInt256) (op := .PUSH2) (width := 2) (by decide) (by native_decide)
        (by simp)
    |>.jumpiT (by native_decide) (by rw [hlt]; decide) (by jump_dest) (by simp)
  exact RD.solcAddressAddressUint256ExternalMaskAndJumpMasked (routine := ⟨1087⟩) h455
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by simp only [List.length_singleton]; omega)

/-! ## Shared body tail + boolean return (pc 1282 → `RDret`) -/


/-- The bool-encoder scratch memory (`isZero(isZero 1) = 1` written at the free pointer 0x80). -/
abbrev wtfBoolReturnMem (src dst wad : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)))).write 0
    (solcScratchReturnMem (wordAt0Mem dst (twoWordHashMem src ⟨3⟩ mem)) wad) 128 32

/-- From pc 1282 with `ret = 361` (the bool encoder), run the two balance stores + LOG3 tail, then
    the boolean-return encoder, halting with output `0x…01` and the two-store post-state. -/
theorem weth9TFReturnTrue {ee g s0 rdata σ k C} {src dst wad : UInt256} {S : List UInt256}
    {mem : ByteArray}
    (h : RD weth9Bytecode ee g s0 ⟨1282⟩ (⟨0⟩ :: wad :: dst :: src :: ⟨361⟩ :: S)
      mem (UInt256.ofNat 3) rdata σ k C)
    (hperm : ee.perm = true) (hsrc : src.toNat < EVM.addressModulus)
    (hdst : dst.toNat < EVM.addressModulus)
    (hmemsize : mem.size = 96) (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : S.length + 16 ≤ 1024) :
    RDret weth9Bytecode g s0 (wtfPostMap ee σ src dst wad)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, h361⟩ := weth9TFTail h hperm hsrc hdst hmemsize hread64 (by jump_dest) hov
  have hM1size : (wordAt0Mem dst (twoWordHashMem src ⟨3⟩ mem)).size = 96 :=
    wordAt0Mem_size_96 dst (twoWordHashMem_size_96 src ⟨3⟩ hmemsize)
  have hM1read64 : (wordAt0Mem dst (twoWordHashMem src ⟨3⟩ mem)).readWithPadding 64 32
      = UInt256.toByteArray ⟨128⟩ := by
    rw [wordAt0Mem_read64_preserved_word dst (twoWordHashMem_size_96 src ⟨3⟩ hmemsize)]
    exact twoWordHashMem_read64 src ⟨3⟩ hmemsize hread64
  have hretWf : solcReturnBoolFromMemWf weth9Bytecode ⟨361⟩ := by
    unfold solcReturnBoolFromMemWf
    repeat' first | apply And.intro | native_decide
  have hbool : UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ := by native_decide
  have hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (wtfBoolReturnMem src dst wad mem).size then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((wtfBoolReturnMem src dst wad mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
    refine mloadFreePtrValue (by
        unfold wtfBoolReturnMem
        rw [toByteArray_write32_size_of_le
          (solcScratchReturnMem (wordAt0Mem dst (twoWordHashMem src ⟨3⟩ mem)) wad)
          (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) 128 160 160
          (solcScratchReturnMem_size wad hM1size)
          (by rw [solcScratchReturnMem_size wad hM1size]; decide) (by decide)]
        decide) ?_
    unfold wtfBoolReturnMem
    rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [solcScratchReturnMem_size wad hM1size]; omega) (by omega)]
    exact solcScratchReturnMem_read64 wad hM1size hM1read64
  have hread128 : (wtfBoolReturnMem src dst wad mem).readWithPadding 128 32
      = UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) := by
    unfold wtfBoolReturnMem
    exact toByteArray_write32_read_back
      (solcScratchReturnMem (wordAt0Mem dst (twoWordHashMem src ⟨3⟩ mem)) wad)
      (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) 128
      (by rw [solcScratchReturnMem_size wad hM1size]; decide)
  have hret := RD.solcReturnBoolFromMem h361 hretWf
    (solcScratchReturnMem_mload64 wad hM1size hM1read64) (by rfl) hmemoutLoad64 hread128
    (by omega)
  simpa [hbool] using hret

/-! ## Source ⟺ EVM branch-condition reconciliation -/

theorem tfSrcMasked_eq_solcSourceWord_of_address_eq (I : ExecutionEnv)
    (heq : AccountAddress.ofNat (tfSrcWord I).toNat = I.source) :
    tfSrcMasked I = solcSourceWord I := by
  have hmask := keyValueToWord_address_ofNat_mask (tfSrcWord I)
  rw [heq, keyValueToWord_address] at hmask
  exact hmask.symm

theorem tfAddress_eq_of_srcMasked_eq (I : ExecutionEnv) (heq : tfSrcMasked I = solcSourceWord I) :
    AccountAddress.ofNat (tfSrcWord I).toNat = I.source := by
  have hcomm : UInt256.land (tfSrcWord I) solcAddrMask = solcSourceWord I := by
    rw [u256_land_comm]; exact heq
  refine Eq.trans ?_ (solcMaskedAddress_eq_source_of_word_eq hcomm)
  apply Fin.ext
  unfold AccountAddress.ofNat
  simp only [Fin.val_ofNat]
  rw [uland_toNat]
  show (tfSrcWord I).toNat % AccountAddress.size
      = Nat.land (tfSrcWord I).toNat solcAddrMask.toNat % AccountAddress.size
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide, nat_land_mask_eq_mod,
    show AccountAddress.size = 2 ^ 160 by rfl, Nat.mod_mod]

/-! ## Dispatch and return encoding -/

theorem weth9SelectorDispatchTransferFrom {I : ExecutionEnv} (hsel : selIs I (weth9SelBytes 3)) :
    selectorDispatchMsg contract I.calldata = some transferFromTransition := by
  have hcd : I.calldata.extract 0 4 = weth9SelBytes 3 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp only [contract, dispatchList, selectorOf, hcd,
    weth9NameSelectorBytes, weth9ApproveSelectorBytes, weth9TotalSupplySelectorBytes,
    weth9TransferFromSelectorBytes]
  native_decide

/-- The shared refinement bridge for a `transferFrom` success run. -/
theorem weth9TFConnect {σ σ₀ A I} {g : UInt256} {evmPost : EVM.State} {cs}
    {evmPostMap : AccountMap}
    (hcode : I.code = weth9Bytecode) (hsel : selIs I (weth9SelBytes 3))
    (hsz100 : 100 ≤ I.calldata.size)
    (hX : RDret weth9Bytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) evmPostMap
      (UInt256.toByteArray (⟨1⟩ : UInt256)))
    (hbody : ExecTransitionBody config contract
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) (tfStore I)
      transferFromTransition.body (.returned cs evmPost (some [.bool true])))
    (hbodyMap : evmPost.accountMap = evmPostMap) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  refine weth9ReEquivExecGen (t := transferFromTransition) hcode hX
    (weth9SelectorDispatchTransferFrom hsel) ?_ hbody ?_ ?_
  · show decodeCalldataWithMode config.abiDecodeMode (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = some (tfStore I)
    exact tfDecode_ok hsz100
  · exact hbodyMap.symm
  · exact returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding)

/-! ## Revert reach lemmas -/

/-- `callvalue ≠ 0`: the payable guard at pc 420 reverts. -/
theorem weth9TFGuardRev {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue ≠ ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 3)) :
    RDrev weth9Bytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, h420⟩ := weth9ReachTransferFrom (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  exact solcFunctionGuardPeelRev (gt := ⟨432⟩) h420 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)

/-- Short calldata (`< 100`, but `callvalue = 0`): the 3-word length check reverts. -/
theorem weth9TFDecodeFailRev {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (weth9SelBytes 3)) :
    RDrev weth9Bytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, h420⟩ := weth9ReachTransferFrom (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h434⟩ := solcFunctionGuardPeelOk (gt := ⟨432⟩) h420 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
  have hltShort : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (show (⟨4⟩ : UInt256).toNat ≤ I.calldata.size by simpa using hsz4) hsize]
    simp only [show (⟨96⟩ : UInt256).toNat = 96 from rfl, show (⟨4⟩ : UInt256).toNat = 4 from rfl]
    omega
  exact h434.pushConst (⟨361⟩ : UInt256) (op := .PUSH2) (width := 2) (by decide)
      (by native_decide) (by simp)
    |>.push1 ⟨4⟩ (by native_decide) (by simp)
    |>.dup1 (by native_decide) (by simp)
    |>.calldatasize (by native_decide) (by simp)
    |>.sub (by native_decide) (by simp)
    |>.push1 ⟨96⟩ (by native_decide) (by simp)
    |>.dup2 (by native_decide) (by simp)
    |>.lt (by native_decide) (by simp)
    |>.iszero (by native_decide) (by simp)
    |>.pushConst (⟨455⟩ : UInt256) (op := .PUSH2) (width := 2) (by decide) (by native_decide) (by simp)
    |>.jumpiNT (by native_decide) (by rw [hltShort]; decide) (by simp)
    |>.solcPush1Dup1Revert0 (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem weth9TransferFromBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I (weth9SelBytes 3)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (weth9SelBytes 3) (by native_decide) hsel
  have hdisp := weth9SelectorDispatchTransferFrom hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz100 : 100 ≤ I.calldata.size
    · -- decode succeeds; reach the shared body
      obtain ⟨_, _, h1087⟩ := weth9TFReachBody (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz100 hsize hsel
      by_cases hbal : (tfWadWord I).toNat ≤ (tfBalSrcWord I σ).toNat
      · obtain ⟨_, _, h1124⟩ := weth9TFReqBalanceOk h1087 (tfSrcMasked_canonical I) hbal
          (by simp only [List.length_cons, List.length_nil]; omega)
        by_cases hsrcAddr : AccountAddress.ofNat (tfSrcWord I).toNat = I.source
        · -- SkipSender
          obtain ⟨_, _, h1282⟩ := weth9TFBranchSkipSender h1124 (tfSrcMasked_canonical I)
            (tfSrcMasked_eq_solcSourceWord_of_address_eq I hsrcAddr)
            (by simp only [List.length_cons, List.length_nil]; omega)
          have hX := weth9TFReturnTrue h1282 hperm (tfSrcMasked_canonical I) (tfDstMasked_canonical I)
            (twoWordHashMem_size_96 (tfSrcMasked I) ⟨3⟩ solcFreePtrMem_size)
            (wtfBalHashMem_read64 (tfSrcMasked I))
            (by simp only [List.length_cons, List.length_nil]; omega)
          obtain ⟨evmPost, cs, hbody, hmap⟩ :=
            weth9TFSolmSkipSender (σ := σ) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) hwv hsrcAddr hbal
          exact weth9TFConnect hcode hsel hsz100 hX hbody hmap
        · -- src ≠ caller: load the allowance
          have hne : solcSourceWord I ≠ tfSrcMasked I := fun h =>
            hsrcAddr (tfAddress_eq_of_srcMasked_eq I h.symm)
          obtain ⟨_, _, h1186⟩ := weth9TFAllowLoaded h1124 (tfSrcMasked_canonical I) hne
            (by simp only [List.length_cons, List.length_nil]; omega)
          by_cases hmax : (tfAllowWord I σ).toNat = UInt256.size - 1
          · -- SkipMax
            obtain ⟨_, _, h1282⟩ := weth9TFBranchSkipMax h1186 hmax
              (by simp only [List.length_cons, List.length_nil]; omega)
            have hX := weth9TFReturnTrue h1282 hperm (tfSrcMasked_canonical I) (tfDstMasked_canonical I)
              (wtfAllowHashMem_size I (tfSrcMasked I)) (wtfAllowHashMem_read64 I (tfSrcMasked I))
              (by simp only [List.length_cons, List.length_nil]; omega)
            obtain ⟨evmPost, cs, hbody, hmap⟩ :=
              weth9TFSolmSkipMax (σ := σ) (σ₀ := σ₀)
                (A := A) (I := I) (g := Sat256.ofUInt256 g) hwv hsrcAddr hmax
                hbal
            exact weth9TFConnect hcode hsel hsz100 hX hbody hmap
          · by_cases hallow : (tfWadWord I).toNat ≤ (tfAllowWord I σ).toNat
            · -- Spend
              have hnotMax : solcSlotWord σ I (wtfAllowSlot I (tfSrcMasked I)) ≠ UInt256.lnot ⟨0⟩ :=
                fun h => hmax (by unfold tfAllowWord; rw [h]; exact wtf_lnot0_toNat)
              obtain ⟨_, _, h1282⟩ := weth9TFBranchSpendOk h1186 hperm (tfSrcMasked_canonical I)
                hnotMax hallow (by simp only [List.length_cons, List.length_nil]; omega)
              have hspendbase : (solcNestedMappingCallerHashMem ⟨4⟩ (tfSrcMasked I) I
                  (wtfAllowHashMem I (tfSrcMasked I))).size = 96 :=
                nestedHashMem_size ⟨4⟩ (tfSrcMasked I) I _ (wtfAllowHashMem_size I (tfSrcMasked I))
              have hX := weth9TFReturnTrue h1282 hperm (tfSrcMasked_canonical I) (tfDstMasked_canonical I)
                (nestedHashMem_size ⟨4⟩ (tfSrcMasked I) I _ hspendbase)
                (nestedHashMem_read64 ⟨4⟩ (tfSrcMasked I) I _ hspendbase
                  (nestedHashMem_read64 ⟨4⟩ (tfSrcMasked I) I _
                    (wtfAllowHashMem_size I (tfSrcMasked I)) (wtfAllowHashMem_read64 I (tfSrcMasked I))))
                (by simp only [List.length_cons, List.length_nil]; omega)
              obtain ⟨evmPost, cs, hbody, hmap⟩ :=
                weth9TFSolmSpend (σ := σ) (σ₀ := σ₀)
                  (A := A) (I := I) (g := Sat256.ofUInt256 g) hwv hsrcAddr
                  hmax hallow
                  hbal
              exact weth9TFConnect hcode hsel hsz100 hX hbody hmap
            · -- allowance < wad: inner require reverts
              have hnotMax : solcSlotWord σ I (wtfAllowSlot I (tfSrcMasked I)) ≠ UInt256.lnot ⟨0⟩ :=
                fun h => hmax (by unfold tfAllowWord; rw [h]; exact wtf_lnot0_toNat)
              have hrev := weth9TFBranchSpendRev h1186 (tfSrcMasked_canonical I) hnotMax
                (by change (tfAllowWord I σ).toNat < (tfWadWord I).toNat; omega)
                (by simp only [List.length_cons, List.length_nil]; omega)
              exact weth9ReEquivExecRev hcode hrev hdisp (tfDecode_ok hsz100)
                (weth9TFSolmRevAllow (σ := σ) (σ₀ := σ₀)
                  (A := A) (I := I) (g := Sat256.ofUInt256 g) hwv
                  hsrcAddr hmax hbal
                  (by omega))
      · -- bal < wad: initial require reverts
        have hrev := weth9TFReqBalanceRev h1087 (tfSrcMasked_canonical I)
          (by change (tfBalSrcWord I σ).toNat < (tfWadWord I).toNat; omega)
          (by simp only [List.length_cons, List.length_nil]; omega)
        exact weth9ReEquivExecRev hcode hrev hdisp (tfDecode_ok hsz100)
          (weth9TFSolmRevBal (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := Sat256.ofUInt256 g) hwv
            (by omega))
    · -- calldata < 100: decode failure
      exact weth9ReEquivDecodeFailed hcode
        (weth9TFDecodeFailRev (g := Sat256.ofUInt256 g) hcode hwv hsz4 (by omega) hsize hsel) hdisp
        (tfDecode_none_short hsz4 (by omega))
  · -- callvalue ≠ 0: the payable guard reverts
    exact weth9NonpayableRevert hcode
      (weth9TFGuardRev (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel) hdisp
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.WETH9
