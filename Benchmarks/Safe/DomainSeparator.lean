import Benchmarks.Safe.Routines
import Reasoning.MemCascade

/-! # Safe `domainSeparator()` refinement -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Safe

abbrev safeDomainSeparatorTypehashBytes : List UInt8 :=
  [ 0x47, 0xe7, 0x95, 0x34, 0xa2, 0x45, 0x95, 0x2e,
    0x8b, 0x16, 0x89, 0x3a, 0x33, 0x6b, 0x85, 0xa3,
    0xd9, 0xea, 0x9f, 0xa8, 0xc5, 0x73, 0xf3, 0xd8,
    0x03, 0xaf, 0xb9, 0x2a, 0x79, 0x46, 0x92, 0x18 ]

abbrev safeDomainSeparatorTypehashWord : UInt256 :=
  ⟨0x47e79534a245952e8b16893a336b85a3d9ea9fa8c573f3d803afb92a79469218⟩

abbrev safeDomainSeparatorChainIdWord : UInt256 :=
  UInt256.ofNat Ethereum.chainId

abbrev safeDomainSeparatorAddressWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.codeOwner.val

abbrev safeDomainSeparatorPackedBytes (I : ExecutionEnv) : List UInt8 :=
  safeDomainSeparatorTypehashBytes ++
    (EVM.Word.toBytesBE safeDomainSeparatorChainIdWord ++
      EVM.Word.toBytesBE (safeDomainSeparatorAddressWord I))

abbrev safeDomainSeparatorPreimage (I : ExecutionEnv) : ByteArray :=
  (safeDomainSeparatorPackedBytes I).toByteArray

abbrev safeDomainSeparatorHashBytes (I : ExecutionEnv) : List UInt8 :=
  (ffi.KEC (safeDomainSeparatorPreimage I)).toList

abbrev safeDomainSeparatorWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (ffi.KEC (safeDomainSeparatorPreimage I))

noncomputable abbrev safeDomainSeparatorMem1 : ByteArray :=
  writeWord solcFreePtrMem 128 safeDomainSeparatorTypehashWord

noncomputable abbrev safeDomainSeparatorMem2 : ByteArray :=
  writeWord safeDomainSeparatorMem1 160 safeDomainSeparatorChainIdWord

noncomputable abbrev safeDomainSeparatorMem3 (I : ExecutionEnv) : ByteArray :=
  writeWord safeDomainSeparatorMem2 192 (safeDomainSeparatorAddressWord I)

theorem safeDomainSeparatorTypehashBytes_length :
    safeDomainSeparatorTypehashBytes.length = 32 := by
  native_decide

theorem safeDomainSeparatorTypehashBytes_eq_word :
    safeDomainSeparatorTypehashBytes = EVM.Word.toBytesBE safeDomainSeparatorTypehashWord := by
  native_decide

theorem safeDomainSeparatorTypehashBytes_toByteArray :
    safeDomainSeparatorTypehashBytes.toByteArray =
      UInt256.toByteArray safeDomainSeparatorTypehashWord := by
  rw [safeDomainSeparatorTypehashBytes_eq_word]
  exact word_toBytesBE_toByteArray_eq_toByteArray safeDomainSeparatorTypehashWord

theorem safeDomainSeparatorPreimage_eq_words (I : ExecutionEnv) :
    safeDomainSeparatorPreimage I =
      UInt256.toByteArray safeDomainSeparatorTypehashWord ++
        (UInt256.toByteArray safeDomainSeparatorChainIdWord ++
          UInt256.toByteArray (safeDomainSeparatorAddressWord I)) := by
  unfold safeDomainSeparatorPreimage safeDomainSeparatorPackedBytes
  rw [List.toByteArray_append, List.toByteArray_append,
    safeDomainSeparatorTypehashBytes_toByteArray,
    word_toBytesBE_toByteArray_eq_toByteArray safeDomainSeparatorChainIdWord,
    word_toBytesBE_toByteArray_eq_toByteArray (safeDomainSeparatorAddressWord I)]

theorem safeDomainSeparatorHashBytes_eq_word (I : ExecutionEnv) :
    safeDomainSeparatorHashBytes I = EVM.Word.toBytesBE (safeDomainSeparatorWord I) := by
  unfold safeDomainSeparatorHashBytes safeDomainSeparatorWord
  exact (toBytesBE_uInt256OfByteArray_of_size (keccak_size _)).symm

theorem safeDomainSeparatorMem1_size : safeDomainSeparatorMem1.size = 160 := by
  unfold safeDomainSeparatorMem1
  rw [writeWord_size]
  · rw [solcFreePtrMem_size]; native_decide
  · rw [solcFreePtrMem_size]; native_decide

theorem safeDomainSeparatorMem2_size : safeDomainSeparatorMem2.size = 192 := by
  unfold safeDomainSeparatorMem2
  rw [writeWord_size]
  · rw [safeDomainSeparatorMem1_size]; native_decide
  · rw [safeDomainSeparatorMem1_size]; native_decide

theorem safeDomainSeparatorMem3_size (I : ExecutionEnv) :
    (safeDomainSeparatorMem3 I).size = 224 := by
  unfold safeDomainSeparatorMem3
  rw [writeWord_size]
  · rw [safeDomainSeparatorMem2_size]; native_decide
  · rw [safeDomainSeparatorMem2_size]; native_decide

theorem safeDomainSeparatorMem_read64 (I : ExecutionEnv) :
    (safeDomainSeparatorMem3 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold safeDomainSeparatorMem3 safeDomainSeparatorMem2 safeDomainSeparatorMem1
  change (writeCascade solcFreePtrMem
      [(128, safeDomainSeparatorTypehashWord),
        (160, safeDomainSeparatorChainIdWord),
        (192, safeDomainSeparatorAddressWord I)]).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [writeCascade_read_preserved_of_base solcFreePtrMem
    [(128, safeDomainSeparatorTypehashWord),
      (160, safeDomainSeparatorChainIdWord),
      (192, safeDomainSeparatorAddressWord I)]
    solcFreePtrMem_size (by
      simp [WindowDisjointFromWrites]
      all_goals
        have h32 : 32 < USize.size := lt_usize 32 (by norm_num)
        omega)]
  exact solcFreePtrMem_read64

theorem safeDomainSeparatorMem_read128 (I : ExecutionEnv) :
    (safeDomainSeparatorMem3 I).readWithPadding 128 32 =
      UInt256.toByteArray safeDomainSeparatorTypehashWord := by
  unfold safeDomainSeparatorMem3 safeDomainSeparatorMem2 safeDomainSeparatorMem1
  change (writeCascade solcFreePtrMem
      [(128, safeDomainSeparatorTypehashWord),
        (160, safeDomainSeparatorChainIdWord),
        (192, safeDomainSeparatorAddressWord I)]).readWithPadding 128 32 =
    UInt256.toByteArray safeDomainSeparatorTypehashWord
  exact writeCascade_read_word_of_head_of_base solcFreePtrMem
    safeDomainSeparatorTypehashWord
    [(160, safeDomainSeparatorChainIdWord), (192, safeDomainSeparatorAddressWord I)]
    solcFreePtrMem_size (by native_decide) (by simp [WindowDisjointFromWrites])

theorem safeDomainSeparatorMem_read160 (I : ExecutionEnv) :
    (safeDomainSeparatorMem3 I).readWithPadding 160 32 =
      UInt256.toByteArray safeDomainSeparatorChainIdWord := by
  unfold safeDomainSeparatorMem3 safeDomainSeparatorMem2
  change (writeCascade safeDomainSeparatorMem1
      [(160, safeDomainSeparatorChainIdWord),
        (192, safeDomainSeparatorAddressWord I)]).readWithPadding 160 32 =
    UInt256.toByteArray safeDomainSeparatorChainIdWord
  have hgap : 160 - safeDomainSeparatorMem1.size < USize.size := by
    rw [safeDomainSeparatorMem1_size]; native_decide
  have hlater :
      WindowDisjointFromWrites (max safeDomainSeparatorMem1.size (160 + 32)) 160 32
        [(192, safeDomainSeparatorAddressWord I)] := by
    rw [safeDomainSeparatorMem1_size]
    simp [WindowDisjointFromWrites]
  exact writeCascade_read_word_of_head safeDomainSeparatorMem1 160
    safeDomainSeparatorChainIdWord [(192, safeDomainSeparatorAddressWord I)] hgap hlater

theorem safeDomainSeparatorMem_read192 (I : ExecutionEnv) :
    (safeDomainSeparatorMem3 I).readWithPadding 192 32 =
      UInt256.toByteArray (safeDomainSeparatorAddressWord I) := by
  unfold safeDomainSeparatorMem3
  exact writeWord_read_back safeDomainSeparatorMem2 192 (safeDomainSeparatorAddressWord I)
    (by rw [safeDomainSeparatorMem2_size]; native_decide)

theorem safeDomainSeparatorMem_preimage (I : ExecutionEnv) :
    (safeDomainSeparatorMem3 I).readWithPadding 128 96 = safeDomainSeparatorPreimage I := by
  have hsize := safeDomainSeparatorMem3_size I
  rw [byteArray_readWithPadding_split (safeDomainSeparatorMem3 I) 128 32 64
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by omega)]
  rw [byteArray_readWithPadding_split (safeDomainSeparatorMem3 I) 160 32 32
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by omega)]
  rw [safeDomainSeparatorMem_read128 I, safeDomainSeparatorMem_read160 I,
    safeDomainSeparatorMem_read192 I, safeDomainSeparatorPreimage_eq_words I]

theorem safeDomainSeparatorKeccakWord (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((safeDomainSeparatorMem3 I).readWithPadding 128 96))) =
      safeDomainSeparatorWord I := by
  rw [safeDomainSeparatorMem_preimage]
  unfold safeDomainSeparatorWord
  exact keccakSlot_eq _

theorem safeDecode_domainSeparator_ok {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (domainseparatorTransition.params.map Param.name)
      (transitionSignature domainseparatorTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

theorem safeDomainSeparatorChainIdWord_toNat :
    safeDomainSeparatorChainIdWord.toNat = Ethereum.chainId := by
  unfold safeDomainSeparatorChainIdWord
  exact ulit_toNat' Ethereum.chainId (by native_decide)

theorem safeDomainSeparatorAddressWord_toNat (I : ExecutionEnv) :
    (safeDomainSeparatorAddressWord I).toNat = I.codeOwner.val := by
  unfold safeDomainSeparatorAddressWord
  exact ulit_toNat' I.codeOwner.val (lt_of_lt_of_le I.codeOwner.isLt (by decide))

theorem byteArray_mk_toArray_eq_toByteArray (xs : List UInt8) :
    ByteArray.mk xs.toArray = xs.toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem safeEncodePacked_uint256_word (value : UInt256) :
    encodePackedValue? uint256 (.int (Int.ofNat value.toNat)) =
      some (EVM.Word.toBytesBE value) := by
  have hword : EVM.word value.toNat = value := u256_ofNat_toNat value
  have hlt : value.toNat < EVM.twoPow 256 := by
    change value.val.val < EVM.twoPow 256
    exact value.val.isLt
  simp [encodePackedValue?, uint256, uint256Int, encodeABIWord?, hword, hlt]

theorem safeEncodePacked_bytes32_of_length {bytes : List UInt8}
    (hlen : bytes.length = fixedBytesSize bytes32Width) :
    encodePackedValue? bytes32 (.fixedBytes bytes32Width bytes) = some bytes := by
  simp [encodePackedValue?, bytes32, fixedBytesSize, hlen]

theorem safeEvalPackedArgs_cons_ok {cfg : Config} {solm : Frame} {evm : EVM.State}
    {ty : ABIType} {e : Expr} {v : Value} {head tailBytes : List UInt8}
    {rest : List (ABIType × Expr)}
    (heval : evalExpr? cfg solm evm e = .ok v)
    (henc : encodePackedValue? ty v = some head)
    (htail : evalPackedArgs? cfg solm evm rest = .ok tailBytes) :
    evalPackedArgs? cfg solm evm ((ty, e) :: rest) = .ok (head ++ tailBytes) := by
  rw [evalPackedArgs?]
  simp only [heval, henc, htail, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem safeEval_domainSeparatorExpr {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := ∅ }
        (initState cA gh bl σ σ₀ g A I) domainSeparatorExpr =
      .ok (.fixedBytes bytes32Width (safeDomainSeparatorHashBytes I)) := by
  have hpacked :
      evalPackedArgs? config { contract := contract, locals := ∅ }
          (initState cA gh bl σ σ₀ g A I)
          [ (bytes32, domainSeparatorTypehash),
            (uint256, .env .chainid),
            (uint256, addressAsUint256 this) ] =
        .ok (safeDomainSeparatorPackedBytes I) := by
    refine safeEvalPackedArgs_cons_ok
      (cfg := config) (solm := { contract := contract, locals := ∅ })
      (evm := initState cA gh bl σ σ₀ g A I)
      (ty := bytes32) (e := domainSeparatorTypehash)
      (v := .fixedBytes bytes32Width safeDomainSeparatorTypehashBytes)
      (head := safeDomainSeparatorTypehashBytes)
      (tailBytes :=
        EVM.Word.toBytesBE safeDomainSeparatorChainIdWord ++
          EVM.Word.toBytesBE (safeDomainSeparatorAddressWord I))
      (rest := [(uint256, .env .chainid), (uint256, addressAsUint256 this)])
      ?_ (safeEncodePacked_bytes32_of_length (by native_decide)) ?_
    · unfold domainSeparatorTypehash safeDomainSeparatorTypehashBytes
      simp only [evalExpr?, pure]
    · refine safeEvalPackedArgs_cons_ok
        (cfg := config) (solm := { contract := contract, locals := ∅ })
        (evm := initState cA gh bl σ σ₀ g A I)
        (ty := uint256) (e := .env .chainid)
        (v := .int (Int.ofNat safeDomainSeparatorChainIdWord.toNat))
        (head := EVM.Word.toBytesBE safeDomainSeparatorChainIdWord)
        (tailBytes := EVM.Word.toBytesBE (safeDomainSeparatorAddressWord I))
        (rest := [(uint256, addressAsUint256 this)])
        ?_ (safeEncodePacked_uint256_word safeDomainSeparatorChainIdWord) ?_
      · simp [evalExpr?, envValue, initState, safeDomainSeparatorChainIdWord_toNat]
        rfl
      · have haddr :
            evalPackedArgs? config { contract := contract, locals := ∅ }
                (initState cA gh bl σ σ₀ g A I) [(uint256, addressAsUint256 this)] =
              .ok (EVM.Word.toBytesBE (safeDomainSeparatorAddressWord I) ++ []) := by
          refine safeEvalPackedArgs_cons_ok
            (cfg := config) (solm := { contract := contract, locals := ∅ })
            (evm := initState cA gh bl σ σ₀ g A I)
            (ty := uint256) (e := addressAsUint256 this)
            (v := .int (Int.ofNat (safeDomainSeparatorAddressWord I).toNat))
            (head := EVM.Word.toBytesBE (safeDomainSeparatorAddressWord I))
            (tailBytes := []) (rest := [])
            ?_ (safeEncodePacked_uint256_word (safeDomainSeparatorAddressWord I)) ?_
          · unfold addressAsUint256 this
            rw [evalExpr?]
            simp only [evalExpr?, envValue, EvalResult.bind, bind, EvalResult.ofOption, pure]
            unfold castValue? uint256St uint256Int
            have haddr : I.codeOwner.val < EVM.twoPow 256 :=
              lt_of_lt_of_le I.codeOwner.isLt (by decide)
            simp [initState, haddr, safeDomainSeparatorAddressWord_toNat]
          · rw [evalPackedArgs?]
            rfl
        simpa using haddr
  unfold domainSeparatorExpr safeDomainSeparatorHashBytes safeDomainSeparatorPreimage
  simp only [evalExpr?, hpacked, EvalResult.bind, bind, pure]
  simp [bytes32Width, byteArray_mk_toArray_eq_toByteArray]

theorem safeDomainSeparatorBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) ∅
      domainseparatorTransition.body
      (.returned { contract := contract, locals := ∅ } (initState cA gh bl σ σ₀ g A I)
        (some [(.fixedBytes bytes32Width (safeDomainSeparatorHashBytes I))])) := by
  refine nonpayableReturnExprBodyReturns (cfg := config) (contract := contract)
    (by simp only [initState]; exact hwv) ?_
  exact safeEval_domainSeparatorExpr

theorem RD.safeReturnWordFromDomainMem974 {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {k C : ℕ} {val : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD safeBytecode ee g s0 ⟨974⟩ (val :: R) mem (UInt256.ofNat 7) rdata acc k C)
    (hmem : mem.size = 224)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 3 ≤ 1024) :
    RDret safeBytecode g s0 acc (UInt256.toByteArray val) := by
  have hret64 :
      (solcScratchReturnMem mem val).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    unfold solcScratchReturnMem
    rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [hmem]; omega) (by omega)]
    exact hread64
  have hret128 :
      (solcScratchReturnMem mem val).readWithPadding 128 32 =
        UInt256.toByteArray val := by
    unfold solcScratchReturnMem
    rw [write32_read_back _ _ 128 (by rw [toByteArray_size]) (by rw [hmem]; omega),
      toByteArray_extract_all]
  exact evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost (mloadFreePtrValue (by rw [hmem]; omega) (by decide) hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (solcScratchReturnMem mem val) (UInt256.ofNat 7) (by native_decide)
      mem_cost (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw push2 ⟨771⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost (mloadFreePtrValue (by
        unfold solcScratchReturnMem
        rw [write32_eq _ _ 128 (by rw [toByteArray_size]) (by rw [hmem]; omega)]
        rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
          ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
        omega) (by decide) hret64) (by decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw ret 0 (UInt256.toByteArray val) (by native_decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + ⟨128⟩).sub ⟨128⟩ = ⟨32⟩ from by decide]
        exact hret128)
      (by evm_ov)]

theorem safeDomainSeparatorX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (safeSelBytes 10)) :
    RDret safeBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (safeDomainSeparatorWord I)) := by
  obtain ⟨_, _, h1552⟩ := safeReachDomainSeparatorBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h1565⟩ := safeGuardPeelOk (gt := ⟨1563⟩) h1552 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  have h1569 := h1565.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov)
  have h1602 := h1569.pushConst safeDomainSeparatorTypehashWord (width := 32)
    (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have h1604 := h1602.dup2 (by native_decide) (by evm_ov)
    |>.mstore 6 safeDomainSeparatorMem1 (UInt256.ofNat 5) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov)
  have h1609 := h1604.chainid (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.add (by native_decide) (by evm_ov)
  have h1610 := h1609.mstore 3 safeDomainSeparatorMem2 (UInt256.ofNat 6)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have h1616 := h1610.uniswapAddress (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.add (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
  have h1617 := h1616.mstore 3 (safeDomainSeparatorMem3 I) (UInt256.ofNat 7)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have h1620 := h1617.push1 ⟨96⟩ (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
  have h1621 := h1620.keccak256 0 (safeDomainSeparatorWord I) (UInt256.ofNat 7)
    (by native_decide) mem_cost (safeDomainSeparatorKeccakWord I) (by native_decide)
    (by evm_ov)
  have h974 := h1621.push2 ⟨974⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by native_decide) (by evm_ov)
  exact RD.safeReturnWordFromDomainMem974 h974
    (safeDomainSeparatorMem3_size I) (safeDomainSeparatorMem_read64 I) (by simp)

theorem safeDomainSeparatorBodyCoreOk {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (safeSelBytes 10))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (safeSelBytes 10) (by native_decide) hsel
  exact safeReEquivExecTransport hcode
    (safeDomainSeparatorX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    (safeSelectorDispatchDomainSeparator hsel) (safeDecode_domainSeparator_ok hsz4)
    (safeDomainSeparatorBodyReturns hwv) rfl hAccounts
    (returnEquiv_of_encode
      (by
        rw [safeDomainSeparatorHashBytes_eq_word]
        simpa [bytes32, bytes32Width] using
          bytes32ReturnEncoding (safeDomainSeparatorWord I)))

theorem safeDomainSeparatorBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hsel : selIs I (safeSelBytes 10))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact safeDomainSeparatorBodyCoreOk hcode hsize hwv hsel hAccounts
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (safeSelBytes 10) (by native_decide) hsel
    obtain ⟨_, _, h1552⟩ := safeReachDomainSeparatorBody (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode
      hsz4 hsize hsel
    have hrev := safeGuardPeelRev (gt := ⟨1563⟩) h1552 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide)
    exact safeNonpayableRevert hcode hrev (safeSelectorDispatchDomainSeparator hsel)
      (fun _ _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.Safe
