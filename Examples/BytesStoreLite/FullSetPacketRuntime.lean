import Examples.BytesStoreLite.FullSetPacket

namespace BytesStoreLite

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketEmptyOldShortValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hlenZero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hreach := bytesStoreLiteSetPacketDecodeValidReachToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    hcode hwv hsize hsel hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadWord
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setPacket_empty (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList hlenZero
  have hlenMaxWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  exact bytesStoreLiteSetPacketEmptyOldShortRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (tag := bytesStoreLiteSetPacketTagWord I)
    (len := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (payloadStart := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
    hcode hperm hwv hAccounts hreach hd hdec hlenMaxWord hflag hvalid hlenZero

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketShortNonemptyOldShortValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewShort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  have hreach := bytesStoreLiteSetPacketDecodeValidReachToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    hcode hwv hsize hsel hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadWord
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setPacketTransition.params.map Param.name)
        (transitionSignature setPacketTransition).paramTypes I.calldata =
          some (bytesStoreLiteSetPacketLocalsOf
            (BytesStoreLiteCore.setDecodedValueBytes I)
            (bytesStoreLiteSetPacketTagWord I)) := by
    have hdec₀ := bytesStoreLiteDecode_setPacket (I := I)
      hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
    simpa [bytesStoreLiteSetPacketLocals, bytesStoreLiteSetPacketLocalsOf,
      bytesStoreLiteSetPacketTagWord] using hdec₀
  have hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  exact bytesStoreLiteSetPacketShortNonemptyOldShortRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
    (tag := bytesStoreLiteSetPacketTagWord I)
    (len := len)
    (payloadStart := payloadStart)
    hcode hperm hwv hAccounts haccEvm hreach hd hdec
    (by dsimp [len]) (by dsimp [payloadStart]) hoffMax hsrc hpayloadList
    hlenMaxWord hflag hvalid (by simpa [len] using hnz) (by simpa [len] using hnewShort)

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketShortNonemptyOldShortAbsentRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hmissingEvm : σ_evm.find? I.codeOwner = none)
    (hsz68 : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewShort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value := BytesStoreLiteCore.setDecodedValueBytes I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hmissingSolm : σ_solm.find? I.codeOwner = none :=
    accountMapEquiv_find?_none hAccounts hmissingEvm
  have hmissingSolm0 :
      evmSolm0.accountMap.find? evmSolm0.executionEnv.codeOwner = none := by
    simpa [evmSolm0, initState] using hmissingSolm
  have hreach := bytesStoreLiteSetPacketDecodeValidReachToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    hcode hwv hsize hsel hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadWord
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setPacketTransition.params.map Param.name)
        (transitionSignature setPacketTransition).paramTypes I.calldata =
          some (bytesStoreLiteSetPacketLocalsOf
            (BytesStoreLiteCore.setDecodedValueBytes I)
            (bytesStoreLiteSetPacketTagWord I)) := by
    have hdec₀ := bytesStoreLiteDecode_setPacket (I := I)
      hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
    simpa [bytesStoreLiteSetPacketLocals, bytesStoreLiteSetPacketLocalsOf,
      bytesStoreLiteSetPacketTagWord] using hdec₀
  have hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σ_evm) (UInt256.toByteArray ⟨0⟩) := by
    exact bytesStoreLiteX_setPacketShortNonemptyOldShortAbsentReturns
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (tag := bytesStoreLiteSetPacketTagWord I) (len := len)
      (payloadStart := payloadStart)
      hperm hreach hlenMaxWord hflag hvalid (by simpa [len] using hnz)
      (by simpa [len] using hnewShort) hmissingEvm
  have hwrite₀ := bytesStoreLiteWritePacketDataDecodedShortPacked
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
    hAccounts (by dsimp [len]) hpayloadList (by simpa [len] using hnewShort)
    hflag hvalid
  have hdataAbsent :
      Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩
        (solidityShortBytesWord value) = evmSolm0 := by
    exact storageStore_absent evmSolm0 evmSolm0.executionEnv.codeOwner hmissingSolm0
      ⟨2⟩ (solidityShortBytesWord value)
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
          .ok evmSolm0 := by
    simpa [evmSolm0, value, hdataAbsent] using hwrite₀
  have hstore :
      storageLocStore evmSolm0 (uint256Loc ⟨3⟩)
          (.int (Int.ofNat (bytesStoreLiteSetPacketTagWord I).toNat)) =
        some evmSolm0 := by
    have hstore₀ := storageLocStore_uint256 evmSolm0 ⟨3⟩ (bytesStoreLiteSetPacketTagWord I)
    have habs := storageStore_absent evmSolm0 evmSolm0.executionEnv.codeOwner hmissingSolm0
      ⟨3⟩ (bytesStoreLiteSetPacketTagWord I)
    simpa [habs] using hstore₀
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig evmSolm0
        { base := "packet", steps := [.field "data"] } = .ok 0 := by
    have hload :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ = ⟨0⟩ := by
      rw [Solm.EVM.storageLoad, State.lookupAccount, hmissingSolm0]
      rfl
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLitePacketDataRef) (evm := evmSolm0) (baseSlot := ⟨2⟩)
      (header := (⟨0⟩ : UInt256)) (len := 0)
      (bytesStoreLitePacketDataRef_length_slot evmSolm0) hload
      solidityDecodeBytesLengthHeader_zero
  have henc :
      returnEquiv (UInt256.toByteArray ⟨0⟩) (some (.int 0))
        setPacketTransition.returnType := by
    change returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    exact returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256))
  exact bytesStoreLiteSetPacketRuntimeOfWriteAccountMapEquivLength
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
    (tag := bytesStoreLiteSetPacketTagWord I) (n := 0) (o := UInt256.toByteArray ⟨0⟩)
    (acc := (cA, σ_evm)) (evmData := evmSolm0) (evmTag := evmSolm0)
    hcode hwv hret hd (by simpa [value] using hdec) hwrite hstore hlen
    (by simp [evmSolm0, initState]) hAccounts henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketLongOldShortAbsentRuntimeOfReturn
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hmissingEvm : σ_evm.find? I.codeOwner = none)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setPacketTransition)
    (hdec : decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetPacketLocalsOf
          (BytesStoreLiteCore.setDecodedValueBytes I)
          (bytesStoreLiteSetPacketTagWord I)))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hlong : ¬ len.toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σ_evm) (UInt256.toByteArray ⟨0⟩)) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := BytesStoreLiteCore.setDecodedValueBytes I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hmissingSolm : σ_solm.find? I.codeOwner = none :=
    accountMapEquiv_find?_none hAccounts hmissingEvm
  have hmissingSolm0 :
      evmSolm0.accountMap.find? evmSolm0.executionEnv.codeOwner = none := by
    simpa [evmSolm0, initState] using hmissingSolm
  have hwrite₀ := bytesStoreLiteWritePacketDataDecodedLongPacked
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
    hAccounts hlenAbi hpayloadList hlong hflag hvalid
  have hdataWords :
      writeSolidityBytesDataWordsFrom evmSolm0 ⟨2⟩ value 0
          (solidityBytesDataWordCount value.size) = evmSolm0 := by
    exact writeSolidityBytesDataWordsFrom_absent_same
      (evm := evmSolm0) (baseSlot := ⟨2⟩) (value := value) (idx := 0)
      (fuel := solidityBytesDataWordCount value.size) hmissingSolm0
  have hdataAbsent :
      Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom evmSolm0 ⟨2⟩ value 0
            (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom evmSolm0 ⟨2⟩ value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          ⟨2⟩ (solidityBytesHeaderWord value.size) = evmSolm0 := by
    rw [hdataWords]
    exact storageStore_absent evmSolm0 evmSolm0.executionEnv.codeOwner hmissingSolm0
      ⟨2⟩ (solidityBytesHeaderWord value.size)
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
          .ok evmSolm0 := by
    simpa [evmSolm0, value, hdataAbsent] using hwrite₀
  have hstore :
      storageLocStore evmSolm0 (uint256Loc ⟨3⟩)
          (.int (Int.ofNat (bytesStoreLiteSetPacketTagWord I).toNat)) =
        some evmSolm0 := by
    have hstore₀ := storageLocStore_uint256 evmSolm0 ⟨3⟩ (bytesStoreLiteSetPacketTagWord I)
    have habs := storageStore_absent evmSolm0 evmSolm0.executionEnv.codeOwner hmissingSolm0
      ⟨3⟩ (bytesStoreLiteSetPacketTagWord I)
    simpa [habs] using hstore₀
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig evmSolm0
        { base := "packet", steps := [.field "data"] } = .ok 0 := by
    have hload :
        Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ = ⟨0⟩ := by
      rw [Solm.EVM.storageLoad, State.lookupAccount, hmissingSolm0]
      rfl
    exact bytesStoreLiteReadLengthOfHeaderLoad
      (er := bytesStoreLitePacketDataRef) (evm := evmSolm0) (baseSlot := ⟨2⟩)
      (header := (⟨0⟩ : UInt256)) (len := 0)
      (bytesStoreLitePacketDataRef_length_slot evmSolm0) hload
      solidityDecodeBytesLengthHeader_zero
  have henc :
      returnEquiv (UInt256.toByteArray ⟨0⟩) (some (.int 0))
        setPacketTransition.returnType := by
    change returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    exact returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256))
  exact bytesStoreLiteSetPacketRuntimeOfWriteAccountMapEquivLength
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
    (tag := bytesStoreLiteSetPacketTagWord I) (n := 0) (o := UInt256.toByteArray ⟨0⟩)
    (acc := (cA, σ_evm)) (evmData := evmSolm0) (evmTag := evmSolm0)
    hcode hwv hret hd (by simpa [value] using hdec) hwrite hstore hlen
    (by simp [evmSolm0, initState]) hAccounts henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketShortNonemptyOldLongValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat ≠ 0)
    (hnewShort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let oldStoredLen : UInt256 := UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩
  have hreach := bytesStoreLiteSetPacketDecodeValidReachToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    hcode hwv hsize hsel hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadWord
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setPacketTransition.params.map Param.name)
        (transitionSignature setPacketTransition).paramTypes I.calldata =
          some (bytesStoreLiteSetPacketLocalsOf
            (BytesStoreLiteCore.setDecodedValueBytes I)
            (bytesStoreLiteSetPacketTagWord I)) := by
    have hdec₀ := bytesStoreLiteDecode_setPacket (I := I)
      hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
    simpa [bytesStoreLiteSetPacketLocals, bytesStoreLiteSetPacketLocalsOf,
      bytesStoreLiteSetPacketTagWord] using hdec₀
  have hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  exact bytesStoreLiteSetPacketShortNonemptyOldLongRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
    (tag := bytesStoreLiteSetPacketTagWord I)
    (len := len)
    (payloadStart := payloadStart)
    (oldStoredLen := oldStoredLen)
    hcode hperm hwv hAccounts haccEvm hreach hd hdec
    (by dsimp [len]) (by dsimp [payloadStart]) hoffMax hsrc hpayloadList
    hlenMaxWord hflag (by dsimp [oldStoredLen])
    (by simpa [oldStoredLen] using hvalid)
    (by simpa [len] using hnz) (by simpa [len] using hnewShort)

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketEmptyOldLongValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hlenZero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let oldStoredLen : UInt256 := UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩
  have hreach := bytesStoreLiteSetPacketDecodeValidReachToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    hcode hwv hsize hsel hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadWord
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setPacket_empty (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList hlenZero
  have hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  exact bytesStoreLiteSetPacketEmptyOldLongRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (tag := bytesStoreLiteSetPacketTagWord I)
    (len := len)
    (payloadStart := payloadStart)
    (oldStoredLen := oldStoredLen)
    hcode hperm hwv hAccounts hreach hd hdec hlenMaxWord
    hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
    (by simpa [len] using hlenZero)

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketLongNoTailOldShortValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 = 0)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  have hreach := bytesStoreLiteSetPacketDecodeValidReachToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    hcode hwv hsize hsel hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadWord
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setPacketTransition.params.map Param.name)
        (transitionSignature setPacketTransition).paramTypes I.calldata =
          some (bytesStoreLiteSetPacketLocalsOf
            (BytesStoreLiteCore.setDecodedValueBytes I)
            (bytesStoreLiteSetPacketTagWord I)) := by
    have hdec₀ := bytesStoreLiteDecode_setPacket (I := I)
      hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
    simpa [bytesStoreLiteSetPacketLocals, bytesStoreLiteSetPacketLocalsOf,
      bytesStoreLiteSetPacketTagWord] using hdec₀
  have hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size := by
    intro i hi
    have hmod : len.toNat % 32 = 0 := by
      simpa [len] using hnoTailMod
    have hltLen : 32 * i < len.toNat := by
      have hdiv := Nat.div_add_mod len.toNat 32
      omega
    have hsumLt : payloadStart.toNat + 32 * i < I.calldata.size := by
      omega
    omega
  exact bytesStoreLiteSetPacketLongNoTailOldShortRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
    (tag := bytesStoreLiteSetPacketTagWord I)
    (len := len)
    (payloadStart := payloadStart)
    hcode hperm hwv hAccounts haccEvm hreach hd hdec
    (by dsimp [len]) (by dsimp [payloadStart]) hoffMax hsrc haddrBound hpayloadList
    hlenMaxWord (by dsimp [len]; exact Nat.le_of_not_gt hlenMax)
    hflag hvalid
    (by simpa [len] using hnewLong) (by simpa [len] using hnoTailMod)

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketLongNoTailOldShortAbsentRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hmissingEvm : σ_evm.find? I.codeOwner = none)
    (hsz68 : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 = 0)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  have hreach := bytesStoreLiteSetPacketDecodeValidReachToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    hcode hwv hsize hsel hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadWord
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setPacketTransition.params.map Param.name)
        (transitionSignature setPacketTransition).paramTypes I.calldata =
          some (bytesStoreLiteSetPacketLocalsOf
            (BytesStoreLiteCore.setDecodedValueBytes I)
            (bytesStoreLiteSetPacketTagWord I)) := by
    have hdec₀ := bytesStoreLiteDecode_setPacket (I := I)
      hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
    simpa [bytesStoreLiteSetPacketLocals, bytesStoreLiteSetPacketLocalsOf,
      bytesStoreLiteSetPacketTagWord] using hdec₀
  have hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σ_evm) (UInt256.toByteArray ⟨0⟩) := by
    exact bytesStoreLiteX_setPacketLongNoTailOldShortAbsentReturns
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (tag := bytesStoreLiteSetPacketTagWord I) (len := len)
      (payloadStart := payloadStart)
      hperm hreach hlenMaxWord hflag hvalid (by simpa [len] using hnewLong)
      (by simpa [len] using hnoTailMod) hmissingEvm
  exact bytesStoreLiteSetPacketLongOldShortAbsentRuntimeOfReturn
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
    (payloadStart := payloadStart)
    hcode hwv hAccounts hmissingEvm hd hdec (by dsimp [len]) hpayloadList
    (by simpa [len] using hnewLong) hflag hvalid hret

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketLongTailOldShortValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (htailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 ≠ 0)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  have hreach := bytesStoreLiteSetPacketDecodeValidReachToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    hcode hwv hsize hsel hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadWord
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setPacketTransition.params.map Param.name)
        (transitionSignature setPacketTransition).paramTypes I.calldata =
          some (bytesStoreLiteSetPacketLocalsOf
            (BytesStoreLiteCore.setDecodedValueBytes I)
            (bytesStoreLiteSetPacketTagWord I)) := by
    have hdec₀ := bytesStoreLiteDecode_setPacket (I := I)
      hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
    simpa [bytesStoreLiteSetPacketLocals, bytesStoreLiteSetPacketLocalsOf,
      bytesStoreLiteSetPacketTagWord] using hdec₀
  have hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size := by
    intro i hi
    have hfull : 32 * i < len.toNat := by
      have hsucc : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
      have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) :=
        Nat.mul_le_mul_left 32 hsucc
      have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
      have hle := le_trans hmul hdiv
      omega
    exact lt_of_lt_of_le (by omega) (lt_of_le_of_lt hsrc hsize)
  have htailAddrBound :
      payloadStart.toNat + 32 * (len.toNat / 32) < UInt256.size := by
    have htailModLen : len.toNat % 32 ≠ 0 := by
      simpa [len] using htailMod
    have hremPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero htailModLen
    have hdiv := Nat.div_add_mod len.toNat 32
    have hltLen : 32 * (len.toNat / 32) < len.toNat := by
      omega
    exact lt_of_lt_of_le (by omega) (lt_of_le_of_lt hsrc hsize)
  have htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32) :=
    bytesStoreLiteCalldataLongDataAddr_toNat_of_bound
      (payloadStart := payloadStart) (i := len.toNat / 32) htailAddrBound
  exact bytesStoreLiteSetPacketLongTailOldShortRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
    (tag := bytesStoreLiteSetPacketTagWord I)
    (len := len)
    (payloadStart := payloadStart)
    hcode hperm hwv hAccounts haccEvm hreach hd hdec
    (by dsimp [len]) (by dsimp [payloadStart]) hoffMax hsrc haddrBound htailAddr
    hpayloadList hlenMaxWord (by dsimp [len]; exact Nat.le_of_not_gt hlenMax)
    hflag hvalid
    (by simpa [len] using hnewLong) (by simpa [len] using htailMod)

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketLongTailOldShortAbsentRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hmissingEvm : σ_evm.find? I.codeOwner = none)
    (hsz68 : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (htailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 ≠ 0)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  have hreach := bytesStoreLiteSetPacketDecodeValidReachToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    hcode hwv hsize hsel hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadWord
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setPacketTransition.params.map Param.name)
        (transitionSignature setPacketTransition).paramTypes I.calldata =
          some (bytesStoreLiteSetPacketLocalsOf
            (BytesStoreLiteCore.setDecodedValueBytes I)
            (bytesStoreLiteSetPacketTagWord I)) := by
    have hdec₀ := bytesStoreLiteDecode_setPacket (I := I)
      hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
    simpa [bytesStoreLiteSetPacketLocals, bytesStoreLiteSetPacketLocalsOf,
      bytesStoreLiteSetPacketTagWord] using hdec₀
  have hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σ_evm) (UInt256.toByteArray ⟨0⟩) := by
    exact bytesStoreLiteX_setPacketLongTailOldShortAbsentReturns
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (tag := bytesStoreLiteSetPacketTagWord I) (len := len)
      (payloadStart := payloadStart)
      hperm hreach hlenMaxWord hflag hvalid (by simpa [len] using hnewLong)
      (by simpa [len] using htailMod) hmissingEvm
  exact bytesStoreLiteSetPacketLongOldShortAbsentRuntimeOfReturn
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
    (payloadStart := payloadStart)
    hcode hwv hAccounts hmissingEvm hd hdec (by dsimp [len]) hpayloadList
    (by simpa [len] using hnewLong) hflag hvalid hret

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketLongNoTailOldLongNoClearValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 = 0)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew :
      UInt256.gt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let oldStoredLen : UInt256 := UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩
  have hreach := bytesStoreLiteSetPacketDecodeValidReachToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    hcode hwv hsize hsel hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadWord
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setPacketTransition.params.map Param.name)
        (transitionSignature setPacketTransition).paramTypes I.calldata =
          some (bytesStoreLiteSetPacketLocalsOf
            (BytesStoreLiteCore.setDecodedValueBytes I)
            (bytesStoreLiteSetPacketTagWord I)) := by
    have hdec₀ := bytesStoreLiteDecode_setPacket (I := I)
      hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
    simpa [bytesStoreLiteSetPacketLocals, bytesStoreLiteSetPacketLocalsOf,
      bytesStoreLiteSetPacketTagWord] using hdec₀
  have hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size := by
    intro i hi
    have hmod : len.toNat % 32 = 0 := by
      simpa [len] using hnoTailMod
    have hltLen : 32 * i < len.toNat := by
      have hdiv := Nat.div_add_mod len.toNat 32
      omega
    have hsumLt : payloadStart.toNat + 32 * i < I.calldata.size := by
      omega
    omega
  exact bytesStoreLiteSetPacketLongNoTailOldLongNoClearRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
    (tag := bytesStoreLiteSetPacketTagWord I)
    (len := len)
    (payloadStart := payloadStart)
    (oldStoredLen := oldStoredLen)
    hcode hperm hwv hAccounts haccEvm hreach hd hdec
    (by dsimp [len]) (by dsimp [payloadStart]) hoffMax hsrc haddrBound hpayloadList
    hlenMaxWord (by dsimp [len]; exact Nat.le_of_not_gt hlenMax)
    hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
    (by simpa [oldStoredLen, len] using hgtOldNew)
    (by simpa [len] using hnewLong) (by simpa [len] using hnoTailMod)

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketLongTailOldLongNoClearValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (htailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 ≠ 0)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew :
      UInt256.gt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let oldStoredLen : UInt256 := UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩
  have hreach := bytesStoreLiteSetPacketDecodeValidReachToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    hcode hwv hsize hsel hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadWord
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setPacketTransition.params.map Param.name)
        (transitionSignature setPacketTransition).paramTypes I.calldata =
          some (bytesStoreLiteSetPacketLocalsOf
            (BytesStoreLiteCore.setDecodedValueBytes I)
            (bytesStoreLiteSetPacketTagWord I)) := by
    have hdec₀ := bytesStoreLiteDecode_setPacket (I := I)
      hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
    simpa [bytesStoreLiteSetPacketLocals, bytesStoreLiteSetPacketLocalsOf,
      bytesStoreLiteSetPacketTagWord] using hdec₀
  have hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size := by
    intro i hi
    have hfull : 32 * i < len.toNat := by
      have hsucc : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
      have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) :=
        Nat.mul_le_mul_left 32 hsucc
      have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
      have hle := le_trans hmul hdiv
      omega
    exact lt_of_lt_of_le (by omega) (lt_of_le_of_lt hsrc hsize)
  have htailAddrBound :
      payloadStart.toNat + 32 * (len.toNat / 32) < UInt256.size := by
    have htailModLen : len.toNat % 32 ≠ 0 := by
      simpa [len] using htailMod
    have hremPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero htailModLen
    have hdiv := Nat.div_add_mod len.toNat 32
    have hltLen : 32 * (len.toNat / 32) < len.toNat := by
      omega
    exact lt_of_lt_of_le (by omega) (lt_of_le_of_lt hsrc hsize)
  have htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32) :=
    bytesStoreLiteCalldataLongDataAddr_toNat_of_bound
      (payloadStart := payloadStart) (i := len.toNat / 32) htailAddrBound
  exact bytesStoreLiteSetPacketLongTailOldLongNoClearRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
    (tag := bytesStoreLiteSetPacketTagWord I)
    (len := len)
    (payloadStart := payloadStart)
    (oldStoredLen := oldStoredLen)
    hcode hperm hwv hAccounts haccEvm hreach hd hdec
    (by dsimp [len]) (by dsimp [payloadStart]) hoffMax hsrc haddrBound htailAddr
    hpayloadList hlenMaxWord (by dsimp [len]; exact Nat.le_of_not_gt hlenMax)
    hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
    (by simpa [oldStoredLen, len] using hgtOldNew)
    (by simpa [len] using hnewLong) (by simpa [len] using htailMod)

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketLongNoTailOldLongClearValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 = 0)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew :
      UInt256.gt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨1⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let oldStoredLen : UInt256 := UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩
  have hreach := bytesStoreLiteSetPacketDecodeValidReachToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    hcode hwv hsize hsel hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadWord
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setPacketTransition.params.map Param.name)
        (transitionSignature setPacketTransition).paramTypes I.calldata =
          some (bytesStoreLiteSetPacketLocalsOf
            (BytesStoreLiteCore.setDecodedValueBytes I)
            (bytesStoreLiteSetPacketTagWord I)) := by
    have hdec₀ := bytesStoreLiteDecode_setPacket (I := I)
      hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
    simpa [bytesStoreLiteSetPacketLocals, bytesStoreLiteSetPacketLocalsOf,
      bytesStoreLiteSetPacketTagWord] using hdec₀
  have hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size := by
    intro i hi
    have hmod : len.toNat % 32 = 0 := by
      simpa [len] using hnoTailMod
    have hltLen : 32 * i < len.toNat := by
      have hdiv := Nat.div_add_mod len.toNat 32
      omega
    have hsumLt : payloadStart.toNat + 32 * i < I.calldata.size := by
      omega
    omega
  exact bytesStoreLiteSetPacketLongNoTailOldLongClearRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
    (tag := bytesStoreLiteSetPacketTagWord I)
    (len := len)
    (payloadStart := payloadStart)
    (oldStoredLen := oldStoredLen)
    hcode hperm hwv hAccounts haccEvm hreach hd hdec
    (by dsimp [len]) (by dsimp [payloadStart]) hoffMax hsrc haddrBound hpayloadList
    hlenMaxWord (by dsimp [len]; exact Nat.le_of_not_gt hlenMax)
    hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
    (by simpa [oldStoredLen, len] using hgtOldNew)
    (by simpa [len] using hnewLong) (by simpa [len] using hnoTailMod)

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketLongTailOldLongClearValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (htailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat % 32 ≠ 0)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew :
      UInt256.gt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)) = ⟨1⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let oldStoredLen : UInt256 := UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩
  have hreach := bytesStoreLiteSetPacketDecodeValidReachToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    hcode hwv hsize hsel hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadWord
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setPacketTransition.params.map Param.name)
        (transitionSignature setPacketTransition).paramTypes I.calldata =
          some (bytesStoreLiteSetPacketLocalsOf
            (BytesStoreLiteCore.setDecodedValueBytes I)
            (bytesStoreLiteSetPacketTagWord I)) := by
    have hdec₀ := bytesStoreLiteDecode_setPacket (I := I)
      hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
    simpa [bytesStoreLiteSetPacketLocals, bytesStoreLiteSetPacketLocalsOf,
      bytesStoreLiteSetPacketTagWord] using hdec₀
  have hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart, len]
    rw [BytesStoreLiteCore.setPayloadStart_toNat I.calldata hoffMax]
    exact BytesStoreLiteCore.setPayloadStartLen_le_of_payload I.calldata hlenWord hpayloadList
  have haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size := by
    intro i hi
    have hfull : 32 * i < len.toNat := by
      have hsucc : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
      have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) :=
        Nat.mul_le_mul_left 32 hsucc
      have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
      have hle := le_trans hmul hdiv
      omega
    exact lt_of_lt_of_le (by omega) (lt_of_le_of_lt hsrc hsize)
  have htailAddrBound :
      payloadStart.toNat + 32 * (len.toNat / 32) < UInt256.size := by
    have htailModLen : len.toNat % 32 ≠ 0 := by
      simpa [len] using htailMod
    have hremPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero htailModLen
    have hdiv := Nat.div_add_mod len.toNat 32
    have hltLen : 32 * (len.toNat / 32) < len.toNat := by
      omega
    exact lt_of_lt_of_le (by omega) (lt_of_le_of_lt hsrc hsize)
  have htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32) :=
    bytesStoreLiteCalldataLongDataAddr_toNat_of_bound
      (payloadStart := payloadStart) (i := len.toNat / 32) htailAddrBound
  exact bytesStoreLiteSetPacketLongTailOldLongClearRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
    (tag := bytesStoreLiteSetPacketTagWord I)
    (len := len)
    (payloadStart := payloadStart)
    (oldStoredLen := oldStoredLen)
    hcode hperm hwv hAccounts haccEvm hreach hd hdec
    (by dsimp [len]) (by dsimp [payloadStart]) hoffMax hsrc haddrBound htailAddr
    hpayloadList hlenMaxWord (by dsimp [len]; exact Nat.le_of_not_gt hlenMax)
    hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
    (by simpa [oldStoredLen, len] using hgtOldNew)
    (by simpa [len] using hnewLong) (by simpa [len] using htailMod)

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketOldLongMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  let tag : UInt256 := bytesStoreLiteSetPacketTagWord I
  have hreach := bytesStoreLiteSetPacketDecodeValidReachToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    hcode hwv hsize hsel hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadWord
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setPacketTransition.params.map Param.name)
        (transitionSignature setPacketTransition).paramTypes I.calldata =
          some (bytesStoreLiteSetPacketLocalsOf value tag) := by
    have hdec₀ := bytesStoreLiteDecode_setPacket (I := I)
      hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
    simpa [value, tag, bytesStoreLiteSetPacketLocals, bytesStoreLiteSetPacketLocalsOf,
      bytesStoreLiteSetPacketTagWord] using hdec₀
  have hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hrev :
      RDrev bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    simpa [tag, len, payloadStart] using
      bytesStoreLiteX_setPacketLongMalformedHeader
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (tag := tag) (len := len) (payloadStart := payloadStart)
        hreach hlenMaxWord hflag hbad
  have hwrite :
      writeStorage? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
          .revert := by
    have hwrite₀ := bytesStoreLiteWritePacketDataMalformedLongOfAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
      hAccounts hflag hbad
    simpa [value] using hwrite₀
  exact bytesStoreLiteSetPacketRuntimeOfWriteRevert
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value) (tag := tag)
    hcode hwv hrev hd hdec hwrite

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketOldShortMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  let payloadStart : UInt256 := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩
  let value : ByteArray := BytesStoreLiteCore.setDecodedValueBytes I
  let tag : UInt256 := bytesStoreLiteSetPacketTagWord I
  have hreach := bytesStoreLiteSetPacketDecodeValidReachToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    hcode hwv hsize hsel hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadWord
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setPacketTransition.params.map Param.name)
        (transitionSignature setPacketTransition).paramTypes I.calldata =
          some (bytesStoreLiteSetPacketLocalsOf value tag) := by
    have hdec₀ := bytesStoreLiteDecode_setPacket (I := I)
      hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
    simpa [value, tag, bytesStoreLiteSetPacketLocals, bytesStoreLiteSetPacketLocalsOf,
      bytesStoreLiteSetPacketTagWord] using hdec₀
  have hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    dsimp [len]
    exact Nat.le_of_not_gt hlenMax
  have hrev :
      RDrev bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    simpa [tag, len, payloadStart] using
      bytesStoreLiteX_setPacketShortMalformedHeader
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (tag := tag) (len := len) (payloadStart := payloadStart)
        hreach hlenMaxWord hflag hbad
  have hwrite :
      writeStorage? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
          .revert := by
    have hwrite₀ := bytesStoreLiteWritePacketDataMalformedShortOfAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value)
      hAccounts hflag hbad
    simpa [value] using hwrite₀
  exact bytesStoreLiteSetPacketRuntimeOfWriteRevert
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value) (tag := tag)
    hcode hwv hrev hd hdec hwrite

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketDecodedRuntimeOfAccount
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
  by_cases hlenZero : len = ⟨0⟩
  · by_cases hflagShort :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
    · by_cases hvalidShort :
        UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩
      · exact bytesStoreLiteSetPacketEmptyOldShortValidRuntime
          hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
          hlenMax hpayloadList hpayloadWord (by simpa [len] using hlenZero)
          hflagShort hvalidShort
      · exact bytesStoreLiteSetPacketOldShortMalformedRuntime
          hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
          hlenMax hpayloadList hpayloadWord hflagShort (not_ne_iff.mp hvalidShort)
    · have hflagLong :
        UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ := hflagShort
      by_cases hvalidLong :
        UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨32⟩) ≠ ⟨0⟩
      · exact bytesStoreLiteSetPacketEmptyOldLongValidRuntime
          hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
          hlenMax hpayloadList hpayloadWord (by simpa [len] using hlenZero)
          hflagLong hvalidLong
      · exact bytesStoreLiteSetPacketOldLongMalformedRuntime
          hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
          hlenMax hpayloadList hpayloadWord hflagLong (not_ne_iff.mp hvalidLong)
  · have hnz : len.toNat ≠ 0 := by
      intro hz
      apply hlenZero
      apply u256_inj
      simpa [hz]
    by_cases hnewShort : len.toNat < 32
    · by_cases hflagShort :
        UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
      · by_cases hvalidShort :
          UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
            (UInt256.lt
              (UInt256.land
                (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
                ⟨127⟩)
              ⟨32⟩) ≠ ⟨0⟩
        · exact bytesStoreLiteSetPacketShortNonemptyOldShortValidRuntime
            hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign hoffMax
            hlenWord hlenMax hpayloadList hpayloadWord (by simpa [len] using hnz)
            (by simpa [len] using hnewShort) hflagShort hvalidShort
        · exact bytesStoreLiteSetPacketOldShortMalformedRuntime
            hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
            hlenMax hpayloadList hpayloadWord hflagShort (not_ne_iff.mp hvalidShort)
      · have hflagLong :
          UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ := hflagShort
        by_cases hvalidLong :
          UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
            (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
              ⟨32⟩) ≠ ⟨0⟩
        · exact bytesStoreLiteSetPacketShortNonemptyOldLongValidRuntime
            hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign hoffMax
            hlenWord hlenMax hpayloadList hpayloadWord (by simpa [len] using hnz)
            (by simpa [len] using hnewShort) hflagLong hvalidLong
        · exact bytesStoreLiteSetPacketOldLongMalformedRuntime
            hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
            hlenMax hpayloadList hpayloadWord hflagLong (not_ne_iff.mp hvalidLong)
    · have hnewLong :
        ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32 := by
        simpa [len] using hnewShort
      by_cases hflagShort :
        UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
      · by_cases hvalidShort :
          UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
            (UInt256.lt
              (UInt256.land
                (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
                ⟨127⟩)
              ⟨32⟩) ≠ ⟨0⟩
        · by_cases hnoTail :
            (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat %
                32 = 0
          · exact bytesStoreLiteSetPacketLongNoTailOldShortValidRuntime
              hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign hoffMax
              hlenWord hlenMax hpayloadList hpayloadWord hnewLong hnoTail hflagShort
              hvalidShort
          · exact bytesStoreLiteSetPacketLongTailOldShortValidRuntime
              hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign hoffMax
              hlenWord hlenMax hpayloadList hpayloadWord hnewLong hnoTail hflagShort
              hvalidShort
        · exact bytesStoreLiteSetPacketOldShortMalformedRuntime
            hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
            hlenMax hpayloadList hpayloadWord hflagShort (not_ne_iff.mp hvalidShort)
      · have hflagLong :
          UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ := hflagShort
        by_cases hvalidLong :
          UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
            (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
              ⟨32⟩) ≠ ⟨0⟩
        · let oldLen : UInt256 :=
            UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩
          by_cases hgtOldNew :
            UInt256.gt oldLen len = ⟨1⟩
          · by_cases hnoTail :
              (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat %
                  32 = 0
            · exact bytesStoreLiteSetPacketLongNoTailOldLongClearValidRuntime
                hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign hoffMax
                hlenWord hlenMax hpayloadList hpayloadWord hnewLong hnoTail hflagLong
                hvalidLong (by simpa [oldLen, len] using hgtOldNew)
            · exact bytesStoreLiteSetPacketLongTailOldLongClearValidRuntime
                hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign hoffMax
                hlenWord hlenMax hpayloadList hpayloadWord hnewLong hnoTail hflagLong
                hvalidLong (by simpa [oldLen, len] using hgtOldNew)
          · have hgtOldNew0 : UInt256.gt oldLen len = ⟨0⟩ := by
              by_cases hle : oldLen.toNat ≤ len.toNat
              · exact ugt_zero hle
              · exact False.elim (hgtOldNew (ugt_one (Nat.lt_of_not_ge hle)))
            by_cases hnoTail :
              (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat %
                  32 = 0
            · exact bytesStoreLiteSetPacketLongNoTailOldLongNoClearValidRuntime
                hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign hoffMax
                hlenWord hlenMax hpayloadList hpayloadWord hnewLong hnoTail hflagLong
                hvalidLong (by simpa [oldLen, len] using hgtOldNew0)
            · exact bytesStoreLiteSetPacketLongTailOldLongNoClearValidRuntime
                hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign hoffMax
                hlenWord hlenMax hpayloadList hpayloadWord hnewLong hnoTail hflagLong
                hvalidLong (by simpa [oldLen, len] using hgtOldNew0)
        · exact bytesStoreLiteSetPacketOldLongMalformedRuntime
            hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
            hlenMax hpayloadList hpayloadWord hflagLong (not_ne_iff.mp hvalidLong)

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketDecodedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  cases hacc : σ_evm.find? I.codeOwner with
  | some accEvm =>
      exact bytesStoreLiteSetPacketDecodedRuntimeOfAccount
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
        hcode hsize hperm hwv hsel hAccounts hacc hsz68 hhi hsizeSign hoffMax
        hlenWord hlenMax hpayloadList hpayloadWord
  | none =>
      let len : UInt256 :=
        calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)
      have hflagShort :
          UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
        change UInt256.land
            ((σ_evm.find? I.codeOwner).option ⟨0⟩
              (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩ = ⟨0⟩
        rw [hacc]
        native_decide
      have hvalidShort :
          UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
            (UInt256.lt
              (UInt256.land
                (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
                ⟨127⟩)
              ⟨32⟩) ≠ ⟨0⟩ := by
        change UInt256.sub (UInt256.land
            ((σ_evm.find? I.codeOwner).option ⟨0⟩
              (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩)
            (UInt256.lt
              (UInt256.land
                (UInt256.div
                  ((σ_evm.find? I.codeOwner).option ⟨0⟩
                    (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨2⟩)
                ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
        rw [hacc]
        native_decide
      by_cases hlenZero : len = ⟨0⟩
      · exact bytesStoreLiteSetPacketEmptyOldShortValidRuntime
          hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
          hlenMax hpayloadList hpayloadWord (by simpa [len] using hlenZero)
          hflagShort hvalidShort
      · have hnz : len.toNat ≠ 0 := by
          intro hz
          apply hlenZero
          apply u256_inj
          simpa [hz]
        by_cases hnewShort : len.toNat < 32
        · exact bytesStoreLiteSetPacketShortNonemptyOldShortAbsentRuntime
            hcode hsize hperm hwv hsel hAccounts hacc hsz68 hhi hsizeSign hoffMax
            hlenWord hlenMax hpayloadList hpayloadWord (by simpa [len] using hnz)
            (by simpa [len] using hnewShort) hflagShort hvalidShort
        · have hnewLong :
            ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32 := by
            simpa [len] using hnewShort
          by_cases hnoTail :
            (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat %
                32 = 0
          · exact bytesStoreLiteSetPacketLongNoTailOldShortAbsentRuntime
              hcode hsize hperm hwv hsel hAccounts hacc hsz68 hhi hsizeSign hoffMax
              hlenWord hlenMax hpayloadList hpayloadWord hnewLong hnoTail hflagShort
              hvalidShort
          · exact bytesStoreLiteSetPacketLongTailOldShortAbsentRuntime
              hcode hsize hperm hwv hsel hAccounts hacc hsz68 hhi hsizeSign hoffMax
              hlenWord hlenMax hpayloadList hpayloadWord hnewLong hnoTail hflagShort
              hvalidShort

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketRuntimeOfAccount
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hshort : I.calldata.size < 68
  · exact bytesStoreLiteSetPacketDecodeShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hshort
  · have hsz68 : 68 ≤ I.calldata.size := Nat.le_of_not_gt hshort
    by_cases hbig : 2 ^ 255 + 4 ≤ I.calldata.size
    · exact bytesStoreLiteSetPacketDecodeHugeRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hbig
    · have hhi : I.calldata.size < 2 ^ 255 + 4 := Nat.lt_of_not_ge hbig
      by_cases hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat
      · exact bytesStoreLiteSetPacketDecodeOffsetHugeRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts hsz68 hhi hoff
      · have hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat := hoff
        by_cases hsizeSign : I.calldata.size < 2 ^ 255
        · by_cases hlenShort :
            I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32
          · exact bytesStoreLiteSetPacketDecodeLengthShortRuntime
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenShort
          · have hlenWord :
              4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size :=
              Nat.le_of_not_gt hlenShort
            by_cases hlenHuge :
                ABI.solcMaxU64 <
                  (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat
            · exact bytesStoreLiteSetPacketDecodeLengthHugeRuntime
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax
                hlenWord hlenHuge
            · by_cases hpayloadList :
                ((((I.calldata.toList.drop 4).drop
                  ((calldataWord I.calldata 4).toNat + 32)).take
                  (calldataWord I.calldata
                    (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
                  (calldataWord I.calldata
                    (4 + (calldataWord I.calldata 4).toNat)).toNat)
              · have hpayloadWord :
                  UInt256.gt
                    (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
                      uInt256OfByteArray
                        (I.calldata.readBytes
                          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
                      ⟨32⟩))
                    (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
                  have hpayloadWordCore :=
                    BytesStoreLiteCore.setPayloadWord_zero_of_payload I.calldata hsize
                      hoffMax hlenWord hlenHuge hpayloadList
                  exact bytesStoreLiteSetPayloadWordFull_of_core hpayloadWordCore
                exact bytesStoreLiteSetPacketDecodedRuntimeOfAccount
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  (accEvm := accEvm)
                  hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign
                  hoffMax hlenWord hlenHuge hpayloadList hpayloadWord
              · have hpayloadListNe :
                  ((((I.calldata.toList.drop 4).drop
                    ((calldataWord I.calldata 4).toNat + 32)).take
                    (calldataWord I.calldata
                      (4 + (calldataWord I.calldata 4).toNat)).toNat).length ≠
                    (calldataWord I.calldata
                      (4 + (calldataWord I.calldata 4).toNat)).toNat) := hpayloadList
                have hpayloadWord :
                    UInt256.gt
                      (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
                        uInt256OfByteArray
                          (I.calldata.readBytes
                            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
                        ⟨32⟩))
                      (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
                  have hpayloadWordCore :=
                    BytesStoreLiteCore.setPayloadWord_one_of_payload_short I.calldata hsize
                      hoffMax hlenWord hlenHuge hpayloadListNe
                  exact bytesStoreLiteSetPayloadWordFull_of_core hpayloadWordCore
                exact bytesStoreLiteSetPacketDecodePayloadShortRuntime
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax
                  hlenWord hlenHuge hpayloadListNe hpayloadWord
        · exact bytesStoreLiteSetPacketDecodeTotalHighRuntime
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hcode hsize hperm hwv hsel hAccounts hsz68 hhi hoffMax hsizeSign

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hshort : I.calldata.size < 68
  · exact bytesStoreLiteSetPacketDecodeShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hshort
  · have hsz68 : 68 ≤ I.calldata.size := Nat.le_of_not_gt hshort
    by_cases hbig : 2 ^ 255 + 4 ≤ I.calldata.size
    · exact bytesStoreLiteSetPacketDecodeHugeRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hbig
    · have hhi : I.calldata.size < 2 ^ 255 + 4 := Nat.lt_of_not_ge hbig
      by_cases hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat
      · exact bytesStoreLiteSetPacketDecodeOffsetHugeRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts hsz68 hhi hoff
      · have hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat := hoff
        by_cases hsizeSign : I.calldata.size < 2 ^ 255
        · by_cases hlenShort :
            I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32
          · exact bytesStoreLiteSetPacketDecodeLengthShortRuntime
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenShort
          · have hlenWord :
              4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size :=
              Nat.le_of_not_gt hlenShort
            by_cases hlenHuge :
                ABI.solcMaxU64 <
                  (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat
            · exact bytesStoreLiteSetPacketDecodeLengthHugeRuntime
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax
                hlenWord hlenHuge
            · by_cases hpayloadList :
                ((((I.calldata.toList.drop 4).drop
                  ((calldataWord I.calldata 4).toNat + 32)).take
                  (calldataWord I.calldata
                    (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
                  (calldataWord I.calldata
                    (4 + (calldataWord I.calldata 4).toNat)).toNat)
              · have hpayloadWord :
                  UInt256.gt
                    (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
                      uInt256OfByteArray
                        (I.calldata.readBytes
                          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
                      ⟨32⟩))
                    (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
                  have hpayloadWordCore :=
                    BytesStoreLiteCore.setPayloadWord_zero_of_payload I.calldata hsize
                      hoffMax hlenWord hlenHuge hpayloadList
                  exact bytesStoreLiteSetPayloadWordFull_of_core hpayloadWordCore
                exact bytesStoreLiteSetPacketDecodedRuntime
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign
                  hoffMax hlenWord hlenHuge hpayloadList hpayloadWord
              · have hpayloadListNe :
                  ((((I.calldata.toList.drop 4).drop
                    ((calldataWord I.calldata 4).toNat + 32)).take
                    (calldataWord I.calldata
                      (4 + (calldataWord I.calldata 4).toNat)).toNat).length ≠
                    (calldataWord I.calldata
                      (4 + (calldataWord I.calldata 4).toNat)).toNat) := hpayloadList
                have hpayloadWord :
                    UInt256.gt
                      (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
                        uInt256OfByteArray
                          (I.calldata.readBytes
                            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
                        ⟨32⟩))
                      (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
                  have hpayloadWordCore :=
                    BytesStoreLiteCore.setPayloadWord_one_of_payload_short I.calldata hsize
                      hoffMax hlenWord hlenHuge hpayloadListNe
                  exact bytesStoreLiteSetPayloadWordFull_of_core hpayloadWordCore
                exact bytesStoreLiteSetPacketDecodePayloadShortRuntime
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax
                  hlenWord hlenHuge hpayloadListNe hpayloadWord
        · exact bytesStoreLiteSetPacketDecodeTotalHighRuntime
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hcode hsize hperm hwv hsel hAccounts hsz68 hhi hoffMax hsizeSign

end BytesStoreLite
