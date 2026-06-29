import Examples.OpenZeppelinBench.ERC6909.Storage
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.ERC6909

/-! ## ABI decode and source-level body for `allowance(address,address,uint256)` -/

/-- The raw ABI word for `allowance`'s `owner` argument. -/
abbrev allowanceOwnerWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

/-- The raw ABI word for `allowance`'s `spender` argument. -/
abbrev allowanceSpenderWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

/-- The raw ABI word for `allowance`'s `id` argument. -/
abbrev allowanceIdWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨64⟩ + ⟨4⟩ : UInt256).toNat 32)

abbrev allowanceOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)

abbrev allowanceSpenderValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (allowanceSpenderWord I).toNat)

abbrev allowanceIdValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (allowanceIdWord I).toNat)

abbrev allowanceStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "owner" (allowanceOwnerValue I)).insert "spender"
    (allowanceSpenderValue I)).insert "id" (allowanceIdValue I)

def allowanceSlotOf (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat))
    (.address (AccountAddress.ofNat (allowanceSpenderWord I).toNat))
    (.int (Int.ofNat (allowanceIdWord I).toNat))

def allowanceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD (allowanceSlotOf I) ⟨0⟩)

theorem erc6909Decode_allowance_ok {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = some (allowanceStore I) := by
  exact Reasoning.Theory.decodeCalldata_address_address_uint256_ok
    (cd := I.calldata) (x := "owner") (y := "spender") (z := "id")
    hsz100 hbig hcanonOwner hcanonSpender

theorem erc6909Decode_allowance_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender", "id"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, uint256Int, abiUInt256]
    using Reasoning.Theory.decodeCalldata_address_address_uint256_none_short
      (cd := I.calldata) (x := "owner") (y := "spender") (z := "id") hsz4 hshort

theorem erc6909Decode_allowance_none_noncanon_owner {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hncOwner : ¬ (allowanceOwnerWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender", "id"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, uint256Int, allowanceOwnerWord, calldataWord, abiUInt256]
    using Reasoning.Theory.decodeCalldata_address_address_uint256_none_noncanon0
      (cd := I.calldata) (x := "owner") (y := "spender") (z := "id")
      hsz100 hbig hncOwner

theorem erc6909Decode_allowance_none_noncanon_spender {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hncSpender : ¬ (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender", "id"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, uint256Int, allowanceOwnerWord, allowanceSpenderWord, calldataWord,
    abiUInt256]
    using Reasoning.Theory.decodeCalldata_address_address_uint256_none_noncanon1
      (cd := I.calldata) (x := "owner") (y := "spender") (z := "id")
      hsz100 hbig hcanonOwner hncSpender

theorem erc6909Decode_allowance_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["owner", "spender", "id"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, uint256Int, abiUInt256]
    using Reasoning.Theory.decodeCalldata_address_address_uint256_none_huge
      (cd := I.calldata) (x := "owner") (y := "spender") (z := "id") hbig

theorem allowanceStore_owner (I : ExecutionEnv) :
    (allowanceStore I).get? "owner" = some (allowanceOwnerValue I) := by
  rw [allowanceStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem allowanceStore_spender (I : ExecutionEnv) :
    (allowanceStore I).get? "spender" = some (allowanceSpenderValue I) := by
  rw [allowanceStore, store_get_ne _ _ (by decide), store_get_self]

theorem allowanceStore_id (I : ExecutionEnv) :
    (allowanceStore I).get? "id" = some (allowanceIdValue I) := by
  rw [allowanceStore, store_get_self]

theorem allowanceStore_owner_getElem? (I : ExecutionEnv) :
    (allowanceStore I)["owner"]? = some (allowanceOwnerValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, allowanceStore_owner]

theorem allowanceStore_spender_getElem? (I : ExecutionEnv) :
    (allowanceStore I)["spender"]? = some (allowanceSpenderValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, allowanceStore_spender]

theorem allowanceStore_id_getElem? (I : ExecutionEnv) :
    (allowanceStore I)["id"]? = some (allowanceIdValue I) := by
  rw [← Std.HashMap.get?_eq_getElem?, allowanceStore_id]

theorem evalExpr_allowance_storage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := allowanceStore I } evm
      (.storage (allowanceRef (.var "owner") (.var "spender") (.var "id"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (allowanceSlotOf I)).toNat)) := by
  have hgowner := allowanceStore_owner_getElem? I
  have hgspender := allowanceStore_spender_getElem? I
  have hgid := allowanceStore_id_getElem? I
  have her : evalStorageRef config { contract := contract, locals := allowanceStore I } evm
      (allowanceRef (.var "owner") (.var "spender") (.var "id")) =
      .ok { base := "_allowances",
            steps := [.mindex (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)),
                      .mindex (.address (AccountAddress.ofNat (allowanceSpenderWord I).toNat)),
                      .mindex (.int (Int.ofNat (allowanceIdWord I).toNat))] } := by
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, allowanceRef, evalExpr?,
      EvalResult.bind, EvalResult.ofOption, bind, pure, valueToKey?,
      Std.HashMap.get?_eq_getElem?, hgowner, hgspender, hgid,
      allowanceOwnerValue, allowanceSpenderValue, allowanceIdValue]
  have hty : storageTypeAt? contract.storage
      { base := "_allowances",
        steps := [.mindex (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)),
                  .mindex (.address (AccountAddress.ofNat (allowanceSpenderWord I).toNat)),
                  .mindex (.int (Int.ofNat (allowanceIdWord I).toNat))] } =
      some (.elem (.int uint256Int)) := by
    simp [storageTypeAt?, contract, storageDecls, uint256St, storageTypeStep?]
  have hloc : config.storage.layout
      { base := "_allowances",
        steps := [.mindex (.address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)),
                  .mindex (.address (AccountAddress.ofNat (allowanceSpenderWord I).toNat)),
                  .mindex (.int (Int.ofNat (allowanceIdWord I).toNat))] } =
      fun _ => some (wordLoc (allowanceSlotOf I)) := by
    rfl
  rw [evalExpr_storage_scalar
    (hbase := by
      rw [allowanceStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
        store_get_ne _ _ (by decide)]
      simp)
    (her := her) (hty := hty) (hloc := hloc)]
  congr 1
  exact erc6909StorageLocLoad_uint256 evm (allowanceSlotOf I)

theorem erc6909AllowanceBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (allowanceStore I) allowanceTransition.body
      (.returned { contract := contract, locals := allowanceStore I } evm
        (some (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (allowanceSlotOf I)).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      simpa [allowanceRef] using evalExpr_allowance_storage evm I)

end OpenZeppelinBench.ERC6909

namespace OpenZeppelinBench.ERC6909

/-! ## EVM decode trace for `allowance(address,address,uint256)` -/

set_option maxHeartbeats 1000000 in
/-- ERC6909's shared optimizer-on address decoder at pc 1629, success branch. -/
theorem erc6909AllowanceDecodeAddrOk {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {off ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    (h : RD erc6909BenchBytecode I g s0 ⟨1629⟩ (off :: ret :: R) mem aw rdata (cA, σ) k C)
    (hcanon : (uInt256OfByteArray (I.calldata.readBytes off.toNat 32)).toNat
        < EVM.addressModulus)
    (hret : (D_J erc6909BenchBytecode 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD erc6909BenchBytecode I g s0 ret
      (uInt256OfByteArray (I.calldata.readBytes off.toNat 32) :: R)
      mem aw rdata (cA, σ) k' C' := by
  have hclean : UInt256.eq (uInt256OfByteArray (I.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (I.calldata.readBytes off.toNat 32)) solcAddrMask) =
      ⟨1⟩ :=
    solcAddrCanon_eq hcanon
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    decide
  exact ⟨_, _, evm_run h with [
    jumpdest, dup1, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup2, and, dup2, eq, push2 ⟨1651⟩,
    jumpiT (by rw [hmask, hclean]; decide) (by jump_dest),
    jumpdest, swap2, swap1, pop, jump hret ]⟩

set_option maxHeartbeats 1000000 in
/-- ERC6909's shared optimizer-on address decoder at pc 1629, non-canonical revert branch. -/
theorem erc6909AllowanceDecodeAddrRevert
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {off ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    (h : RD erc6909BenchBytecode I g s0 ⟨1629⟩ (off :: ret :: R) mem aw rdata (cA, σ) k C)
    (hnc : UInt256.eq (uInt256OfByteArray (I.calldata.readBytes off.toNat 32))
        (UInt256.land (uInt256OfByteArray (I.calldata.readBytes off.toNat 32)) solcAddrMask) =
        ⟨0⟩)
    (hov : R.length + 6 ≤ 1024) :
    RDrev erc6909BenchBytecode g s0 := by
  have hmask : ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩ = solcAddrMask := by
    decide
  exact (evm_run h with [
    jumpdest, dup1, calldataload, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup2, and, dup2, eq, push2 ⟨1651⟩,
    jumpiNT (by rw [hmask, hnc]),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ] :
    RDrev erc6909BenchBytecode g s0)

/-- Wrapper pc 266 sets up calldata bounds for `allowance` and jumps to the three-word decoder. -/
theorem erc6909AllowanceX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (_hsz4 : 4 ≤ I.calldata.size) (_hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1847⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨280⟩, ⟨155⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨155⟩, push2 ⟨280⟩, calldatasize, push1 ⟨4⟩, push2 ⟨1847⟩,
    jump (by jump_dest) ]
  exact ⟨_, _, rd'⟩

theorem erc6909AllowanceX_dec1629_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1629⟩
      [⟨4⟩, ⟨1874⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨280⟩, ⟨155⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      ⟨96⟩ = ⟨0⟩ := by
    simpa using solcCalldataStaticLenCheckOk (sz := I.calldata.size) (words := 3)
      hsz100 hszhi hsize
  obtain ⟨k, C, rd⟩ := erc6909AllowanceX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨1865⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push2 ⟨1874⟩, dup5, push2 ⟨1629⟩, jump (by jump_dest) ]⟩

theorem erc6909AllowanceX_dec1874_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1874⟩
      [allowanceOwnerWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨280⟩, ⟨155⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc6909AllowanceX_dec1629_owner (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hreach
  simpa [allowanceOwnerWord] using
    erc6909AllowanceDecodeAddrOk (cA := cA) (σ := σ) (I := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) rd hcanonOwner (by jump_dest) (by evm_ov)

theorem erc6909AllowanceX_dec1629_spender {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1629⟩
      [⟨4⟩ + ⟨32⟩, ⟨1888⟩, ⟨0⟩, ⟨0⟩, allowanceOwnerWord I, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨280⟩, ⟨155⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc6909AllowanceX_dec1874_owner (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonOwner hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, push2 ⟨1888⟩, push1 ⟨32⟩, dup6, add, push2 ⟨1629⟩,
    jump (by jump_dest) ]⟩

theorem erc6909AllowanceX_dec1888_spender {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1888⟩
      [allowanceSpenderWord I, ⟨0⟩, ⟨0⟩, allowanceOwnerWord I, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨280⟩, ⟨155⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc6909AllowanceX_dec1629_spender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonOwner hreach
  simpa [allowanceSpenderWord] using
    erc6909AllowanceDecodeAddrOk (cA := cA) (σ := σ) (I := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) rd hcanonSpender (by jump_dest) (by evm_ov)

theorem erc6909AllowanceX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD erc6909BenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨280⟩
      [allowanceIdWord I, allowanceSpenderWord I, allowanceOwnerWord I, ⟨155⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := erc6909AllowanceX_dec1888_spender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonOwner hcanonSpender hreach
  have rd' := evm_run rd with [
    jumpdest, swap3, swap6, swap3, swap5, pop, pop, pop, push1 ⟨64⟩, swap2, swap1,
    swap2, add, calldataload, swap1, jump (by jump_dest) ]
  exact ⟨_, _, by simpa [allowanceIdWord] using rd'⟩

/-! ## Decode-failure traces -/

theorem erc6909AllowanceX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      ⟨96⟩ = ⟨1⟩ := by
    simpa using solcCalldataStaticLenCheckShort (sz := I.calldata.size) (words := 3)
      hsz4 hshort hsize (by norm_num)
  obtain ⟨k, C, rd⟩ := erc6909AllowanceX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨1865⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909AllowanceX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      ⟨96⟩ = ⟨1⟩ := by
    simpa using solcCalldataStaticLenCheckHuge (sz := I.calldata.size) (words := 3)
      hbig hsize (by norm_num)
  obtain ⟨k, C, rd⟩ := erc6909AllowanceX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨1865⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem erc6909AllowanceX_noncanon_owner {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (allowanceOwnerWord I)
      (UInt256.land (allowanceOwnerWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := erc6909AllowanceX_dec1629_owner (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hreach
  simpa [allowanceOwnerWord] using
    erc6909AllowanceDecodeAddrRevert (cA := cA) (σ := σ) (I := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) rd hnc (by evm_ov)

theorem erc6909AllowanceX_noncanon_spender {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (allowanceSpenderWord I)
      (UInt256.land (allowanceSpenderWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := erc6909AllowanceX_dec1629_spender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonOwner hreach
  simpa [allowanceSpenderWord] using
    erc6909AllowanceDecodeAddrRevert (cA := cA) (σ := σ) (I := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) rd hnc (by evm_ov)

/-! ## EVM scratch memory for the three-level `_allowances` mapping access -/

theorem toByteArray_extract0_32 (w : UInt256) :
    (UInt256.toByteArray w).extract 0 32 = UInt256.toByteArray w := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray w).size ≤ 32
    rw [toByteArray_size])

/-- Memory after storing the `owner` key at scratch offset `0x00`. -/
noncomputable def allowanceOwnerMem (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray owner).write 0 solcFreePtrMem 0 32

/-- Memory after storing the `_allowances` base slot `2` at scratch offset `0x20`. -/
noncomputable def allowanceOwnerHashMem (owner : UInt256) : ByteArray :=
  (UInt256.toByteArray (⟨2⟩ : UInt256)).write 0 (allowanceOwnerMem owner) 32 32

/-- Solidity's base slot for `_allowances[owner]`. -/
noncomputable def allowanceOwnerSlotWord (owner : UInt256) : UInt256 :=
  mapSlot owner ⟨2⟩

/-- Memory after storing the `spender` key at scratch offset `0x00`. -/
noncomputable def allowanceSpenderMem (owner spender : UInt256) : ByteArray :=
  (UInt256.toByteArray spender).write 0 (allowanceOwnerHashMem owner) 0 32

/-- Memory after storing the `_allowances[owner]` base slot at scratch offset `0x20`. -/
noncomputable def allowanceSpenderHashMem (owner spender : UInt256) : ByteArray :=
  (UInt256.toByteArray (allowanceOwnerSlotWord owner)).write 0
    (allowanceSpenderMem owner spender) 32 32

/-- Solidity's base slot for `_allowances[owner][spender]`. -/
noncomputable def allowanceSpenderSlotWord (owner spender : UInt256) : UInt256 :=
  mapSlot spender (allowanceOwnerSlotWord owner)

/-- Memory after storing the `id` key at scratch offset `0x00`. -/
noncomputable def allowanceIdMem (owner spender id : UInt256) : ByteArray :=
  (UInt256.toByteArray id).write 0 (allowanceSpenderHashMem owner spender) 0 32

/-- Memory after storing the `_allowances[owner][spender]` base slot at scratch offset `0x20`. -/
noncomputable def allowanceIdHashMem (owner spender id : UInt256) : ByteArray :=
  (UInt256.toByteArray (allowanceSpenderSlotWord owner spender)).write 0
    (allowanceIdMem owner spender id) 32 32

theorem allowanceOwnerMem_size (owner : UInt256) : (allowanceOwnerMem owner).size = 96 := by
  unfold allowanceOwnerMem
  exact writeWord_size_of_96 solcFreePtrMem owner 0 solcFreePtrMem_size (by omega)

theorem allowanceOwnerHashMem_size (owner : UInt256) :
    (allowanceOwnerHashMem owner).size = 96 := by
  unfold allowanceOwnerHashMem
  exact writeWord_size_of_96 (allowanceOwnerMem owner) ⟨2⟩ 32
    (allowanceOwnerMem_size owner) (by omega)

theorem allowanceSpenderMem_size (owner spender : UInt256) :
    (allowanceSpenderMem owner spender).size = 96 := by
  unfold allowanceSpenderMem
  exact writeWord_size_of_96 (allowanceOwnerHashMem owner) spender 0
    (allowanceOwnerHashMem_size owner) (by omega)

theorem allowanceSpenderHashMem_size (owner spender : UInt256) :
    (allowanceSpenderHashMem owner spender).size = 96 := by
  unfold allowanceSpenderHashMem
  exact writeWord_size_of_96 (allowanceSpenderMem owner spender) (allowanceOwnerSlotWord owner) 32
    (allowanceSpenderMem_size owner spender) (by omega)

theorem allowanceIdMem_size (owner spender id : UInt256) :
    (allowanceIdMem owner spender id).size = 96 := by
  unfold allowanceIdMem
  exact writeWord_size_of_96 (allowanceSpenderHashMem owner spender) id 0
    (allowanceSpenderHashMem_size owner spender) (by omega)

theorem allowanceIdHashMem_size (owner spender id : UInt256) :
    (allowanceIdHashMem owner spender id).size = 96 := by
  unfold allowanceIdHashMem
  exact writeWord_size_of_96 (allowanceIdMem owner spender id)
    (allowanceSpenderSlotWord owner spender) 32 (allowanceIdMem_size owner spender id)
    (by omega)

theorem allowanceOwnerMem_read0 (owner : UInt256) :
    (allowanceOwnerMem owner).readWithPadding 0 32 = UInt256.toByteArray owner := by
  unfold allowanceOwnerMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega),
    toByteArray_extract0_32]

theorem allowanceOwnerMem_read64 (owner : UInt256) :
    (allowanceOwnerMem owner).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold allowanceOwnerMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega) (by omega)
      (by rw [solcFreePtrMem_size]),
    solcFreePtrMem_read64]

theorem allowanceOwnerHashMem_read32 (owner : UInt256) :
    (allowanceOwnerHashMem owner).readWithPadding 32 32 =
      UInt256.toByteArray (⟨2⟩ : UInt256) := by
  unfold allowanceOwnerHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [allowanceOwnerMem_size]; omega),
    toByteArray_extract0_32]

theorem allowanceOwnerHashMem_read64 (owner : UInt256) :
    (allowanceOwnerHashMem owner).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold allowanceOwnerHashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [allowanceOwnerMem_size]; omega) (by omega)
      (by rw [allowanceOwnerMem_size]),
    allowanceOwnerMem_read64]

theorem allowanceOwnerHashMem_read0_64 (owner : UInt256) :
    (allowanceOwnerHashMem owner).readWithPadding 0 64 =
      UInt256.toByteArray owner ++ UInt256.toByteArray (⟨2⟩ : UInt256) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [allowanceOwnerHashMem_size]; omega)]
  unfold allowanceOwnerHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [allowanceOwnerMem_size]; omega)]
  have hownerFull :
      (allowanceOwnerMem owner).extract 0 32 = UInt256.toByteArray owner := by
    have hread := allowanceOwnerMem_read0 owner
    rw [readWithPadding_eq_extract _ 0 (by rw [allowanceOwnerMem_size]; omega)] at hread
    exact hread
  have hslotFull :
      (UInt256.toByteArray (⟨2⟩ : UInt256)).extract 0 32 =
        UInt256.toByteArray (⟨2⟩ : UInt256) :=
    toByteArray_extract0_32 _
  let A0 := (allowanceOwnerMem owner).extract 0 32
  let B0 := (UInt256.toByteArray (⟨2⟩ : UInt256)).extract 0 32
  let C0 := (allowanceOwnerMem owner).extract (32 + 32) (allowanceOwnerMem owner).size
  change (A0 ++ B0 ++ C0).extract 0 64 =
    UInt256.toByteArray owner ++ UInt256.toByteArray (⟨2⟩ : UInt256)
  have hA0 : A0.size = 32 := by
    dsimp [A0]
    rw [ByteArray.size_extract, allowanceOwnerMem_size]
    omega
  have hB0 : B0.size = 32 := by
    dsimp [B0]
    rw [hslotFull, toByteArray_size]
  rw [ByteArray.append_assoc]
  rw [extract_append_span A0 (B0 ++ C0) 0 64 (by omega) (by rw [hA0]; omega)]
  rw [byteArray_extract_self A0, hA0, show 64 - 32 = 32 from rfl]
  rw [extract_append_left B0 C0 0 32 (by rw [hB0])]
  rw [← hB0, byteArray_extract_self B0]
  dsimp [A0, B0]
  rw [hownerFull, hslotFull]

theorem allowanceOwnerKeccakSlot (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((allowanceOwnerHashMem (allowanceOwnerWord I)).readWithPadding 0 64)))
      = allowanceOwnerSlotWord (allowanceOwnerWord I) := by
  rw [allowanceOwnerHashMem_read0_64]
  unfold allowanceOwnerSlotWord mapSlot
  exact mappingSlot_single (allowanceOwnerWord I) ⟨2⟩

theorem allowanceSpenderMem_read0 (owner spender : UInt256) :
    (allowanceSpenderMem owner spender).readWithPadding 0 32 =
      UInt256.toByteArray spender := by
  unfold allowanceSpenderMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [allowanceOwnerHashMem_size]; omega),
    toByteArray_extract0_32]

theorem allowanceSpenderMem_read64 (owner spender : UInt256) :
    (allowanceSpenderMem owner spender).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold allowanceSpenderMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [allowanceOwnerHashMem_size]; omega) (by omega)
      (by rw [allowanceOwnerHashMem_size]),
    allowanceOwnerHashMem_read64]

theorem allowanceSpenderHashMem_read32 (owner spender : UInt256) :
    (allowanceSpenderHashMem owner spender).readWithPadding 32 32 =
      UInt256.toByteArray (allowanceOwnerSlotWord owner) := by
  unfold allowanceSpenderHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [allowanceSpenderMem_size]; omega),
    toByteArray_extract0_32]

theorem allowanceSpenderHashMem_read64 (owner spender : UInt256) :
    (allowanceSpenderHashMem owner spender).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold allowanceSpenderHashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [allowanceSpenderMem_size]; omega) (by omega)
      (by rw [allowanceSpenderMem_size]),
    allowanceSpenderMem_read64]

theorem allowanceSpenderHashMem_read0_64 (owner spender : UInt256) :
    (allowanceSpenderHashMem owner spender).readWithPadding 0 64 =
      UInt256.toByteArray spender ++ UInt256.toByteArray (allowanceOwnerSlotWord owner) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [allowanceSpenderHashMem_size]; omega)]
  unfold allowanceSpenderHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [allowanceSpenderMem_size]; omega)]
  have hspenderFull :
      (allowanceSpenderMem owner spender).extract 0 32 = UInt256.toByteArray spender := by
    have hread := allowanceSpenderMem_read0 owner spender
    rw [readWithPadding_eq_extract _ 0 (by rw [allowanceSpenderMem_size]; omega)] at hread
    exact hread
  have hslotFull :
      (UInt256.toByteArray (allowanceOwnerSlotWord owner)).extract 0 32 =
        UInt256.toByteArray (allowanceOwnerSlotWord owner) :=
    toByteArray_extract0_32 _
  let A0 := (allowanceSpenderMem owner spender).extract 0 32
  let B0 := (UInt256.toByteArray (allowanceOwnerSlotWord owner)).extract 0 32
  let C0 := (allowanceSpenderMem owner spender).extract (32 + 32)
    (allowanceSpenderMem owner spender).size
  change (A0 ++ B0 ++ C0).extract 0 64 =
    UInt256.toByteArray spender ++ UInt256.toByteArray (allowanceOwnerSlotWord owner)
  have hA0 : A0.size = 32 := by
    dsimp [A0]
    rw [ByteArray.size_extract, allowanceSpenderMem_size]
    omega
  have hB0 : B0.size = 32 := by
    dsimp [B0]
    rw [hslotFull, toByteArray_size]
  rw [ByteArray.append_assoc]
  rw [extract_append_span A0 (B0 ++ C0) 0 64 (by omega) (by rw [hA0]; omega)]
  rw [byteArray_extract_self A0, hA0, show 64 - 32 = 32 from rfl]
  rw [extract_append_left B0 C0 0 32 (by rw [hB0])]
  rw [← hB0, byteArray_extract_self B0]
  dsimp [A0, B0]
  rw [hspenderFull, hslotFull]

theorem allowanceSpenderKeccakSlot (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((allowanceSpenderHashMem (allowanceOwnerWord I) (allowanceSpenderWord I))
          |>.readWithPadding 0 64)))
      = allowanceSpenderSlotWord (allowanceOwnerWord I) (allowanceSpenderWord I) := by
  rw [allowanceSpenderHashMem_read0_64]
  unfold allowanceSpenderSlotWord
  exact mappingSlot_single (allowanceSpenderWord I) (allowanceOwnerSlotWord (allowanceOwnerWord I))

theorem allowanceIdMem_read0 (owner spender id : UInt256) :
    (allowanceIdMem owner spender id).readWithPadding 0 32 =
      UInt256.toByteArray id := by
  unfold allowanceIdMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [allowanceSpenderHashMem_size]; omega),
    toByteArray_extract0_32]

theorem allowanceIdMem_read64 (owner spender id : UInt256) :
    (allowanceIdMem owner spender id).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold allowanceIdMem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [allowanceSpenderHashMem_size]; omega) (by omega)
      (by rw [allowanceSpenderHashMem_size]),
    allowanceSpenderHashMem_read64]

theorem allowanceIdHashMem_read32 (owner spender id : UInt256) :
    (allowanceIdHashMem owner spender id).readWithPadding 32 32 =
      UInt256.toByteArray (allowanceSpenderSlotWord owner spender) := by
  unfold allowanceIdHashMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [allowanceIdMem_size]; omega),
    toByteArray_extract0_32]

theorem allowanceIdHashMem_read64 (owner spender id : UInt256) :
    (allowanceIdHashMem owner spender id).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold allowanceIdHashMem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [allowanceIdMem_size]; omega) (by omega)
      (by rw [allowanceIdMem_size]),
    allowanceIdMem_read64]

theorem allowanceIdHashMem_mload64 (owner spender id : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (allowanceIdHashMem owner spender id).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((allowanceIdHashMem owner spender id).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [allowanceIdHashMem_size]; decide) (by decide)
    (allowanceIdHashMem_read64 owner spender id)

theorem allowanceIdHashMem_read0_64 (owner spender id : UInt256) :
    (allowanceIdHashMem owner spender id).readWithPadding 0 64 =
      UInt256.toByteArray id ++ UInt256.toByteArray (allowanceSpenderSlotWord owner spender) := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [allowanceIdHashMem_size]; omega)]
  unfold allowanceIdHashMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [allowanceIdMem_size]; omega)]
  have hidFull :
      (allowanceIdMem owner spender id).extract 0 32 = UInt256.toByteArray id := by
    have hread := allowanceIdMem_read0 owner spender id
    rw [readWithPadding_eq_extract _ 0 (by rw [allowanceIdMem_size]; omega)] at hread
    exact hread
  have hslotFull :
      (UInt256.toByteArray (allowanceSpenderSlotWord owner spender)).extract 0 32 =
        UInt256.toByteArray (allowanceSpenderSlotWord owner spender) :=
    toByteArray_extract0_32 _
  let A0 := (allowanceIdMem owner spender id).extract 0 32
  let B0 := (UInt256.toByteArray (allowanceSpenderSlotWord owner spender)).extract 0 32
  let C0 := (allowanceIdMem owner spender id).extract (32 + 32)
    (allowanceIdMem owner spender id).size
  change (A0 ++ B0 ++ C0).extract 0 64 =
    UInt256.toByteArray id ++ UInt256.toByteArray (allowanceSpenderSlotWord owner spender)
  have hA0 : A0.size = 32 := by
    dsimp [A0]
    rw [ByteArray.size_extract, allowanceIdMem_size]
    omega
  have hB0 : B0.size = 32 := by
    dsimp [B0]
    rw [hslotFull, toByteArray_size]
  rw [ByteArray.append_assoc]
  rw [extract_append_span A0 (B0 ++ C0) 0 64 (by omega) (by rw [hA0]; omega)]
  rw [byteArray_extract_self A0, hA0, show 64 - 32 = 32 from rfl]
  rw [extract_append_left B0 C0 0 32 (by rw [hB0])]
  rw [← hB0, byteArray_extract_self B0]
  dsimp [A0, B0]
  rw [hidFull, hslotFull]

theorem allowanceFinalKeccakSlot (I : ExecutionEnv)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((allowanceIdHashMem (allowanceOwnerWord I) (allowanceSpenderWord I)
          (allowanceIdWord I)).readWithPadding 0 64)))
      = allowanceSlotOf I := by
  rw [allowanceIdHashMem_read0_64]
  unfold allowanceSlotOf allowanceSlot allowanceSpenderSlotWord allowanceOwnerSlotWord mapSlot
  rw [keyValueToWord_address_of_canonical _ hcanonOwner,
    keyValueToWord_address_of_canonical _ hcanonSpender]
  rw [keyValueToWord_uint256 (allowanceIdWord I)]
  exact mappingSlot_single (allowanceIdWord I)
    (uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (allowanceSpenderWord I) ++
      UInt256.toByteArray
        (uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (allowanceOwnerWord I) ++
          UInt256.toByteArray (⟨2⟩ : UInt256)))))))

/-! ## Return memory after the shared one-word wrapper -/

noncomputable def allowanceReturnMem (owner spender id val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 (allowanceIdHashMem owner spender id) 128 32

theorem allowanceReturnMem_size (owner spender id val : UInt256) :
    (allowanceReturnMem owner spender id val).size = 160 := by
  unfold allowanceReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [allowanceIdHashMem_size]; omega)
      (by rw [allowanceIdHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, allowanceIdHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem allowanceReturnMem_read64 (owner spender id val : UInt256) :
    (allowanceReturnMem owner spender id val).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold allowanceReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [allowanceIdHashMem_size]; omega)
      (by rw [allowanceIdHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, allowanceIdHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, allowanceIdHashMem_size, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [allowanceIdHashMem_size]),
    ← readWithPadding_eq_extract _ 64 (by rw [allowanceIdHashMem_size]),
    allowanceIdHashMem_read64]

theorem allowanceReturnMem_mload64 (owner spender id val : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (allowanceReturnMem owner spender id val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((allowanceReturnMem owner spender id val).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [allowanceReturnMem_size]; decide) (by decide)
    (allowanceReturnMem_read64 owner spender id val)

theorem allowanceReturnMem_read128 (owner spender id val : UInt256) :
    (allowanceReturnMem owner spender id val).readWithPadding 128 32 =
      UInt256.toByteArray val := by
  unfold allowanceReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [allowanceIdHashMem_size]; omega)
      (by rw [allowanceIdHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 128 (by
      rw [ByteArray.size_append, ByteArray.size_append, allowanceIdHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size])]
  rw [extract_append_right_window
      (allowanceIdHashMem owner spender id ++
        ffi.ByteArray.zeroes (USize.ofNat (128 - (allowanceIdHashMem owner spender id).size)))
      (UInt256.toByteArray val) 128 160 (by
        rw [ByteArray.size_append, allowanceIdHashMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (128 - 96)).toNat = 32 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))])]
  rw [ByteArray.size_append, allowanceIdHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  norm_num
  exact toByteArray_extract0_32 val

set_option maxHeartbeats 2000000 in
theorem erc6909X_allowance {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus)
    (hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD erc6909BenchBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret erc6909BenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (allowanceWord σ I)) := by
  obtain ⟨_, _, rd280⟩ := erc6909AllowanceX_decoded (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonOwner hcanonSpender hreach
  have hownerSlot := allowanceOwnerKeccakSlot I
  have hspenderSlot := allowanceSpenderKeccakSlot I
  have hslot := allowanceFinalKeccakSlot I hcanonOwner hcanonSpender
  have rd308 := evm_run rd280 with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap3, dup4, and,
    push0, swap1, dup2,
    raw mstore 0 (allowanceOwnerMem (allowanceOwnerWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean_left hcanonOwner]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨2⟩, push1 ⟨32⟩, swap1, dup2,
    raw mstore 0 (allowanceOwnerHashMem (allowanceOwnerWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (allowanceOwnerSlotWord (allowanceOwnerWord I)) (UInt256.ofNat 3)
      (by decide) mem_cost hownerSlot (by decide) (by evm_ov) ]
  have rd309 := RD.swap5 rd308 (by decide) (by evm_ov)
  have rd310 := evm_run rd309 with [swap1]
  have rd311 := RD.swap6 rd310 (by decide) (by evm_ov)
  have rd326 := evm_run rd311 with [
    and, dup3,
    raw mstore 0 (allowanceSpenderMem (allowanceOwnerWord I) (allowanceSpenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rw [solcAddrMask_clean_left hcanonSpender]
        rfl)
      (by decide) (by evm_ov),
    swap3, dup4,
    raw mstore 0 (allowanceSpenderHashMem (allowanceOwnerWord I) (allowanceSpenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup4, dup2,
    raw keccak256 0 (allowanceSpenderSlotWord (allowanceOwnerWord I) (allowanceSpenderWord I))
      (UInt256.ofNat 3) (by decide) mem_cost hspenderSlot (by decide) (by evm_ov),
    swap2, dup2,
    raw mstore 0 (allowanceIdMem (allowanceOwnerWord I) (allowanceSpenderWord I)
        (allowanceIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap2,
    raw mstore 0 (allowanceIdHashMem (allowanceOwnerWord I) (allowanceSpenderWord I)
        (allowanceIdWord I))
      (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw keccak256 0 (allowanceSlotOf I) (UInt256.ofNat 3)
      (by decide) mem_cost hslot (by decide) (by evm_ov) ]
  obtain ⟨_, _, rd327⟩ := rd326.sload (by decide) (by evm_ov)
  have rd155 := evm_run rd327 with [
    swap1, jump (by jump_dest) ]
  have rd165 := evm_run rd155 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (allowanceIdHashMem_mload64 (allowanceOwnerWord I) (allowanceSpenderWord I)
        (allowanceIdWord I))
      (by decide) (by evm_ov),
    swap1, dup2,
    raw mstore 6
      (allowanceReturnMem (allowanceOwnerWord I) (allowanceSpenderWord I)
        (allowanceIdWord I) (allowanceWord σ I))
      (UInt256.ofNat 5) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add ]
  exact evm_run rd165 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (allowanceReturnMem_mload64 (allowanceOwnerWord I) (allowanceSpenderWord I)
        (allowanceIdWord I) (allowanceWord σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (allowanceWord σ I)) (by decide)
      mem_cost
      (by
        rw [show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32
          from by decide]
        change (allowanceReturnMem (allowanceOwnerWord I) (allowanceSpenderWord I)
            (allowanceIdWord I) (allowanceWord σ I)).readWithPadding 128 32 =
          UInt256.toByteArray (allowanceWord σ I)
        exact allowanceReturnMem_read128 (allowanceOwnerWord I) (allowanceSpenderWord I)
          (allowanceIdWord I) (allowanceWord σ I))
      (by evm_ov) ]

theorem erc6909AllowanceSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x59, 0x8a, 0xf9, 0xe7]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x59, 0x8a, 0xf9, 0xe7]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem erc6909Dispatch_allowance {cd : ByteArray}
    (hsel : ((⟨#[0x59, 0x8a, 0xf9, 0xe7]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some allowanceTransition := by
  refine dispatchMsg_eq_some_of_split (pre := [])
    (post := [approveTransition, balanceOfTransition, isOperatorTransition, setOperatorTransition,
      supportsInterfaceTransition, transferTransition, transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, erc6909AllowanceSelectorBytes]; exact hsel)
  intro t ht
  simp at ht

theorem erc6909AllowanceBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = erc6909BenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : ((⟨#[0x59, 0x8a, 0xf9, 0xe7]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true)
    (hreach : ∃ k C, RD erc6909BenchBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := erc6909AllowanceSelector_size hsel
  have hd := erc6909Dispatch_allowance (cd := I.calldata) hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonOwner : (allowanceOwnerWord I).toNat < EVM.addressModulus
      · by_cases hcanonSpender : (allowanceSpenderWord I).toNat < EVM.addressModulus
        · have hdec := erc6909Decode_allowance_ok (I := I) hsz100 hbig
            hcanonOwner hcanonSpender
          have hword : allowanceWord σ_evm I = allowanceWord σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner (allowanceSlotOf I) ⟨0⟩
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (allowanceStore I)
                allowanceTransition.body
                (.returned { contract := contract, locals := allowanceStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (some (.int (Int.ofNat (allowanceWord σ_solm I).toNat)))) := by
            simpa [allowanceWord, initState, Solm.EVM.storageLoad,
              State.lookupAccount] using erc6909AllowanceBodyReturns
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv)
          exact (erc6909X_allowance (g := Sat256.ofUInt256 g)
              hsz100 hsize hbig hcanonOwner hcanonSpender hreach)
            |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [← hword])
              hAccounts
              (returnEquiv_of_encode (by
                simpa [uint256] using uint256ReturnEncoding (allowanceWord σ_evm I)))
        · have hdec := erc6909Decode_allowance_none_noncanon_spender
            (I := I) hsz100 hbig hcanonOwner hcanonSpender
          have hnc : UInt256.eq (allowanceSpenderWord I)
              (UInt256.land (allowanceSpenderWord I) solcAddrMask) = ⟨0⟩ :=
            uInt256_eq_zero_of_ne (fun he => hcanonSpender (solcAddrCanonical_of_clean he))
          exact (erc6909AllowanceX_noncanon_spender (g := Sat256.ofUInt256 g)
              hsz100 hsize hbig hcanonOwner hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := erc6909Decode_allowance_none_noncanon_owner
          (I := I) hsz100 hbig hcanonOwner
        have hnc : UInt256.eq (allowanceOwnerWord I)
            (UInt256.land (allowanceOwnerWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanonOwner (solcAddrCanonical_of_clean he))
        exact (erc6909AllowanceX_noncanon_owner (g := Sat256.ofUInt256 g)
            hsz100 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := erc6909Decode_allowance_none_huge (I := I) hbigge
      exact (erc6909AllowanceX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 100 := by omega
    have hdec := erc6909Decode_allowance_none_short (I := I) hsz4 hshort
    exact (erc6909AllowanceX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end OpenZeppelinBench.ERC6909
