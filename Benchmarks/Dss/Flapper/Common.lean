import Reasoning.PackedStorage
import Reasoning.SolcRoutines
import Benchmarks.Dss.Flapper.Bytecode
import Reasoning.ABI
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Storage
import Reasoning.Dispatch
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# MakerDAO/Sky DSS Flapper shared proof foundation

Contract-wide selector notation and constants for the optimized Flapper runtime.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flapper

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev flapperSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order. -/
def flapperSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x7d, 0x78, 0x0d, 0x82]⟩  -- beg()
  | 1 => ⟨#[0x44, 0x23, 0xc5, 0xf1]⟩  -- bids(uint256)
  | 2 => ⟨#[0xa2, 0xf9, 0x1a, 0xf2]⟩  -- cage(uint256)
  | 3 => ⟨#[0xc9, 0x59, 0xc4, 0x2b]⟩  -- deal(uint256)
  | 4 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩  -- deny(address)
  | 5 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩  -- file(bytes32,uint256)
  | 6 => ⟨#[0xd9, 0xc5, 0x5c, 0xe1]⟩  -- fill()
  | 7 => ⟨#[0x7b, 0xd2, 0xbe, 0xa7]⟩  -- gem()
  | 8 => ⟨#[0xca, 0x40, 0xc4, 0x19]⟩  -- kick(uint256,uint256)
  | 9 => ⟨#[0xcf, 0xdd, 0x33, 0x02]⟩  -- kicks()
  | 10 => ⟨#[0x26, 0xd2, 0xad, 0xdc]⟩ -- lid()
  | 11 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()
  | 12 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 13 => ⟨#[0xcf, 0xc4, 0xaf, 0x55]⟩ -- tau()
  | 14 => ⟨#[0x4b, 0x43, 0xed, 0x12]⟩ -- tend(uint256,uint256,uint256)
  | 15 => ⟨#[0xfc, 0x7b, 0x6a, 0xee]⟩ -- tick(uint256)
  | 16 => ⟨#[0x4e, 0x8b, 0x1d, 0xd5]⟩ -- ttl()
  | 17 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | 18 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)
  | _ => ⟨#[0x26, 0xe0, 0x27, 0xf1]⟩  -- yank(uint256)


theorem flapperAddressGetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storageBackend.locate? er = some (.leaf (addrLoc slot))) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbackend := rfl) (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (storageLocLoad_address_offset0 evm slot))

theorem flapperUint48GetterBodyReturns_offset0 (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint48Int)))
    (hloc :
      config.storageBackend.locate? er =
        some (.leaf (uint48Loc slot ⟨0, by decide⟩ (by decide)))) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (uint48Offset0Word slot evm.accountMap evm.executionEnv).toNat))])) := by
  simpa [nonpayable, uint48Offset0Word, solcSlotWordAt] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbackend := rfl) (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (storageLocLoad_uint48_offset0 evm slot))

theorem flapperUint48GetterBodyReturns_offset6 (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint48Int)))
    (hloc :
      config.storageBackend.locate? er =
        some (.leaf (uint48Loc slot ⟨6, by decide⟩ (by decide)))) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (uint48Offset6Word slot evm.accountMap evm.executionEnv).toNat))])) := by
  simpa [nonpayable, uint48Offset6Word, solcSlotWordAt] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbackend := rfl) (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      have hload :
          storageLocLoad evm (uint48Loc slot ⟨6, by decide⟩ (by decide)) =
            .int (Int.ofNat (UInt256.land uint48Mask
              (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
                (UInt256.ofNat (256 ^ 6)))).toNat) := by
        rw [show uint48Loc = packedUInt48Loc from rfl, storageLocLoad_uint48_offset6]
        rw [u256_land_comm
          (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.ofNat (256 ^ 6)))
          uint48Mask]
      exact congrArg EvalResult.ok hload)

theorem flapperUint256GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)))
    (hloc : config.storageBackend.locate? er = some (.leaf (wordLoc slot))) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbackend := rfl) (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (storageLocLoad_uint256 evm slot))

theorem flapperUint256GetterBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = flapperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf flapperBytecode entry returnPc routine)
    (hgetter : solcWordSlotGetterWf flapperBytecode routine slot)
    (hroutine : (D_J flapperBytecode 0).contains routine = true)
    (hreturnJd : (D_J flapperBytecode 0).contains returnPc = true)
    (hretmem : solcReturnWordFromMemWf flapperBytecode returnPc)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (solcSlotWordAt slot σ I).toNat))]))) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hword : solcSlotWordAt slot σ I = solcSlotWordAt slot σ I :=
    rfl
  have hval :
      some [Value.int (Int.ofNat (solcSlotWordAt slot σ I).toNat)] =
        some [Value.int (Int.ofNat (solcSlotWordAt slot σ I).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (solcSlotWordAt slot σ I))
        (some [(.int (Int.ofNat (solcSlotWordAt slot σ I).toNat))])
        transition.returnType := by
      rw [hreturn]
      exact returnEquiv_of_encode
        (by simpa [uint256] using uint256ReturnEncoding (solcSlotWordAt slot σ I))
  have hret := RD.solcWordGetterExternal (code := flapperBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret flapperBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (solcSlotWordAt slot σ I)) := by
    simpa [solcSlotWordAt] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval henc


theorem flapperUint48Offset0GetterBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = flapperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf flapperBytecode entry returnPc routine)
    (hgetter : solcUint48Offset0SlotGetterWf flapperBytecode routine slot)
    (hroutine : (D_J flapperBytecode 0).contains routine = true)
    (hreturnJd : (D_J flapperBytecode 0).contains returnPc = true)
    (hretmem : solcReturnUint48FromMemWf flapperBytecode returnPc)
    (hreturn : transition.returnType = [uint48])
    (hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int
            (Int.ofNat (uint48Offset0Word slot σ I).toNat))]))) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hslot : solcSlotWordAt slot σ I = solcSlotWordAt slot σ I :=
    rfl
  have hslot' : solcSlotWord σ I slot = solcSlotWord σ I slot := by
    simpa [solcSlotWordAt] using hslot.symm
  have hword :
      uint48Offset0Word slot σ I = uint48Offset0Word slot σ I := by
    simp [uint48Offset0Word, solcSlotWordAt, hslot']
  have hval :
      some [Value.int (Int.ofNat (uint48Offset0Word slot σ I).toNat)] =
        some [Value.int (Int.ofNat (uint48Offset0Word slot σ I).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (uint48Offset0Word slot σ I))
        (some [(.int (Int.ofNat (uint48Offset0Word slot σ I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by
        simpa [uint48] using
          uint48ReturnEncoding (uint48Offset0Word slot σ I)
            (uint48Masked_lt (solcSlotWordAt slot σ I)))
  have hret := RD.solcUint48Offset0GetterExternal (code := flapperBytecode)
    (g := Sat256.ofUInt256 g) (returnPc := returnPc) (entry := entry)
    (routine := routine) (slot := slot) hreach hentry hgetter hroutine hreturnJd hretmem
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval henc

theorem flapperUint48Offset6GetterBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = flapperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf flapperBytecode entry returnPc routine)
    (hgetter : solcUint48Offset6SlotGetterWf flapperBytecode routine slot)
    (hroutine : (D_J flapperBytecode 0).contains routine = true)
    (hreturnJd : (D_J flapperBytecode 0).contains returnPc = true)
    (hretmem : solcReturnUint48FromMemWf flapperBytecode returnPc)
    (hreturn : transition.returnType = [uint48])
    (hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int
            (Int.ofNat (uint48Offset6Word slot σ I).toNat))]))) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hslot : solcSlotWordAt slot σ I = solcSlotWordAt slot σ I :=
    rfl
  have hslot' : solcSlotWord σ I slot = solcSlotWord σ I slot := by
    simpa [solcSlotWordAt] using hslot.symm
  have hword :
      uint48Offset6Word slot σ I = uint48Offset6Word slot σ I := by
    simp [uint48Offset6Word, solcSlotWordAt, hslot']
  have hval :
      some [Value.int (Int.ofNat (uint48Offset6Word slot σ I).toNat)] =
        some [Value.int (Int.ofNat (uint48Offset6Word slot σ I).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (uint48Offset6Word slot σ I))
        (some [(.int (Int.ofNat (uint48Offset6Word slot σ I).toNat))])
        transition.returnType := by
    have hlt :
        (uint48Offset6Word slot σ I).toNat < EVM.twoPow 48 := by
      rw [uint48Offset6Word]
      rw [u256_land_comm uint48Mask
        (UInt256.div (solcSlotWordAt slot σ I) (UInt256.ofNat (256 ^ 6)))]
      exact uint48Masked_lt
        (UInt256.div (solcSlotWordAt slot σ I) (UInt256.ofNat (256 ^ 6)))
    rw [hreturn]
    exact returnEquiv_of_encode
      (by
        simpa [uint48] using
          uint48ReturnEncoding (uint48Offset6Word slot σ I) hlt)
  have hret := RD.solcUint48Offset6GetterExternal (code := flapperBytecode)
    (g := Sat256.ofUInt256 g) (returnPc := returnPc) (entry := entry)
    (routine := routine) (slot := slot) hreach hentry hgetter hroutine hreturnJd hretmem
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval henc

theorem flapperAddressGetterBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = flapperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf flapperBytecode entry returnPc routine)
    (hgetter : solcAddressSlotGetterWf flapperBytecode routine slot)
    (hroutine : (D_J flapperBytecode 0).contains routine = true)
    (hreturnJd : (D_J flapperBytecode 0).contains returnPc = true)
    (hretmem : solcReturnAddressFromMemWf flapperBytecode returnPc)
    (hreturn : transition.returnType = [addr])
    (hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (solcAddressSlotWord slot σ I).toNat))]))) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hword : solcSlotWordAt slot σ I = solcSlotWordAt slot σ I :=
    rfl
  have hval :
      some [Value.address (AccountAddress.ofNat (solcAddressSlotWord slot σ I).toNat)] =
        some [Value.address (AccountAddress.ofNat (solcAddressSlotWord slot σ I).toNat)] := by
    have hslot : solcSlotWordAt slot σ I = solcSlotWordAt slot σ I := hword.symm
    simp [solcAddressSlotWord, hslot]
  have henc :
      returnEquiv (UInt256.toByteArray (solcAddressSlotWord slot σ I))
        (some [(.address (AccountAddress.ofNat (solcAddressSlotWord slot σ I).toNat))])
        transition.returnType := by
    rw [hreturn]
    simpa [solcAddressSlotWord] using
      (returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (solcSlotWordAt slot σ I)))
  have hret := RD.solcAddressGetterExternal (code := flapperBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret flapperBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (solcAddressSlotWord slot σ I)) := by
    simpa [solcAddressSlotWord, solcSlotWordAt] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval henc


end Benchmarks.Dss.Flapper
