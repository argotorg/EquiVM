import Reasoning.SolcRoutines
import Benchmarks.Dss.DaiJoin.Bytecode
import Reasoning.ABI
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Memory
import Reasoning.Storage
import Reasoning.Dispatch
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# MakerDAO/Sky DSS DaiJoin shared proof foundation

Contract-wide selector notation and constants for the optimized DaiJoin runtime.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.DaiJoin

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev daiJoinSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order. -/
def daiJoinSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x69, 0x24, 0x50, 0x09]⟩ -- cage()
  | 1 => ⟨#[0xf4, 0xb9, 0xfa, 0x75]⟩ -- dai()
  | 2 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 3 => ⟨#[0xef, 0x69, 0x3b, 0xed]⟩ -- exit(address,uint256)
  | 4 => ⟨#[0x3b, 0x4d, 0xa6, 0x9f]⟩ -- join(address,uint256)
  | 5 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()
  | 6 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 7 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | _ => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)


theorem daiJoinAddressGetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (storageLocLoad_address_offset0 evm slot))

theorem daiJoinUint256GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)))
    (hloc : config.storage.layout er = fun _ => some (wordLoc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (storageLocLoad_uint256 evm slot))

theorem daiJoinAddressGetterBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = daiJoinBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf daiJoinBytecode entry returnPc routine)
    (hgetter : solcAddressSlotGetterWf daiJoinBytecode routine slot)
    (hroutine : (D_J daiJoinBytecode 0).contains routine = true)
    (hreturnJd : (D_J daiJoinBytecode 0).contains returnPc = true)
    (hretmem : solcReturnAddressFromMemWf daiJoinBytecode returnPc)
    (hreturn : transition.returnType = [addr])
    (hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (solcAddressSlotWord slot σ I).toNat))]))) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have henc :
      returnEquiv (UInt256.toByteArray (solcAddressSlotWord slot σ I))
        (some [(.address (AccountAddress.ofNat (solcAddressSlotWord slot σ I).toNat))])
        transition.returnType := by
    rw [hreturn]
    simpa [solcAddressSlotWord] using
      (returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (solcSlotWordAt slot σ I)))
  have hret := RD.solcAddressGetterExternal (code := daiJoinBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret daiJoinBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (solcAddressSlotWord slot σ I)) := by
    simpa [solcAddressSlotWord, solcSlotWordAt] using hret
  exact hret'.reEquivExecution hcode hdispatch hdecode hbody henc

theorem daiJoinUint256GetterBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = daiJoinBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf daiJoinBytecode entry returnPc routine)
    (hgetter : solcWordSlotGetterWf daiJoinBytecode routine slot)
    (hroutine : (D_J daiJoinBytecode 0).contains routine = true)
    (hreturnJd : (D_J daiJoinBytecode 0).contains returnPc = true)
    (hretmem : solcReturnWordFromMemWf daiJoinBytecode returnPc)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (solcSlotWordAt slot σ I).toNat))]))) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have henc :
      returnEquiv (UInt256.toByteArray (solcSlotWordAt slot σ I))
        (some [(.int (Int.ofNat (solcSlotWordAt slot σ I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (solcSlotWordAt slot σ I))
  have hret := RD.solcWordGetterExternal (code := daiJoinBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret daiJoinBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (solcSlotWordAt slot σ I)) := by
    simpa [solcSlotWordAt] using hret
  exact hret'.reEquivExecution hcode hdispatch hdecode hbody henc


/-! ### LOG2

The reasoning library has LOG1/LOG3/LOG4 combinators; this contract emits two-topic auth logs.
-/


end Benchmarks.Dss.DaiJoin
