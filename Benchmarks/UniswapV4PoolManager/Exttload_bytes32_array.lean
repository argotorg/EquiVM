import Benchmarks.UniswapV4PoolManager.Dispatch
import Benchmarks.UniswapV4PoolManager.ExttloadArraySource
import Benchmarks.UniswapV4PoolManager.ExttloadArrayReturn

/-!
# PoolManager `exttload(bytes32[])`

The dynamic ABI decoder, transient-read loop, empty-array read, and return buffer
are composed from their source and bytecode proofs.
-/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolManagerExttload_bytes32_arrayBodyCore {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (poolManagerSelBytes 22)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (poolManagerSelBytes 22) rfl hsel
  have hd : dispatchMsg contract I.calldata = some exttload_bytes32_arrayTransition := by
    apply poolManagerDispatch_exttload_bytes32_array <;> first
    | exact hsel
    | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rdEntry⟩ := poolManagerReachExttload_bytes32_arrayBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  change RD (deployedRuntime v) I (Sat256.ofUInt256 g)
    (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨2865⟩ [solcSelectorWord I]
    entryMemory ⟨3⟩ .empty σ k C at rdEntry
  have hjump : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 816) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rdSize := poolManagerBlocks.poolManager_block_2865_fallthrough (by simp) hwv rdEntry
    have hjDecode : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 12155) = true := by
      rw [deployedRuntime_jumps]; jump_dest
    have rdDecode := poolManagerBlocks.poolManager_block_2871 (by simp) hjDecode rdSize
    have hjReturn : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 2879) = true := by
      rw [deployedRuntime_jumps]; jump_dest
    rcases decodeWordArray v (by simp) hsz hsize hjReturn rdDecode with hbad | hgood
    · exact hbad.2.reEquivDecodingFailed hcode hd (decodeCalldata_wordArray_none "slots" hbad.1)
    · obtain ⟨hb, k', C', rdBody⟩ := hgood
      obtain ⟨slots, hdecoded, hdec⟩ := decodeCalldata_wordArray_exists "slots" hb
      have hn : slots.length ≤ solcMaxU64 := by rw [hdecoded.length]; exact hb.2.2.2.2.1
      have hword : UInt256.ofNat slots.length =
          calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := by
        rw [hdecoded.length, u256_ofNat_toNat]
      rw [← hword] at rdBody
      have htrace := exttloadArrayTrace v (by simp) hn hb.2.2.1 rdBody
      obtain ⟨frame, hbody⟩ := exttloadArraySource
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) slots (immStore v) hwv hdecoded
      exact htrace.reEquivExecution hcode hd hdec hbody
        (returnEquiv_of_encode (wordArrayReturn_encoding _ _))
  · have rdRevert := poolManagerBlocks.poolManager_block_2865_taken (by simp) hwv hjump rdEntry
    exact selectedRevert hcode (emptyRevert v (by simp) rdRevert) hd
      (fun _ => bodyReverts_nonPayable hwv)

/-- `exttload(bytes32[])`: the theorem `Correct.lean` routes selector 22 to. -/
theorem poolManagerExttload_bytes32_arrayBody {σ σ₀ A I} {g : UInt256} (v : PoolManagerImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (_hWF : Syntax.poolManagerWF σ I) (_hGas : Syntax.poolManagerGasBound g)
    (hsel : selIs I (poolManagerSelBytes 22)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) :=
  poolManagerExttload_bytes32_arrayBodyCore v hcode hsize hsel

end Benchmarks.UniswapV4PoolManager
