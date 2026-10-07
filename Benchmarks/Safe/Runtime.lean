import Benchmarks.Safe.Version
import Benchmarks.Safe.AddOwnerWithThreshold
import Benchmarks.Safe.ApproveHash
import Benchmarks.Safe.ApprovedHashes
import Benchmarks.Safe.ChangeThreshold
import Benchmarks.Safe.CheckNSignatures
import Benchmarks.Safe.CheckNSignaturesAddress
import Benchmarks.Safe.CheckSignatures
import Benchmarks.Safe.CheckSignaturesAddress
import Benchmarks.Safe.DisableModule
import Benchmarks.Safe.DomainSeparator
import Benchmarks.Safe.EnableModule
import Benchmarks.Safe.ExecTransaction
import Benchmarks.Safe.ExecTransactionFromModule
import Benchmarks.Safe.ExecTransactionFromModuleReturnData
import Benchmarks.Safe.GetModulesPaginated
import Benchmarks.Safe.GetOwners
import Benchmarks.Safe.GetStorageAt
import Benchmarks.Safe.GetThreshold
import Benchmarks.Safe.GetTransactionHash
import Benchmarks.Safe.IsModuleEnabled
import Benchmarks.Safe.IsOwner
import Benchmarks.Safe.Nonce
import Benchmarks.Safe.RemoveOwner
import Benchmarks.Safe.SetFallbackHandler
import Benchmarks.Safe.SetGuard
import Benchmarks.Safe.SetModuleGuard
import Benchmarks.Safe.Setup
import Benchmarks.Safe.SignedMessages
import Benchmarks.Safe.SimulateAndRevert
import Benchmarks.Safe.SwapOwner
import Benchmarks.Safe.Receive
import Benchmarks.Safe.Fallback

/-!
Proof scaffolds for every Safe runtime entrypoint. All obligations retain the unqualified
refinement relation: arbitrary account maps, calldata (including decoding failures), call value,
gas, call depth, and either permission mode. Bodies are intentionally unproved.
-/

