import Benchmarks.Safe.Spec

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Safe

inductive GuardKind where
  | transaction
  | moduleGuard

def guardName : GuardKind → Ident
  | .transaction => "guard"
  | .moduleGuard => "moduleGuard"

def guardField : GuardKind → Ident
  | .transaction => "_guard"
  | .moduleGuard => "_moduleGuard"

def guardStorageRef (kind : GuardKind) : StorageRef := { base := guardField kind }

def guardStorageSlot : GuardKind → UInt256
  | .transaction => guardSlot
  | .moduleGuard => moduleGuardSlot

def guardInterfaceExpr : GuardKind → Expr
  | .transaction => transactionGuardInterfaceId
  | .moduleGuard => moduleGuardInterfaceId

def guardInterfaceValue : GuardKind → Value
  | .transaction => .fixedBytes bytes4Width [0xe6, 0xd7, 0xa8, 0x3a]
  | .moduleGuard => .fixedBytes bytes4Width [0x58, 0x40, 0x1e, 0xd8]

def guardInterfaceWord : GuardKind → UInt256
  | .transaction => UInt256.shiftLeft ⟨1936446493⟩ ⟨225⟩
  | .moduleGuard => UInt256.shiftLeft ⟨185074651⟩ ⟨227⟩

def guardTransition : GuardKind → TransitionDecl
  | .transaction => setguardTransition
  | .moduleGuard => setmoduleguardTransition

def guardEvent : GuardKind → Ident
  | .transaction => "ChangedGuard"
  | .moduleGuard => "ChangedModuleGuard"

end Benchmarks.Safe
