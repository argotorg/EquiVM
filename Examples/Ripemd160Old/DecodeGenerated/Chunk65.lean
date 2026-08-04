import Examples.Ripemd160Old.DecodeGenerated.Chunk64

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes65 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨8986⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8987⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨288⟩, 2))),
  (⟨8990⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8991⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8992⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨8993⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8694⟩, 2))),
  (⟨8996⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨8997⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨8998⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨8999⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨9001⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨9003⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨9004⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MUL), none)),
  (⟨9005⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none)),
  (⟨9006⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨9007⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨9009⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨9010⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨9011⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨9012⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨9013⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.BYTE), none)),
  (⟨9014⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨24⟩, 1))),
  (⟨9016⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none)),
  (⟨9017⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨9019⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨9020⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨9021⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨9022⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨9023⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.BYTE), none)),
  (⟨9024⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨9026⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none)),
  (⟨9027⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none)),
  (⟨9028⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨9029⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none)),
  (⟨9030⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨9031⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨9032⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨9033⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨9034⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.BYTE), none)),
  (⟨9035⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨9037⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none)),
  (⟨9038⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨9039⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨9040⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨9041⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.BYTE), none)),
  (⟨9042⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none)),
  (⟨9043⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none)),
  (⟨9044⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1))),
  (⟨9046⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨9047⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MUL), none)),
  (⟨9048⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP9), none)),
  (⟨9049⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨9050⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨9051⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨9052⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8635⟩, 2))),
  (⟨9055⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨9056⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨9057⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨9058⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨9059⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1))),
  (⟨9061⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨9062⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none)),
  (⟨9063⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨9064⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨9065⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨9066⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8359⟩, 2))),
  (⟨9069⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨9070⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨9071⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨9072⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨9073⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1))),
  (⟨9075⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨9076⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none)),
  (⟨9077⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨9078⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none)),
  (⟨9079⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none)),
  (⟨9080⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none)),
  (⟨9081⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨9082⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨9083⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨9084⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨9085⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8350⟩, 2))),
  (⟨9088⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨9089⟩, some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none)),
  (⟨9090⟩, some (Ethereum.Operation.Log (Ethereum.Operation.LOp.LOG2), none)),
  (⟨9091⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH5), some (⟨452857328472⟩, 5))),
  (⟨9097⟩, some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none)),
  (⟨9098⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SLT), none)),
  (⟨9099⟩, some (Ethereum.Operation.Keccak (Ethereum.Operation.KOp.KECCAK256), none)),
  (⟨9100⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP7), none)),
  (⟨9101⟩, some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none)),
  (⟨9102⟩, some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none)),
  (⟨9103⟩, some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none)),
  (⟨9104⟩, some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none)),
  (⟨9105⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP10), none)),
  (⟨9106⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH17), some (⟨15787899755922987897276027893907491661920⟩, 17))),
  (⟨9124⟩, some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none)),
  (⟨9125⟩, some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none)),
  (⟨9126⟩, some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none)),
  (⟨9127⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none))
]

private theorem generatedDecodes65_correct : ∀ i : Fin generatedDecodes65.size,
    decode runtimeBytecode generatedDecodes65[i].1 = generatedDecodes65[i].2 := by
  native_decide

theorem decode_8986 : decode runtimeBytecode ⟨8986⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨0, by decide⟩
theorem decode_8987 : decode runtimeBytecode ⟨8987⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨288⟩, 2)) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨1, by decide⟩
theorem decode_8990 : decode runtimeBytecode ⟨8990⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨2, by decide⟩
theorem decode_8991 : decode runtimeBytecode ⟨8991⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨3, by decide⟩
theorem decode_8992 : decode runtimeBytecode ⟨8992⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨4, by decide⟩
theorem decode_8993 : decode runtimeBytecode ⟨8993⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8694⟩, 2)) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨5, by decide⟩
theorem decode_8996 : decode runtimeBytecode ⟨8996⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨6, by decide⟩
theorem decode_8997 : decode runtimeBytecode ⟨8997⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨7, by decide⟩
theorem decode_8998 : decode runtimeBytecode ⟨8998⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨8, by decide⟩
theorem decode_8999 : decode runtimeBytecode ⟨8999⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨9, by decide⟩
theorem decode_9001 : decode runtimeBytecode ⟨9001⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨10, by decide⟩
theorem decode_9003 : decode runtimeBytecode ⟨9003⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨11, by decide⟩
theorem decode_9004 : decode runtimeBytecode ⟨9004⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MUL), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨12, by decide⟩
theorem decode_9005 : decode runtimeBytecode ⟨9005⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨13, by decide⟩
theorem decode_9006 : decode runtimeBytecode ⟨9006⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨14, by decide⟩
theorem decode_9007 : decode runtimeBytecode ⟨9007⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨15, by decide⟩
theorem decode_9009 : decode runtimeBytecode ⟨9009⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨16, by decide⟩
theorem decode_9010 : decode runtimeBytecode ⟨9010⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨17, by decide⟩
theorem decode_9011 : decode runtimeBytecode ⟨9011⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨18, by decide⟩
theorem decode_9012 : decode runtimeBytecode ⟨9012⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨19, by decide⟩
theorem decode_9013 : decode runtimeBytecode ⟨9013⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.BYTE), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨20, by decide⟩
theorem decode_9014 : decode runtimeBytecode ⟨9014⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨24⟩, 1)) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨21, by decide⟩
theorem decode_9016 : decode runtimeBytecode ⟨9016⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨22, by decide⟩
theorem decode_9017 : decode runtimeBytecode ⟨9017⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨23, by decide⟩
theorem decode_9019 : decode runtimeBytecode ⟨9019⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨24, by decide⟩
theorem decode_9020 : decode runtimeBytecode ⟨9020⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨25, by decide⟩
theorem decode_9021 : decode runtimeBytecode ⟨9021⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨26, by decide⟩
theorem decode_9022 : decode runtimeBytecode ⟨9022⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨27, by decide⟩
theorem decode_9023 : decode runtimeBytecode ⟨9023⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.BYTE), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨28, by decide⟩
theorem decode_9024 : decode runtimeBytecode ⟨9024⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨29, by decide⟩
theorem decode_9026 : decode runtimeBytecode ⟨9026⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨30, by decide⟩
theorem decode_9027 : decode runtimeBytecode ⟨9027⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨31, by decide⟩
theorem decode_9028 : decode runtimeBytecode ⟨9028⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨32, by decide⟩
theorem decode_9029 : decode runtimeBytecode ⟨9029⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨33, by decide⟩
theorem decode_9030 : decode runtimeBytecode ⟨9030⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨34, by decide⟩
theorem decode_9031 : decode runtimeBytecode ⟨9031⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨35, by decide⟩
theorem decode_9032 : decode runtimeBytecode ⟨9032⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨36, by decide⟩
theorem decode_9033 : decode runtimeBytecode ⟨9033⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨37, by decide⟩
theorem decode_9034 : decode runtimeBytecode ⟨9034⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.BYTE), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨38, by decide⟩
theorem decode_9035 : decode runtimeBytecode ⟨9035⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨39, by decide⟩
theorem decode_9037 : decode runtimeBytecode ⟨9037⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHL), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨40, by decide⟩
theorem decode_9038 : decode runtimeBytecode ⟨9038⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨41, by decide⟩
theorem decode_9039 : decode runtimeBytecode ⟨9039⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨42, by decide⟩
theorem decode_9040 : decode runtimeBytecode ⟨9040⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨43, by decide⟩
theorem decode_9041 : decode runtimeBytecode ⟨9041⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.BYTE), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨44, by decide⟩
theorem decode_9042 : decode runtimeBytecode ⟨9042⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨45, by decide⟩
theorem decode_9043 : decode runtimeBytecode ⟨9043⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.OR), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨46, by decide⟩
theorem decode_9044 : decode runtimeBytecode ⟨9044⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1)) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨47, by decide⟩
theorem decode_9046 : decode runtimeBytecode ⟨9046⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨48, by decide⟩
theorem decode_9047 : decode runtimeBytecode ⟨9047⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MUL), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨49, by decide⟩
theorem decode_9048 : decode runtimeBytecode ⟨9048⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP9), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨50, by decide⟩
theorem decode_9049 : decode runtimeBytecode ⟨9049⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨51, by decide⟩
theorem decode_9050 : decode runtimeBytecode ⟨9050⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨52, by decide⟩
theorem decode_9051 : decode runtimeBytecode ⟨9051⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨53, by decide⟩
theorem decode_9052 : decode runtimeBytecode ⟨9052⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8635⟩, 2)) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨54, by decide⟩
theorem decode_9055 : decode runtimeBytecode ⟨9055⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨55, by decide⟩
theorem decode_9056 : decode runtimeBytecode ⟨9056⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨56, by decide⟩
theorem decode_9057 : decode runtimeBytecode ⟨9057⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨57, by decide⟩
theorem decode_9058 : decode runtimeBytecode ⟨9058⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨58, by decide⟩
theorem decode_9059 : decode runtimeBytecode ⟨9059⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1)) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨59, by decide⟩
theorem decode_9061 : decode runtimeBytecode ⟨9061⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨60, by decide⟩
theorem decode_9062 : decode runtimeBytecode ⟨9062⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP7), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨61, by decide⟩
theorem decode_9063 : decode runtimeBytecode ⟨9063⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨62, by decide⟩
theorem decode_9064 : decode runtimeBytecode ⟨9064⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨63, by decide⟩
theorem decode_9065 : decode runtimeBytecode ⟨9065⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨64, by decide⟩
theorem decode_9066 : decode runtimeBytecode ⟨9066⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8359⟩, 2)) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨65, by decide⟩
theorem decode_9069 : decode runtimeBytecode ⟨9069⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨66, by decide⟩
theorem decode_9070 : decode runtimeBytecode ⟨9070⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨67, by decide⟩
theorem decode_9071 : decode runtimeBytecode ⟨9071⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨68, by decide⟩
theorem decode_9072 : decode runtimeBytecode ⟨9072⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨69, by decide⟩
theorem decode_9073 : decode runtimeBytecode ⟨9073⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨32⟩, 1)) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨70, by decide⟩
theorem decode_9075 : decode runtimeBytecode ⟨9075⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨71, by decide⟩
theorem decode_9076 : decode runtimeBytecode ⟨9076⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨72, by decide⟩
theorem decode_9077 : decode runtimeBytecode ⟨9077⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨73, by decide⟩
theorem decode_9078 : decode runtimeBytecode ⟨9078⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MLOAD), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨74, by decide⟩
theorem decode_9079 : decode runtimeBytecode ⟨9079⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP2), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨75, by decide⟩
theorem decode_9080 : decode runtimeBytecode ⟨9080⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP8), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨76, by decide⟩
theorem decode_9081 : decode runtimeBytecode ⟨9081⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨77, by decide⟩
theorem decode_9082 : decode runtimeBytecode ⟨9082⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨78, by decide⟩
theorem decode_9083 : decode runtimeBytecode ⟨9083⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨79, by decide⟩
theorem decode_9084 : decode runtimeBytecode ⟨9084⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨80, by decide⟩
theorem decode_9085 : decode runtimeBytecode ⟨9085⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨8350⟩, 2)) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨81, by decide⟩
theorem decode_9088 : decode runtimeBytecode ⟨9088⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨82, by decide⟩
theorem decode_9089 : decode runtimeBytecode ⟨9089⟩ = some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨83, by decide⟩
theorem decode_9090 : decode runtimeBytecode ⟨9090⟩ = some (Ethereum.Operation.Log (Ethereum.Operation.LOp.LOG2), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨84, by decide⟩
theorem decode_9091 : decode runtimeBytecode ⟨9091⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH5), some (⟨452857328472⟩, 5)) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨85, by decide⟩
theorem decode_9097 : decode runtimeBytecode ⟨9097⟩ = some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨86, by decide⟩
theorem decode_9098 : decode runtimeBytecode ⟨9098⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SLT), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨87, by decide⟩
theorem decode_9099 : decode runtimeBytecode ⟨9099⟩ = some (Ethereum.Operation.Keccak (Ethereum.Operation.KOp.KECCAK256), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨88, by decide⟩
theorem decode_9100 : decode runtimeBytecode ⟨9100⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP7), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨89, by decide⟩
theorem decode_9101 : decode runtimeBytecode ⟨9101⟩ = some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨90, by decide⟩
theorem decode_9102 : decode runtimeBytecode ⟨9102⟩ = some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨91, by decide⟩
theorem decode_9103 : decode runtimeBytecode ⟨9103⟩ = some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨92, by decide⟩
theorem decode_9104 : decode runtimeBytecode ⟨9104⟩ = some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨93, by decide⟩
theorem decode_9105 : decode runtimeBytecode ⟨9105⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP10), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨94, by decide⟩
theorem decode_9106 : decode runtimeBytecode ⟨9106⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH17), some (⟨15787899755922987897276027893907491661920⟩, 17)) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨95, by decide⟩
theorem decode_9124 : decode runtimeBytecode ⟨9124⟩ = some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨96, by decide⟩
theorem decode_9125 : decode runtimeBytecode ⟨9125⟩ = some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨97, by decide⟩
theorem decode_9126 : decode runtimeBytecode ⟨9126⟩ = some (Ethereum.Operation.System (Ethereum.Operation.SOp.INVALID), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨98, by decide⟩
theorem decode_9127 : decode runtimeBytecode ⟨9127⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.SHR), none) := by
  simpa [generatedDecodes65] using generatedDecodes65_correct ⟨99, by decide⟩

end Ripemd160Old
