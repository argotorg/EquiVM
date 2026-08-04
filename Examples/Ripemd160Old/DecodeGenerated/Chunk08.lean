import Examples.Ripemd160Old.DecodeGenerated.Chunk07

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes8 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨1302⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1303⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1304⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1305⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1306⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨1308⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1309⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1310⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1311⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1312⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1313⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2))),
  (⟨1316⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1317⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1318⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1319⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1320⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1321⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1322⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1323⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1324⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1325⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨1327⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1328⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1329⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1330⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1331⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1332⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2))),
  (⟨1335⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1336⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1337⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1338⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1339⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1340⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1341⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1342⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1343⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1344⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨1346⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1347⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1348⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1349⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1350⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1351⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2))),
  (⟨1354⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1355⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1356⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1357⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1358⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1359⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1360⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1361⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1362⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1363⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨1365⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1366⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1367⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1368⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1369⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1370⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2))),
  (⟨1373⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1374⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1375⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1376⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1377⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1378⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1379⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1380⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1381⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1382⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨1384⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1385⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1386⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1387⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1388⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1389⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2))),
  (⟨1392⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1393⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1394⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1395⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1396⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1397⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1398⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1399⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1400⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1401⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨1403⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1404⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1405⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1406⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1407⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1408⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2))),
  (⟨1411⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1412⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1413⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1414⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1415⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1416⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1417⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1418⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1419⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none))
]

private theorem generatedDecodes8_correct : ∀ i : Fin generatedDecodes8.size,
    decode runtimeBytecode generatedDecodes8[i].1 = generatedDecodes8[i].2 := by
  native_decide

theorem decode_1302 : decode runtimeBytecode ⟨1302⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨0, by decide⟩
theorem decode_1303 : decode runtimeBytecode ⟨1303⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨1, by decide⟩
theorem decode_1304 : decode runtimeBytecode ⟨1304⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨2, by decide⟩
theorem decode_1305 : decode runtimeBytecode ⟨1305⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨3, by decide⟩
theorem decode_1306 : decode runtimeBytecode ⟨1306⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨4, by decide⟩
theorem decode_1308 : decode runtimeBytecode ⟨1308⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨5, by decide⟩
theorem decode_1309 : decode runtimeBytecode ⟨1309⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨6, by decide⟩
theorem decode_1310 : decode runtimeBytecode ⟨1310⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨7, by decide⟩
theorem decode_1311 : decode runtimeBytecode ⟨1311⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨8, by decide⟩
theorem decode_1312 : decode runtimeBytecode ⟨1312⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨9, by decide⟩
theorem decode_1313 : decode runtimeBytecode ⟨1313⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2)) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨10, by decide⟩
theorem decode_1316 : decode runtimeBytecode ⟨1316⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨11, by decide⟩
theorem decode_1317 : decode runtimeBytecode ⟨1317⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨12, by decide⟩
theorem decode_1318 : decode runtimeBytecode ⟨1318⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨13, by decide⟩
theorem decode_1319 : decode runtimeBytecode ⟨1319⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨14, by decide⟩
theorem decode_1320 : decode runtimeBytecode ⟨1320⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨15, by decide⟩
theorem decode_1321 : decode runtimeBytecode ⟨1321⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨16, by decide⟩
theorem decode_1322 : decode runtimeBytecode ⟨1322⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨17, by decide⟩
theorem decode_1323 : decode runtimeBytecode ⟨1323⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨18, by decide⟩
theorem decode_1324 : decode runtimeBytecode ⟨1324⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨19, by decide⟩
theorem decode_1325 : decode runtimeBytecode ⟨1325⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨20, by decide⟩
theorem decode_1327 : decode runtimeBytecode ⟨1327⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨21, by decide⟩
theorem decode_1328 : decode runtimeBytecode ⟨1328⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨22, by decide⟩
theorem decode_1329 : decode runtimeBytecode ⟨1329⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨23, by decide⟩
theorem decode_1330 : decode runtimeBytecode ⟨1330⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨24, by decide⟩
theorem decode_1331 : decode runtimeBytecode ⟨1331⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨25, by decide⟩
theorem decode_1332 : decode runtimeBytecode ⟨1332⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2)) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨26, by decide⟩
theorem decode_1335 : decode runtimeBytecode ⟨1335⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨27, by decide⟩
theorem decode_1336 : decode runtimeBytecode ⟨1336⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨28, by decide⟩
theorem decode_1337 : decode runtimeBytecode ⟨1337⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨29, by decide⟩
theorem decode_1338 : decode runtimeBytecode ⟨1338⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨30, by decide⟩
theorem decode_1339 : decode runtimeBytecode ⟨1339⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨31, by decide⟩
theorem decode_1340 : decode runtimeBytecode ⟨1340⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨32, by decide⟩
theorem decode_1341 : decode runtimeBytecode ⟨1341⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨33, by decide⟩
theorem decode_1342 : decode runtimeBytecode ⟨1342⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨34, by decide⟩
theorem decode_1343 : decode runtimeBytecode ⟨1343⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨35, by decide⟩
theorem decode_1344 : decode runtimeBytecode ⟨1344⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨36, by decide⟩
theorem decode_1346 : decode runtimeBytecode ⟨1346⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨37, by decide⟩
theorem decode_1347 : decode runtimeBytecode ⟨1347⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨38, by decide⟩
theorem decode_1348 : decode runtimeBytecode ⟨1348⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨39, by decide⟩
theorem decode_1349 : decode runtimeBytecode ⟨1349⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨40, by decide⟩
theorem decode_1350 : decode runtimeBytecode ⟨1350⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨41, by decide⟩
theorem decode_1351 : decode runtimeBytecode ⟨1351⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2)) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨42, by decide⟩
theorem decode_1354 : decode runtimeBytecode ⟨1354⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨43, by decide⟩
theorem decode_1355 : decode runtimeBytecode ⟨1355⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨44, by decide⟩
theorem decode_1356 : decode runtimeBytecode ⟨1356⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨45, by decide⟩
theorem decode_1357 : decode runtimeBytecode ⟨1357⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨46, by decide⟩
theorem decode_1358 : decode runtimeBytecode ⟨1358⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨47, by decide⟩
theorem decode_1359 : decode runtimeBytecode ⟨1359⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨48, by decide⟩
theorem decode_1360 : decode runtimeBytecode ⟨1360⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨49, by decide⟩
theorem decode_1361 : decode runtimeBytecode ⟨1361⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨50, by decide⟩
theorem decode_1362 : decode runtimeBytecode ⟨1362⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨51, by decide⟩
theorem decode_1363 : decode runtimeBytecode ⟨1363⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨52, by decide⟩
theorem decode_1365 : decode runtimeBytecode ⟨1365⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨53, by decide⟩
theorem decode_1366 : decode runtimeBytecode ⟨1366⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨54, by decide⟩
theorem decode_1367 : decode runtimeBytecode ⟨1367⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨55, by decide⟩
theorem decode_1368 : decode runtimeBytecode ⟨1368⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨56, by decide⟩
theorem decode_1369 : decode runtimeBytecode ⟨1369⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨57, by decide⟩
theorem decode_1370 : decode runtimeBytecode ⟨1370⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2)) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨58, by decide⟩
theorem decode_1373 : decode runtimeBytecode ⟨1373⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨59, by decide⟩
theorem decode_1374 : decode runtimeBytecode ⟨1374⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨60, by decide⟩
theorem decode_1375 : decode runtimeBytecode ⟨1375⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨61, by decide⟩
theorem decode_1376 : decode runtimeBytecode ⟨1376⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨62, by decide⟩
theorem decode_1377 : decode runtimeBytecode ⟨1377⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨63, by decide⟩
theorem decode_1378 : decode runtimeBytecode ⟨1378⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨64, by decide⟩
theorem decode_1379 : decode runtimeBytecode ⟨1379⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨65, by decide⟩
theorem decode_1380 : decode runtimeBytecode ⟨1380⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨66, by decide⟩
theorem decode_1381 : decode runtimeBytecode ⟨1381⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨67, by decide⟩
theorem decode_1382 : decode runtimeBytecode ⟨1382⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨68, by decide⟩
theorem decode_1384 : decode runtimeBytecode ⟨1384⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨69, by decide⟩
theorem decode_1385 : decode runtimeBytecode ⟨1385⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨70, by decide⟩
theorem decode_1386 : decode runtimeBytecode ⟨1386⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨71, by decide⟩
theorem decode_1387 : decode runtimeBytecode ⟨1387⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨72, by decide⟩
theorem decode_1388 : decode runtimeBytecode ⟨1388⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨73, by decide⟩
theorem decode_1389 : decode runtimeBytecode ⟨1389⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2)) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨74, by decide⟩
theorem decode_1392 : decode runtimeBytecode ⟨1392⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨75, by decide⟩
theorem decode_1393 : decode runtimeBytecode ⟨1393⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨76, by decide⟩
theorem decode_1394 : decode runtimeBytecode ⟨1394⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨77, by decide⟩
theorem decode_1395 : decode runtimeBytecode ⟨1395⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨78, by decide⟩
theorem decode_1396 : decode runtimeBytecode ⟨1396⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨79, by decide⟩
theorem decode_1397 : decode runtimeBytecode ⟨1397⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨80, by decide⟩
theorem decode_1398 : decode runtimeBytecode ⟨1398⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨81, by decide⟩
theorem decode_1399 : decode runtimeBytecode ⟨1399⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨82, by decide⟩
theorem decode_1400 : decode runtimeBytecode ⟨1400⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨83, by decide⟩
theorem decode_1401 : decode runtimeBytecode ⟨1401⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨84, by decide⟩
theorem decode_1403 : decode runtimeBytecode ⟨1403⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨85, by decide⟩
theorem decode_1404 : decode runtimeBytecode ⟨1404⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨86, by decide⟩
theorem decode_1405 : decode runtimeBytecode ⟨1405⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨87, by decide⟩
theorem decode_1406 : decode runtimeBytecode ⟨1406⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨88, by decide⟩
theorem decode_1407 : decode runtimeBytecode ⟨1407⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨89, by decide⟩
theorem decode_1408 : decode runtimeBytecode ⟨1408⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1119⟩, 2)) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨90, by decide⟩
theorem decode_1411 : decode runtimeBytecode ⟨1411⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨91, by decide⟩
theorem decode_1412 : decode runtimeBytecode ⟨1412⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨92, by decide⟩
theorem decode_1413 : decode runtimeBytecode ⟨1413⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨93, by decide⟩
theorem decode_1414 : decode runtimeBytecode ⟨1414⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨94, by decide⟩
theorem decode_1415 : decode runtimeBytecode ⟨1415⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨95, by decide⟩
theorem decode_1416 : decode runtimeBytecode ⟨1416⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨96, by decide⟩
theorem decode_1417 : decode runtimeBytecode ⟨1417⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨97, by decide⟩
theorem decode_1418 : decode runtimeBytecode ⟨1418⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨98, by decide⟩
theorem decode_1419 : decode runtimeBytecode ⟨1419⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes8] using generatedDecodes8_correct ⟨99, by decide⟩

end Ripemd160Old
