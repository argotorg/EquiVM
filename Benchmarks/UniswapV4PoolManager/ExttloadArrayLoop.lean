import Benchmarks.UniswapV4PoolManager.WordArrayLoop

namespace Benchmarks.UniswapV4PoolManager
abbrev exttloadArrayCond := wordArrayCond
abbrev exttloadArrayLoopBody := wordArrayLoopBody true
abbrev exttloadArrayValue := wordArrayValue true
abbrev ExttloadArrayLocals := WordArrayLocals
abbrev exttloadArrayLoopStep {fork : Ethereum.Fork} := wordArrayLoopStep (fork := fork) true
abbrev exttloadArraySourceLoop {fork : Ethereum.Fork} := wordArraySourceLoop (fork := fork) true
end Benchmarks.UniswapV4PoolManager
