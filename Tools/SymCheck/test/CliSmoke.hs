module Main (main) where

import Data.List (isInfixOf)
import System.Exit (ExitCode(..))
import System.Process (readProcessWithExitCode)

data TestCase = TestCase
  { testName :: String
  , testArgs :: [String]
  , expectedExit :: ExitCode
  , expectedStdout :: [String]
  , expectedStderr :: [String]
  }

main :: IO ()
main =
  mapM_ runTest tests

tests :: [TestCase]
tests =
  [ TestCase
      { testName = "cli-pre-post-qed"
      , testArgs =
          [ "run"
          , "--code", "600160020100"
          , "--pc", "2"
          , "--stack", "var:x"
          , "--fuel", "3"
          , "--pre", "stack[0]==1"
          , "--post", "stack[0]==3"
          ]
      , expectedExit = ExitSuccess
      , expectedStdout =
          [ "postconditions:"
          , "=> qed"
          ]
      , expectedStderr = []
      }
  , TestCase
      { testName = "cli-post-cex"
      , testArgs =
          [ "run"
          , "--code", "600160020100"
          , "--pc", "2"
          , "--stack", "0x1"
          , "--fuel", "3"
          , "--pre", "stack[0]==1"
          , "--post", "stack[0]==4"
          ]
      , expectedExit = ExitSuccess
      , expectedStdout =
          [ "postconditions:"
          , "=> cex"
          ]
      , expectedStderr = []
      }
  , TestCase
      { testName = "cli-invalid-precondition"
      , testArgs =
          [ "run"
          , "--code", "600160020100"
          , "--pc", "2"
          , "--stack", "0x1"
          , "--fuel", "3"
          , "--pre", "pc==2"
          ]
      , expectedExit = ExitFailure 1
      , expectedStdout = []
      , expectedStderr =
          [ "pc preconditions are not supported; set --pc directly"
          ]
      }
  ]

runTest :: TestCase -> IO ()
runTest test = do
  (exitCode, stdoutText, stderrText) <- readProcessWithExitCode "equivm-symcheck" (testArgs test) ""
  assertEqual (testName test) "exit code" (expectedExit test) exitCode stderrText
  mapM_ (assertContains (testName test) stdoutText) (expectedStdout test)
  mapM_ (assertContains (testName test) stderrText) (expectedStderr test)

assertEqual :: (Eq a, Show a) => String -> String -> a -> a -> String -> IO ()
assertEqual name field expected actual context =
  if expected == actual
    then pure ()
    else fail $
      name
        <> ": unexpected "
        <> field
        <> "\nexpected: "
        <> show expected
        <> "\nactual:   "
        <> show actual
        <> renderContext context

assertContains :: String -> String -> String -> IO ()
assertContains name haystack needle =
  if needle `isInfixOf` haystack
    then pure ()
    else fail $
      name
        <> ": expected stdout to contain "
        <> show needle
        <> "\nactual stdout:\n"
        <> haystack

renderContext :: String -> String
renderContext context
  | null context = ""
  | otherwise = "\ncontext:\n" <> context
