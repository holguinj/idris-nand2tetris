module Main

import Nand2tetris.Asm
import Nand2tetris.AsmGen
import Nand2tetris.Emulator

printSteps : MemoryState -> IO ()
printSteps mem =
  case step mem of
    Nothing => do putStrLn "All done!"
                  pure ()
    Just new => do putStrLn $ show new
                   putStrLn ""
                   printSteps new

main : IO ()
main =
  let init = record { program = Nand2tetris.AsmGen.sum100 } initialMemory in
    do putStrLn $ show init
       putStrLn ""
       printSteps init
