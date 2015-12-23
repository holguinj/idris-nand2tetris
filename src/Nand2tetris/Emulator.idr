module Nand2tetris.Emulator

import Data.Vect
import Data.SortedMap

import Nand2tetris.Bit
import Nand2tetris.Asm

||| The two hardware registers, A and D.
record RealRegisters where
  constructor MkRealRegisters
  aReg : Byte
  dReg : Byte

instance Show RealRegisters where
  show (MkRealRegisters aReg dReg) =
    "Register A=" ++ (show $ cast {to=Integer} aReg) ++ "\n" ++
    "Register D=" ++ (show $ cast {to=Integer} dReg)

emptyRegisters : RealRegisters
emptyRegisters = MkRealRegisters zero zero

||| The full set of registers: A, D, and M.
record VirtualRegisters where
  constructor MkVirtualRegisters
  aReg : Byte
  dReg : Byte
  mReg : Byte

record MemoryState where
  constructor MkMemoryState
  program : List Instruction
  programCounter : Nat
  memoryMap : SortedMap Byte Byte
  registers : RealRegisters

%name MemoryState mem

showMem : SortedMap Byte Byte -> String
showMem memoryMap =
  let listified = toList memoryMap in
    show $ map show' listified
  where
    show' : (Byte, Vect 16 Bit) -> String
    show' (a, b) =
      let addr = show $ cast {to=Integer} a
          val = show $ cast {to=Integer} b in
        addr ++ "=" ++ val

instance Show MemoryState where
  show (MkMemoryState program programCounter memoryMap registers) =
    "Program=" ++ (show $ map show program) ++ "\n" ++
    "PC=" ++ (show programCounter) ++ "\n" ++
    "Instruction=" ++ (show $ index' programCounter $ program) ++ "\n" ++
    (show registers) ++ "\n" ++
    "Memory: " ++ (showMem memoryMap)

initialMemory : MemoryState
initialMemory = MkMemoryState [] Z empty emptyRegisters

getMemory : MemoryState -> Byte -> Byte
getMemory mem addr =
  case lookup addr (memoryMap mem) of
    Nothing => zero
    Just byte => byte

setMemory : MemoryState -> Byte -> Byte -> MemoryState
setMemory mem addr byte =
  let mmap = memoryMap mem in
    record { memoryMap = (insert addr byte mmap) } mem

getVirtualRegisters : MemoryState -> VirtualRegisters
getVirtualRegisters mem =
  let regs = registers mem
      a = aReg regs
      d = dReg regs
      m = getMemory mem a in
    MkVirtualRegisters a d m

setAReg : MemoryState -> Byte -> MemoryState
setAReg mem byte =
  record { registers->aReg = byte } mem

setDReg : MemoryState -> Byte -> MemoryState
setDReg mem byte =
  record { registers->dReg = byte } mem

setMReg : MemoryState -> Byte -> MemoryState
setMReg mem byte =
  let mmap = memoryMap mem
      addr = aReg $ registers mem in
    record { memoryMap = insert addr byte mmap } mem

incPC : MemoryState -> MemoryState
incPC mem = record { programCounter = (programCounter mem) + 1 } mem

doJump : MemoryState -> MemoryState
doJump mem =
  let addr = fromIntegerNat $ cast $ aReg $ registers mem in
    record { programCounter = addr } mem

destSetter : DestField -> Byte -> (MemoryState -> MemoryState)
destSetter DNull _ mem = mem
destSetter DM byte mem = setMReg mem byte
destSetter DD byte mem = setDReg mem byte
destSetter DMD byte mem = setMReg (setDReg mem byte) byte
destSetter DA byte mem = setAReg mem byte
destSetter DAM byte mem = setAReg (setMReg mem byte) byte
destSetter DAD byte mem = setAReg (setDReg mem byte) byte
destSetter DAMD byte mem = setAReg (setMReg (setDReg mem byte) byte) byte

isJump : Byte -> JumpField -> Bool
isJump byte JNull = False
isJump byte JGT = byte `gt` zero
isJump byte JEQ = byte == zero
isJump byte JGE = byte `gte` zero
isJump byte JLT = byte `lt` zero
isJump byte JNE = byte /= zero
isJump byte JLE = byte `lte` zero
isJump byte JMP = True

evalComp : VirtualRegisters -> CompField -> Byte
evalComp _ C0 = zero
evalComp _ C1 = one
evalComp _ CNeg1 = neg one
evalComp (MkVirtualRegisters _ dReg _) CD = dReg
evalComp (MkVirtualRegisters aReg _ _) CA = aReg
evalComp (MkVirtualRegisters _ dReg _) CNotD = not dReg
evalComp (MkVirtualRegisters aReg _ _) CNotA = not aReg
evalComp (MkVirtualRegisters _ dReg _) CNegD = neg dReg
evalComp (MkVirtualRegisters aReg _ _) CNegA = neg aReg
evalComp (MkVirtualRegisters _ dReg _) CDPlus1 = dReg `plus` one
evalComp (MkVirtualRegisters aReg _ _) CAPlus1 = aReg `plus` one
evalComp (MkVirtualRegisters _ dReg _) CDMinus1 = dReg `minus` one
evalComp (MkVirtualRegisters aReg _ _) CAMinus1 = aReg `minus` one
evalComp (MkVirtualRegisters aReg dReg _) CDPlusA = dReg `plus` aReg
evalComp (MkVirtualRegisters aReg dReg _) CDMinusA = dReg `minus` aReg
evalComp (MkVirtualRegisters aReg dReg _) CAMinusD = aReg `minus` dReg
evalComp (MkVirtualRegisters aReg dReg _) CDAndA = dReg `and` aReg
evalComp (MkVirtualRegisters aReg dReg _) CDOrA = dReg `or` aReg
evalComp (MkVirtualRegisters _ _ mReg) CM = mReg
evalComp (MkVirtualRegisters _ _ mReg) CNotM = not mReg
evalComp (MkVirtualRegisters _ _ mReg) CNegM = neg mReg
evalComp (MkVirtualRegisters _ _ mReg) CMPlus1 = mReg `plus` one
evalComp (MkVirtualRegisters _ _ mReg) CMMinus1 = mReg `minus` one
evalComp (MkVirtualRegisters _ dReg mReg) CDPlusM = dReg `plus` mReg
evalComp (MkVirtualRegisters _ dReg mReg) CDMinusM = dReg `minus` mReg
evalComp (MkVirtualRegisters _ dReg mReg) CMMinusD = mReg `minus` dReg
evalComp (MkVirtualRegisters _ dReg mReg) CDAndM = dReg `and` mReg
evalComp (MkVirtualRegisters _ dReg mReg) CDOrM = dReg `or` mReg

runCommand : MemoryState -> Instruction -> MemoryState
runCommand mem (AInstruction byte) = incPC $ setAReg mem byte
runCommand mem (CInstruction cmp dest jmp) =
  let virtRegs = getVirtualRegisters mem
      compVal = evalComp virtRegs cmp
      shouldJump = isJump compVal jmp
      setPC = if shouldJump then doJump else incPC
      setDest = destSetter dest compVal in
    setPC $ setDest mem

step : MemoryState -> Maybe MemoryState
step mem =
  do cmd <- index' (programCounter mem) (program mem)
     pure $ runCommand mem cmd

exec' : MemoryState -> MemoryState
exec' mem =
  case step mem of
    Nothing => mem
    Just newState => exec' newState

exec : List Instruction -> MemoryState
exec prog =
  let init = record { program = prog } initialMemory in
    exec' init

sum100 : List Instruction
sum100 = [ (AInstruction (integerToBinary 17))  -- @i
         , (CInstruction C1 DM JNull)           -- M=1
         , (AInstruction (integerToBinary 18))  -- @sum
         , (CInstruction C0 DM JNull)           -- M=0
         {- "(LOOP)" = 4 -}
         , (AInstruction (integerToBinary 17))  -- @i
         , (CInstruction CM DD JNull)           -- D=M
         , (AInstruction (integerToBinary 100)) -- @100
         , (CInstruction CDMinusA DD JNull)     -- D=D-A
         , (AInstruction (integerToBinary 18))  -- @END
         , (CInstruction CD DNull JGT)          -- D;JGT
         , (AInstruction (integerToBinary 17))  -- @i
         , (CInstruction CM DD JNull)           -- D=M
         , (AInstruction (integerToBinary 18))  -- @sum
         , (CInstruction CDPlusM DM JNull)      -- M=D+M
         , (AInstruction (integerToBinary 17))  -- @i
         , (CInstruction CMPlus1 DM JNull)      -- M=M+1
         , (AInstruction (integerToBinary 4))   -- @LOOP
         , (CInstruction C0 DNull JMP)          -- 0;JMP
         {- (END) = 18 -}
         , (AInstruction (integerToBinary 18))  -- @END
         -- , (CInstruction C0 DNull JMP)          -- 0;JMP
  ]
