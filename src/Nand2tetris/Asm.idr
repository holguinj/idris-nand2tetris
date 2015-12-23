module Nand2tetris.Asm

import Data.Vect

import Nand2tetris.Bit

data CompField = C0
               | C1
               | CNeg1
               | CD
               | CA
               | CNotD
               | CNotA
               | CNegD
               | CNegA
               | CDPlus1
               | CAPlus1
               | CDMinus1
               | CAMinus1
               | CDPlusA
               | CDMinusA
               | CAMinusD
               | CDAndA
               | CDOrA
               | CM
               | CNotM
               | CNegM
               | CMPlus1
               | CMMinus1
               | CDPlusM
               | CDMinusM
               | CMMinusD
               | CDAndM
               | CDOrM

%name CompField cmp

instance Show CompField where
  show C0 = "0"
  show C1 = "1"
  show CNeg1 = "-1"
  show CD = "D"
  show CA = "A"
  show CNotD = "!D"
  show CNotA = "!A"
  show CNegD = "-D"
  show CNegA = "-A"
  show CDPlus1 = "D+1"
  show CAPlus1 = "A+1"
  show CDMinus1 = "D-1"
  show CAMinus1 = "A-1"
  show CDPlusA = "D+A"
  show CDMinusA = "D-A"
  show CAMinusD = "A-D"
  show CDAndA = "D&A"
  show CDOrA = "D|A"
  show CM = "M"
  show CNotM = "!M"
  show CNegM = "-M"
  show CMPlus1 = "M+1"
  show CMMinus1 = "M-1"
  show CDPlusM = "D+M"
  show CDMinusM = "D-M"
  show CMMinusD = "M-D"
  show CDAndM = "D&M"
  show CDOrM = "D|M"

data DestField = DNull
               | DM
               | DD
               | DMD
               | DA
               | DAM
               | DAD
               | DAMD

instance Show DestField where
  show DNull = ""
  show DM = "M="
  show DD = "D="
  show DMD = "MD="
  show DA = "A="
  show DAM = "AM="
  show DAD = "AD="
  show DAMD = "AMD="

%name DestField dest

data JumpField = JNull
               | JGT
               | JEQ
               | JGE
               | JLT
               | JNE
               | JLE
               | JMP

instance Show JumpField where
  show JNull = ""
  show JGT = ";JGT"
  show JEQ = ";JEQ"
  show JGE = ";JGE"
  show JLT = ";JLT"
  show JNE = ";JNE"
  show JLE = ";JLE"
  show JMP = ";JMP"

%name JumpField jmp

data Instruction = AInstruction Byte
                 | CInstruction CompField DestField JumpField
%name Instruction inst

instance Show Instruction where
  show (AInstruction xs) = "@" ++ (show $ cast {to=Integer} xs)
  show (CInstruction cmp dest jmp) = (show dest) ++ (show cmp) ++ (show jmp)
