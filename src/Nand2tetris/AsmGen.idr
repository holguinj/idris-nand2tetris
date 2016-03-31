module Nand2tetris.AsmGen

import Data.Vect
import Debug.Error

import Nand2tetris.Asm
import Nand2tetris.AsmParse
import Nand2tetris.Bit

%default total
%access public export

SymbolTable : Type
SymbolTable = List (String, Nat)

%name SymbolTable syms

baseSymbols : SymbolTable
baseSymbols = [ ("SP", 0)
              , ("LCL", 1)
              , ("ARG", 2)
              , ("THIS", 3)
              , ("THAT", 4)
              , ("R0", 0)
              , ("R1", 1)
              , ("R2", 2)
              , ("R3", 3)
              , ("R4", 4)
              , ("R5", 5)
              , ("R6", 6)
              , ("R7", 7)
              , ("R8", 8)
              , ("R9", 9)
              , ("R10", 10)
              , ("R11", 11)
              , ("R12", 12)
              , ("R13", 13)
              , ("R14", 14)
              , ("R15", 15)
              , ("SCREEN", 16384)
              , ("KBD", 24576)
              ]


varBaseAddress : Nat
varBaseAddress = 16

symLookup : String -> SymbolTable -> Maybe Nat
symLookup s [] = Nothing
symLookup s ((a, addr) :: xs) =
  if s == a
    then Just addr
    else symLookup s xs

jumpTargets : List ParseResult -> SymbolTable
jumpTargets xs =
  jumpTargets' Z xs
  where
    jumpTargets' : Nat -> List ParseResult -> SymbolTable
    jumpTargets' line [] = []
    jumpTargets' line (Meta (JumpTarget target) :: xs) =
      (target, line) :: jumpTargets' line xs
    jumpTargets' line (_ :: xs) = jumpTargets' (S line) xs

addVars : List ParseResult -> SymbolTable -> SymbolTable
addVars xs syms =
  addVars' varBaseAddress xs syms
  where
    addVars' : Nat -> List ParseResult -> SymbolTable -> SymbolTable
    addVars' i [] syms = syms
    addVars' i ((Meta (ALabel label)) :: xs) syms =
      case symLookup label syms of
        Nothing => addVars' (S i) xs $ (label, i) :: syms
        (Just _) => addVars' i xs syms
    addVars' i (_ :: xs) syms = addVars' i xs syms

createSymbolTable : List ParseResult -> SymbolTable
createSymbolTable xs = (baseSymbols ++) $ addVars xs $ jumpTargets xs

normalize : List ParseResult -> List Instruction
normalize xs =
  let syms = createSymbolTable xs in
    normalize' xs syms
  where
    normalize' : List ParseResult -> SymbolTable -> List Instruction
    normalize' [] syms = []
    normalize' ((Meta (ALabel x)) :: xs) syms =
      assert_total $
      case symLookup x syms of
        Nothing => error "symbol table generation appears to be broken"
        (Just addr) => AInstruction (integerToBinary $ cast addr) :: normalize' xs syms
    normalize' ((Meta (JumpTarget x)) :: xs) syms = normalize' xs syms
    normalize' ((Native inst) :: xs) syms = inst :: normalize' xs syms
    normalize' ((Comment x) :: xs) syms = normalize' xs syms

sum100 : List Instruction
sum100 = normalize
         [ Meta (ALabel "i")
         , Native (CInstruction C1 DM JNull)
         , Meta (ALabel "sum")
         , Native (CInstruction C0 DM JNull)
         , Meta (JumpTarget "LOOP")
         , Meta (ALabel "i")
         , Native (CInstruction CM DD JNull)
         , Native (AInstruction (integerToBinary 100))
         , Native (CInstruction CDMinusA DD JNull)
         , Meta (ALabel "END")
         , Native (CInstruction CD DNull JGT)
         , Meta (ALabel "i")
         , Native (CInstruction CM DD JNull)
         , Meta (ALabel "sum")
         , Native (CInstruction CDPlusM DM JNull)
         , Meta (ALabel "i")
         , Native (CInstruction CMPlus1 DM JNull)
         , Meta (ALabel "LOOP")
         , Native (CInstruction C0 DNull JMP)
         , Meta (ALabel "END")
         -- , "0;JMP"
         ]

compNibble : CompField -> Vect 7 Bit
compNibble C0 = [O, I, O, I, O, I, O]
compNibble C1 = [O, I, I, I, I, I, I]
compNibble CNeg1 = [O, I, I, I, O, I, O]
compNibble CD = [O, O, O, I, I, O, O]
compNibble CA = [O, I, I, O, O, O, O]
compNibble CNotD = [O, O, O, I, I, O, I]
compNibble CNotA = [O, I, I, O, O, O, I]
compNibble CNegD = [O, O, O, I, I, I, I]
compNibble CNegA = [O, I, I, O, O, I, I]
compNibble CDPlus1 = [O, O, I, I, I, I, I]
compNibble CAPlus1 = [O, I, I, O, I, I, I]
compNibble CDMinus1 = [O, O, O, I, I, I, O]
compNibble CAMinus1 = [O, I, I, O, O, I, O]
compNibble CDPlusA = [O, O, O, O, O, I, O]
compNibble CDMinusA = [O, O, I, O, O, I, I]
compNibble CAMinusD = [O, O, O, O, I, I, I]
compNibble CDAndA = [O, O, O, O, O, O, O]
compNibble CDOrA = [O, O, I, O, I, O, I]
compNibble CM = [I, I, I, O, O, O, O]
compNibble CNotM = [I, I, I, O, O, O, I]
compNibble CNegM = [I, I, I, O, O, I, I]
compNibble CMPlus1 = [I, I, I, O, I, I, I]
compNibble CMMinus1 = [I, I, I, O, O, I, O]
compNibble CDPlusM = [I, O, O, O, O, I, O]
compNibble CDMinusM = [I, O, I, O, O, I, I]
compNibble CMMinusD = [I, O, O, O, I, I, I]
compNibble CDAndM = [I, O, O, O, O, O, O]
compNibble CDOrM = [I, O, I, O, I, O, I]

destNibble : DestField -> Vect 3 Bit
destNibble DNull = [O, O, O]
destNibble DM = [O, O, I]
destNibble DD = [O, I, O]
destNibble DMD = [O, I, I]
destNibble DA = [I, O, O]
destNibble DAM = [I, O, I]
destNibble DAD = [I, I, O]
destNibble DAMD = [I, I, I]

jumpNibble : JumpField -> Vect 3 Bit
jumpNibble JNull = [O, O, O]
jumpNibble JGT = [O, O, I]
jumpNibble JEQ = [O, I, O]
jumpNibble JGE = [O, I, I]
jumpNibble JLT = [I, O, O]
jumpNibble JNE = [I, O, I]
jumpNibble JLE = [I, I, O]
jumpNibble JMP = [I, I, I]

instructionByte : Instruction -> Byte
instructionByte (AInstruction (_ :: xs)) = O :: xs
instructionByte (CInstruction cmp dest jmp) =
  let cPrefix = the (Vect 3 Bit) [I, I, I]
      cmp' = compNibble cmp
      dest' = destNibble dest
      jmp' = jumpNibble jmp in
    cPrefix ++ cmp' ++ dest' ++ jmp'
