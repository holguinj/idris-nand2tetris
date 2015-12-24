module Nand2tetris.AsmParse

import Debug.Error

import Lightyear.Char
import Lightyear.Combinators
import Lightyear.Core
import Lightyear.Errmsg
import Lightyear.Strings

import Nand2tetris.Asm
import Nand2tetris.Bit

||| Types that only apply during compilation.
data MetaInstruction = ALabel String
                     | JumpTarget String

||| May be either a type that exists only at compile time or a native
||| instruction type.
data ParseResult = Meta MetaInstruction
                 | Native Instruction
                 | Comment String

instance Eq ParseResult where
  (==) (Meta (ALabel x)) (Meta (ALabel y)) = x == y
  (==) (Meta (JumpTarget x)) (Meta (JumpTarget y)) = x == y
  (==) (Native x) (Native y) = x == y
  (==) _ _ = False

labelString : Parser String
labelString =
  do letters <- some $ alphaNum <|> oneOf "_.$:"
     pure $ pack letters

aInstruction : Parser ParseResult
aInstruction =
  do char '@'
     digits <- some digit
     (pure $ Native $ AInstruction $ toByte digits) <?> "A Instruction"
  where
    toByte : List (Fin 10) -> Byte
    toByte xs =
      integerToBinary $ cast {to=Integer} $ concat $ map (show . finToInteger) xs

aLabel : Parser ParseResult
aLabel =
  do char '@'
     label <- labelString
     (pure $ Meta $ ALabel label) <?> "A Label"

jumpTarget : Parser ParseResult
jumpTarget =
  do name <- parens labelString
     (pure $ Meta $ JumpTarget name) <?> "Jump Target"

compField : Parser CompField
compField = (string "A+1" *> return CAPlus1)
        <|> (string "A-1" *> return CAMinus1)
        <|> (string "A-D" *> return CAMinusD)
        <|> (string "D&A" *> return CDAndA)
        <|> (string "D+1" *> return CDPlus1)
        <|> (string "D+A" *> return CDPlusA)
        <|> (string "D+M" *> return CDPlusM)
        <|> (string "D-1" *> return CDMinus1)
        <|> (string "D-A" *> return CDMinusA)
        <|> (string "D-M" *> return CDMinusM)
        <|> (string "D|A" *> return CDOrA)
        <|> (string "D|M" *> return CDOrM)
        <|> (string "M+1" *> return CMPlus1)
        <|> (string "M-1" *> return CMMinus1)
        <|> (string "M-D" *> return CMMinusD)
        <|> (string "!A" *> return CNotA)
        <|> (string "!D" *> return CNotD)
        <|> (string "!M" *> return CNotM)
        <|> (string "-1" *> return CNeg1)
        <|> (string "-A" *> return CNegA)
        <|> (string "-D" *> return CNegD)
        <|> (string "-M" *> return CNegM)
        <|> (string "0" *> return C0)
        <|> (string "1" *> return C1)
        <|> (string "A" *> return CA)
        <|> (string "D" *> return CD)
        <|> (string "M" *> return CM)
        <?> "Comp Field"

destField : Parser DestField
destField = (string "AMD=" *> return DAMD)
        <|> (string "AD=" *> return DAD)
        <|> (string "AM=" *> return DAM)
        <|> (string "MD=" *> return DMD)
        <|> (string "A=" *> return DA)
        <|> (string "D=" *> return DD)
        <|> (string "M=" *> return DM)
        <|> (string "" *> return DNull)
        <?> "Dest Field"

jumpField : Parser JumpField
jumpField = (string ";JGT" *> return JGT)
        <|> (string ";JEQ" *> return JEQ)
        <|> (string ";JGE" *> return JGE)
        <|> (string ";JLT" *> return JLT)
        <|> (string ";JNE" *> return JNE)
        <|> (string ";JLE" *> return JLE)
        <|> (string ";JMP" *> return JMP)
        <|> (string "" *> return JNull)
        <?> "Jump Field"

comment : Parser ParseResult
comment =
  do spaces
     string "//"
     cmt <- (manyTill anyChar endOfLine) <|> many anyChar
     pure $ Comment $ trim $ pack cmt

cInstruction : Parser ParseResult
cInstruction =
  do dest <- destField
     comp <- compField
     jump <- jumpField
     pure $ Native $ CInstruction comp dest jump

instruction' : Parser ParseResult
instruction' = aInstruction
           <|> aLabel
           <|> jumpTarget
           <|> cInstruction

instruction : Parser ParseResult
instruction =
  do spaces
     inst <- instruction'
     spaces
     opt endOfLine
     pure $ inst

program : Parser (List ParseResult)
program = many (comment <|> instruction)

instructionExamples : List $ (String, ParseResult)
instructionExamples = [ ("@1", Native (AInstruction (integerToBinary 1)))
                       , ("@123", Native (AInstruction (integerToBinary 123)))
                       , ("@1024", Native (AInstruction (integerToBinary 1024)))
                       , ("@foo", Meta (ALabel "foo"))
                       , ("@BAR", Meta (ALabel "BAR"))
                       , ("(foot)", Meta (JumpTarget "foot"))
                       , ("(Main$fooClass_1)", Meta (JumpTarget "Main$fooClass_1"))
                       , ("M=D+M", Native (CInstruction CDPlusM DM JNull))
                       , ("0;JMP", Native (CInstruction C0 DNull JMP))
                       , ("AMD=D-A", Native (CInstruction CDMinusA DAMD JNull))
                       ]

sum100 : List (String, ParseResult)
sum100 = [ ("@i", Meta (ALabel "i"))
         , ("M=1", Native (CInstruction C1 DM JNull))
         , ("@sum", Meta (ALabel "sum"))
         , ("M=0", Native (CInstruction C0 DM JNull))
         , ("(LOOP)", Meta (JumpTarget "LOOP"))
         , ("@i", Meta (ALabel "i"))
         , ("D=M", Native (CInstruction CM DD JNull))
         , ("@100", Native (AInstruction (integerToBinary 100)))
         , ("D=D-A", Native (CInstruction CDMinusA DD JNull))
         , ("@END", Meta (ALabel "END"))
         , ("D;JGT", Native (CInstruction CD DNull JGT))
         , ("@i", Meta (ALabel "i"))
         , ("D=M", Native (CInstruction CM DD JNull))
         , ("@sum", Meta (ALabel "sum"))
         , ("M=D+M", Native (CInstruction CDPlusM DM JNull))
         , ("@i", Meta (ALabel "i"))
         , ("M=M+1", Native (CInstruction CMPlus1 DM JNull))
         , ("@LOOP", Meta (ALabel "LOOP"))
         , ("T;JMP", Native (CInstruction C0 DNull JMP))
         , ("@END", Meta (ALabel "END"))
         -- , "0;JMP"
         ]

data TestResult t = Error (String, String)
                  | Mismatch (String, t, t)
                  | Good

testExample : Eq t => Parser t -> (String, t) -> TestResult t
testExample parser (str, expected) =
  case parse parser str of
    (Left err) => Error (str, err)
    (Right result) =>
      if result == expected
        then Good
        else Mismatch (str, expected, result)

||| Given a parser and a list of (String, result) tuples, return a list of cases
||| where the example either failed to parse or else didn't match the expected
||| result. If all tests succeed, returns the empty list.
testExamples : Eq t => Parser t -> List (String, t) -> List $ TestResult t
testExamples parser [] = []
testExamples parser (x :: xs) =
  case testExample parser x of
    err@(Error _) => err :: testExamples parser xs
    mism@(Mismatch _) => mism :: testExamples parser xs
    Good => testExamples parser xs

testResults : List $ TestResult ParseResult
testResults = testExamples instruction sum100


proggy : String
proggy = unlines
         [ "D=M "
         , "// hi mom"
         , " //helllo"
         , "A=1//sup"
         , " D;JGT"
         , "0;JMP //hellooooooo"
         ]
