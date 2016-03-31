module Nand2tetris.Bit

import Data.Vect

%default total
%access public export

data Bit = O | I

implementation Cast Bit Integer where
  cast O = 0
  cast I = 1

implementation Eq Bit where
  (==) O O = True
  (==) O I = False
  (==) I O = False
  (==) I I = True

implementation Ord Bit where
  compare O O = EQ
  compare O I = LT
  compare I O = GT
  compare I I = EQ

Byte : Type
Byte = Vect 16 Bit

%name Byte byte

zero : Byte
zero = replicate 16 O

one : Byte
one = (replicate 15 O) ++ [I]

negOne : Byte
negOne = replicate 16 I

uBinToInteger : Vect n Bit -> Integer
uBinToInteger xs =
  binToInteger' 0 Z $ reverse xs
  where
  binToInteger' : (acc : Integer) -> (pos : Nat) -> Vect n Bit -> Integer
  binToInteger' acc _ [] = acc
  binToInteger' acc pos (bit :: bits) =
    let n = cast bit in
      binToInteger' (acc + (n * (2 `pow` pos))) (pos + 1) bits

not : Vect n Bit -> Vect n Bit
not [] = []
not (O :: xs) = I :: not xs
not (I :: xs) = O :: not xs

binToInteger : Vect n Bit -> Integer
binToInteger [] = 0
binToInteger (O :: xs) = uBinToInteger xs
binToInteger (I :: xs) = (-1) + (uBinToInteger $ not xs) * (-1)

implementation Cast (Vect n Bit) Integer where
  cast [] = 0
  cast bits = binToInteger bits

isEven : Integer -> Bool
isEven = assert_total $ (==0) . (flip mod 2)

integerToBinary' : (acc : List Bit) -> Integer -> List Bit
integerToBinary' acc 0 = O :: acc
integerToBinary' acc 1 = I :: acc
integerToBinary' acc n =
  if isEven n
    -- both of these are shrinking on the second argument, but Uncle Edwin
    -- doesn't believe me.
    then assert_total $ integerToBinary' (O :: acc) (n `div` 2)
    else assert_total $ integerToBinary' (I :: acc) (n `div` 2)

||| Constructs a vector of size n given a list. Intended to be used with bytes,
||| so elements are added (as `def`) or dropped from the beginning if necessary.
vectSizer : (n : Nat) -> (def : a) -> List a -> Vect n a
vectSizer n def xs =
  reverse $ vectSizer' n def $ reverse xs
  where
    vectSizer' Z def xs = []
    vectSizer' (S k) def [] = def :: vectSizer' k def []
    vectSizer' (S k) def (x :: xs) = x :: vectSizer' k def xs

toByte : List Bit -> Byte
toByte = vectSizer 16 O

integerToBinary : Integer -> Byte
integerToBinary x =
  let unsigned = if x >= 0 then x else byteMax + x
      bitList = integerToBinary' [] unsigned in
    toByte bitList
  where
    byteMax : Integer
    byteMax = 2 `pow` 16

roundTripProp : Integer -> Bool
roundTripProp x =
  (x==) $ binToInteger $ integerToBinary x

or : Vect n Bit -> Vect n Bit -> Vect n Bit
or [] [] = []
or (O :: xs) (y :: ys) = y :: or xs ys
or (I :: xs) (y :: ys) = I :: or xs ys

and : Vect n Bit -> Vect n Bit -> Vect n Bit
and [] [] = []
and (O :: xs) (y :: ys) = O :: and xs ys
and (I :: xs) (y :: ys) = y :: and xs ys

minus : Byte -> Byte -> Byte
minus x y =
  let a = binToInteger x
      b = binToInteger y
      diff = a - b in
    integerToBinary diff

neg : Byte -> Byte
neg x =
  let n = binToInteger x in
    integerToBinary (-n)

inc : Byte -> Byte
inc x =
  let n = binToInteger x in
    integerToBinary (n+1)

dec : Byte -> Byte
dec x =
  let n = binToInteger x in
    integerToBinary (n-1)

plus : Byte -> Byte -> Byte
plus x y =
  let a = binToInteger x
      b = binToInteger y in
    integerToBinary (a+b)

byteCompare : Byte -> Byte -> Ordering
byteCompare a b =
  let x = binToInteger a
      y = binToInteger b in
    compare x y

byteComparison : Ordering -> (Byte -> Byte -> Bool)
byteComparison ord byte1 byte2 = ord == (byteCompare byte1 byte2)

gt : Byte -> Byte -> Bool
gt = byteComparison GT

gte : Byte -> Byte -> Bool
gte byte1 byte2 = (byte1 == byte2) || (gt byte1 byte2)

lt : Byte -> Byte -> Bool
lt = byteComparison LT

lte : Byte -> Byte -> Bool
lte byte1 byte2 = (byte1 == byte2) || (lt byte1 byte2)
