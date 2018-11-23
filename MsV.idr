module MsV

import Data.Fin

%default total
%access public export

||| Encode a rational number as a fraction of a numerator and a decremental
||| denominator, thereby structural eliminating the possible of division by
||| zero.
record Frac where
  constructor Fract
  numerat : Nat
  decrDen : Nat

Fraction : Nat -> (d : Nat) -> { auto prf : IsSucc d } -> Frac
Fraction k Z {prf=ItIsSucc} impossible
Fraction k (S j) = Fract k j

Num Frac where
  (Fract n d) + (Fract m e) =
    if d == e
    then Fract (n + m) d
    else
      let d' = S d in
      let e' = S e in
      Fraction (n * e' + m * d') (d' * e')

  (Fract n d) * (Fract m e) =
    let d' = S d in
    let e' = S e in
    Fraction (n * m) (d' * e')

  fromInteger x = Fraction (fromInteger x) 1

intDiv : Frac -> Nat
intDiv (Fract n d) = intDiv' d n d where
  intDiv' : Nat -> Nat -> Nat -> Nat
  intDiv' _ Z _ = Z
  intDiv' Z n _ = n
  intDiv' origD (S n) Z = S (intDiv' origD n origD)
  intDiv' origD (S n) (S d) = intDiv' origD n d

Digit : Type
Digit = Fin 10

||| Whether we are carrying a digit during addition
data Carry = CarryOne | CarryNone

natToDigit : Nat -> Maybe Digit
natToDigit n = natToFin n 10

||| Add two fins
addFins : Fin (S n) -> Fin (S m) -> Fin (S n + S m)
addFins {n} {m} FZ x = rewrite plusCommutative (S n) (S m) in weakenN (S n) x
addFins {n} {m} x FZ = weakenN (S m) x
addFins {n = (S _)} {m = (S _)} (FS x) y@(FS _) = FS $ addFins x y

checkForCarry : Fin 20 -> (Carry, Digit)
checkForCarry FZ = (CarryNone, 0)
checkForCarry (FS FZ) = (CarryNone, 1)
checkForCarry (FS (FS FZ)) = (CarryNone, 2)
checkForCarry (FS (FS (FS FZ))) = (CarryNone, 3)
checkForCarry (FS (FS (FS (FS FZ)))) = (CarryNone, 4)
checkForCarry (FS (FS (FS (FS (FS FZ))))) = (CarryNone, 5)
checkForCarry (FS (FS (FS (FS (FS (FS FZ)))))) = (CarryNone, 6)
checkForCarry (FS (FS (FS (FS (FS (FS (FS FZ))))))) = (CarryNone, 7)
checkForCarry (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))) = (CarryNone, 8)
checkForCarry (FS (FS (FS (FS (FS (FS (FS (FS (FS x))))))))) = (CarryNone, 9)
checkForCarry (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS x)))))))))) = (CarryOne, x)

addDigits : Digit -> Digit -> (Carry, Digit)
addDigits x y = checkForCarry $ addFins x y

||| Enode a rational number as either a terminating or repeating decimal
record Dec where
  constructor Decimal
  integPart : Nat
  nonrepeat : List Digit
  repeating : List Digit

infixr 5 +++

(+++) : Dec -> Dec -> Dec

-- 0.25 + 0.^3^ = 0.58^3^

fracToDec : Frac -> Dec

decToFrac : Dec -> Frac

OneNinth : Frac
OneNinth = Fraction 1 9

EightNinths : Frac
EightNinths = Fraction 8 9

NineNinths : Frac
NineNinths = Fraction 9 9

One : Dec
One = Decimal 1 [] []

DotOnesRepeating : Dec
DotOnesRepeating = Decimal 0 [] [1]

DotEightsRepeating : Dec
DotEightsRepeating = Decimal 0 [] [8]

DotNinesRepeating : Dec
DotNinesRepeating = Decimal 0 [] [9]

lemma1 : fracToDec OneNinth = DotOnesRepeating

lemma8 : fracToDec EightNinths = DotEightsRepeating

lemmaAddFrac : OneNinth + EightNinths = NineNinths

lemmaAddDec : DotOnesRepeating +++ DotEightsRepeating = DotNinesRepeating

theoremFD : fracToDec NineNinths = DotNinesRepeating

theoremDF : decToFrac DotNinesRepeating = NineNinths

||| Are the two decimals different encodings of the same number?
iso : Dec -> Dec -> Bool

theorem : iso One DotNinesRepeating = True
