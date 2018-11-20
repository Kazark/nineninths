module MsV

%default total
%access public export

record Rat where
  constructor Ratio
  numerat : Nat
  decrDen : Nat

ratio : Nat -> (d : Nat) -> { auto prf : IsSucc d} -> Rat
ratio k Z {prf=ItIsSucc} impossible
ratio k (S j) = Ratio k j

intDiv : Rat -> Nat
intDiv (Ratio n d) = intDiv' n d n where
  intDiv' : Nat -> Nat -> Nat -> Nat
  intDiv' _ Z _ = Z
  intDiv' Z n _ = n
  intDiv' origD (S n) Z = S (intDiv' origD n origD)
  intDiv' origD (S n) (S d) = intDiv' origD n d
