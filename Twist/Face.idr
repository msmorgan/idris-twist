module Twist.Face

import Data.Vect
import Data.Fin

import Twist.Util


%default total
%access export

data Face : (n : Nat) -> Type where
  Side : Fin (S k) -> Face (S k)

Uninhabited (Face Z) where
  uninhabited (Side SZ) impossible

Eq (Face n) where
  (Side j) == (Side k) = j == k

-- face : (n : Nat) -> (x : Nat) -> {auto n_GT_0 : GT n 0} -> {auto x_LT_n : LT x n} -> Face n
-- face n x {n_GT_0=_} {x_LT_n=_} with (natToFin x n)
--   | Maybe j = Side j
--   | Nothing impossible

equals : Face m -> Face n -> {auto p : m = n} -> Bool
equals x y {p=Refl} = x == y
equals _ _ {p=_}    = False


showFace_debug : Face n -> String
showFace_debug (Side k) = "[" ++ show (finToNat k) ++ "]"

showFace_6 : Face 6 -> String
showFace_6 (Side k) = getAt k ["Side", "R", "U", "B", "L", "D"]

showFace : {n : Nat} -> Face n -> String
showFace {n=(S (S (S (S (S (S Z))))))} f = showFace_6 f
showFace {n=_} f = showFace_debug f

Show (Face n) where
  show = showFace


faceZAbsurd : Face Z -> Void
faceZAbsurd (Side Z) impossible

DecEq (Face n) where
  decEq (Side x) (Side y) with (decEq x y)
    | Yes p = Yes $ cong p
    | No  p = let result = No p in ?helpMe

