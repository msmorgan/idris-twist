module Twist.Face

import Data.Vect
import Data.Fin

import Twist.Util


%default total
%access export

data Face : (n : Nat) -> Type where
  F : Fin (S k) -> Face (S k)

Uninhabited (Face Z) where
  uninhabited (F SZ) impossible

Eq (Face n) where
  (F j) == (F k) = j == k

showFace_debug : Face n -> String
showFace_debug (F k) = "[" ++ show (finToNat k) ++ "]"

showFace_6 : Face 6 -> String
showFace_6 (F k) = getAt k ["F", "R", "U", "B", "L", "D"]

showFace : {n : Nat} -> Face n -> String
showFace {n=(S (S (S (S (S (S Z))))))} f = showFace_6 f
showFace {n=_} f = showFace_debug f

Show (Face n) where
  show = showFace


faceZAbsurd : Face Z -> Void
faceZAbsurd (F Z) impossible

DecEq (Face n) where
  decEq (F x) (F y) with (decEq x y)
    | Yes p = Yes $ cong p
    | No  p = let result = No p in ?helpMe

