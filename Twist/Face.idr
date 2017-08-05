module Twist.Face

import Data.Vect
import Data.Fin

import Twist.Util


%default total
%access export

data Face : (n : Nat) -> Type where
  F : Fin (S k) -> Face (S k)

Eq (Face n) where
  (F j) == (F k) = j == k

Show (Face 6) where
  show (F k) = getAt k ["F", "R", "U", "B", "L", "D"]

faceZAbsurd : Face Z -> Void
faceZAbsurd (F Z) impossible

DecEq (Face n) where
  decEq (F x) (F y) with (decEq x y)
    | Yes p = Yes $ cong p
    | No  p = let result = No p in ?helpMe

