module Twist.Face

import Data.Vect
import Data.Fin


%default total
%access export

data Face : (n : Nat) -> Type where
  Side : {k : Nat} -> Fin (S k) -> Face (S k)

Uninhabited (Face Z) where
  uninhabited (Side SZ) impossible

Eq (Face n) where
  (Side j) == (Side k) = j == k

-- compat' : (Face j) -> (Face k) -> Bool
-- compat' {j} {k} x y with (the (Face j) y)
--   compat' {j} {j}x y' | y' = True

-- Compatible (Face j) (Face k) where
--   compat {j} {k} _ _ with (decEq j k)
--     compat {j=n} {k=n} _ _ | Yes Refl = True
--     compat {j} {k} _ _     | _        = False

-- Equatable (Face j) (Face k) where
--   equals (Side x) (Side y) {c=Refl} = x == y
--   equals _ _ {c=_}                  = False

    
equals : (Face (S j)) -> (Face (S k)) -> {auto p : j = k} -> Bool
equals (Side x) (Side y) {p=Refl} = x == y
equals _ _ {p=_}                  = False

-- face : (n : Nat) -> (x : Nat) -> {auto n_GT_0 : GT n 0} -> {auto x_LT_n : LT x n} -> Face n
-- face n x {n_GT_0=_} {x_LT_n=_} with (natToFin x n)
--   | Maybe j = Side j
--   | Nothing impossible

showFace_debug : Face n -> String
showFace_debug (Side k) = "[" ++ show (finToNat k) ++ "]"

showFace_6 : Face 6 -> String
showFace_6 (Side k) = index k ["F", "R", "U", "B", "L", "D"]

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
    | No  p = let result = No p in ?helpCycle

