--module Twist.Rewrite
module Main

import Control.Algebra
import Data.Fin
import Data.Fin.Modular
import Data.Vect

%default total
%access public export

data Count : Type where
  CO : Count
  CS : Count -> Count

data Range : Nat -> Type where
  RO : Range (S k)
  RS : Range k -> Range (S k)

SideFunc : Nat -> Type
SideFunc n = Fin (S n) -> Nat

data Axis : (n : Nat) -> (p : SideFunc n) -> Type where
  Ax : (face : Fin (S n)) -> Axis n p

showAxis_debug : (axis : Axis n p) -> String
showAxis_debug (Ax f) = "[" ++ show (toNat f) ++ "]"

CubeFace : Fin 6 -> Nat
CubeFace n = pred 4 --4 sides

CubeAxis : Type
CubeAxis = Axis (pred 6) CubeFace

showAxis_cube : (axis : Axis (pred 6) p) -> String
showAxis_cube (Ax FZ) = "F"
showAxis_cube (Ax (FS FZ)) = "R"
showAxis_cube (Ax (FS (FS FZ))) = "U"
showAxis_cube (Ax (FS (FS (FS FZ)))) = "B"
showAxis_cube (Ax (FS (FS (FS (FS FZ))))) = "L"
showAxis_cube (Ax (FS (FS (FS (FS (FS FZ)))))) = "D"

showAxis : (x : Axis n p) -> String
showAxis {n} x = case n of
                      (S (S (S (S (S Z))))) => showAxis_cube x
                      _                     => showAxis_debug x

Show (Axis n p) where
  show = showAxis


Eq (Axis n p) where
  (Ax x) == (Ax y) = x == y

axInjective : {x : Fin (S n)} -> {y : Fin (S n)} -> (Ax x = Ax y) -> x = y
axInjective Refl = Refl

DecEq (Axis n p) where
  decEq (Ax x) (Ax y) with (decEq x y)
    decEq (Ax x) (Ax x) | Yes Refl  = Yes Refl
    decEq (Ax x) (Ax y) | No contra = No (\h : Ax x = Ax y => contra $ axInjective h)

dof : Axis n p -> Nat
dof (Ax face) = p face

axDofEq : {ax : Axis n p} -> {ay : Axis n p} -> (ax = ay) -> ((dof ax) = (dof ay))
axDofEq Refl = Refl

F : Axis (pred 6) CubeFace
F = Ax 0

R : Axis (pred 6) CubeFace
R = Ax 1

U : Axis (pred 6) CubeFace
U = Ax 2

B : Axis (pred 6) CubeFace
B = Ax 3

L : Axis (pred 6) CubeFace
L = Ax 4

D : Axis (pred 6) CubeFace
D = Ax 5

data Twist : (n : Nat) -> (p : SideFunc n) -> Type where
  Rotate : (axis : Axis n p) -> (amount : Fin (S (dof axis))) -> Twist n p
  -- Orient : (ax : Axis n p) -> (ay : Axis n p) -> Twist n p

Eq (Twist n p) where
  (==) (Rotate ax x) (Rotate ay y) with (decEq ax ay)
    (==) (Rotate ax x) (Rotate ax y) | Yes Refl = x == y
    (==) _ _                         | No _     = False

inverse : Twist n p -> Twist n p
inverse (Rotate ax x) = Rotate ax (inverse x)

rotateAxisInjective : (Rotate ax x = Rotate ay y) -> ax = ay
rotateAxisInjective Refl = Refl

rotateAmountInjective : (Rotate ax x = Rotate ay y) -> x = y
rotateAmountInjective Refl = Refl

DecEq (Twist n p) where
  decEq (Rotate ax x) (Rotate ay y) with (decEq ax ay)
    decEq (Rotate ax x) (Rotate ay y) | No contra = No (\h : Rotate ax x = Rotate ay y => contra $ rotateAxisInjective h) 
    decEq (Rotate ax x) (Rotate ax y) | Yes Refl  with (decEq x y)
      decEq (Rotate ax x) (Rotate ax x) | Yes Refl | Yes Refl  = Yes Refl
      decEq (Rotate ax x) (Rotate ax y) | Yes Refl | No contra = No (\h : Rotate ax x = Rotate ax y => contra $ rotateAmountInjective h)


Show (Twist n p) where
  show (Rotate ax x) = show ax ++ show (toNat x)

||| Combine two twists if possible. Also eliminates zero twists.
combine : (tx : Twist n p) -> (ty : Twist n p) -> Maybe (Twist n p)
combine (Rotate ax FZ) (Rotate ay y) = Just (Rotate ay y)
combine (Rotate ax x) (Rotate ay FZ) = Just (Rotate ax x)
combine (Rotate ax x) (Rotate ay y) with (decEq ax ay)
  combine (Rotate ax x) (Rotate ax y) | Yes Refl = Just (Rotate ax (x <+> y))
  combine (Rotate ax x) (Rotate ay y) | No _     = Nothing


twist : (axis : Axis n p) -> Twist n p
twist axis = Rotate axis (next FZ)

twist' : (axis : Axis n p) -> Twist n p
twist' axis = Rotate axis (prev FZ)

CubeTwist : Type
CubeTwist = Twist (pred 6) CubeFace

data MoveList : (n : Nat) -> (p : SideFunc n) -> Type where
  Moves : Vect len (Twist n p) -> MoveList n p

Eq (MoveList n p) where
  (Moves xs) == (Moves ys) = (length xs == length ys) && (isPrefixOf xs ys)

Show (MoveList n p) where
  show (Moves Nil)           = ""
  show (Moves xss@(x :: xs)) = foldl (\a, b => a ++ " " ++ b) (show x) $ map show xs

(++) : MoveList n p -> MoveList n p -> MoveList n p
(Moves xs) ++ (Moves ys) = Moves (xs ++ ys)

move : Twist n p -> MoveList n p
move x = Moves [x]

reverse : MoveList n p -> MoveList n p
reverse (Moves xs) = Moves (reverse xs)

combineFirstVect : Vect (S k) (Twist n p) -> Either (Vect (S k) (Twist n p)) (Vect k (Twist n p))
combineFirstVect {k=Z} (x :: Nil) = Left (x :: Nil)
combineFirstVect {k=S j} (x :: y :: xs) = case combine x y of
                                               Just xy => Right (xy :: xs)
                                               Nothing => Left (x :: y :: xs)

-- TODO: somehow prove that len <= k
simplifyVect : Vect k (Twist n p) -> (len ** Vect len (Twist n p))
simplifyVect {k=Z} Nil = (Z ** Nil)
simplifyVect {k=S Z} (x :: Nil) = (S Z ** x :: Nil)
simplifyVect {k=S Z} (Rotate _ FZ :: Nil) = (Z ** Nil)
-- simplifyVect {k=S (S j)} xxs = simplifyVect' xxs
simplifyVect {k=S (S j)} xxs with (combineFirstVect xxs)
  simplifyVect {k=S (S j)} xxs | Right combined = simplifyVect combined
  simplifyVect {k=S (S j)} xxs | _              = (S (S j) ** xxs)
  -- simplifyVect {k=S (S j)} xxs with (simplifyVect' xxs)
  --   simplifyVect {k=S (S j)} xxs | (l ** xxs') = simplifyVect xxs'

%default partial

simplify : MoveList n p -> MoveList n p
simplify (Moves xs) = Moves (snd (simplifyVect xs))

Semigroup (MoveList n p) where
  xs <+> ys = simplify $ xs ++ ys

Monoid (MoveList n p) where
  neutral = Moves Nil


inverseEach : MoveList n p -> MoveList n p
inverseEach (Moves xxs) = Moves (map inverse xxs)

Group (MoveList n p) where
  inverse xs = inverseEach $ reverse xs

conjugate : MoveList n p -> MoveList n p -> MoveList n p
conjugate a b = a <+> b <+> inverse a

commutator : MoveList n p -> MoveList n p -> MoveList n p
commutator a b = a <+> b <+> inverse a <+> inverse b

CubeMoveList : Type
CubeMoveList = MoveList (pred 6) CubeFace

rur_u_ : CubeMoveList
rur_u_ = commutator (move (twist R)) (move (twist U))


main : IO ()
main = putStrLn (show (rur_u_ <+> inverse rur_u_))

