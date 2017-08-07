module Twist.Rewrite

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

||| Combine two twists if possible.
combine : (tx : Twist n p) -> (ty : Twist n p) -> Maybe (Twist n p)
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
  Nil  : MoveList n p
  (::) : Twist n p -> MoveList n p -> MoveList n p

Eq (MoveList n p) where
  (==) Nil Nil             = True
  (==) _ Nil               = False
  (==) Nil _               = False
  (==) (x :: xs) (y :: ys) with (decEq x y)
    (==) (x :: xs) (x :: ys) | Yes Refl  = xs == ys
    (==) (x :: xs) (y :: ys) | No contra = False

Show (MoveList n p) where
  show Nil        = ""
  show (x :: Nil) = show x
  show (x :: xs)  = show xs ++ " " ++ show x

(++) : MoveList n p -> MoveList n p -> MoveList n p
(++) Nil ys = ys
(++) (x :: xs) ys = x :: (xs ++ ys)

move : Twist n p -> MoveList n p
move x = x :: Nil

reverse : MoveList n p -> MoveList n p
reverse xxs = reverse' Nil xxs where
  reverse' : MoveList n p -> MoveList n p -> MoveList n p
  reverse' acc Nil = acc
  reverse' acc (x :: xs) = reverse' (x :: acc) xs

simplify : MoveList n p -> MoveList n p
simplify Nil                 = Nil
simplify xs@(_ :: Nil)       = xs
simplify (Rotate _ FZ :: xs) = simplify xs
simplify (x :: y :: xs)      = case combine y x of
                                    Just xy => simplify $ assert_smaller (x :: y :: xs) (xy :: xs)
                                    Nothing => x :: simplify (y :: xs)



Semigroup (MoveList n p) where
  xs <+> ys = simplify $ ys ++ xs

Monoid (MoveList n p) where
  neutral = Nil

inverseEach : MoveList n p -> MoveList n p
inverseEach Nil       = Nil
inverseEach ((Rotate ax x) :: xs) = Rotate ax (inverse x) :: inverseEach xs

Group (MoveList n p) where
  inverse xs = inverseEach $ reverse xs

conjugate : MoveList n p -> MoveList n p -> MoveList n p
conjugate a b = a <+> b <+> inverse a

commutator : MoveList n p -> MoveList n p -> MoveList n p
commutator a b = a <+> b <+> inverse a <+> inverse b

CubeMoveList : Type
CubeMoveList = MoveList (pred 6) CubeFace

rur_u_ : CubeMoveList
rur_u_ = commutator (twist R :: Nil) (twist U :: Nil)


--CubeAxis : Type
--CubeAxis = Axis 6 (const (4 ** Fin 4))

-- Front : CubeAxis
-- Front = Ax (FZ ** (4 ** Fin 4))

-- data Rotation

