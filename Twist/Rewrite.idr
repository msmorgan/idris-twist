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

-- DecEq (Axis n p) where
--   decEq (Ax x) (Ax y) with (decEq x y)
--     decEq (Ax x) (Ax x) | Yes Refl = Yes Refl
--     decEq _ _           | No contra = No $ absurd contra

getDof : Axis n p -> Nat
getDof (Ax face) = p face

CubeFace : Fin 6 -> Nat
CubeFace n = pred 4 --4 sides

CubeAxis : Type
CubeAxis = Axis (pred 6) CubeFace

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

data Rotation : (axis : Axis n p) -> Type where
  Rot : (amount : Fin (S (getDof axis))) -> Rotation axis

Semigroup (Rotation axis) where
  (Rot x) <+> (Rot y) = Rot (x <+> y)

Monoid (Rotation axis) where
  neutral = Rot 0

Group (Rotation axis) where
  inverse (Rot x) = Rot (inverse x)

data MoveList : (n : Nat) -> (p : SideFunc n) -> Type where
  Nil  : MoveList n p
  (::) : {axis : Axis n p} -> Rotation axis -> MoveList n p -> MoveList n p

(++) : MoveList n p -> MoveList n p -> MoveList n p
(++) Nil ys = ys
(++) (x :: xs) ys = x :: (xs ++ ys)

reverse : MoveList n p -> MoveList n p
reverse xxs = reverse' Nil xxs where
  reverse' : MoveList n p -> MoveList n p -> MoveList n p
  reverse' acc Nil = acc
  reverse' acc (x :: xs) = reverse' (x :: acc) xs


Semigroup (MoveList n p) where
  xs <+> ys = xs ++ (reverse ys)

Monoid (MoveList n p) where
  neutral = Nil

inverseMoveList' : MoveList n' p' -> MoveList n' p' -> MoveList n' p'
inverseMoveList' acc Nil = acc
inverseMoveList' acc (x :: xs) = inverseMoveList' (inverse x :: acc) xs

Group (MoveList n p) where
  inverse xs = inverseMoveList' Nil xs
  







--CubeAxis : Type
--CubeAxis = Axis 6 (const (4 ** Fin 4))

-- Front : CubeAxis
-- Front = Ax (FZ ** (4 ** Fin 4))

-- data Rotation

