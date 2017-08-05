module Twist.Rotation

import Control.Algebra

import Twist.Cycle
import Twist.Face
import Twist.Util

%default total
%access export


data Rotation : (f : Type) -> (c : Type) -> (face : f) -> Type where
  Rot : (face : (Face (S k))) -> (c : Cycle (S j)) -> Rotation (Face (S k)) (Cycle (S j)) face

Eq c => Eq (Rotation f c face) where
  (Rot face cx) == (Rot face cy) = cx == cy

Show (Rotation f c face) where
  show (Rot face x) = show face ++ show x

cw : (Rotation f c face) -> (Rotation f c face)
cw (Rot face cx) = Rot face (next cx)

ccw : (Rotation f c face) -> (Rotation f c face)
ccw (Rot face cx) = Rot face (prev cx)

Semigroup (Rotation f c face) where
  (Rot face cx) <+> (Rot face cy) = Rot face (cx <+> cy)

rotateZ : (face : Face (S k)) -> Rotation (Face (S k)) (Cycle (S j)) face
rotateZ x = Rot x neutral

rotate : (face : Face (S k)) -> Rotation (Face (S k)) (Cycle (S j)) face
rotate x = Rot x (next neutral)

rotate' : (face : Face (S k)) -> Rotation (Face (S k)) (Cycle (S j)) face
rotate' x = Rot x (prev neutral)

Monoid (Rotation (Face (S k)) (Cycle (S j)) face) where
  neutral = Rot face neutral

Group (Rotation (Face (S k)) (Cycle (S j)) face) where
  inverse (Rot face cx) = Rot face (inverse cx)

