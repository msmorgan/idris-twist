module Twist.Rotation

import Control.Algebra

import Twist.Cycle
import Twist.Face
import Twist.Util

%default total
%access export


data Rotation : (f : Type) -> (c : Type) -> (face : f) -> Type where
  Rot : (face : (Face (S k))) -> (c : Cycle (S j)) -> Rotation (Face (S k)) (Cycle (S j)) face

Eq (Rotation f c face) where
  (Rot face cx) == (Rot face cy) = cx == cy

-- the face types are implied by the faces being equal
--compat : Rotation f c x -> Rotation g d y -> {auto f_EQ_g : f = g} -> {auto c_EQ_d : c = d} -> Bool
--compat (Rot x cx) (Rot y cy) {f_EQ_g=Refl} {c_EQ_d=Refl} = x == y
--compat _ _ {f_EQ_g=_} {c_EQ_d=_}                         = False

--sameRotType : (r : Rotation f c x) -> (s : Rotation g d y) -> {auto p : compat r s = True} -> Rotation f c x = Rotation g d y
--sameRotType r s {p=Refl} = Refl
--sameRotType _ _ {p=_} impossible

-- compat' : Rotation f c x ->
--           Rotation g d y ->
--           {auto f_EQ_g : f = g} ->
--           {auto c_EQ_d : c = d} ->
--           {auto x_EQ_y : x ~=~ y} -> Bool
-- compat' (Rot x cx) (Rot y cy) {f_EQ_g=Refl} {c_EQ_d=Refl} {x_EQ_y=Refl} = True
-- compat' _ _ {f_EQ_g=_} {c_EQ_d=_} {x_EQ_y}                              = False


--equals : Rotation f c x -> Rotation g d y -> {auto f_EQ_g : f = g} -> {auto c_EQ_d : c = d} -> Bool
--equals (Rot x cx) (Rot y cy) {f_EQ_g=Refl} {c_EQ_d=Refl} = x == y && cx == cy
--equals _ _ {f_EQ_g=_} {c_EQ_d=_}                         = False



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

