module Twist.Move

import Control.Algebra

import Twist.Cycle
import Twist.Face
import Twist.Rotation

%default total
%access export


data Move : (f : Type) -> Type where
  Rest : Move f
  Turn : Rotation f c face -> Move f -> Move f


Show (Move f) where
  show Rest                = ""
  show (Turn r Rest)       = show r
  show (Turn r (Turn s m)) = show m ++ show s ++ show r

