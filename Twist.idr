module Twist

import Control.Algebra
import Data.Fin
import Data.Vect

import Twist.Cycle
import Twist.Face
import Twist.Move
import Twist.Rotation
import Twist.Util

%default total


Face' : Type
Face' = Face 6

Rotation' : Face' -> Type
Rotation' = Rotation Face' (Cycle 4)


data MoveSeq : Type where
  Nil : MoveSeq
  (::) : Rotation' f -> MoveSeq -> MoveSeq

Show MoveSeq where
  show Nil = ""
  show (x :: Nil) = show x
  show (x :: xs) = show xs ++ " " ++ show x

||| Concatenate two MoveSeqs together (in reverse order!)
(++) : MoveSeq -> MoveSeq -> MoveSeq
Nil ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

reverse : MoveSeq -> MoveSeq
reverse m = reverse' Nil m where
  reverse' : MoveSeq -> MoveSeq -> MoveSeq
  reverse' acc Nil = acc
  reverse' acc (x :: xs) = reverse' (x :: acc) xs

inverseEach : MoveSeq -> MoveSeq
inverseEach Nil = Nil
inverseEach (x :: xs) = inverse x :: inverseEach xs


||| Construct a MoveSeq from a single Rotation'.
move : Rotation' f -> MoveSeq
move r = r :: Nil

twist : Face' -> MoveSeq
twist f = move (rotate f)


twist' : Face' -> MoveSeq
twist' f = move (rotate' f)

||| Combine two Rotation's into a MoveSeq.
combine : (Rotation' f) -> (Rotation' g) -> MoveSeq
combine {f=R} {g=R} first second = (first <+> second) :: Nil
combine {f=L} {g=L} first second = (first <+> second) :: Nil
combine {f=U} {g=U} first second = (first <+> second) :: Nil
combine {f=D} {g=D} first second = (first <+> second) :: Nil
combine {f=F} {g=F} first second = (first <+> second) :: Nil
combine {f=B} {g=B} first second = (first <+> second) :: Nil
combine {f=Dbg n} {g=Dbg m} first second =  second :: first :: Nil
combine {f=_} {g=_} first second = second :: first :: Nil


simplify : MoveSeq -> MoveSeq
simplify Nil = Nil
simplify (r :: Nil) = r :: Nil
simplify (last :: prev :: xs) = (combine prev last) ++ xs


Semigroup MoveSeq where
  xs <+> Nil = xs
  xs <+> (last :: ys) = simplify (last :: (xs <+> ys))

Monoid MoveSeq where
  neutral = Nil

Group MoveSeq where
  inverse m = inverse' Nil m where
    inverse' : MoveSeq -> MoveSeq -> MoveSeq
    inverse' acc Nil = acc
    inverse' acc (x :: xs) = inverse' (inverse x :: acc) xs

conjugate : MoveSeq -> MoveSeq -> MoveSeq
conjugate a b = a <+> b <+> (inverse a)

commutator : MoveSeq -> MoveSeq -> MoveSeq
commutator a b = a <+> b <+> (inverse a) <+> (inverse b)

namespace Moves
  rur_ : MoveSeq
  rur_ = conjugate (twist R) (twist U)

  r_ur : MoveSeq
  r_ur = inverseEach rur_

  rur_u_ : MoveSeq
  rur_u_ = commutator (twist R) (twist U)

  r_u_ru : MoveSeq
  r_u_ru = commutator (twist' R) (twist' U)

  r_frf_ : MoveSeq
  r_frf_ = commutator (twist' R) (twist F)

  fru_ : MoveSeq
  fru_ = twist F <+> twist R <+> twist' U

  fr : MoveSeq
  fr = move (rotate F) <+> move (rotate R)

  namespace OLL
    fish_4 : MoveSeq
    fish_4 = conjugate fru_ r_ur
    oll_37 : MoveSeq
    oll_37 = conjugate (twist U) fish_4

    t_1 : MoveSeq
    t_1 = rur_u_ <+> r_frf_
    oll_33 : MoveSeq
    oll_33 = t_1

  namespace PLL
    yPerm : MoveSeq
    yPerm = OLL.fish_4 <+> OLL.t_1

    tPerm : MoveSeq
    tPerm = OLL.t_1 <+> OLL.fish_4




[zipList] Applicative List where
  pure x = [x]
  fns <*> values = zipWith id fns values



{-
data Move : Type where
  Nil : Move
  Twist : Face' -> Rotation' -> Move -> Move

-- FIXME: use proofs to make this more elegant
simplify : Move -> Move
simplify Nil = Nil
simplify final@(Twist f CW (Twist g CCW initial))             = if f == g then initial else final
simplify final@(Twist f CCW (Twist g CW initial))             = if f == g then initial else final
simplify final@(Twist f CW (Twist g CW (Twist h CW initial))) = if f == g && f == h
                                                                   then Twist f CCW initial
                                                                   else final
simplify final@(Twist f CW (Twist g CW (Twist h CW initial))) = if f == g && f == h
                                                                   then Twist f CCW initial
                                                                   else final

Semigroup Move where
  (<+>) Nil Nil = Nil
  (<+>) Nil m = m
  (<+>) m Nil = m

-}


