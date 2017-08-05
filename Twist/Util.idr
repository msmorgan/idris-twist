module Twist.Util

import Data.Fin
import Data.Vect

%default total
%access export


getAt : {n : Nat} -> Fin (S n) -> Vect (S n) a -> a
getAt {n=_} FZ (x :: _)          = x
getAt {n=(S k)} (FS j) (_ :: xs) = getAt j xs

