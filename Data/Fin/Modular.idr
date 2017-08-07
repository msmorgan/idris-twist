module Data.Fin.Modular

import Control.Algebra
import Data.Fin

%default total
%access public export

promote : Fin n -> Fin (S n)
promote x = weaken x

promote' : Fin n -> Fin (S n)
promote' x = FS x

demote : Fin (S (S n)) -> Fin (S n)
demote x = either (const FZ) id (strengthen x)

demote' : Fin (S (S n)) -> Fin (S n)
demote' FZ      = last
demote' (FS x') = x'


next : Fin (S k) -> Fin (S k)
next x = demote (promote' x)

prev : Fin (S k) -> Fin (S k)
prev x = demote' (promote x)


Semigroup (Fin (S k)) where
  (<+>) FZ y        = y
  (<+>) {k=S _} (FS FZ) y = next y
  (<+>) {k=S _} (FS x') y = promote (x' <+> demote y)

Monoid (Fin (S k)) where
  neutral = FZ <+> FZ

Group (Fin (S k)) where
  inverse FZ              = FZ
  inverse {k=S _} (FS FZ) = last
  inverse {k=S _} x       = promote (inverse (demote' x))

