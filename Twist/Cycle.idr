module Twist.Cycle

import Control.Algebra
import Data.Fin
import Data.Vect

import Twist.Util

%default total
%access export

data Cycle : (n : Nat) -> Type where
  By : Fin (S k) -> Cycle (S k)

Uninhabited (Cycle Z) where
  uninhabited (By SZ) impossible

Eq (Cycle n) where
  (By x) == (By y) = x == y

DecEq (Cycle n) where
  decEq (By x) (By y) with (decEq x y)
    | Yes p = Yes $ cong p
    | No p  = let result = No p in ?helpCycle

showCycle : {n : Nat} -> Cycle n -> String
showCycle {n=Z}     _      impossible
showCycle {n=(S k)} (By x) = show (finToNat x) ++ "/" ++ show (S k)

Show (Cycle 4) where
  show (By x) = getAt x ["0", "", "2", "'"]

[debug] Show (Cycle n) where
  show = showCycle

||| Convert from (Cycle n) to (Cycle (S n)), without incrementing its value.
||| The resulting cycle will have the same degree as the original.
promote : Cycle (S n) -> Cycle (S (S n))
promote {n} (By x) = By (weaken x)

-- fullPromote : {n, m : Nat} -> {auto p : LTE n m} -> Cycle (S n) -> Cycle (S m)
-- fullPromote {n} {m=(S k)} {p} c = promote (fullPromote {n} {m=k} c)

||| Convert from (Cycle n) to (Cycle (S n)) by incrementing the value.
promote' : Cycle (S n) -> Cycle (S (S n))
promote' {n} (By x) = By (FS x)

||| Convert fom (Cycle (S n)) to (Cycle n), without decrementing its value.
||| The resulting cycle will have the same degree as the original (mod n).
demote : {n : Nat} -> Cycle (S (S n)) -> Cycle (S n)
demote {n} (By x) = By (either (const FZ) id (strengthen x))

||| Convert from (Cycle (S n)) to (Cycle n) by decrementing the underlying value.
demote' : {n : Nat} -> Cycle (S (S n)) -> Cycle (S n)
demote' {n} (By FZ)     = By last
demote' {n} (By (FS x)) = By x

next : Cycle (S n) -> Cycle (S n)
next {n=Z}     _ = By FZ
next {n=(S _)} c = demote (promote' c)

nextN : Nat -> Cycle (S n) -> Cycle (S n)
nextN Z c = c
nextN (S j) c = nextN j (next c)

prev : Cycle (S n) -> Cycle (S n)
prev {n=Z}     _ = By FZ
prev {n=(S _)} c = promote (demote' c)

invertCycle : {n : Nat} -> Cycle (S n) -> Cycle (S n)
invertCycle {n=_}     (By FZ)       = (By FZ)
invertCycle {n=(S k)} (By (FS FZ))  = By last
invertCycle {n=(S k)} (By (FS x))   = promote (invertCycle (By x))

||| Construct a (Cycle n) with degree 0.
cycleZ : (n : Nat) -> {auto n_GTE_1 : GTE n (S Z)} -> Cycle n
cycleZ (S k) {n_GTE_1} = By FZ

||| Construct a (Cycle n) with degree 1.
cycle : (n : Nat) -> {auto n_GTE_2 : GTE n (S (S Z))} -> Cycle n
cycle n@(S _) {n_GTE_2} = next (cycleZ n)

||| Construct a (Cycle n) with degree' 1.
cycle' : (n : Nat) -> {auto n_GTE_2 : GTE n (S (S Z))} -> Cycle n
cycle' n@(S _) {n_GTE_2} = invertCycle (cycle n)

||| Construct a (Cycle n) with degree x.
cycleN : (n : Nat) -> {auto n_GT_0 : GT n Z} -> (x : Nat) -> {auto x_LT_n : LT x n} -> Cycle n
cycleN (S k) {n_GT_0} x {x_LT_n} = nextN x (cycleZ (S k))

cyclePlus : {n : Nat} -> Cycle (S n) -> Cycle (S n) -> Cycle (S n)
cyclePlus {n=_}     (By FZ)     y = y
cyclePlus {n=(S j)} (By (FS p)) y = promote' (cyclePlus (By p) (demote y))

Semigroup (Cycle (S n)) where
  (<+>) = cyclePlus

Monoid (Cycle (S n)) where
  neutral = By FZ

Group (Cycle (S n)) where
  inverse = invertCycle

