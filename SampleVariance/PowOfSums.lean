-- import Mathlib
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin

open Finset BigOperators


theorem pow_sum_castSucc_eq_sum_add_pow
  {R : Type u_1} [CommSemiring R]
  {n : ℕ}
  {f : Fin (n.succ) → R}
  {k : ℕ}
  : (∑ i : Fin n.succ, f i) ^ k
    = ∑ j : Fin k.succ, (∑ i : Fin n, f i.castSucc) ^ j.toNat
    * (f (Fin.last n)) ^ (k - j) * k.choose j
  := by
  rw [Fin.sum_univ_castSucc, add_pow, Finset.sum_range, Nat.succ_eq_add_one]
  rfl

def ifun_first_n
  {R : Type u_1}
  {n : ℕ}
  (f : (Fin n) → R)
  (i : Fin n)
  : (Fin i.toNat) → R
  := by
  intro j
  apply f
  apply Fin.castLT j
  apply lt_trans (Fin.is_lt j) (Fin.is_lt i)
