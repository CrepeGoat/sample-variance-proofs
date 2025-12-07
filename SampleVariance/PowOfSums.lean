import Mathlib
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Choose.Sum

open Finset BigOperators


theorem pow_sum_castSucc_eq_sum_add_pow
  {R : Type u_1} [CommSemiring R]
  {n k : ℕ}
  {f : Fin (n.succ) → ℝ}
  : (∑ i : Fin n.succ, f i) ^ k
    = ∑ j : Fin k.succ, (∑ i : Fin n, f i.castSucc) ^ j.toNat
    * (f (Fin.last n)) ^ (k - j) * k.choose j
  := by
  rw [Fin.sum_univ_castSucc, add_pow, Finset.sum_range]
  simp only [Nat.succ_eq_add_one, Fin.toNat_eq_val]
