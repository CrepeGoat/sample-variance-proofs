-- import Mathlib
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin

open Finset BigOperators

theorem sum_sq_eq
  {R : Type u_1} [Field R]
  {ι : Type u_2} [DecidableEq ι]
  {s : Finset ι}
  {f : ι → R}
  : (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, (f i) ^ 2 + ∑ i ∈ s, ∑ j ∈ s.erase i, f i * f j
  := by
  rw [sq, sum_mul]
  conv =>
    enter [1, 2, i]
    rw [mul_sum]

  conv_rhs =>
    enter [2]
    apply_congr
    · skip
    · rw [sum_erase_eq_sub (by assumption)]

  conv in (fun i => _ - f i * f i) => intro i; rw [<- sq]
  rw [sum_sub_distrib, add_sub, add_comm, <- add_sub, sub_self, add_zero]

theorem sum2_ne_symm
  {R1 : Type u_1}
  {R2 : Type u_2} [AddCommMonoid R2]
  {n : ℕ}
  (s : Finset (Fin n))
  (f g : Fin n → R1)
  (h : R1 → R1 → R2)
  : ∑ i ∈ s, ∑ j ∈ s.erase i, h (f i) (g j) = ∑ i ∈ s, ∑ j ∈ s.erase i, h (g i) (f j)
  := by
  sorry

theorem sum_sq_mul_sq_sum
  {R : Type u_1} [Field R]
  {n : ℕ}
  {f : Fin n → R}
  : (∑ i, f i ^ 2) * (∑ i, f i) ^ 2
    = (∑ i, f i ^ 2) ^ 2
    + ∑ i1, ∑ i2 ∈ univ.erase i1, ∑ i3 ∈ (univ.erase i1).erase i2, f i1 * f i2 * f i3 ^ 2
    + 2 * ∑ i1, ∑ i2 ∈ univ.erase i1, f i1 * f i2 ^ 3
  := by
  rw [sum_sq_eq, mul_add, <- sq, add_assoc, add_right_inj]
  rw [mul_sum]
  conv =>
    enter [1, 2, i1]
    rw [<- mul_sum, <- mul_assoc]
  conv =>
    enter [1, 2, i1, 1]
    rw [mul_comm]
  conv =>
    enter [1, 2, i1]
    rw [mul_assoc]

  conv =>
    enter [1, 2, i1]
    rw [<- sum_erase_add Finset.univ (fun i => f i ^ 2) (by exact mem_univ i1)]
    rw [mul_comm, mul_assoc, add_mul, <- mul_assoc, <- mul_assoc]
  rw [sum_add_distrib]
  conv =>
    enter [1, 2, 2, i1]
    rw [mul_comm, <- mul_assoc, <- pow_succ']
    simp only [Nat.reduceAdd]
  rw [two_mul, <- add_assoc]
  conv =>
    enter [1, 2, 2, i1]
    rw [mul_sum]
  conv =>
    enter [1, 2]
    rw [sum2_ne_symm]
  rw [add_left_inj]

  conv =>
    enter [1, 2, i1]
    rw [mul_comm]
  conv =>
    enter [1, 2, i1, 2]
    rw [mul_comm, sum_mul]

  -- conv =>
  --   enter [1, 2, i1, 2, 2, i2, 2]
  --   rw [<- sum_erase_add (univ.erase i1) (fun i => f i ^ 2) (by
  --     simp only [mem_erase, ne_eq, mem_univ, and_true]
  --     sorry
  --     )]


  -- conv =>
  --   enter [1, 2, i1, 2, 2, i2]
  --   rw [<- mul_sum]
  -- conv =>
  --   enter [1, 2, i1, 2, 2, i2, 2]
  --   apply sum_erase_eq_sub (by simp only [mem_univ])
  -- conv =>
  --   enter [1, 2, i1, 2, 2, i2]
  --   rw [mul_sub, <- sq]
  -- rw [sum_sub_distrib]
  -- conv =>
  --   enter [1, 2, i1, 2, 1]
  --   rw [<- sum_mul, <- sq]
  -- conv =>
  --   enter [1, 2, i1]
  --   rw [mul_sub]
  -- rw [sum_sub_distrib, <- sum_mul, <- sum_mul, <- mul_sub]

  -- rw [<- sum_erase_eq_sub]

  -- conv in (fun i => f i ^ 2 * ∑ i1, _) =>
  --   intro i
  --   rw [sq, mul_assoc, mul_sum]
  -- conv =>
  --   enter [1, 2, i, 2, 2, i1]
  --   rw [mul_sum]
  -- conv =>
  --   enter [1, 2, i, 2, 2, i1, 2, i]
  --   rw [<- mul_assoc]


  sorry


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

def ifun_drop_last
  {R : Type u_1}
  {n : ℕ}
  (f : (Fin n.succ) → R)
  : (Fin n) → R
  := by
  intro j
  apply f
  apply Fin.castLT j
  apply lt_trans (Fin.is_lt j) (n |> Fin.last |> Fin.is_lt)
