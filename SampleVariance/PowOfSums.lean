import Mathlib
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

theorem sum2_unique_symm
  {R : Type u_1} [Field R]
  {ι : Type u_2} [DecidableEq ι]
  {s : Finset ι}
  {f : ι → ι → R}
  : ∑ i ∈ s, ∑ j ∈ s.erase i, f i j = ∑ j ∈ s, ∑ i ∈ s.erase j, f i j
  := by
  conv_lhs =>
    apply_congr
    · skip
    · rw [sum_erase_eq_sub (by assumption)]
  conv_rhs =>
    apply_congr
    · skip
    · rw [sum_erase_eq_sub (by assumption)]
  rw [sum_sub_distrib, sum_sub_distrib, sub_left_inj, @sum_comm]

theorem sum_sq_mul_sq_sum
  {R : Type u_1} [Field R]
  {n : ℕ}
  {f : Fin n → R}
  : (∑ i, f i ^ 2) * (∑ i, f i) ^ 2
    = (∑ i, f i ^ 2) ^ 2
    + ∑ i1, ∑ i2 ∈ univ.erase i1, ∑ i3 ∈ (univ.erase i1).erase i2, f i1 * f i2 * f i3 ^ 2
    + 2 * ∑ i1, ∑ i2 ∈ univ.erase i1, f i1 * f i2 ^ 3
  := by

  conv =>
    enter [2, 1, 2, 2, i1]
    apply_congr
    · skip
    · rw [sum_erase_eq_sub (by assumption)]
  conv =>
    enter [2, 1, 2, 2, i1]
    rw [sum_sub_distrib]
  conv =>
    enter [2, 1, 2]
    rw [sum_sub_distrib]

  conv =>
    enter [2, 1, 2, 1, 2, i1, 2, i2]
    rw [<- mul_sum]
  conv =>
    enter [2, 1, 2, 1, 2, i1]
    rw [<- sum_mul, <- mul_sum]
  conv =>
    enter [2, 1, 2, 1]
    apply_congr
    · skip
    · rw [sum_erase_eq_sub (by assumption)]
  conv =>
    enter [2, 1, 2, 1]
    apply_congr
    · skip
    · rw [sum_erase_eq_sub (by assumption)]
  conv =>
    enter [2, 1, 2, 1, 2, i1]
    rw [mul_sub, mul_sub, sub_mul, sub_mul, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
    rw [<- pow_succ', <- pow_succ']
    simp only [Nat.reduceAdd]
  conv =>
    enter [2, 1, 2, 2, 2, i1, 2, i2]
    rw [mul_assoc, <- pow_succ']
    simp only [Nat.reduceAdd]
  conv =>
    enter [2, 1, 2, 1, 2, i1, 1, 2]
    rw [<- mul_assoc, <- sq]
  conv =>
    enter [2, 1, 2, 1, 2, i1, 2, 1]
    rw [mul_comm, mul_assoc, <- pow_succ]
    simp only [Nat.reduceAdd]
  conv =>
    enter [2, 1, 2, 2, 2, i1]
    rw [<- mul_sum]
  conv =>
    enter [2, 1, 2, 2]
    apply_congr
    · skip
    · rw [sum_erase_eq_sub (by assumption)]
  conv =>
    enter [2, 1, 2, 2, 2, i1]
    rw [mul_sub, <- pow_succ']
    simp only [Nat.reduceAdd]
  conv =>
    enter [2, 2, 2]
    apply_congr
    · skip
    · rw [sum_erase_eq_sub (by assumption)]
  rw [sum_sub_distrib, sum_sub_distrib, sum_sub_distrib, sum_sub_distrib, sum_sub_distrib,
    <- sum_mul, <- sum_mul, <- sum_mul, <- mul_sum]
  conv =>
    enter [2, 2, 2, 1, 2, i1]
    rw [<- mul_sum]
  rw [<- sum_mul]
  conv =>
    enter [2, 2, 2, 2, 2, i1]
    rw [<- pow_succ']
    simp only [Nat.reduceAdd]
  conv =>
    enter [2, 1, 2, 1, 1, 1]
    rw [<- mul_assoc, <- sq, mul_comm]
  rw [<- sq]
  rw [sub_sub, <- two_mul, add_assoc, sub_add, sub_self, sub_zero]
  rw [add_sub, add_comm, <- add_sub, sub_self, add_zero]

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
