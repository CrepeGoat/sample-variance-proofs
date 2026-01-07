import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.Finset.Range

open Finset MeasureTheory ProbabilityTheory NNReal
open scoped ENNReal

noncomputable def smean
  {R : Type u_1} [Field R]
  {n : ℕ}
  (X : Fin n → R)
  : R := (∑ i : Fin n, X i) / n

noncomputable def biased_svar
  {R : Type u_1} [Field R]
  {n : ℕ}
  (X : Fin n → R)
  : R := (∑ i : Fin n, ((X i - smean X) ^ 2)) / n

theorem biased_svar_eq_sub
  {n : ℕ}
  (X : Fin (n + 1) → ℝ)
  : biased_svar X = smean (fun i => X i ^ 2) - smean X ^ 2
  := by
  have h : @Nat.cast ℝ Real.instNatCast (n + 1) ≠ 0 := by
    rw [Nat.cast_ne_zero, ne_eq, Nat.add_eq_zero]
    simp only [one_ne_zero, and_false, not_false_eq_true]

  unfold biased_svar smean
  rw [div_eq_iff h]
  rw [sub_mul, div_mul_comm]
  nth_rw 2 [(div_eq_one_iff_eq h).mpr (by rfl)]
  rw [one_mul]

  conv =>
    lhs
    congr
    · skip
    · intro i
      rw [sub_sq]
  rw [sum_add_distrib, sum_sub_distrib]
  rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc, add_right_inj]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow]

  rw [<- sum_mul, <- mul_sum, mul_assoc, mul_div, <- sq]
  nth_rw 3 [mul_comm]
  rw [<- eq_sub_iff_add_eq, sub_eq_add_neg, neg_mul_eq_neg_mul, <- two_mul, mul_neg,
    neg_mul_eq_neg_mul, mul_right_inj' (by simp only [ne_eq, neg_eq_zero, OfNat.ofNat_ne_zero,
      not_false_eq_true])]
  rw [div_eq_iff h, mul_comm, <- mul_assoc, <- sq, mul_comm, div_mul_comm]
  nth_rw 1 [<- one_mul (@HPow.hPow ℝ ℕ ℝ instHPow (∑ i, X i) 2)]
  by_cases (@HPow.hPow ℝ ℕ ℝ instHPow (∑ i, X i) 2) = 0
  case pos h2 => rw [h2, mul_zero, mul_zero]
  case neg h2 =>
    rw [<- ne_eq] at h2
    rw [mul_left_inj' h2]
    simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, div_self]

noncomputable def unbiased_svar
  {R : Type u_1} [Field R]
  {n : ℕ}
  (X : Fin n → R)
  : R := (∑ i : Fin n, ((X i - smean X) ^ 2)) / (n - 1)

theorem unbiased_svar_eq_mul_biased_svar
  {n : ℕ}
  (X : Fin (n + 2) → ℝ)
  : unbiased_svar X = (n + 2) / (n + 1) * biased_svar X
  := by
  have h : ∀ m, @Nat.cast ℝ Real.instRing.toAddGroupWithOne.toNatCast m + 1 ≠ 0 := by
    intro m
    rw [<- Nat.cast_add_one, Nat.cast_ne_zero, ne_eq, Nat.add_eq_zero]
    simp only [one_ne_zero, and_false, not_false_eq_true]

  unfold unbiased_svar biased_svar
  simp only [Nat.cast_add, Nat.cast_ofNat]
  rw [mul_div, div_eq_div_iff ?h1 ?h2]
  case h1 =>
    rw [<- add_sub, <- one_add_one_eq_two, <- add_sub, sub_self, add_zero]
    exact h n
  case h2 =>
    rw [<- one_add_one_eq_two, <- add_assoc, <- Nat.cast_add_one]
    exact h (n + 1)
  conv_rhs =>
    rw [mul_comm, <- mul_assoc]
  conv =>
    enter [2, 1]
    rw [mul_div, mul_comm, <- mul_div, <- add_sub, <- one_add_one_eq_two, <- add_sub, sub_self,
      add_zero, one_add_one_eq_two, div_self (h n), mul_one]
  rw [mul_comm]

theorem biased_svar_eq_mul_unbiased_svar
  {R : Type u_1} [Field R]
  {n : ℕ}
  (X : Fin (n + 2) → ℝ)
  : biased_svar X = (n + 1) / (n + 2) * unbiased_svar X
  := by
  rw [unbiased_svar_eq_mul_biased_svar, eq_comm, <- mul_assoc]
  nth_rw 2 [<- one_mul (biased_svar X)]
  rw [mul_eq_mul_right_iff]
  left
  rw [div_mul_div_comm, mul_comm, div_self ?h1]

  have h : ∀ m, @Nat.cast ℝ Real.instRing.toAddGroupWithOne.toNatCast m + 1 ≠ 0 := by
    intro m
    rw [<- Nat.cast_add_one, Nat.cast_ne_zero, ne_eq, Nat.add_eq_zero]
    simp only [one_ne_zero, and_false, not_false_eq_true]

  case h1 =>
    rw [mul_ne_zero_iff]
    constructor
    case right =>
      exact h n
    case left =>
      rw [<- one_add_one_eq_two, <- add_assoc, <- Nat.cast_add_one]
      exact h (n + 1)
