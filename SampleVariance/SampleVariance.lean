
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

noncomputable def mean
  {n : ℕ}
  (X : Fin n → ℝ)
  : ℝ := (∑ i : Fin n, X i) / n

noncomputable def biased_var
  {n : ℕ}
  (X : Fin n → ℝ)
  : ℝ := (∑ i : Fin n, ((X i - mean X) ^ 2)) / n

theorem biased_var_eq_mean_sq_add_sq_mean
  {n : ℕ}
  (X : Fin (n + 1) → ℝ)
  : biased_var X = mean (fun i => X i ^ 2) - mean X ^ 2
  := by
  unfold biased_var mean
  simp only
  -- simp only [<- Nat.cast_add, Nat.cast_one]

  have h : @Nat.cast ℝ Real.instNatCast (n + 1) ≠ 0 := by
    rw [Nat.cast_ne_zero, ne_eq, Nat.add_eq_zero]
    simp only [one_ne_zero, and_false, not_false_eq_true]

  rw [div_eq_iff h]
  rw [sub_mul]
  rw [div_mul_comm]
  nth_rw 2 [(div_eq_one_iff_eq h).mpr (by rfl)]
  rw [one_mul]
  rw [mul_comm]
  -- rw [<- sum_const (@HPow.hPow ℝ ℕ ℝ instHPow ((∑ i, X i) / ↑(n + 1)) 2)]
  -- rw [<- sum_sub_distrib]
  conv =>
    lhs
    congr
    · skip
    · intro i
      rw [sub_sq]
  rw [sum_add_distrib, sum_sub_distrib]
  rw [sum_const]



  -- rw [@div_pow]
  -- nth_rw 2 [pow_succ]
  -- rw [div_mul_eq_div_div]
  -- rw [div_sub_div]
  -- case hb =>
  --   rw [@Nat.cast_ne_zero, Nat.add_one]
  --   simp only [Nat.succ_eq_add_one, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false,
  --     not_false_eq_true]
  -- case hd =>
  --   rw [@Nat.cast_ne_zero, Nat.add_one]
  --   simp only [Nat.succ_eq_add_one, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false,
  --     not_false_eq_true]
  -- rw [div_mul_eq_div_div]
  -- simp only [Nat.cast_add, Nat.cast_one, pow_one]
  -- rw [eq_iff_eq_of_div_eq_div]

  sorry
  -- calc
  --   (∑ i, (X i - mean X) ^ 2) / n
  --     = (∑ i, (X i ^ 2 - 2 * X i * mean X + mean X ^ 2)) / n
  --     := by
  --     conv =>
  --       lhs
  --       congr
  --       · congr
  --         · skip
  --         · intro i
  --           rw [sub_sq]
  --       · skip
  --   _ = (∑ i, (X i ^ 2) - ∑ i, (2 * X i * mean X) + ∑ _ : Fin n, (mean X ^ 2)) / ↑n
  --     := by
  --       rw [div_left_inj]
  --       sorry
  --   := by sorry
  -- sorry


-- ProbabilityTheory.variance_eq_sub
