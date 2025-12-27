
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
  {n : ℕ}
  (X : Fin n → ℝ)
  : ℝ := (∑ i : Fin n, X i) / n

noncomputable def biased_svar
  {n : ℕ}
  (X : Fin n → ℝ)
  : ℝ := (∑ i : Fin n, ((X i - smean X) ^ 2)) / n

theorem biased_svar_eq_smean_sq_add_sq_smean
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

noncomputable def bias
  {Ω : Type u_2} [MeasurableSpace Ω]
  (X : Ω → ℝ)
  (θ : ℝ)
  (P : Measure Ω) [IsFiniteMeasure P]
  : ℝ := P[fun ω : Ω => X ω - θ]

theorem bias_eq_sub
  {Ω : Type u_2} [MeasurableSpace Ω]
  {X : Ω → ℝ}
  {θ : ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P]
  (hXIntegrable : Integrable X P)
  : bias X θ P = P[X] - θ
  := by
  unfold bias
  simp only
  rw [integral_sub hXIntegrable (by simp), integral_const, smul_eq_mul, sub_right_inj,
    measureReal_univ_eq_one, one_mul]

-- theorem bias_svar_var
--   {Ω : Type u_1} [m : MeasurableSpace Ω]
--   {P : Measure Ω} [IsProbabilityMeasure P]
--   {n k : ℕ}
--   (X : Fin (n + 1) → Ω → ℝ)
--   : bias (fun ω => biased_svar (fun i => X i ω)) (variance (X (Fin.last n)) P) P
--     = (-1 / (n + 1)) * (variance (X (Fin.last n)) P)
--   := by
--   have h : @Nat.cast ℝ Real.instNatCast (n + 1) ≠ 0 := by
--     rw [Nat.cast_ne_zero, ne_eq, Nat.add_eq_zero]
--     simp only [one_ne_zero, and_false, not_false_eq_true]

--   rw [bias_eq_sub ?hSvarIntegrable]
--   case hSvarIntegrable =>
--     sorry
--   conv =>
--     lhs
--     congr
--     · congr
--       · skip
--       · ext ω
--         rw [biased_svar_eq_smean_sq_add_sq_smean]
--     · skip

--   rw [sub_eq_iff_eq_add', neg_div, neg_mul, <- sub_eq_add_neg]
--   nth_rw 1 [<- one_mul (@variance Ω m (X (Fin.last n)) P)]
--   rw [<- sub_mul, sub_div' (by simp_all only [Nat.cast_add, Nat.cast_one, ne_eq, not_false_eq_true]), one_mul, add_sub_cancel_right]


--   unfold smean
--   simp only
--   rw [integral_sub, integral_div]
--   rw [moment_def]
--   sorry

noncomputable def mse
  {Ω : Type u_2} [MeasurableSpace Ω]
  (X : Ω → ℝ)
  (θ : ℝ)
  (P : Measure Ω) [IsFiniteMeasure P]
  : ℝ := variance X P + (bias X θ P) ^ 2

-- ProbabilityTheory.variance_eq_sub

theorem mse_eq
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {X : Ω → ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P]
  (hXIntegrable : Integrable X P)
  (hXm2 : MemLp X 2 P)
  (θ : ℝ)
  : mse X θ P = P[X ^ 2] - 2 * P[X] * θ + θ ^ 2
  := by
  unfold mse
  rw [bias_eq_sub hXIntegrable, sub_sq, sub_add, add_sub, sub_add, sub_left_inj]
  rw [<- sub_eq_iff_eq_add.mp]
  rw [variance_eq_sub hXm2]


theorem mse_scaled_svar_var
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {X : Fin (n + 1) → Ω → ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P]
  (hXIntegrable : (i : Fin (n + 1)) → Integrable (X i) P)
  (hXm2 : (i : Fin (n + 1)) → MemLp (X i) 2 P)
  (θ : ℝ)
  (k : ℝ)
  : mse (fun ω => k * biased_svar (fun i => X i ω)) (variance (X (Fin.last n)) P) P
    =
      -- P[X (Fin.last n) ^ 2] - P[X (Fin.last n)] ^ 2
      P[X (Fin.last n) ^ 2] ^ 2
      - 2 * P[X (Fin.last n) ^ 2] * P[X (Fin.last n)] ^ 2
      + P[X (Fin.last n)] ^ 4
  := by
  rw [mse_eq]
  case hXIntegrable =>
    unfold biased_svar
    simp only [Nat.cast_add, Nat.cast_one]
    sorry
    -- rw [integrable_mul_const_iff]
  case hXm2 =>
    sorry

  conv =>
    lhs
    congr
    · congr
      · congr
        · skip
        · simp only [Pi.pow_apply]
          ext ω
          rw [mul_pow]
          congr
          · skip
          · congr
            · rw [biased_svar_eq_smean_sq_add_sq_smean]
              unfold smean
            · skip
      · congr
        · congr
          · skip
          · congr
            · skip
            · ext ω
              rw [biased_svar_eq_smean_sq_add_sq_smean]
              unfold smean
        · skip
    · skip

  simp only
  conv =>
    lhs
    congr
    · congr
      · congr
        · skip
        · ext ω
          rw [mul_comm, sub_sq]
      · congr
        · congr
          · skip
          · congr
            · skip
            · ext ω
              rw [mul_comm]
        · skip
    · skip

  rw [integral_mul_const, mul_comm]
  rw [variance_eq_sub, sub_sq, <- pow_mul]
  nth_rw 2 [sub_add]
  rw [add_sub, <- sub_add]
  rw [add_left_inj, sub_left_inj, add_eq_right]

  conv =>
    lhs
    rw [<- moment]

  sorry
