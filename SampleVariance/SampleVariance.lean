
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.Finset.Range

import SampleVariance.MomentsOfSums

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
  (hXm2 : MemLp X 2 P)
  (hXIntegrable : Integrable X P)
  (θ : ℝ)
  : mse X θ P = P[X ^ 2] - 2 * P[X] * θ + θ ^ 2
  := by
  unfold mse
  rw [bias_eq_sub hXIntegrable, sub_sq, sub_add, add_sub, sub_add, sub_left_inj]
  rw [<- sub_eq_iff_eq_add.mp]
  rw [variance_eq_sub hXm2]


theorem mse_scaled_svar_var
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P]
  (hX : ∀ i, MemLp (X i) 4 P)
  (hXIntegrable : (i : Fin (n + 1)) → Integrable (X i) P)
  (hXIdent : (i j : Fin (n + 1)) → IdentDistrib (X i) (X j) P P)
  (θ : ℝ)
  (k : ℝ)
  : mse (fun ω => k * biased_svar (fun i => X i ω)) (variance (X (Fin.last n)) P) P
    =
      k ^ 2 * (
        (1 / (↑n + 1)) * moment (X (Fin.last n)) 4 P
        + (↑n / (↑n + 1)) * moment (X (Fin.last n)) 2 P ^ 2
        - (2 / (↑n + 1) ^ 3) * (∫ (a : Ω), (∑ x, X x a ^ 2) * (∑ x, X x a) ^ 2 ∂P)
        + (
          moment (X (Fin.last n)) 4 P
          + 3 * ↑n * moment (X (Fin.last n)) 2 P ^ 2
          + 4 * ↑n * moment (X (Fin.last n)) 3 P * moment (X (Fin.last n)) 1 P
          + 6 * ↑n * (↑n - 1) * moment (X (Fin.last n)) 2 P * moment (X (Fin.last n)) 1 P ^ 2
          + ↑n * (↑n - 1) * (↑n - 2) * moment (X (Fin.last n)) 1 P ^ 4
        ) / (↑n + 1) ^ 3
      )
      - (2 * k * (↑n / (↑n + 1)) + 1) * (
        moment (X (Fin.last n)) 2 P
        - moment (X (Fin.last n)) 1 P ^ 2
      ) ^ 2
  := by
  rw [mse_eq]
  case hXIntegrable =>
    unfold biased_svar
    simp only [Nat.cast_add, Nat.cast_one]
    sorry
    -- rw [integrable_mul_const_iff]
  case hXm2 =>
    sorry

  -- conv =>
  --   lhs
  --   congr
  --   · congr
  --     · congr
  --       · skip
  --       · simp only [Pi.pow_apply]
  --         ext ω
  --         rw [mul_pow]
  --         congr
  --         · skip
  --         · congr
  --           · rw [biased_svar_eq_smean_sq_add_sq_smean]
  --             unfold smean
  --           · skip
  --     · congr
  --       · congr
  --         · skip
  --         · congr
  --           · skip
  --           · ext ω
  --             rw [biased_svar_eq_smean_sq_add_sq_smean]
  --             unfold smean
  --       · skip
  --   · skip

  -- simp only
  -- conv =>
  --   lhs
  --   congr
  --   · congr
  --     · congr
  --       · skip
  --       · ext ω
  --         rw [mul_comm, sub_sq]
  --     · congr
  --       · congr
  --         · skip
  --         · congr
  --           · skip
  --           · ext ω
  --             rw [mul_comm]
  --       · skip
  --   · skip

  -- rw [integral_mul_const, mul_comm]
  -- rw [variance_eq_sub, sub_sq, <- pow_mul]
  -- nth_rw 2 [sub_add]
  -- rw [add_sub, <- sub_add]
  -- rw [add_left_inj, sub_left_inj, add_eq_right]
  -- rw [integral_add, integral_sub, integral_mul_const, integral_sub, integral_div]

  -- conv =>
  --   lhs
  --   congr
  --   · congr
  --     · skip
  --     · congr
  --       · congr
  --         · congr
  --           · skip
  --           · ext ω
  --             rw [div_pow]
  --         · congr
  --           · skip
  --           · ext ω
  --             rw [div_pow, mul_assoc, div_mul_div_comm, <- pow_succ' (@Nat.cast ℝ Real.instNatCast (n + 1))]
  --             simp only [Nat.reduceAdd]
  --             rw [mul_div, mul_comm, <- mul_div]
  --       · congr
  --         · skip
  --         · ext ω
  --           rw [div_pow, div_pow, <- pow_mul, <- pow_mul]
  --           simp only [Nat.reduceMul]
  --   · congr
  --     · congr
  --       · skip
  --       · congr
  --         · congr
  --           · skip
  --           · congr
  --             · skip
  --             · ext ω
  --               rw [div_pow]
  --         · skip
  --     · skip
  -- simp only [Pi.pow_apply]
  -- rw [integral_div, integral_div, integral_div, integral_mul_const]
  -- -- rw [<- Pi.pow_apply]

  -- have moment_1_sum_sq : ∫ (a : Ω), ∑ i, X i a ^ 2 ∂P = (n + 1) * moment (X (Fin.last n)) 2 P
  --   := by
  --   calc
  --     ∫ (a : Ω), ∑ i, X i a ^ 2 ∂P
  --       = ∫ (a : Ω), (∑ i, X i ^ 2) a ∂P
  --     := by simp only [sum_apply, Pi.pow_apply]
  --     _ = moment (∑ i, X i ^ 2) 1 P
  --     := by rw [moment_def, pow_one]
  --     _ = moment (∑ i, (X ^ 2) i) 1 P
  --     := by simp only [Pi.pow_apply]
  --     _ = (n + 1) * moment ((X ^ 2) (Fin.last n)) 1 P
  --     := by
  --       apply _1_moment_sum
  --       case hX => sorry
  --       case hXIdent => sorry
  --       case hXIndep => sorry
  --     _ = (n + 1) * moment (X (Fin.last n)) 2 P
  --     := by
  --       rw [moment_def, moment_def]
  --       simp only [Pi.pow_apply, pow_one]

  -- have moment_2_sum_sq : ∫ (a : Ω), (∑ x, X x a ^ 2) ^ 2 ∂P
  --   = (n + 1) * moment (X (Fin.last n)) 4 P
  --     + (n + 1) * n * moment (X (Fin.last n)) 2 P ^ 2
  --   := by
  --   calc
  --     ∫ (a : Ω), (∑ x, X x a ^ 2) ^ 2 ∂P
  --       = ∫ (ω : Ω), ((∑ i, (X i) ^ 2) ^ 2) ω ∂P
  --     := by simp only [Pi.pow_apply, sum_apply]
  --     _ = moment (∑ i, (fun j => (X j) ^ 2) i) 2 P
  --     := by rw [moment_def]
  --     _ = (n + 1) * moment (X (Fin.last n) ^ 2) 2 P
  --       + (n + 1) * n * moment (X (Fin.last n) ^ 2) 1 P ^ 2
  --     := by
  --       rw [_2_moment_sum ?hX ?hXIndep ?hXIdent]
  --       case hX =>
  --         intro i
  --         sorry
  --       case hXIndep =>
  --         -- apply iIndepFun.comp ?h1
  --         sorry
  --       case hXIdent =>
  --         sorry
  --     _ = (n + 1) * moment (X (Fin.last n)) 4 P
  --       + (n + 1) * n * moment (X (Fin.last n)) 2 P ^ 2
  --     := by
  --       rw [moment_def, moment_def, <- pow_mul, <- pow_mul, <- moment_def, <- moment_def]

  -- conv =>
  --   lhs
  --   congr
  --   · congr
  --     · skip
  --     · congr
  --       · congr
  --         · congr
  --           · rw [moment_2_sum_sq]
  --           · skip
  --         · congr
  --           · skip -- TODO
  --           · skip
  --       · congr
  --         · calc
  --           ∫ (a : Ω), (∑ x, X x a) ^ 4 ∂P
  --             = ∫ (a : Ω), ((∑ x, X x) ^ 4) a ∂P
  --           := by simp only [Pi.pow_apply, sum_apply]
  --           _ = moment (∑ x, X x) 4 P
  --           := by rw [moment_def]
  --           _ = 1 * (n + 1) * moment (X (Fin.last n)) 4 P
  --             + 3 * (n + 1) * n * (moment (X (Fin.last n)) 2 P) ^ 2
  --             + 4 * (n + 1) * n * (moment (X (Fin.last n)) 3 P) * (moment (X (Fin.last n)) 1 P)
  --             + 6 * (n + 1) * n * (n - 1) * (moment (X (Fin.last n)) 2 P) * (moment (X (Fin.last n)) 1 P) ^ 2
  --             + 1 * (n + 1) * n * (n - 1) * (n - 2) * (moment (X (Fin.last n)) 1 P ^ 4)
  --           := by
  --             apply _4_moment_sum
  --             case hX => sorry
  --             case hXIndep => sorry
  --             case hXIdent => sorry
  --         · skip
  --   · congr
  --     · congr
  --       · skip
  --       · congr
  --         · congr
  --           · congr
  --             · rw [moment_1_sum_sq]
  --             · skip
  --           · congr
  --             · calc
  --               ∫ (a : Ω), (∑ x, X x a) ^ 2 ∂P
  --                 = ∫ (a : Ω), ((∑ x, X x) ^ 2) a ∂P
  --               := by simp only [Pi.pow_apply, sum_apply]
  --               _ = moment (∑ x, X x) 2 P
  --               := by rw [moment_def]
  --               _ = (n + 1) * moment (X (Fin.last n)) 2 P
  --                 + (n + 1) * n * moment (X (Fin.last n)) 1 P ^ 2
  --               := by
  --                 apply _2_moment_sum
  --                 case hX => sorry
  --                 case hXIdent => sorry
  --                 case hXIndep => sorry
  --             · skip
  --         · skip
  --     · congr
  --       · calc
  --         ∫ (x : Ω), X (Fin.last n) x ^ 2 ∂P
  --           = moment (X (Fin.last n)) 2 P
  --         := by
  --           rw [moment_def]
  --           simp only [Pi.pow_apply]
  --         _ = moment (X (Fin.last n)) 2 P
  --         := by simp only
  --       · congr
  --         · calc
  --           ∫ (x : Ω), X (Fin.last n) x ∂P
  --             = moment (X (Fin.last n)) 1 P
  --           := by
  --             rw [moment_def]
  --             simp only [Pi.pow_apply, pow_one]
  --           _ = moment (X (Fin.last n)) 1 P
  --           := by simp only
  --         · skip

  -- simp only [Nat.cast_add, Nat.cast_one]
  -- let Xi : Ω → ℝ := X (Fin.last n)
  -- have hXi : Xi = X (Fin.last n) := by rfl
  -- simp_rw [<- hXi]

  -- simp only [one_mul]
  -- conv in (((↑n + 1) * moment Xi 4 P + (↑n + 1) * ↑n * moment Xi 2 P ^ 2) / (↑n + 1) ^ 2) => rw [add_div]
  -- conv in ((↑n + 1) * moment Xi 4 P / (↑n + 1) ^ 2) => rw [mul_comm, <- mul_div]
  -- nth_rw 1 [<- pow_one (@HAdd.hAdd ℝ ℝ ℝ instHAdd (↑n) 1)]
  -- -- rw [div_eq_mul_inv]
  -- conv in ((↑n + 1) ^ 1 / (↑n + 1) ^ 2) => calc
  --   (@HDiv.hDiv ℝ ℝ ℝ instHDiv ((↑n + 1) ^ 1) ((↑n + 1) ^ 2))
  --     = ((n + 1) ^ 0 / (n + 1) ^ 1)
  --   := by
  --     rw [div_eq_div_iff]
  --     case hb =>
  --       rw [ne_eq, sq_eq_zero_iff, <- Nat.cast_one, <- Nat.cast_add, Nat.cast_eq_zero]
  --       rw [<- Nat.succ_eq_add_one, <- ne_eq]
  --       apply Nat.succ_ne_zero
  --     case hd =>
  --       rw [ne_eq, pow_one, <- Nat.cast_one, <- Nat.cast_add, Nat.cast_eq_zero]
  --       rw [<- Nat.succ_eq_add_one, <- ne_eq]
  --       apply Nat.succ_ne_zero
  --     linarith only []
  --   _ = (1 / (n + 1))
  --   := by simp only [pow_zero, pow_one, one_div]

  -- simp_rw [mul_add, add_mul, mul_sub, sub_mul, add_div, one_mul]
  -- simp_rw [mul_add, add_mul, mul_sub, sub_mul]
  -- simp_rw [mul_add, add_mul]


  -- rw [mul_add, add_div, add_div, add_mul, add_mul, add_mul, add_mul, add_mul, mul_sub, mul_sub, sub_mul]
  -- simp only [one_mul]
  -- rw [mul_add, add_mul, mul_sub, mul_add, sub_mul, add_mul, sub_mul, add_div, mul_add, add_mul]
  sorry
