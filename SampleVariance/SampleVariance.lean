
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.Finset.Range

import SampleVariance.MomentsOfSums
import SampleVariance.SampleStatisticsDefs

open Finset MeasureTheory ProbabilityTheory NNReal
open scoped ENNReal


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
--         rw [biased_svar_eq_sub]
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

private theorem moment_1_smean
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P]
  (hX : ∀ i, MemLp (X i) 1 P)
  (hXIndep : iIndepFun X P)
  (hXIdent : (i j : Fin (n + 1)) → IdentDistrib (X i) (X j) P P)
  : P[fun ω => smean (fun i => X i ω)]
    = moment (X (Fin.last n)) 1 P
  := by
  have h1 : @HAdd.hAdd ℝ ℝ ℝ instHAdd (↑n) 1 ≠ 0 := by
    rw [ne_eq, <- Nat.cast_one, <- Nat.cast_add, @Nat.cast_eq_zero, Nat.add_one, <- ne_eq]
    apply Nat.succ_ne_zero

  unfold smean
  rw [integral_div]
  conv =>
    enter [1, 1, 2, ω]
    simp only
    rw [<- sum_apply]
  conv =>
    enter [1, 1, 2, ω]
    rw [<- pow_one ((∑ x, X x))]
  rw [<- moment_def, _1_moment_sum hX hXIndep hXIdent]
  rw [mul_comm, <- mul_div, Nat.cast_add_one, div_self h1, mul_one]

private theorem moment_1_smean_sq
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P]
  (hX : ∀ i, MemLp (X i) 2 P)
  (hXIndep : iIndepFun X P)
  (hXIdent : (i j : Fin (n + 1)) → IdentDistrib (X i) (X j) P P)
  : P[fun ω => smean (fun i => X i ω ^ 2)]
    = moment (X (Fin.last n)) 2 P
  := by
  rw [moment_1_smean]
  case hX =>
    intro i
    rw [memLp_one_iff_integrable]
    apply MemLp.integrable_sq (hX i)
  case hXIndep =>
    have h2 : ∀ k, (X k ^ 2) = (fun x => x ^ 2) ∘ X k := by
      intro k
      unfold Function.comp
      simp only
      rw [@Pi.pow_def]
    conv =>
      enter [1, i, ω]
      rw [<- Pi.pow_apply, h2]
    apply iIndepFun.comp hXIndep
    intro i
    apply Measurable.pow (by exact measurable_id) (by exact measurable_const)
  case hXIdent =>
    intro i j
    have h2 : ∀ k, (X k ^ 2) = (fun x => x ^ 2) ∘ X k := by
      intro k
      unfold Function.comp
      simp only
      rw [@Pi.pow_def]
    conv in ((X _ _ ^ 2)) =>
      rw [<- Pi.pow_apply]
    conv in ((X _ _ ^ 2)) =>
      rw [<- Pi.pow_apply]
    rw [h2, h2]
    apply IdentDistrib.comp (hXIdent i j)
    apply Measurable.pow (by exact measurable_id) (by exact measurable_const)

  rw [moment]
  conv =>
    enter [1, 2, ω]
    rw [pow_one, <- Pi.pow_apply]
  rw [<- moment]

private theorem moment_2_smean
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P]
  (hX : ∀ i, MemLp (X i) 2 P)
  (hXIndep : iIndepFun X P)
  (hXIdent : (i j : Fin (n + 1)) → IdentDistrib (X i) (X j) P P)
  : P[fun ω => (smean fun i ↦ X i ω) ^ 2]
    = (1 / (n + 1)) * moment (X (Fin.last n)) 2 P
    + (n / (n + 1)) * moment (X (Fin.last n)) 1 P ^ 2
  := by
  unfold smean
  simp only
  conv in ((_ / _) ^ 2) => rw [div_pow]
  rw [integral_div]
  conv =>
    enter [1, 1, 2, ω]
    rw [<- sum_apply, <- Pi.pow_apply]
  rw [<- moment, _2_moment_sum hX hXIndep hXIdent, mul_assoc, <- mul_add, mul_comm, <- mul_div]
  simp only [Nat.cast_add, Nat.cast_one]
  conv in ((↑n + 1) ^ 2) => rw [sq]

  have h1 : @HAdd.hAdd ℝ ℝ ℝ instHAdd (↑n) 1 ≠ 0 := by
    rw [ne_eq, <- Nat.cast_one, <- Nat.cast_add, @Nat.cast_eq_zero, Nat.add_one, <- ne_eq]
    apply Nat.succ_ne_zero

  rw [div_mul_eq_div_div, div_self h1, mul_comm, mul_add, add_right_inj]
  rw [<- mul_assoc]
  nth_rw 2 [mul_comm]
  rw [mul_div, mul_one]

private theorem moment_1_biased_svar
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P]
  (hX : ∀ i, MemLp (X i) 2 P)
  (hXIndep : iIndepFun X P)
  (hXIdent : (i j : Fin (n + 1)) → IdentDistrib (X i) (X j) P P)
  : P[fun ω => biased_svar (fun i => X i ω)]
    = (↑n / (↑n + 1)) * (
      moment (X (Fin.last n)) 2 P
      - moment (X (Fin.last n)) 1 P ^ 2
    )
  := by
  conv in (biased_svar _) => rw [biased_svar_eq_sub]
  simp only
  rw [integral_sub ?hInteg1 ?hInteg2]
  case hInteg1 =>
    unfold smean
    simp only [Nat.cast_add, Nat.cast_one]
    apply Integrable.div_const
    apply integrable_finset_sum; intro i hi
    conv =>
      enter [1, ω]
      rw [<- Pi.pow_apply]
    apply MemLp.integrable_sq (hX i)
  case hInteg2 =>
    unfold smean
    conv in ((_ / _) ^ 2) => rw [div_pow, sum_sq_eq_sum_sum_mul]
    apply Integrable.div_const
    apply integrable_finset_sum; intro i hi
    apply integrable_finset_sum;  intro j hj
    conv =>
      enter [1, ω]
      rw [<- Pi.mul_apply]
    -- https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/ISO.20help.20with.20theorem.20using.20MemLp.20and.20IdentDistrib/near/566627078
    apply MemLp.integrable_mul (hX i) (hX j)
  rw [moment_2_smean hX hXIndep hXIdent, moment_1_smean_sq hX hXIndep hXIdent]
  rw [mul_sub, <- sub_sub, sub_left_inj]
  nth_rw 1 [<- one_mul (moment (X (Fin.last n)) 2 P)]

  let mX := moment (X (Fin.last n)) 2 P
  have hmX : mX = moment (X (Fin.last n)) 2 P := by rfl
  rw [<- hmX]

  rw [<- sub_mul, mul_eq_mul_right_iff]
  left
  rw [<- sub_eq_zero, sub_sub, <- add_div, add_comm, div_self ?h1, sub_self]
  case h1 =>
    rw [ne_eq, <- Nat.cast_one, <- Nat.cast_add, @Nat.cast_eq_zero, Nat.add_one, <- ne_eq]
    apply Nat.succ_ne_zero

example
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P]
  (hX : ∀ i, MemLp (X i) 2 P)
  (hXIntegrable : (i : Fin (n + 1)) → Integrable (X i) P)
  (hXIndep : iIndepFun X P)
  (hXIdent : (i j : Fin (n + 1)) → IdentDistrib (X i) (X j) P P)
  (k : ℝ)
  : P[fun ω => k * biased_svar (fun i => X i ω)]
    = k * (↑n / (↑n + 1)) * (
      moment (X (Fin.last n)) 2 P
      - moment (X (Fin.last n)) 1 P ^ 2
    )
  := by
  rw [integral_const_mul, mul_assoc, mul_eq_mul_left_iff]
  left
  -- apply moment_1_biased_svar hX hXIntegrable hXIndep hXIdent
  sorry

private theorem moment_2_scaled_svar
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P]
  (hX : ∀ i, MemLp (X i) 4 P)
  (hXIntegrable : (i : Fin (n + 1)) → Integrable (X i) P)
  (hXIndep : iIndepFun X P)
  (hXIdent : (i j : Fin (n + 1)) → IdentDistrib (X i) (X j) P P)
  (k : ℝ)
  : P[(fun ω => k * biased_svar (fun i => X i ω)) ^ 2]
    = k ^ 2 * (
      ((↑n + 1) ^ 2 + 1) / (↑n + 1) ^ 3 * moment (X (Fin.last n)) 4 P
      + ↑n / (↑n + 1) * (1 + 3 / (↑n + 1) ^ 2) * moment (X (Fin.last n)) 2 P ^ 2
    )
  := by
  let Xi : Ω → ℝ := X (Fin.last n)
  have hXi : Xi = X (Fin.last n) := by rfl
  -- rw [<- hXi]

  have h1 : @HAdd.hAdd ℝ ℝ ℝ instHAdd (↑n) 1 ≠ 0 := by
    rw [ne_eq, <- Nat.cast_one, <- Nat.cast_add, @Nat.cast_eq_zero, Nat.add_one, <- ne_eq]
    apply Nat.succ_ne_zero

  conv in (biased_svar _) => rw [biased_svar_eq_sub]
  unfold smean
  simp only [Nat.cast_add, Nat.cast_one, Pi.pow_apply]

  conv =>
    enter [1, 2, ω]
    rw [mul_pow, sub_sq]
  rw [integral_const_mul, mul_eq_mul_left_iff]
  left
  rw [integral_add ?hf1 ?hg1, integral_sub ?hf2 ?hg2]
  case hf1 => sorry
  case hg1 => sorry
  case hf2 => sorry
  case hg2 => sorry
  conv =>
    enter [1, 1, 1, 2, ω]
    rw [div_pow]
    calc
      @HDiv.hDiv ℝ ℝ ℝ instHDiv ((∑ x, X x ω ^ 2) ^ 2) ((↑n + 1) ^ 2)
        = @HDiv.hDiv ℝ ℝ ℝ instHDiv ((∑ x, X x ^ 2) ω ^ 2) ((↑n + 1) ^ 2)
      := by simp?
      _ = @HDiv.hDiv ℝ ℝ ℝ instHDiv (((∑ x, X x ^ 2) ^ 2) ω) ((↑n + 1) ^ 2)
      := by simp?
      _ = @HDiv.hDiv ℝ ℝ ℝ instHDiv (((∑ x, (X ^ 2) x) ^ 2) ω) ((↑n + 1) ^ 2)
      := by simp?
  rw [integral_div, <- moment_def, _2_moment_sum ?hX ?hXIndep ?hXIdent]
  case hX => sorry
  case hXIndep => sorry
  case hXIdent => sorry
  conv =>
    enter [1, 1, 1, 1]
    rw [moment_def, moment_def, Pi.pow_apply, <- pow_mul, <- pow_mul]
    simp only [Nat.reduceMul]
    rw [<- moment, <- moment, <- hXi]
  conv =>
    enter [1, 1, 2, 2, ω]
    rw [mul_assoc, div_pow, div_mul_div_comm, <- pow_succ']
    simp only [Nat.reduceAdd]
  rw [integral_const_mul, integral_div]
  conv =>
    enter [1, 2, 2, ω]
    rw [<- pow_mul, div_pow]
    simp only [Nat.reduceMul]
    calc
      (∑ x, X x ω) ^ 4 / (↑n + 1) ^ 4
        = (∑ x, X x) ω ^ 4 / (↑n + 1) ^ 4
      := by simp?
      _ = (((∑ x, X x) ^ 4) ω) / (↑n + 1) ^ 4
      := by simp?
  rw [integral_div, <- moment, _4_moment_sum ?hX ?hXIndep ?hXIdent]
  case hX => sorry
  case hXIndep => sorry
  case hXIdent => sorry
  rw [<- hXi, one_mul]
  simp_rw [add_div]
  conv =>
    enter [1, 1, 1, 1]
    rw [mul_comm, <- mul_div, sq, div_mul_eq_div_div, div_self h1, mul_div, mul_one]
  conv =>
    enter [1, 1, 1, 2]
    rw [mul_assoc, mul_comm, <- mul_div, sq (_ + 1), div_mul_eq_div_div, div_self h1,
      mul_div, mul_one]
  simp_rw [add_assoc]
  rw [add_comm, add_sub, add_comm]
  simp_rw [add_assoc, <- add_assoc]
  conv =>
    enter [1, 1, 1, 1, 1, 1]
    rw [add_comm, <- add_assoc]
  conv =>
    enter [1, 1, 1, 1, 1, 1, 1]
    calc
      (↑n + 1) * moment Xi 4 P / (↑n + 1) ^ 4 + moment Xi 4 P / (↑n + 1)
        = moment Xi 4 P / (↑n + 1) ^ 3 + moment Xi 4 P / (↑n + 1)
      := by
        rw [add_left_inj, mul_comm, <- mul_div]
        nth_rw 2 [div_eq_mul_one_div]
        rw [mul_eq_mul_left_iff]
        left
        rw [pow_succ', div_mul_eq_div_div, div_self h1]
      _ = moment Xi 4 P * (1 / (↑n + 1) ^ 3 + 1 / (↑n + 1))
      := by
        rw [<- mul_one (moment Xi 4 P), <- mul_div, <- mul_div, <- mul_add, mul_one]
      _ = (((↑n + 1) ^ 2 + 1) / (↑n + 1) ^ 3) * moment Xi 4 P
      := by
        rw [mul_comm, mul_eq_mul_right_iff]
        left
        nth_rw 1 [pow_succ']
        rw [div_mul_eq_div_div, div_eq_mul_one_div]
        nth_rw 2 [<- mul_one (@HDiv.hDiv ℝ ℝ ℝ instHDiv 1 (↑n + 1) : ℝ)]
        rw [<- mul_add]
        nth_rw 3 [pow_succ]
        rw [div_mul_eq_div_div]
        nth_rw 3 [div_eq_mul_one_div]
        rw [mul_comm, mul_eq_mul_right_iff]
        left
        rw [add_div, <- div_pow, div_self h1, one_pow, add_comm]
  rw [add_assoc, add_assoc, add_assoc, add_assoc, <- add_sub]
  nth_rw 1 [add_div]
  rw [add_right_inj]

  rw [<- add_assoc, <- add_assoc, <- add_assoc]
  conv =>
    enter [1, 1, 1, 1, 1]
    calc
      ↑n * moment Xi 2 P ^ 2 / (↑n + 1)
        + 3 * (↑n + 1) * ↑n * moment Xi 2 P ^ 2 / (↑n + 1) ^ 4
        = ↑n * moment Xi 2 P ^ 2 * (1 / (↑n + 1) + 3 * (↑n + 1) / (↑n + 1) ^ 4)
      := by
        rw [mul_assoc]
        nth_rw 2 [mul_comm]
        nth_rw 1 [div_eq_mul_one_div]
        rw [<- mul_div, <- mul_add, mul_eq_mul_left_iff]
        left
        simp only [one_div]
      _ = ↑n / (↑n + 1) * moment Xi 2 P ^ 2 * (1 + 3 * (↑n + 1) / (↑n + 1) ^ 3)
      := by
        nth_rw 5 [mul_comm]
        nth_rw 1 [mul_div]
        nth_rw 5 [mul_comm]
        nth_rw 4 [mul_comm]
        nth_rw 1 [mul_div]
        nth_rw 4 [mul_comm]
        nth_rw 2 [<- mul_div]
        rw [mul_eq_mul_left_iff]
        left
        rw [add_div, add_right_inj, <- mul_div, <- mul_div, <- mul_div, mul_eq_mul_left_iff]
        left
        rw [div_div, pow_succ]
      _ = ↑n / (↑n + 1) * moment Xi 2 P ^ 2 * (1 + 3 / (↑n + 1) ^ 2)
      := by
        rw [mul_eq_mul_left_iff]
        left
        rw [add_right_inj]
        nth_rw 2 [div_eq_mul_one_div]
        rw [<- mul_div, mul_eq_mul_left_iff]
        left
        rw [pow_succ', div_mul_eq_div_div, div_self h1]
      _ = ↑n / (↑n + 1) * (1 + 3 / (↑n + 1) ^ 2) * moment Xi 2 P ^ 2
      := by linarith only []
  rw [add_assoc, add_assoc, <- add_sub]
  rw [add_eq_left]
  sorry

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

  let Xi : Ω → ℝ := X (Fin.last n)
  have hXi : Xi = X (Fin.last n) := by rfl
  rw [<- hXi]

  conv in (biased_svar _) => rw [biased_svar_eq_sub]
  conv in (biased_svar _) => rw [biased_svar_eq_sub]
  unfold smean
  simp only [Pi.pow_apply]
  rw [variance_eq_sub ?hMemLp]
  case hMemLp =>
    apply MemLp.mono_exponent
    case q => exact 4
    case hpq =>
      rw [Nat.ofNat_le]
      simp only [Nat.reduceLeDiff]
    case hfq => exact hX (Fin.last n)

  have hn_neq_0 : @Ne ℝ (↑(n + 1)) 0 := by
    rw [Nat.cast_ne_zero];
    simp only [ne_eq, Nat.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]

  simp only [Pi.pow_apply]
  rw [integral_const_mul, integral_sub, integral_div]
  -- rw [integral_const_mul, integral_mul_const, integral_div, integral_add, integral_sub]
  conv =>
    enter [1, 1, 1, 2, ω]
    rw [mul_pow, div_pow, sub_sq, div_pow, div_pow, <- pow_mul, <- pow_mul]
    simp only [Nat.reduceMul]
  rw [integral_const_mul, integral_add, integral_sub, integral_div, integral_div, mul_add, mul_sub]

  -- conv =>
  --   enter [1, 1, 1, 2, ω]
  --   rw [mul_div, mul_comm, <- mul_div, mul_comm, mul_pow]
  -- conv =>
  --   enter [1, 1, 1]
  --   rw [integral_const_mul]
  -- conv =>
  --   enter [1, 1, 1, 2, 2, ω, 1, 2, i]
  --   rw [sub_sq]
  -- conv =>
  --   enter [1, 1, 1, 2, 2, ω]
  --   rw [sum_add_distrib, sum_sub_distrib]
  -- conv =>
  --   enter [1, 1, 1, 2, 2, ω, 1, 1, 2, 2, x]
  --   rw [mul_div, mul_assoc, mul_comm, <- mul_div, mul_comm]
  -- conv =>
  --   enter [1, 1, 1, 2, 2, ω, 1, 1, 2]
  --   rw [<- mul_sum, <- sum_mul]
  -- conv =>
  --   enter [1, 1, 1, 2, 2, ω, 1, 2, 2, i]
  --   rw [div_pow, <- mul_one (@HPow.hPow ℝ ℕ ℝ instHPow (∑ x, X x ω) 2), <- mul_div, mul_comm]
  -- conv =>
  --   enter [1, 1, 1, 2, 2, ω, 1, 2]
  --   rw [<- mul_sum]
  -- conv =>
  --   enter [1, 1, 1, 2, 2, ω]
  --   rw [add_sq, mul_sub, mul_pow, div_pow, <- pow_mul, sub_sq]
  --   simp only [sum_const, Nat.reduceMul, card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- conv =>
  --   enter [1, 1, 1, 2, 2, ω, 1, 2, 2]
  --   rw [<- mul_assoc, div_mul, sq, <- mul_div, div_self hn_neq_0, mul_one]
  -- conv =>
  --   enter [1, 1, 1, 2, 2, ω, 2]
  --   rw [one_pow, mul_pow, <- pow_mul, <- mul_assoc, div_mul, pow_succ, pow_succ, mul_assoc, <- sq,
  --     <- mul_div, div_self (by rw [ne_eq, sq_eq_zero_iff, <- ne_eq]; apply hn_neq_0), mul_one]
  --   simp only [Nat.reduceMul]
  -- rw [integral_add, integral_add, integral_add, integral_sub]
  -- conv =>
  --   enter [1, 1, 1, 2, 1, 2, 2, ω]
  --   rw [sub_mul, <- sq]
  -- rw [integral_sub]


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
  --           · rw [biased_svar_eq_sub]
  --             unfold smean
  --           · skip
  --     · congr
  --       · congr
  --         · skip
  --         · congr
  --           · skip
  --           · ext ω
  --             rw [biased_svar_eq_sub]
  --             unfold smean
  --       · skip
  --   · skip
  --
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
  --
  -- rw [integral_mul_const, mul_comm]
  -- rw [variance_eq_sub, sub_sq, <- pow_mul]
  -- nth_rw 2 [sub_add]
  -- rw [add_sub, <- sub_add]
  -- rw [add_left_inj, sub_left_inj, add_eq_right]
  -- rw [integral_add, integral_sub, integral_mul_const, integral_sub, integral_div]
  --
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
  --
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
  --
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
  --
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
  --
  -- simp only [Nat.cast_add, Nat.cast_one]
  -- let Xi : Ω → ℝ := X (Fin.last n)
  -- have hXi : Xi = X (Fin.last n) := by rfl
  -- simp_rw [<- hXi]
  --
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
  --
  -- simp_rw [mul_add, add_mul, mul_sub, sub_mul, add_div, one_mul]
  -- simp_rw [mul_add, add_mul, mul_sub, sub_mul]
  -- simp_rw [mul_add, add_mul]
  --
  -- rw [mul_add, add_div, add_div, add_mul, add_mul, add_mul, add_mul, add_mul, mul_sub, mul_sub, sub_mul]
  -- simp only [one_mul]
  -- rw [mul_add, add_mul, mul_sub, mul_add, sub_mul, add_mul, sub_mul, add_div, mul_add, add_mul]
  sorry
