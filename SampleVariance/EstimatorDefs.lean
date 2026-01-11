import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Moments.Basic
import Mathlib.Data.Finset.Range

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

noncomputable def mse
  {Ω : Type u_2} [MeasurableSpace Ω]
  (X : Ω → ℝ)
  (θ : ℝ)
  (P : Measure Ω) [IsFiniteMeasure P]
  : ℝ := variance X P + (bias X θ P) ^ 2

theorem mse_eq
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {X : Ω → ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P]
  (hXm2 : MemLp X 2 P)
  (θ : ℝ)
  : mse X θ P = P[X ^ 2] - 2 * P[X] * θ + θ ^ 2
  := by
  unfold mse
  rw [bias_eq_sub ?hXIntegrable, sub_sq, sub_add, add_sub, sub_add, sub_left_inj]
  case hXIntegrable =>
    rw [<- memLp_one_iff_integrable]
    apply MemLp.mono_exponent hXm2
    exact one_le_two
  rw [<- sub_eq_iff_eq_add.mp]
  rw [variance_eq_sub hXm2]
