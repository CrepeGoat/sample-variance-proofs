import Mathlib

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

import SampleVariance.PowOfSums

-- https://leanprover-community.github.io/blog/posts/basic-probability-in-mathlib/
open MeasureTheory ProbabilityTheory NNReal
open scoped ENNReal


-- https://leanprover-community.githb.io/blog/posts/basic-probability-in-mathlib/#:~:text=Measure%20%CE%A9.-,Identically%20distributed,-IdentDistrib%20X%20Y
-- https://leanprover-community.github.io/blog/posts/basic-probability-in-mathlib/#:~:text=of%20the%20indicator).-,Independence,-Mathlib%20has%20several


noncomputable def isum_rv
  {R : Type u_1} [NormedAddCommGroup R] [NormedSpace ℝ R] [CommSemiring R] -- [MeasurableSpace R]
  {Ω : Type u_2} [MeasurableSpace Ω]
  {n : ℕ}
  (X : (Fin n) → Ω → R)
  -- (hX : (i : Fin n) → Measurable (X i))
  : (Ω → R) := fun (ω : Ω) => (∑ i : Fin n, X i ω)


-- -- set_option maxHeartbeats 10000000 in
-- theorem iindepfun_then_indep_isum_drop_last_last
--   {Ω : Type u_1} [MeasurableSpace Ω]
--   {μ : Measure Ω} [IsProbabilityMeasure μ]
--   {n : ℕ}
--   {X : Fin n.succ → Ω → ℝ}
--   (hXIndep : iIndepFun X μ)
--   (m : Fin n)
--   : IndepFun
--     (m.castSucc |> ifun_first_n X |> isum_rv)
--     (n |> Fin.last |> X) μ
--   := by
--   induction m
--   case mk
--   ·
--   sorry

example
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ}
  {X : Fin n → Ω → ℝ}
  -- (hX : (i : Fin n) → Measurable (X i))
  (hXIntegrable : (i : Fin n) → Integrable (X i) μ)
  : (moment (isum_rv X) 1 μ = ∑ i : Fin n, moment (X i) 1 μ)
  := by
  unfold isum_rv moment
  simp only [pow_one, Pi.pow_apply]
  rw [integral_finset_sum]
  intro i _
  exact hXIntegrable i

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Integration.html#ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral


example
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ}
  {X : Fin n → Ω → ℝ}
  -- (hXIntegrable : (i : Fin n) → Integrable (X i) μ)
  (hXIndep : iIndepFun X μ)
  : (moment (∏ i : Fin n, X i) 1 μ = ∏ i : Fin n, moment (X i) 1 μ)
  := by
  unfold moment
  simp only [Finset.prod_apply, Pi.pow_apply, pow_one]
  sorry


theorem k_moment_sum_expand
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ}
  (X : Fin n.succ → Ω → ℝ)
  (k : ℕ)
  : moment (isum_rv X) k μ
   = μ[∑ ki : Fin k.succ, (X |> ifun_drop_last |> isum_rv) ^ ki.toNat
    * (n |> Fin.last |> X) ^ (k - ki) * k.choose ki]
  := by
    unfold moment ifun_drop_last isum_rv
    simp only [Nat.succ_eq_add_one, Pi.pow_apply, Fin.toNat_eq_val,
      Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply]
    rewrite [<- MeasureTheory.setIntegral_univ]
    nth_rewrite 2 [<- MeasureTheory.setIntegral_univ]
    apply setIntegral_congr_fun
    · exact MeasurableSet.univ
    rw [Set.eqOn_univ, funext_iff]
    intro ω
    rw [pow_sum_castSucc_eq_sum_add_pow]
    rfl


set_option maxHeartbeats 0 in
theorem k_moment_sum_recursive
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ}
  (X : Fin n.succ → Ω → ℝ)
  (k : ℕ)
  (hXIntegrable : (i : Fin n.succ) → Integrable (X i) μ)
  (hXIndep : iIndepFun X μ)
  -- (hXIdent : (i : Fin n.succ) → (j : Fin n.succ) → IdentDistrib (X i) (X j) μ μ)
  : moment (isum_rv X) k μ
    = ∑ ki : Fin k.succ, moment (X |> ifun_drop_last |> isum_rv) ki.toNat μ
      * moment (n |> Fin.last |> X) (k - ki) μ * (k.choose ki).cast
  := by
    rw [k_moment_sum_expand]
    simp only [Nat.succ_eq_add_one, Fin.toNat_eq_val, Finset.sum_apply,
      Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply]
    rw [integral_finset_sum]
    case hf =>
      intro i _
      rw [integrable_mul_const_iff]
      case hc =>
        rw [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero, <- ne_eq]
        apply Nat.choose_ne_zero
        rw [@Nat.le_iff_lt_add_one]
        exact i.is_lt
      sorry
    sorry




      -- rw [Integrable.const_mul]

      -- have h : Integrable (X |> ifun_drop_last |> isum_rv) ^ ki.toNat * (n |> Fin.last |> X) ^ (k - ki) * k.choose ki μ := sorry
      -- rw [Nat.add_one]
      -- rw [integral_mul_const_of_integrable]
      -- rw [hXIndep]
