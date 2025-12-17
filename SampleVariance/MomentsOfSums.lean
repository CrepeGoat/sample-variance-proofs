-- import Mathlib

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.Finset.Range

import SampleVariance.PowOfSums

-- https://leanprover-community.github.io/blog/posts/basic-probability-in-mathlib/
open Finset MeasureTheory ProbabilityTheory NNReal
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


variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {n k : ℕ} {X : Fin (n + 1) → Ω → ℝ}

theorem MemLp.integrable_pow
  {f : Ω → ℝ}
  (h : MemLp f k P)
  : Integrable (fun x => f x ^ k) P
  := by
  obtain rfl | hk := eq_or_ne k 0
  · simp only [pow_zero, enorm_one, ne_eq, ENNReal.one_ne_top, not_false_eq_true,
    integrable_const_enorm]
  rw [← integrable_norm_iff]
  · simpa [← memLp_one_iff_integrable] using h.norm_rpow (by norm_cast) (by simp)
  exact h.aestronglyMeasurable.pow k

example (hX : ∀ i, MemLp (X i) k P) (h : iIndepFun X P) :
    moment (∑ i, X i) k P =
    ∑ l ∈ range (k + 1),
      (k.choose l)
      * moment (X (Fin.last n)) (k - l) P
      * moment (∑ i : Fin n, X i.castSucc) l P
  := by
  have key (l : ℕ) : (fun ω => X (Fin.last n) ω ^ (k - l)) ⟂ᵢ[P] fun ω => (∑ i : Fin n, X i.castSucc ω) ^ l
    := by
    apply IndepFun.comp
    · symm
      have : (fun ω ↦ ∑ i : Fin n, X i.castSucc ω) = ∑ i ∈ Iio (Fin.last n), X i
        := by ext; simp only [Fin.Iio_last_eq_map, sum_apply, sum_map, Fin.coe_castSuccEmb]
      rw [this]
      apply h.indepFun_finset_sum_of_notMem₀
      · exact fun i ↦ (hX i).aemeasurable
      · simp only [Fin.Iio_last_eq_map, mem_map, mem_univ, Fin.coe_castSuccEmb,
        Fin.castSucc_ne_last, and_false, exists_false, not_false_eq_true]
    · exact measurable_id.pow_const (k - l)
    · exact measurable_id.pow_const l
  unfold moment
  simp only [Pi.pow_apply, sum_apply]
  simp_rw [Fin.sum_univ_castSucc, add_pow]
  rw [integral_finset_sum]
  · congr with l
    rw [mul_assoc, ← IndepFun.integral_mul_eq_mul_integral, ← integral_const_mul]
    · congr with ω
      simp only [Pi.mul_apply]
      ring
    · exact key l
    · exact (hX _).aestronglyMeasurable.pow (k - l)
    · convert (aestronglyMeasurable_sum (Finset.univ) (fun (i : Fin n) _ ↦ (hX i.castSucc).aestronglyMeasurable)).pow l
      simp
  · intro l hl
    apply Integrable.mul_const
    apply IndepFun.integrable_mul
    · exact (key l).symm
    · apply MemLp.integrable_pow
      apply memLp_finset_sum
      intro i _
      apply (hX i.castSucc).mono_exponent
      simp_all only [mem_range, mem_univ, Nat.cast_le]
      omega
    · apply MemLp.integrable_pow
      apply (hX _).mono_exponent
      simp_all only [mem_range, ENNReal.natCast_sub, tsub_le_iff_right, self_le_add_right]
