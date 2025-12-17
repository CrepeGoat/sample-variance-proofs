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

theorem MemLp.integrable_pow
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {f : Ω → ℝ}
  {k : ℕ}
  (h : MemLp f k P)
  : Integrable (fun x => f x ^ k) P
  := by
  obtain rfl | hk := eq_or_ne k 0
  · simp only [pow_zero, enorm_one, ne_eq, ENNReal.one_ne_top, not_false_eq_true,
    integrable_const_enorm]
  rw [← integrable_norm_iff]
  · simpa [← memLp_one_iff_integrable] using h.norm_rpow (by norm_cast) (by simp)
  exact h.aestronglyMeasurable.pow k

-- https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/stuck.20on.20a.20proof.20on.20probability.20expectations/near/564137993
theorem k_moment_sum_recursive
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {P : Measure Ω} [IsFiniteMeasure P]
  {n : ℕ}
  (X : Fin n.succ → Ω → ℝ)
  (k : ℕ)
  (hX : ∀ i, MemLp (X i) k P)
  (hXIndep : iIndepFun X P)
  : moment (∑ i, X i) k P
    = ∑ l ∈ range (k + 1),
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
      apply hXIndep.indepFun_finset_sum_of_notMem₀
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
