import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.Finset.Range

import SampleVariance.PowOfSums

open Finset MeasureTheory ProbabilityTheory NNReal
open scoped ENNReal


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

-- https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/stuck.20on.20proof.20for.20iIndepFun.20on.20subset.20of.20indices/near/564583898
lemma iIndepFun_succ
  {Ω : Type u_1} [MeasurableSpace Ω]
  {P : Measure Ω}
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  (hXIndep : iIndepFun X P)
  : iIndepFun (fun i : Fin n => X i.castSucc) P
  := by
  exact iIndepFun.precomp (f := X) (Fin.castSucc_injective n) hXIndep

lemma moment_eq_if_identdistrib
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {P : Measure Ω} [IsFiniteMeasure P]
  {n k : ℕ}
  {i j : Fin n}
  {X : Fin (n) → Ω → ℝ}
  (hXIdent : IdentDistrib (X i) (X j) P P)
  : moment (X i) k P = moment (X j) k P
  := by
  have h := IdentDistrib.comp hXIdent (Measurable.pow_const measurable_id k)
  apply h.integral_eq

theorem zero_moment_eq_one
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {P : Measure Ω} [mP : IsProbabilityMeasure P]
  (X : Ω → ℝ)
  : moment X 0 P = 1
  := by
  unfold moment
  simp only [pow_zero, Pi.one_apply, integral_const, measureReal_univ_eq_one, smul_eq_mul, mul_one]
