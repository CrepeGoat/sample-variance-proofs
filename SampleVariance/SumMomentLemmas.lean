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

theorem integrable_sq_sum_sq
  (Ω : Type u_1) [MeasurableSpace Ω]
  (n : ℕ)
  (X : Fin (n + 1) → Ω → ℝ)
  (P : Measure Ω) [IsProbabilityMeasure P]
  (hX : ∀ (i : Fin (n + 1)), MemLp (X i) 4 P)
  : Integrable (fun x ↦ (∑ i, (fun i ↦ X i x ^ 2) i) ^ 2) P
  := by
  conv in (_ ^ 2) => rw [sum_sq_eq_sum_sum_mul]
  apply integrable_finset_sum; intro i hi
  apply integrable_finset_sum; intro j hj
  have hXSqMemLp2 : ∀ k, MemLp (fun a ↦ X k a ^ 2) 2 P := by
    intro k
    conv in (X _ _ ^ 2) => rw [<- sq_abs, <- Real.norm_eq_abs]
    rw [memLp_two_iff_integrable_sq ?h1]
    case h1 =>
      rw [<- memLp_zero_iff_aestronglyMeasurable]
      have hXMemLp0 : MemLp (X k) 0 P := by
        apply MemLp.mono_exponent (hX k)
        simp only [zero_le]
      have hXMemLpNormSq := MemLp.norm_rpow_div (hXMemLp0) (q := 2)
      rw [ENNReal.zero_div, ENNReal.toReal_ofNat] at hXMemLpNormSq
      simp_all only [Real.rpow_ofNat]
    conv in ((_ ^ 2) ^ 2) => rw [<- pow_mul]
    simp only [Nat.reduceMul]
    apply MemLp.integrable_norm_pow ?h1 ?h3
    case h1 =>
      simp only [Nat.cast_ofNat]
      exact hX k
    case h3 => simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  apply MemLp.integrable_mul (p := 2) (q := 2) (hXSqMemLp2 i) (hXSqMemLp2 j)

theorem aestronglyMeasurable_mul
  {α : Type u_1} [m₀ : MeasurableSpace α]
  {μ : Measure α}
  {M : Type u_5} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
  {f g : α → M}
  (hf : AEStronglyMeasurable f μ)
  (hg : AEStronglyMeasurable g μ)
  : AEStronglyMeasurable (f * g) μ
  := by
    -- rw [<- one_mul (a := X j1), <- prod_eq_one (s := {}) (f := X) (by simp?)]
    -- conv in (∅) => rw [erase_eq_empty_iff]
  sorry

theorem memLp_pow
  (Ω : Type u_1) [MeasurableSpace Ω]
  (n m : ℕ)
  (f : Ω → ℝ)
  (P : Measure Ω) [IsProbabilityMeasure P]
  (hFMemLp : MemLp f ((2 * m) * n) P)
  : MemLp (f ^ (2 * m)) n P
  := by
  have hFFun : f ^ (2 * m) = fun ω => f ω ^ (2 * m) := by rfl
  conv in (f ^ (2 * m)) => rw [hFFun]
  conv in (_ ^ (2 * m)) => rw [pow_mul, <- sq_abs, <- Real.norm_eq_abs, <- pow_mul]
  have h1 :=  MemLp.norm_rpow_div (f := f) (q := (2 * m)) (hFMemLp)
  have h2 : ∀ x : ℝ, x ^ (@OfNat.ofNat ℝ 2 instOfNatAtLeastTwo * ↑m) = x ^ (2 * m) := by
    sorry
  conv at h1 in (_ ^ (2 * _).toReal) =>
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast, h2]
  conv at h1 in (_ / _) => rw [mul_comm, <- mul_div]
  -- conv at h1 in (_ / _) => rw [mul_div_mul_comm]
  sorry
  -- rw [ENNReal.toReal_ofNat] at h1
  -- conv at h1 in (4 / 2) => rw []
  -- simp_all? -- only [Real.rpow_ofNat]
      -- have hXFun : X i ^ 2 = fun ω => X i ω ^ 2 := by rfl
      -- conv in (X i ^ 2) => rw [hXFun]
      -- conv in (_ ^ 2) => rw [<- sq_abs, <- Real.norm_eq_abs]
      -- have hMemLp2 : MemLp (X i) 2 P := by
      --   apply MemLp.mono_exponent (hX i)
      --   rw [Nat.ofNat_le, @Nat.add_one_le_add_one_iff, @Nat.add_one_le_add_one_iff]
      --   apply zero_le
      -- have h1 :=  MemLp.norm_rpow_div (f := X i) (p := 4) (q := 2) (hX i)
      -- rw [ENNReal.toReal_ofNat] at h1
      -- conv at h1 in (4 / 2) => rw []
      -- simp_all? -- only [Real.rpow_ofNat]
