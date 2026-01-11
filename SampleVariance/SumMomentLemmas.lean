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
  {Ω : Type u_1} [MeasurableSpace Ω]
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P]
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

theorem integrable_sum_sq_mul_sq_sum
  {Ω : Type u_1} [MeasurableSpace Ω]
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P]
  (hX : ∀ (i : Fin (n + 1)), MemLp (X i) 4 P)
  : Integrable ((∑ i, X i ^ 2) * (∑ i, X i) ^ 2) P
  := by
  sorry

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
  (hm : m ≠ 0)
  : MemLp (f ^ (2 * m)) n P
  := by
  have hFFun : f ^ (2 * m) = fun ω => f ω ^ (2 * m) := by rfl
  conv in (f ^ (2 * m)) => rw [hFFun]
  conv in (_ ^ (2 * m)) => rw [pow_mul, <- sq_abs, <- Real.norm_eq_abs, <- pow_mul]
  -- https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/converting.20between.20reals.2C.20ENNReals.20and.20Nats/near/567358350
  convert MemLp.norm_rpow_div (f := f) (q := (2 * m)) (hFMemLp)
  · rw [← Real.rpow_natCast]
    congr
    norm_num
  · norm_cast
    rw [ENNReal.eq_div_iff]
    · norm_num
    · norm_num
      rw [<- ne_eq]
      exact hm
    · exact ENNReal.natCast_ne_top (2 * m)

theorem integrable_pow4_sum
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  {P : Measure Ω} [inst : IsProbabilityMeasure P]
  (hX : ∀ (i : Fin (n + 1)), MemLp (X i) 4 P)
  : Integrable (fun x ↦ (∑ i, (fun i ↦ X i x) i) ^ 4) P
  := by
  conv in (_ ^ 4) => rw [pow_succ', sum_mul]
  apply integrable_finset_sum; intro i1 hi1
  conv in (_ * _ ^ 3) => rw [pow_succ', sum_mul, mul_sum]
  conv => enter [1, a, 2, i]; rw [<- mul_assoc]
  apply integrable_finset_sum; intro i2 hi2
  conv in (_ * (_ ^ 2)) => rw [sq, sum_mul, mul_sum]
  apply integrable_finset_sum; intro i3 hi3
  conv in (_ * (_ * _)) => rw [<- mul_assoc, mul_sum]
  apply integrable_finset_sum; intro i4 hi4
  conv in (_ * _ * _ * _) => rw [mul_assoc (b := (X i3 a))]

  have hXMemLpSq : ∀ j : Fin (n + 1), MemLp (X j ^ 2) 2 P := by
    intro i
    conv in (_ ^ 2) => rw [<- mul_one (a := 2)]
    apply memLp_pow
    case hm => exact Nat.one_ne_zero
    simp only [Nat.cast_one, mul_one, Nat.cast_ofNat]
    conv in (_ * _) => simp [Nat.reduceMul]
    norm_num
    apply (hX i)
  have hXMemLpMul : ∀ (j1 j2 : Fin (n + 1)), MemLp (X j1 * X j2) 2 P := by
    intro j1 j2
    rw [memLp_two_iff_integrable_sq ?h1]
    case h1 =>
      have hXAEM : ∀ k, AEStronglyMeasurable (X k) P := by
        intro k
        rw [<- memLp_zero_iff_aestronglyMeasurable]
        apply MemLp.mono_exponent (hX k)
        simp only [zero_le]
      apply aestronglyMeasurable_mul (hXAEM j1) (hXAEM j2)
    conv => enter [1, x, 1]; rw [Pi.mul_apply]
    conv in (_ ^ 2) => rw [mul_pow]
    apply MemLp.integrable_mul (hXMemLpSq j1) (hXMemLpSq j2)
  apply MemLp.integrable_mul (hXMemLpMul i1 i2) (hXMemLpMul i3 i4)
