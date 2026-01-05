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

private theorem MemLp.integrable_pow
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
private theorem k_moment_sum_recursive
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {P : Measure Ω} [IsFiniteMeasure P]
  {n k : ℕ}
  (X : Fin (n + 1) → Ω → ℝ)
  (hX : ∀ i, MemLp (X i) k P)
  (hXIndep : iIndepFun X P)
  : moment (∑ i, X i) k P
    = ∑ l ∈ range (k + 1),
    (k.choose l)
    * moment (X (Fin.last n)) (k - l) P
    * moment (∑ i : Fin n, X i.castSucc) l P
  := by
  have key
    (l : ℕ)
    : (fun ω => X (Fin.last n) ω ^ (k - l)) ⟂ᵢ[P] fun ω => (∑ i : Fin n, X i.castSucc ω) ^ l
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
    · convert (
        aestronglyMeasurable_sum (Finset.univ)
        (fun (i : Fin n) _ ↦ (hX i.castSucc).aestronglyMeasurable)
      ).pow l
      simp only [Pi.pow_apply, sum_apply]
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

-- https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/stuck.20on.20proof.20for.20iIndepFun.20on.20subset.20of.20indices/near/564583898
private lemma iIndepFun_succ
  {Ω : Type u_1} [MeasurableSpace Ω]
  {P : Measure Ω}
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  (hXIndep : iIndepFun X P)
  : iIndepFun (fun i : Fin n => X i.castSucc) P
  := by
  exact iIndepFun.precomp (f := X) (Fin.castSucc_injective n) hXIndep

private lemma moment_eq_if_identdistrib
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

private theorem zero_moment_eq_one
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {P : Measure Ω} [mP : IsProbabilityMeasure P]
  (X : Ω → ℝ)
  : moment X 0 P = 1
  := by
  unfold moment
  simp only [pow_zero, Pi.one_apply, integral_const, measureReal_univ_eq_one, smul_eq_mul, mul_one]

set_option linter.unusedVariables false in
theorem _0_moment_sum
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  (hX : ∀ i, MemLp (X i) 0 P)
  (hXIndep : iIndepFun X P)
  -- (hXIdent : (i : Fin n.succ) → (j : Fin n.succ) → IdentDistrib (X i) (X j) μ)
  : moment (∑ i, X i) 0 P
    = 1
  := by
    unfold moment
    simp only [pow_zero, Pi.one_apply, integral_const, measureReal_univ_eq_one, smul_eq_mul,
      mul_one]

theorem _1_moment_sum
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {P : Measure Ω} [mP : IsProbabilityMeasure P]
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  (hX : ∀ i, MemLp (X i) 1 P)
  (hXIndep : iIndepFun X P)
  (hXIdent : (i : Fin (n + 1)) → (j : Fin (n + 1)) → IdentDistrib (X i) (X j) P P)
  : moment (∑ i, X i) 1 P
    = (n + 1) * moment (X (Fin.last n)) 1 P
  := by
  induction n
  case zero =>
    simp only [Nat.reduceAdd, univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton,
      CharP.cast_eq_zero, zero_add, Fin.last_zero, one_mul]
  case succ n hn =>
    simp only [Nat.cast_add, Nat.cast_one]
    rewrite [k_moment_sum_recursive X ?hX hXIndep]
    case hX =>
      intro i
      apply MemLp.mono_exponent (hX i)
      simp only [Nat.cast_one, le_refl]
    simp only [Nat.reduceAdd]
    rewrite [Finset.sum_range, Fin.sum_univ_castSucc]
    simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, Fin.coe_castSucc, Fin.val_eq_zero,
      Nat.choose_succ_self_right, zero_add, Nat.cast_one, tsub_zero, one_mul, sum_const,
      card_singleton, one_smul, Fin.reduceLast, Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.choose_self,
      tsub_self]

    rewrite [_0_moment_sum]
    case hX =>
      intro i
      apply MemLp.mono_exponent (hX i.castSucc)
      simp only [zero_le]
    case hXIndep => exact iIndepFun_succ hXIndep

    rewrite [zero_moment_eq_one, mul_one, one_mul]
    rewrite [add_one_mul, hn, add_comm, add_left_inj, mul_eq_mul_left_iff]
    constructor
    case h =>
      apply moment_eq_if_identdistrib
      exact hXIdent (Fin.last n).castSucc (Fin.last (n + 1))
    case hX =>
      intro i
      exact hX i.castSucc
    case hXIdent =>
      intro i j
      exact hXIdent i.castSucc j.castSucc
    case hXIndep => exact iIndepFun_succ hXIndep

theorem _2_moment_sum
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {P : Measure Ω} [mP : IsProbabilityMeasure P]
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  (hX : ∀ i, MemLp (X i) 2 P)
  (hXIndep : iIndepFun X P)
  (hXIdent : (i j : Fin (n + 1)) → IdentDistrib (X i) (X j) P P)
  : moment (∑ i, X i) 2 P
    = (n + 1) * moment (X (Fin.last n)) 2 P
    + (n + 1) * n * moment (X (Fin.last n)) 1 P ^ 2
  := by
  induction n
  case zero =>
    simp only [Nat.reduceAdd, univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton,
      CharP.cast_eq_zero, zero_add, Fin.last_zero, one_mul, mul_zero, zero_mul, add_zero]
  case succ n hn =>
    have hn2 := by
      apply hn
      case hX =>
        intro i
        exact hX i.castSucc
      case hXIndep => exact iIndepFun_succ hXIndep
      case hXIdent =>
        intro i j
        exact hXIdent i.castSucc j.castSucc
    rewrite [k_moment_sum_recursive X ?hX hXIndep]
    case hX =>
      intro i
      apply MemLp.mono_exponent (hX i)
      simp only [Nat.cast_ofNat, le_refl]
    rewrite [Finset.sum_range, Fin.sum_univ_castSucc]
    simp only [Nat.reduceAdd, Fin.coe_castSucc, Fin.sum_univ_two, Fin.isValue, Fin.coe_ofNat_eq_mod,
      Nat.zero_mod, Nat.choose_zero_right, Nat.cast_one, tsub_zero, one_mul, Nat.mod_succ,
      Nat.choose_succ_self_right, Nat.cast_ofNat, Nat.add_one_sub_one, Fin.reduceLast,
      Nat.choose_self, tsub_self, Nat.cast_add]
    rewrite [hn2, _1_moment_sum, _0_moment_sum]
    case hX =>
      intro i
      apply MemLp.mono_exponent (hX i.castSucc)
      simp only [zero_le]
    case hXIndep => exact iIndepFun_succ hXIndep
    case hX =>
      intro i
      apply MemLp.mono_exponent (hX i.castSucc)
      simp only [Nat.one_le_ofNat]
    case hXIndep => exact iIndepFun_succ hXIndep
    case hXIdent =>
      intro i j
      exact hXIdent i.castSucc j.castSucc

    rewrite [zero_moment_eq_one, mul_one, one_mul]
    rewrite [moment_eq_if_identdistrib (hXIdent (Fin.last n).castSucc (Fin.last (n + 1)))]
    rewrite [moment_eq_if_identdistrib (hXIdent (Fin.last n).castSucc (Fin.last (n + 1)))]
    linarith

theorem _3_moment_sum
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {P : Measure Ω} [mP : IsProbabilityMeasure P]
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  (hX : ∀ i, MemLp (X i) 3 P)
  (hXIndep : iIndepFun X P)
  (hXIdent : (i j : Fin (n + 1)) → IdentDistrib (X i) (X j) P P)
  : moment (∑ i, X i) 3 P
    = 1 * (n + 1) * moment (X (Fin.last n)) 3 P
    + 3 * (n + 1) * n * (moment (X (Fin.last n)) 2 P) * (moment (X (Fin.last n)) 1 P)
    + 1 * (n + 1) * n * (n - 1) * (moment (X (Fin.last n)) 1 P ^ 3)
  := by
  induction n
  case zero =>
    simp only [Nat.reduceAdd, univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton,
      CharP.cast_eq_zero, zero_add, Fin.last_zero, one_mul, mul_one, mul_zero, zero_mul, add_zero,
      zero_sub, mul_neg, neg_zero]
  case succ n hn =>
    have hn2 := by
      apply hn
      case hX =>
        intro i
        exact hX i.castSucc
      case hXIndep => exact iIndepFun_succ hXIndep
      case hXIdent =>
        intro i j
        exact hXIdent i.castSucc j.castSucc
    rewrite [k_moment_sum_recursive X ?hX hXIndep]
    case hX =>
      intro i
      apply MemLp.mono_exponent (hX i)
      simp only [Nat.cast_ofNat, le_refl]
    rewrite [Finset.sum_range, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, Nat.reduceAdd, Fin.coe_castSucc,
      Fin.val_eq_zero, Nat.choose_zero_right, Nat.cast_one, tsub_zero, one_mul, sum_const,
      card_singleton, one_smul, Fin.reduceLast, Fin.castSucc_one, Fin.coe_ofNat_eq_mod, Nat.one_mod,
      Nat.choose_one_right, Nat.cast_ofNat, Nat.add_one_sub_one, Fin.reduceCastSucc, Nat.reduceMod,
      Nat.choose_succ_self_right, Nat.reduceSub, Nat.mod_succ, Nat.choose_self, tsub_self,
      Nat.cast_add, add_sub_cancel_right]

    rewrite [hn2, _2_moment_sum, _1_moment_sum, _0_moment_sum]
    case hX =>
      intro i
      apply MemLp.mono_exponent (hX i.castSucc)
      simp only [zero_le]
    case hXIndep => exact iIndepFun_succ hXIndep
    case hXIdent =>
      intro i j
      exact hXIdent i.castSucc j.castSucc
    case hX =>
      intro i
      apply MemLp.mono_exponent (hX i.castSucc)
      simp only [Nat.one_le_ofNat]
    case hXIndep => exact iIndepFun_succ hXIndep
    case hX =>
      intro i
      apply MemLp.mono_exponent (hX i.castSucc)
      rw [Nat.ofNat_le]
      simp only [Nat.reduceLeDiff]
    case hXIndep => exact iIndepFun_succ hXIndep
    case hXIdent =>
      intro i j
      exact hXIdent i.castSucc j.castSucc

    rewrite [zero_moment_eq_one, mul_one, one_mul]
    rewrite [moment_eq_if_identdistrib (hXIdent (Fin.last n).castSucc (Fin.last (n + 1)))]
    rewrite [moment_eq_if_identdistrib (hXIdent (Fin.last n).castSucc (Fin.last (n + 1)))]
    rewrite [moment_eq_if_identdistrib (hXIdent (Fin.last n).castSucc (Fin.last (n + 1)))]
    linarith

theorem _4_moment_sum
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {P : Measure Ω} [mP : IsProbabilityMeasure P]
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  (hX : ∀ i, MemLp (X i) 4 P)
  (hXIndep : iIndepFun X P)
  (hXIdent : (i j : Fin (n + 1)) → IdentDistrib (X i) (X j) P P)
  : moment (∑ i, X i) 4 P
    = 1 * (n + 1) * moment (X (Fin.last n)) 4 P
    + 3 * (n + 1) * n * (moment (X (Fin.last n)) 2 P) ^ 2
    + 4 * (n + 1) * n * (moment (X (Fin.last n)) 3 P) * (moment (X (Fin.last n)) 1 P)
    + 6 * (n + 1) * n * (n - 1) * (moment (X (Fin.last n)) 2 P) * (moment (X (Fin.last n)) 1 P) ^ 2
    + 1 * (n + 1) * n * (n - 1) * (n - 2) * (moment (X (Fin.last n)) 1 P ^ 4)
  := by
  induction n
  case zero =>
    simp only [Nat.reduceAdd, univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton,
      CharP.cast_eq_zero, zero_add, mul_one, Fin.last_zero, one_mul, mul_zero, zero_mul, add_zero,
      zero_sub, mul_neg, neg_zero]
  case succ n hn =>
    have hn2 := by
      apply hn
      case hX =>
        intro i
        exact hX i.castSucc
      case hXIndep => exact iIndepFun_succ hXIndep
      case hXIdent =>
        intro i j
        exact hXIdent i.castSucc j.castSucc

    rewrite [k_moment_sum_recursive X ?hX hXIndep]
    case hX =>
      intro i
      apply MemLp.mono_exponent (hX i)
      simp only [Nat.cast_ofNat, le_refl]
    rewrite [Finset.sum_range, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc,
      Fin.sum_univ_castSucc]
    simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, Nat.reduceAdd, Fin.coe_castSucc,
      Fin.val_eq_zero, Nat.choose_zero_right, Nat.cast_one, tsub_zero, one_mul, sum_const,
      card_singleton, one_smul, Fin.reduceLast, Fin.castSucc_one, Fin.coe_ofNat_eq_mod, Nat.one_mod,
      Nat.choose_one_right, Nat.cast_ofNat, Nat.add_one_sub_one, Fin.reduceCastSucc, Nat.reduceMod,
      Nat.reduceSub, Nat.choose_succ_self_right, Nat.mod_succ, Nat.choose_self, tsub_self,
      Nat.cast_add, add_sub_cancel_right]

    rewrite [hn2, _3_moment_sum, _2_moment_sum, _1_moment_sum, _0_moment_sum]
    case hX =>
      intro i
      apply MemLp.mono_exponent (hX i.castSucc)
      simp only [zero_le]
    case hXIndep => exact iIndepFun_succ hXIndep
    case hXIdent =>
      intro i j
      exact hXIdent i.castSucc j.castSucc
    case hX =>
      intro i
      apply MemLp.mono_exponent (hX i.castSucc)
      simp only [Nat.one_le_ofNat]
    case hXIndep => exact iIndepFun_succ hXIndep
    case hXIdent =>
      intro i j
      exact hXIdent i.castSucc j.castSucc
    case hX =>
      intro i
      apply MemLp.mono_exponent (hX i.castSucc)
      rw [Nat.ofNat_le]
      simp only [Nat.reduceLeDiff]
    case hXIndep => exact iIndepFun_succ hXIndep
    case hX =>
      intro i
      apply MemLp.mono_exponent (hX i.castSucc)
      rw [Nat.ofNat_le]
      simp only [Nat.reduceLeDiff]
    case hXIndep => exact iIndepFun_succ hXIndep
    case hXIdent =>
      intro i j
      exact hXIdent i.castSucc j.castSucc

    rewrite [zero_moment_eq_one, mul_one, one_mul]
    rewrite [moment_eq_if_identdistrib (hXIdent (Fin.last n).castSucc (Fin.last (n + 1)))]
    rewrite [moment_eq_if_identdistrib (hXIdent (Fin.last n).castSucc (Fin.last (n + 1)))]
    rewrite [moment_eq_if_identdistrib (hXIdent (Fin.last n).castSucc (Fin.last (n + 1)))]
    rewrite [moment_eq_if_identdistrib (hXIdent (Fin.last n).castSucc (Fin.last (n + 1)))]
    unfold Nat.choose
    simp only [Nat.choose_one_right, Nat.reduceAdd, Nat.choose_succ_self_right, Nat.cast_ofNat,
      one_mul]

    linarith

private theorem expt_sum2_unique_mul_eq
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {P : Measure Ω} [mP : IsProbabilityMeasure P]
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  {f g : ℝ → ℝ}
  (hX : ∀ i, MemLp (X i) 4 P)
  (hXIndep : iIndepFun X P)
  (hXIdent : (i j : Fin (n + 1)) → IdentDistrib (X i) (X j) P P)
  : P[fun ω => ∑ i1 : Fin (n + 1), ∑ i2 ∈ univ.erase i1, f (X i1 ω) * g (X i2 ω)]
    = (n + 1) * (@Nat.cast ℝ Real.instNatCast n)
      * P[fun ω => f (X (Fin.last n) ω)]
      * P[fun ω => g (X (Fin.last n) ω)]
  := by sorry

theorem expt_sum_sq_mul_sq_sum
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {P : Measure Ω} [mP : IsProbabilityMeasure P]
  {n : ℕ}
  {X : Fin (n + 1) → Ω → ℝ}
  (hX : ∀ i, MemLp (X i) 4 P)
  (hXIndep : iIndepFun X P)
  (hXIdent : (i j : Fin (n + 1)) → IdentDistrib (X i) (X j) P P)
  : P[(∑ i, X i ^ 2) * (∑ i, X i) ^ 2]
    = P[∑ i, X i ^ 2 ^ 2]
    + P[∑ i1, ∑ i2 ∈ univ.erase i1, ∑ i3 ∈ (univ.erase i1).erase i2, X i1 * X i2 * X i3 ^ 2]
    + 2 * P[∑ i1, ∑ i2 ∈ univ.erase i1, X i1 * X i2 ^ 3]
  := by
    let X' := fun ω i => X i ω
    have hX' : X' = fun ω i => X i ω := by rfl
    calc
      P[(∑ i, X i ^ 2) * (∑ i, X i) ^ 2]
        = P[fun ω => (∑ i, X' ω i ^ 2) * (∑ i, X' ω i) ^ 2]
      := by
        simp only [hX', Pi.mul_apply, sum_apply, Pi.pow_apply]
      _ = P[fun ω =>
        (∑ i, X' ω i ^ 2) ^ 2
        + ∑ i1, ∑ i2 ∈ univ.erase i1, ∑ i3 ∈ (univ.erase i1).erase i2,
          X' ω i1 * X' ω i2 * X' ω i3 ^ 2
        + 2 * ∑ i1, ∑ i2 ∈ univ.erase i1, X' ω i1 * X' ω i2 ^ 3
      ]
      := by
        sorry
      _ = P[fun ω => (∑ i, X' ω i ^ 2) ^ 2]
        + P[fun ω => ∑ i1, ∑ i2 ∈ univ.erase i1, ∑ i3 ∈ (univ.erase i1).erase i2,
          X' ω i1 * X' ω i2 * X' ω i3 ^ 2]
        + (2 : ℝ) * P[fun ω => ∑ i1, ∑ i2 ∈ univ.erase i1, X' ω i1 * X' ω i2 ^ 3]
      := by
        sorry
      _ = P[(∑ i, X i ^ 2) ^ 2]
        + P[∑ i1, ∑ i2 ∈ univ.erase i1, ∑ i3 ∈ (univ.erase i1).erase i2, X i1 * X i2 * X i3 ^ 2]
        + 2 * P[∑ i1, ∑ i2 ∈ univ.erase i1, X i1 * X i2 ^ 3]
      := by
        simp?
        sorry
      _ = (n + 1) * moment (X (Fin.last n) ^ 2) 2 P
        + (n + 1) * n * moment (X (Fin.last n) ^ 2) 1 P ^ 2
        + (n + 1) * n * (n - 1) * moment (X (Fin.last n)) 2 P * moment (X (Fin.last n)) 1 P ^ 2
        + 2 * (n + 1) * n * moment (X (Fin.last n)) 3 P * moment (X (Fin.last n)) 1 P
      := by
        sorry
      _ = (n + 1) * moment (X (Fin.last n)) 4 P
        + (n + 1) * n * moment (X (Fin.last n)) 2 P ^ 2
        + (n + 1) * n * (n - 1) * moment (X (Fin.last n)) 2 P * moment (X (Fin.last n)) 1 P ^ 2
        + 2 * (n + 1) * n * moment (X (Fin.last n)) 3 P * moment (X (Fin.last n)) 1 P
      := by
        sorry

    sorry
