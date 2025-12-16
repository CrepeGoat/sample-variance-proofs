-- import Mathlib

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin

open Finset BigOperators
open MeasureTheory ProbabilityTheory NNReal
open scoped ENNReal


-- working proof of the first set of equations w/o expectations
theorem pow_sum_castSucc_eq_sum_add_pow
  {R : Type u_1} [CommSemiring R]
  {n : ℕ}
  {f : Fin (n.succ) → R}
  {k : ℕ}
  : (∑ i : Fin n.succ, f i) ^ k
    = ∑ j : Fin k.succ, (∑ i : Fin n, f i.castSucc) ^ j.toNat
    * (f (Fin.last n)) ^ (k - j) * k.choose j
  := by
  rw [Fin.sum_univ_castSucc, add_pow, Finset.sum_range, Nat.succ_eq_add_one]
  rfl

def ifun_drop_last
  {R : Type u_1}
  {n : ℕ}
  (f : (Fin n.succ) → R)
  : (Fin n) → R
  := by
  intro j
  apply f
  apply Fin.castLT j
  apply lt_trans (Fin.is_lt j) (n |> Fin.last |> Fin.is_lt)


noncomputable def isum_rv
  {R : Type u_1} [NormedAddCommGroup R] [NormedSpace ℝ R] [CommSemiring R] -- [MeasurableSpace R]
  {Ω : Type u_2} [MeasurableSpace Ω]
  {n : ℕ}
  (X : (Fin n) → Ω → R)
  : (Ω → R) := fun (ω : Ω) => (∑ i : Fin n, X i ω)


-- working proof of expanding the first equations in the expectation
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


-- unfinished proof of the desired final expression
theorem k_moment_sum_recursive
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ}
  (X : Fin n.succ → Ω → ℝ)
  (k : ℕ)
  -- do I need v-this?
  -- (hXIntegrable : Integrable ((isum_rv X) ^ k) μ)
  (hXIndep : iIndepFun X μ)
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
