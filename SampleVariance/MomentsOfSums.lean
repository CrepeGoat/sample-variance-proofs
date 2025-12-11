import Mathlib

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


theorem k_moment_sum_recursive
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ}
  (X : Fin n.succ → Ω → ℝ)
  (k : ℕ)
  (hXIndep : iIndepFun X μ)
  -- (hXIdent : (i : Fin n.succ) → (j : Fin n.succ) → IdentDistrib (X i) (X j) μ μ)
  : moment (isum_rv X) k μ
    = ∑ ki : Fin k.succ, μ[(n |> Fin.last |> ifun_first_n X |> isum_rv) ^ ki.toNat]
      * μ[(n |> Fin.last |> X) ^ (k - ki)] * (k.choose ki).cast
  := calc
    moment (isum_rv X) k μ
      = μ[(isum_rv X) ^ k]
      := by rfl
    _ = μ[∑ ki : Fin k.succ, (n |> Fin.last |> ifun_first_n X |> isum_rv) ^ ki.toNat
      * (n |> Fin.last |> X) ^ (k - ki) * k.choose ki]
      := by
      unfold ifun_first_n isum_rv
      simp only [Nat.succ_eq_add_one, Pi.pow_apply, Fin.toNat_eq_val, Fin.val_last,
        Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply]
      rewrite [<- MeasureTheory.setIntegral_univ]
      nth_rewrite 2 [<- MeasureTheory.setIntegral_univ]
      apply setIntegral_congr_fun
      · exact MeasurableSet.univ
      rw [Set.eqOn_univ, funext_iff]
      intro ω
      rw [pow_sum_castSucc_eq_sum_add_pow]
      rfl
    _ = ∑ ki : Fin k.succ, μ[(n |> Fin.last |> ifun_first_n X |> isum_rv) ^ ki.toNat]
      * μ[(n |> Fin.last |> X) ^ (k - ki)] * (k.choose ki).cast
      := by
      simp only [Nat.succ_eq_add_one, Fin.toNat_eq_val, Fin.val_last, Finset.sum_apply,
        Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply]
      rw [hXIndep]
      sorry
