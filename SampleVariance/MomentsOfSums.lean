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
  {P : Measure Ω} [IsProbabilityMeasure P]
  {n : ℕ}
  {X : Fin n → Ω → ℝ}
  -- (hX : (i : Fin n) → Measurable (X i))
  (hXIntegrable : (i : Fin n) → Integrable (X i) P)
  : (moment (isum_rv X) 1 P = ∑ i : Fin n, moment (X i) 1 P)
  := by
  unfold isum_rv
  unfold moment
  simp only [pow_one, Pi.pow_apply]
  rw [integral_finset_sum]
  intro i _
  exact hXIntegrable i

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Integration.html#ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral


theorem k_moment_sum_recursive
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {n : ℕ}
  (X : Fin n.succ → Ω → ℝ)
  (k : ℕ)
  -- (hXIdent : (i : Fin n.succ) → (j : Fin n.succ) → IdentDistrib (X i) (X j) P P)
  : moment (isum_rv X) k P
    = ∑ i : Fin k, k.choose i
    * moment (X (Fin.last n)) (k - i) P
    * ∑ j : Fin n, moment (isum_rv (ifun_first_n X j.castSucc)) i P
  := calc
    moment (isum_rv X) k P
      = P[(isum_rv X) ^ k]
      := by unfold isum_rv; rfl
    _ = P[(∑ ki : Fin k.succ, isum_rv (ifun_first_n X (Fin.last n)) + X (Fin.last n)) ^ k]
      := by
      unfold ifun_first_n
      unfold isum_rv
      simp
      rewrite [<- MeasureTheory.setIntegral_univ]
      nth_rewrite 2 [<- MeasureTheory.setIntegral_univ]
      apply setIntegral_congr_fun
      · exact MeasurableSet.univ
      rw [Set.eqOn_univ]
      rw [funext_iff]
      intro ω
      rw [Fin.sum_univ_castSucc]
      -- simp
      -- linarith
      sorry
    _ = P[∑ ki : Fin k.succ, (isum_rv (ifun_first_n X (Fin.last n))) ^ ki.toNat
      * (X (Fin.last n)) ^ (k - ki) * k.choose ki]
      := by
      unfold ifun_first_n
      rw [Fin.sum_univ_castSucc]
      simp

      -- rw?
      sorry
    -- _ = ∫ (x : Ω), (∑ i, X i x) ^ k ∂P
    _ = ∑ i : Fin k, k.choose i
      * moment (X (Fin.last n)) (k - i) P
      * ∑ j : Fin n, moment (isum_rv (ifun_first_n X j.castSucc)) i P
      := sorry
  -- := by
  -- unfold isum_rv
  -- simp only [Nat.succ_eq_add_one, Fin.toNat_eq_val, Fin.coe_castSucc]
  -- unfold moment
  -- simp [Pi.pow_apply]
  -- have h1 : ∫ (x : Ω), (∑ i, X i x) ^ k ∂P = ∫ (x : Ω), (∑ i, (fun j => X j x) i) ^ k ∂P := rfl
  -- rewrite [h1]
  -- -- rewrite [pow_sum_castSucc_eq_sum_add_pow]
  -- sorry
