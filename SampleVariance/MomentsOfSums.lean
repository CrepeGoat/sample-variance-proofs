import Mathlib

-- https://leanprover-community.github.io/blog/posts/basic-probability-in-mathlib/
open MeasureTheory ProbabilityTheory NNReal
open scoped ENNReal


-- https://leanprover-community.githb.io/blog/posts/basic-probability-in-mathlib/#:~:text=Measure%20%CE%A9.-,Identically%20distributed,-IdentDistrib%20X%20Y
-- https://leanprover-community.github.io/blog/posts/basic-probability-in-mathlib/#:~:text=of%20the%20indicator).-,Independence,-Mathlib%20has%20several

noncomputable def moment_of_sum
  {R : Type u_1} [NormedAddCommGroup R] [NormedSpace ℝ R] [CommSemiring R] -- [MeasurableSpace R]
  {Ω : Type u_2} [MeasurableSpace Ω]
  (P : Measure Ω)
  {n : ℕ}
  (X : (Fin n) → Ω → R)
  -- (hX : (i : Fin n) → Measurable (X i))
  (k : ℕ)
  : R := P[fun (ω : Ω) => (∑' i : Fin n, X i ω) ^ k]


example
  {Ω : Type u_1} [m : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {P2 : Measure ℝ}
  {μ : ℝ}
  {σ : ℝ≥0}
  {X : Fin 3 → Ω → ℝ}
  (hX : (i : Fin 3) → Measurable (X i))
  (hX2 : (i : Fin 3) → AEStronglyMeasurable (X i) P)
  (h_indep : iIndepFun X P)
  : (moment_of_sum P X 1 = ∑' i : Fin 3, moment (X i) 1 P)
  := by
  unfold moment_of_sum
  unfold moment
  simp only [pow_one, Pi.pow_apply]
  rw [integral_tsum hX2]
  simp
  -- rw [pow_one]
  sorry
