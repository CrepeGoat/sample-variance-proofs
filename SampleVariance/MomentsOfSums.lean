import Mathlib

-- https://leanprover-community.github.io/blog/posts/basic-probability-in-mathlib/
open MeasureTheory ProbabilityTheory NNReal
open scoped ENNReal


-- https://leanprover-community.githb.io/blog/posts/basic-probability-in-mathlib/#:~:text=Measure%20%CE%A9.-,Identically%20distributed,-IdentDistrib%20X%20Y
-- https://leanprover-community.github.io/blog/posts/basic-probability-in-mathlib/#:~:text=of%20the%20indicator).-,Independence,-Mathlib%20has%20several

noncomputable def sum_random_vars
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
  : (moment (sum_random_vars X) 1 P = ∑ i : Fin n, moment (X i) 1 P)
  := by
  unfold sum_random_vars
  unfold moment
  simp only [pow_one, Pi.pow_apply]
  rw [integral_finset_sum]
  intro i _
  exact hXIntegrable i
