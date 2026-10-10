module
public import QuantitativeFollowup.FollowupCavityGeneratedForestProducts
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingActualSource
public import Mathlib.MeasureTheory.Integral.IntegrableOn

@[expose] public section

/-! An arbitrary joint terminal test has an exact finite configuration
basis under the actual independent forest law.  This is a linear identity
for the whole test, with no component factorization hypothesis. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ} {I : Type*} [Fintype I]
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityGeneratedTerminalSingletonTest {A : Type*} (σ τ : A) : ℝ := by
  classical
  exact if τ = σ then 1 else 0

private theorem product_singleton_tests_eq {A : I → Type*}
    (σ τ : (i : I) → A i) :
    (∏ i, cavityGeneratedTerminalSingletonTest (σ i) (τ i)) =
      if τ = σ then 1 else 0 := by
  classical
  by_cases he : τ = σ
  · subst τ
    simp [cavityGeneratedTerminalSingletonTest]
  · have hi : ∃ i, τ i ≠ σ i := by
      by_contra h
      push_neg at h
      exact he (funext h)
    obtain ⟨i, hi⟩ := hi
    rw [if_neg he]
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (by simp only [cavityGeneratedTerminalSingletonTest, if_neg hi])

theorem cavityGeneratedNativeForest_terminal_basis
    (D : AnisotropicSpinModel (n + 1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap)
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ) :
    (∫ σ, F σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _)) =
    ∑ σ : CavityGeneratedForestTerminalSample (n := n) J T,
      F σ * ∏ i, nativeStreamingOldTerminalExpectation D μ a (q i) (T i)
        (cavityGeneratedTerminalSingletonTest (σ i)) := by
  classical
  let M : Measure (CavityGeneratedForestTerminalSample (n := n) J T) :=
    cavityGeneratedNativeForestTerminalProbability D μ a J T q
  have hb (τ : CavityGeneratedForestTerminalSample (n := n) J T) :
      F τ = ∑ σ : CavityGeneratedForestTerminalSample (n := n) J T,
        F σ * ∏ i, cavityGeneratedTerminalSingletonTest (σ i) (τ i) := by
    simp_rw [product_singleton_tests_eq]
    simp [eq_comm]
  have hi (σ : CavityGeneratedForestTerminalSample (n := n) J T) :
      Integrable (fun τ => F σ * ∏ i, cavityGeneratedTerminalSingletonTest (σ i) (τ i)) M := by
    simpa only [integrableOn_univ] using
      (IntegrableOn.of_finite (μ := M) (f := fun τ => F σ *
        ∏ i, cavityGeneratedTerminalSingletonTest (σ i) (τ i)) (s := univ) Set.finite_univ)
  calc
    _ = ∫ τ, ∑ σ : CavityGeneratedForestTerminalSample (n := n) J T,
        F σ * ∏ i, cavityGeneratedTerminalSingletonTest (σ i) (τ i) ∂M :=
      integral_congr_ae (.of_forall hb)
    _ = ∑ σ : CavityGeneratedForestTerminalSample (n := n) J T,
        ∫ τ, F σ * ∏ i, cavityGeneratedTerminalSingletonTest (σ i) (τ i) ∂M :=
      integral_finsetSum _ (fun σ _ => hi σ)
    _ = _ := by
      simp_rw [integral_const_mul]
      apply Finset.sum_congr rfl
      intro σ _
      congr 1
      exact cavityGeneratedNativeForest_terminal_product_expectations D μ a J T q
        (fun i => cavityGeneratedTerminalSingletonTest (σ i))

def followupCavityGeneratedForestTerminalExpectation
    (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap)
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ) (u : ℝ) : ℝ :=
  if hu : u ∈ Icc (0 : ℝ) 1 then
    ∫ σ, F σ ∂(cavityGeneratedNativeForestTerminalProbability
      (followupCavitySpinModel n β ρ hβ hρ u hu) μ a J T q : Measure _)
  else 0

theorem followupCavityGeneratedForestTerminalExpectation_eq_basis
    (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i)) (q : I → ℕ → Paper.Overlap)
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    followupCavityGeneratedForestTerminalExpectation β ρ hβ hρ μ a J T q F u =
    ∑ σ : CavityGeneratedForestTerminalSample (n := n) J T,
      F σ * ∏ i, followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a (q i) (T i)
        (cavityGeneratedTerminalSingletonTest (σ i)) u := by
  classical
  simp only [followupCavityGeneratedForestTerminalExpectation, dif_pos hu]
  rw [cavityGeneratedNativeForest_terminal_basis]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact (followupCavityNativeTerminalExpectation_eq_old_terminal β ρ hβ hρ μ a
    (q i) (T i) (cavityGeneratedTerminalSingletonTest (σ i)) u hu).symm

end QuantitativeFollowup
