module
public import QuantitativeFollowup.FollowupCavityGeneratedForestFirstStreaming

@[expose] public section

/-! Replacing one terminal component leaves the complete joint test intact.
The averaging measure is the actual independent forest probability; its
unused replaced coordinate integrates to one. These identities do not
factor the joint test or bound its configuration-basis coefficients. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ} {I : Type*} [Fintype I]
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityGeneratedForestPartialTerminalTest
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ) (c : I)
    (σ : CavityGeneratedForestTerminalSample (n := n) J T)
    (τ : TerminalSpins (Configuration (n+1)) (T c)) : ℝ := by
  classical
  exact F (Function.update σ c τ)

def cavityGeneratedForestAveragedPartialTerminalTest
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap)
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ) (c : I)
    (τ : TerminalSpins (Configuration (n+1)) (T c)) : ℝ :=
  ∫σ, cavityGeneratedForestPartialTerminalTest J T F c σ τ
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _)

theorem abs_cavityGeneratedForestPartialTerminalTest_le
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ)
    (C : ℝ) (hF : ∀σ, |F σ| ≤ C) (c : I)
    (σ : CavityGeneratedForestTerminalSample (n := n) J T)
    (τ : TerminalSpins (Configuration (n+1)) (T c)) :
    |cavityGeneratedForestPartialTerminalTest J T F c σ τ| ≤ C := by
  classical
  exact hF (Function.update σ c τ)

theorem abs_cavityGeneratedForestAveragedPartialTerminalTest_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap)
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ)
    (C : ℝ) (hF : ∀σ, |F σ| ≤ C) (c : I)
    (τ : TerminalSpins (Configuration (n+1)) (T c)) :
    |cavityGeneratedForestAveragedPartialTerminalTest D μ a J T q F c τ| ≤ C := by
  simpa only [cavityGeneratedForestAveragedPartialTerminalTest, Real.norm_eq_abs,
    probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const
      (μ := (cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _))
      (f := fun σ => cavityGeneratedForestPartialTerminalTest J T F c σ τ)
      (C := C) (.of_forall fun σ => by
        simpa only [Real.norm_eq_abs] using
          abs_cavityGeneratedForestPartialTerminalTest_le J T F C hF c σ τ)

private theorem updated_singleton_product
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (σ y : CavityGeneratedForestTerminalSample (n := n) J T) (c : I)
    (τ : TerminalSpins (Configuration (n+1)) (T c)) :
    cavityGeneratedTerminalSingletonTest σ (Function.update y c τ) =
      ∏ d, if d=c then cavityGeneratedTerminalSingletonTest (σ c) τ
        else cavityGeneratedTerminalSingletonTest (σ d) (y d) := by
  classical
  have hp : (∏ d, cavityGeneratedTerminalSingletonTest (σ d)
      ((Function.update y c τ) d)) =
      cavityGeneratedTerminalSingletonTest σ (Function.update y c τ) := by
    by_cases h : Function.update y c τ=σ
    · simp [cavityGeneratedTerminalSingletonTest, h]
    · have hd : ∃d, (Function.update y c τ) d ≠ σ d := by
        by_contra hh
        push_neg at hh
        exact h (funext hh)
      obtain ⟨d, hd⟩ := hd
      simp only [cavityGeneratedTerminalSingletonTest, if_neg h]
      exact Finset.prod_eq_zero (Finset.mem_univ d)
        (by simp only [cavityGeneratedTerminalSingletonTest, if_neg hd])
  rw [←hp]
  apply Finset.prod_congr rfl
  intro d _
  by_cases h : d=c
  · subst d
    simp
  · simp [h, Function.update_of_ne h]

theorem cavityGeneratedNativeForest_updated_singleton_integral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap)
    (σ : CavityGeneratedForestTerminalSample (n := n) J T) (c : I)
    (τ : TerminalSpins (Configuration (n+1)) (T c)) :
    (∫y, cavityGeneratedTerminalSingletonTest σ (Function.update y c τ)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _)) =
      cavityGeneratedTerminalSingletonTest (σ c) τ *
        ∏d∈Finset.univ.erase c, nativeStreamingOldTerminalExpectation D μ a (q d) (T d)
          (cavityGeneratedTerminalSingletonTest (σ d)) := by
  classical
  let f (d : I) (ξ : TerminalSpins (Configuration (n+1)) (T d)) :=
    if d=c then cavityGeneratedTerminalSingletonTest (σ c) τ
    else cavityGeneratedTerminalSingletonTest (σ d) ξ
  have hf (d : I) :
      (∫z, f d (finiteCascadeRecordTerminalSpins (T d) z.2)
        ∂anisotropicRecordedProfileTreeLaw D μ a (q d) (T d)) =
      if d=c then cavityGeneratedTerminalSingletonTest (σ c) τ
        else nativeStreamingOldTerminalExpectation D μ a (q d) (T d)
          (cavityGeneratedTerminalSingletonTest (σ d)) := by
    by_cases h : d=c
    · simp [f, h, integral_const, probReal_univ]
    · simp only [f, if_neg h, nativeStreamingOldTerminalExpectation]
  calc
    _ = ∫y, ∏d, f d (y d)
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _) :=
      integral_congr_ae (.of_forall fun y => updated_singleton_product J T σ y c τ)
    _ = ∏d, ∫z, f d (finiteCascadeRecordTerminalSpins (T d) z.2)
        ∂anisotropicRecordedProfileTreeLaw D μ a (q d) (T d) :=
      cavityGeneratedNativeForest_terminal_product_expectations D μ a J T q f
    _ = _ := by
      simp_rw [hf]
      rw [←Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
      simp only [if_pos rfl]
      congr 1
      apply Finset.prod_congr rfl
      intro d hd
      simp only [Finset.mem_erase] at hd
      exact if_neg hd.1

theorem cavityGeneratedForestAveragedPartialTerminalTest_eq_basis
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap)
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ) (c : I)
    (τ : TerminalSpins (Configuration (n+1)) (T c)) :
    cavityGeneratedForestAveragedPartialTerminalTest D μ a J T q F c τ =
      ∑σ : CavityGeneratedForestTerminalSample (n := n) J T,
        F σ * cavityGeneratedTerminalSingletonTest (σ c) τ *
        ∏d∈Finset.univ.erase c, nativeStreamingOldTerminalExpectation D μ a (q d) (T d)
          (cavityGeneratedTerminalSingletonTest (σ d)) := by
  classical
  let M : Measure (CavityGeneratedForestTerminalSample (n := n) J T) :=
    cavityGeneratedNativeForestTerminalProbability D μ a J T q
  have hi (σ : CavityGeneratedForestTerminalSample (n := n) J T) :
      Integrable (fun y => F σ * cavityGeneratedTerminalSingletonTest σ (Function.update y c τ)) M := by
    simpa only [integrableOn_univ] using
      (IntegrableOn.of_finite (μ := M)
        (f := fun y => F σ * cavityGeneratedTerminalSingletonTest σ (Function.update y c τ))
        (s := univ) Set.finite_univ)
  have hb (y : CavityGeneratedForestTerminalSample (n := n) J T) :
      cavityGeneratedForestPartialTerminalTest J T F c y τ =
        ∑σ : CavityGeneratedForestTerminalSample (n := n) J T,
          F σ * cavityGeneratedTerminalSingletonTest σ (Function.update y c τ) := by
    simp [cavityGeneratedForestPartialTerminalTest,cavityGeneratedTerminalSingletonTest,eq_comm]
  calc
    _ = ∫y, ∑σ : CavityGeneratedForestTerminalSample (n := n) J T,
        F σ * cavityGeneratedTerminalSingletonTest σ (Function.update y c τ) ∂M :=
      integral_congr_ae (.of_forall hb)
    _ = ∑σ : CavityGeneratedForestTerminalSample (n := n) J T,
        ∫y, F σ * cavityGeneratedTerminalSingletonTest σ (Function.update y c τ) ∂M :=
      integral_finsetSum _ (fun σ _ => hi σ)
    _ = _ := by
      simp_rw [integral_const_mul]
      apply Finset.sum_congr rfl
      intro σ _
      rw [show (∫y, cavityGeneratedTerminalSingletonTest σ (Function.update y c τ) ∂M) =
        cavityGeneratedTerminalSingletonTest (σ c) τ *
          ∏d∈Finset.univ.erase c,nativeStreamingOldTerminalExpectation D μ a (q d) (T d)
            (cavityGeneratedTerminalSingletonTest (σ d)) from
        cavityGeneratedNativeForest_updated_singleton_integral D μ a J T q σ c τ]
      ring

theorem cavityGeneratedNativeForest_partial_functional_integral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap)
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ) (c : I)
    (R : (TerminalSpins (Configuration (n+1)) (T c) → ℝ) → ℝ)
    (hR : ∀G, R G = ∑τ : TerminalSpins (Configuration (n+1)) (T c),
      G τ * R (cavityGeneratedTerminalSingletonTest τ)) :
    (∫y, R (cavityGeneratedForestPartialTerminalTest J T F c y)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _)) =
      R (cavityGeneratedForestAveragedPartialTerminalTest D μ a J T q F c) := by
  classical
  let M : Measure (CavityGeneratedForestTerminalSample (n := n) J T) :=
    cavityGeneratedNativeForestTerminalProbability D μ a J T q
  have hi (τ : TerminalSpins (Configuration (n+1)) (T c)) :
      Integrable (fun y => cavityGeneratedForestPartialTerminalTest J T F c y τ *
        R (cavityGeneratedTerminalSingletonTest τ)) M := by
    simpa only [integrableOn_univ] using
      (IntegrableOn.of_finite (μ := M)
        (f := fun y => cavityGeneratedForestPartialTerminalTest J T F c y τ *
          R (cavityGeneratedTerminalSingletonTest τ)) (s := univ) Set.finite_univ)
  calc
    _ = ∫y, ∑τ : TerminalSpins (Configuration (n+1)) (T c),
        cavityGeneratedForestPartialTerminalTest J T F c y τ *
          R (cavityGeneratedTerminalSingletonTest τ) ∂M :=
      integral_congr_ae (.of_forall fun y => hR _)
    _ = ∑τ : TerminalSpins (Configuration (n+1)) (T c),
        ∫y, cavityGeneratedForestPartialTerminalTest J T F c y τ *
          R (cavityGeneratedTerminalSingletonTest τ) ∂M :=
      integral_finsetSum _ (fun τ _ => hi τ)
    _ = ∑τ : TerminalSpins (Configuration (n+1)) (T c),
        cavityGeneratedForestAveragedPartialTerminalTest D μ a J T q F c τ *
          R (cavityGeneratedTerminalSingletonTest τ) := by
      simp_rw [integral_mul_const]
      rfl
    _ = _ := (hR _).symm

theorem cavityGeneratedNativeForest_partial_functional_basis
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap)
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ) (c : I)
    (R : (TerminalSpins (Configuration (n+1)) (T c) → ℝ) → ℝ)
    (hR : ∀G, R G = ∑τ : TerminalSpins (Configuration (n+1)) (T c),
      G τ * R (cavityGeneratedTerminalSingletonTest τ)) :
    (∫y, R (cavityGeneratedForestPartialTerminalTest J T F c y)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _)) =
      ∑σ : CavityGeneratedForestTerminalSample (n := n) J T,
        F σ * R (cavityGeneratedTerminalSingletonTest (σ c)) *
          ∏d∈Finset.univ.erase c, nativeStreamingOldTerminalExpectation D μ a (q d) (T d)
            (cavityGeneratedTerminalSingletonTest (σ d)) := by
  classical
  rw [cavityGeneratedNativeForest_partial_functional_integral D μ a J T q F c R hR, hR]
  simp_rw [cavityGeneratedForestAveragedPartialTerminalTest_eq_basis, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  calc
    _ = (F σ * ∏d∈Finset.univ.erase c,
          nativeStreamingOldTerminalExpectation D μ a (q d) (T d)
            (cavityGeneratedTerminalSingletonTest (σ d))) *
        ∑τ : TerminalSpins (Configuration (n+1)) (T c),
          cavityGeneratedTerminalSingletonTest (σ c) τ * R (cavityGeneratedTerminalSingletonTest τ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro τ _
      ring
    _ = _ := by
      simp only [cavityGeneratedTerminalSingletonTest, ite_mul, one_mul, zero_mul]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_pos]
      ring

end QuantitativeFollowup
