module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseScalar
public import QuantitativeFollowup.FollowupCavityCppZeroResponseExpectation
public import QuantitativeFollowup.AnisotropicBinaryFeatureFinite
public import QuantitativeFollowup.AnisotropicCovarianceMoments

@[expose] public section

/-! Genuine first and second terminal-row parameter responses at zero
incident coupling. The strict-future sum is the actual normalized scalar/rest
continuation, and keeps the original Stieltjes charges. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets OverlapPaper
variable {k : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityFiniteRowFeature_zero (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1) (j : ℕ)
    (i : Fin n) (P : AnisotropicParameter (n+1)) :
    anisotropicFiniteFeatureMean
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) s j
      (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) P =
      anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s j
        (fun σ => Paper.spinSign (σ i)) (cavityRestParameterProjection n P) *
      parisiFDeriv s (followupCavityScalarBeta n β ρ) j (P (Sum.inr (Fin.last n))) := by
  have he : (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n)) :
      QuantitativePaper.Configuration (n+1) → ℝ) = fun σ =>
      Paper.spinSign (cavityRestConfiguration σ i)*Paper.spinSign (σ (Fin.last n)) := by
    funext σ
    exact anisotropicOrderedCoupling_feature i.castSucc (Fin.last n) σ
  rw [he]
  exact cavityFiniteIncidentFeature_zero s n β ρ hβ hρ j
    (fun σ : QuantitativePaper.Configuration n => Paper.spinSign (σ i)) P

def cavityFiniteRowFutureRestSquare (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1) (p j : ℕ) (i : Fin n)
    (P : AnisotropicParameter n) : ℝ :=
  sourceKernelExpectation
    (fun r => anisotropicDepthKernel (followupCavityRestSpinModel n β ρ hβ hρ) s (p+r)) j
    (fun Q => (anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s p
      (fun σ => Paper.spinSign (σ i)) Q)^2) P

def cavityFiniteRowFutureScalarSquare (s : RSBScheme k) (β : ℝ) (p j : ℕ) (x : ℝ) : ℝ :=
  sourceKernelExpectation (fun r => cavityScalarDepthKernel s β (p+r)) j
    (fun y => (parisiFDeriv s β p y)^2) x

theorem cavityFiniteRowFutureSquare_zero (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1) (p j : ℕ)
    (i : Fin n) (P : AnisotropicParameter (n+1)) :
    sourceKernelExpectation
      (fun r => anisotropicDepthKernel (followupCavitySpinModel n β ρ hβ hρ 0
        ⟨le_rfl,zero_le_one⟩) s (p+r)) j
      (fun Q => (anisotropicFiniteFeatureMean (followupCavitySpinModel n β ρ hβ hρ 0
        ⟨le_rfl,zero_le_one⟩) s p
        (anisotropicPairFeature (anisotropicOrderedCoupling i.castSucc (Fin.last n))) Q)^2) P =
      cavityFiniteRowFutureRestSquare s n β ρ hβ hρ p j i (cavityRestParameterProjection n P) *
      cavityFiniteRowFutureScalarSquare s (followupCavityScalarBeta n β ρ) p j
        (P (Sum.inr (Fin.last n))) := by
  simp_rw [cavityFiniteRowFeature_zero,mul_pow]
  exact cavityDepthExpectation_zero_product s n β ρ hβ hρ p j _ _
    ((measurable_anisotropicFiniteFeatureMean _ s p _).pow_const 2)
    ((parisiF_C2_props s _ p).2.1.pow_const 2) P

theorem cavityFiniteRowSecond_zero (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1) (j : ℕ)
    (i : Fin n) (P : AnisotropicParameter (n+1)) :
    anisotropicFinitePairSecond (followupCavitySpinModel n β ρ hβ hρ 0
      ⟨le_rfl,zero_le_one⟩) s j P (anisotropicOrderedCoupling i.castSucc (Fin.last n)) =
    1-anisotropicSchemeMass s j*
      (anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s j
        (fun σ => Paper.spinSign (σ i)) (cavityRestParameterProjection n P) *
        parisiFDeriv s (followupCavityScalarBeta n β ρ) j (P (Sum.inr (Fin.last n))))^2-
    (∑p∈Finset.range j,(anisotropicSchemeMass s p-anisotropicSchemeMass s (p+1))*
      (cavityFiniteRowFutureRestSquare s n β ρ hβ hρ (p+1) (j-(p+1)) i
        (cavityRestParameterProjection n P) *
       cavityFiniteRowFutureScalarSquare s (followupCavityScalarBeta n β ρ) (p+1) (j-(p+1))
        (P (Sum.inr (Fin.last n))))) := by
  have h := anisotropicFinitePairSecond_future_decomposition
    (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) s j P
    (anisotropicOrderedCoupling i.castSucc (Fin.last n))
  simp_rw [cavityFiniteRowFutureSquare_zero,cavityFiniteRowFeature_zero] at h
  linarith

end QuantitativeFollowup
