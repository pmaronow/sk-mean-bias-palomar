module
public import QuantitativeFollowup.AnisotropicVarianceNativeResponse
public import QuantitativeFollowup.AnisotropicNodeY
public import QuantitativeFollowup.FollowupCavityParameters

@[expose] public section

/-! Literal arbitrary-node/full-profile nodeb response of the actual
anisotropic single-leaf cavity law. The future conditional square is the
genuine whole-past kernel of the terminal last-spin posterior. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
variable {n : ℕ}

theorem anisotropic_measure_node_b (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : Paper.Overlap) (i : Fin n) :
    ∀ᵐp ∂anisotropicMeasureSampleLaw D μ a,
      HasDerivAt (fun b=>anisotropicMeasureTailPotential (anisotropicReplaceVariance D i b) μ q
        (anisotropicProcessParameter D μ q p))
        ((1/2:ℝ)*(1-(q:ℝ)-∫r : Paper.Overlap,
          if q<r then ((r:ℝ)-(q:ℝ))*anisotropicPastSpinSquareKernel D μ a q r i p else 0
            ∂parisiFreeMeasure μ a)) (D.variance i) := by
  filter_upwards [hasDerivAt_anisotropicMeasureTailPotential_variance_native D μ a q i] with p hp
  rw [anisotropicNativeVarianceResponse_eq_free D μ a ha hμ q i p] at hp
  exact hp

theorem anisotropic_marked_variance_nodeb (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : Paper.Overlap) (i : Fin n) :
    ∀ᵐp : AnisotropicDisorderBrownianSample n×Configuration n ∂anisotropicMeasureSpinPathLaw D μ a,
      HasDerivAt (fun b=>anisotropicMeasureTailPotential (anisotropicReplaceVariance D i b) μ q
        (anisotropicProcessParameter D μ q p.1))
        ((1/2:ℝ)*(1-(q:ℝ)-∫r : Paper.Overlap,
          if q<r then ((r:ℝ)-(q:ℝ))*anisotropicPastSpinSquareKernel D μ a q r i p.1 else 0
            ∂parisiFreeMeasure μ a)) (D.variance i) :=
  (measurePreserving_anisotropicMeasureSpinPathLaw_fst D μ a).quasiMeasurePreserving.ae
    (anisotropic_measure_node_b D μ a ha hμ q i)

theorem anisotropic_cavity_last_field_nodeb (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : Paper.Overlap) :
    ∀ᵐp : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)
        ∂anisotropicMeasureSpinPathLaw D μ a,
      HasDerivAt (fun b=>anisotropicMeasureTailPotential (anisotropicReplaceVariance D (Fin.last n) b) μ q
        (anisotropicProcessParameter D μ q p.1))
        ((1/2:ℝ)*(1-(q:ℝ)-∫r : Paper.Overlap,
          if q<r then ((r:ℝ)-(q:ℝ))*anisotropicPastSpinSquareKernel D μ a q r (Fin.last n) p.1 else 0
            ∂parisiFreeMeasure μ a)) (D.variance (Fin.last n)) :=
  anisotropic_marked_variance_nodeb D μ a ha hμ q (Fin.last n)

theorem followup_cavity_node_b (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc 0 1) (u : ℝ) (hu : u∈Icc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : Paper.Overlap) :
    ∀ᵐp : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)
        ∂anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ u hu) μ a,
      HasDerivAt (fun b=>anisotropicMeasureTailPotential
        (anisotropicReplaceVariance (followupCavitySpinModel n β ρ hβ hρ u hu) (Fin.last n) b) μ q
          (anisotropicProcessParameter (followupCavitySpinModel n β ρ hβ hρ u hu) μ q p.1))
        ((1/2:ℝ)*(1-(q:ℝ)-∫r : Paper.Overlap,
          if q<r then ((r:ℝ)-(q:ℝ))*anisotropicPastSpinSquareKernel
            (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q r (Fin.last n) p.1 else 0
              ∂parisiFreeMeasure μ a)) (followupCavityB n β ρ u) := by
  simpa only [followupCavitySpinModel_variance_last] using
    anisotropic_cavity_last_field_nodeb (followupCavitySpinModel n β ρ hβ hρ u hu) μ a ha hμ q

end QuantitativeFollowup
