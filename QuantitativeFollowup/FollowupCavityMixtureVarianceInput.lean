module
public import QuantitativeFollowup.AnisotropicVarianceMapContinuity
public import QuantitativeFollowup.FollowupCavityFixedRowDefinitions

@[expose] public section

/-! Genuine continuity of the actual fixed-coupling finite Gaussian inputs
on a compact positive last-variance band. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper SpinGlass.Targets
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1200000
variable {n k : ℕ}

theorem continuous_cavityFiniteEnergyInput_positive_variance_band
    (D : AnisotropicSpinModel n) (i : Fin n) (s : RSBScheme k)
    (l r : ℝ) (hl : 0<l) (j : ℕ) :
    Continuous (fun b:Icc l r=>cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s j) :=by
  have hn:Continuous (fun b:Icc l r=>anisotropicNoiseMap (anisotropicReplaceVariance D i b)):=by
    apply continuous_iff_continuousAt.mpr
    intro b
    exact (continuousAt_anisotropicReplaceVariance_noiseMap D i b (hl.trans_le b.property.1)).comp
      continuous_subtype_val.continuousAt
  unfold cavityFiniteEnergyInput anisotropicSchemeInput
  simp only [anisotropicReplaceVariance_energyMap]
  exact (continuous_const (y := anisotropicEnergyMap D)).clm_comp
    ((continuous_const (y := Real.sqrt (s.q (k+2-j)-s.q (k+1-j)))).smul
      ((continuous_const (y := anisotropicFieldInjection n)).clm_comp hn))

@[simp] theorem anisotropicRootEnergyMap_replaceVariance_mixture (D : AnisotropicSpinModel n)
    (i : Fin n) (b : ℝ) :
    anisotropicRootEnergyMap (anisotropicReplaceVariance D i b)=anisotropicRootEnergyMap D :=by
  unfold anisotropicRootEnergyMap
  rw [anisotropicReplaceVariance_energyMap]

end QuantitativeFollowup
