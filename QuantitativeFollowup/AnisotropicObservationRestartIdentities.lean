module
public import QuantitativeFollowup.AnisotropicRestartLevelContinuity
public import QuantitativePaper.VectorNoiseStateDriftCongruence

@[expose] public section

/-! Pathwise clock identities for actual anisotropic restarts. The fixed
disorder is retained and the auxiliary initial Gaussian parameter is unused. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem anisotropicExtendedRestartNoiseStatePath_canonical (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x : Field n) (sample : VectorDisorderBrownianSample n) (r : ℝ≥0) (hr : r≤1) :
    anisotropicExtendedRestartNoiseStatePath D μ g q x (vectorCanonicalBrownianPath sample.2) r=
      vectorAdditiveState (anisotropicRestartDriftData D μ g q) 1 x 1 r sample := by
  have he:=vectorNoiseStatePath_drift_congr
    (vectorTimeShiftDriftData (anisotropicWhitenedDriftData D μ g) (q:ℝ).toNNReal)
    (anisotropicRestartDriftData D μ g q) 1 1 0 sample.1 x (vectorCanonicalBrownianPath sample.2)
    (fun _ _ _=>rfl) r ⟨r.coe_nonneg,hr⟩
  exact he.trans (vectorNoiseStatePath_canonical _ 1 x 1 le_rfl sample r hr)

theorem anisotropicRestartNoiseStatePath_canonical_extended (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x : Field n) (sample : VectorDisorderBrownianSample n) (r : ℝ≥0)
    (hr : (r:ℝ)≤1-(q:ℝ)) :
    anisotropicRestartNoiseStatePath D μ q ((g,x),vectorCanonicalBrownianPath sample.2) r=
      vectorAdditiveState (anisotropicRestartDriftData D μ g q) 1 x 1 r sample := by
  rw [anisotropicRestartNoiseStatePath_eq_extended D μ g q x _ r ⟨r.coe_nonneg,hr⟩]
  exact anisotropicExtendedRestartNoiseStatePath_canonical D μ g q x sample r
    (by rw [←NNReal.coe_le_coe];simp only [NNReal.coe_one];linarith [q.property.1])

theorem anisotropicRestartNoiseStatePath_shift (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q r u : Paper.Overlap)
    (hu : (u:ℝ)=(r:ℝ)-(q:ℝ)) (p : Couplings n×ℝ) (x : Field n)
    (W : VectorWienerPath n) (v : ℝ≥0) (hv : (v:ℝ)≤1-(r:ℝ)) :
    vectorNoiseRestartStatePath (anisotropicRestartDriftData D μ g q) 1 u ((p,x),W) v=
      anisotropicRestartNoiseStatePath D μ r ((g,x),W) v := by
  have hqu : (q:ℝ).toNNReal+(u:ℝ).toNNReal=(r:ℝ).toNNReal := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add,Real.coe_toNNReal _ q.property.1,
      Real.coe_toNNReal _ u.property.1,Real.coe_toNNReal _ r.property.1]
    linarith
  have hHu : ((vectorRestartHorizon u:ℝ≥0):ℝ)=1-(u:ℝ) :=
    Real.coe_toNNReal _ (sub_nonneg.mpr u.property.2)
  have hHr : ((vectorRestartHorizon r:ℝ≥0):ℝ)=1-(r:ℝ) :=
    Real.coe_toNNReal _ (sub_nonneg.mpr r.property.2)
  have hH : vectorRestartHorizon r≤vectorRestartHorizon u := by
    rw [←NNReal.coe_le_coe,hHr,hHu]
    linarith [q.property.1]
  have hrestrict:=vectorNoiseStatePath_horizon_eq
    (vectorTimeShiftDriftData (anisotropicRestartDriftData D μ g q) (u:ℝ).toNNReal)
    1 (vectorRestartHorizon r) (vectorRestartHorizon u) hH ((p,x),W) v
    ⟨v.coe_nonneg,by simpa only [hHr] using hv⟩
  refine hrestrict.symm.trans ?_
  apply vectorNoiseStatePath_drift_congr _ _ 1 (vectorRestartHorizon r) p 0 x W ?_ v
    ⟨v.coe_nonneg,by simpa only [hHr] using hv⟩
  intro t _ y
  change (anisotropicWhitenedDriftData D μ g).drift
      ((q:ℝ).toNNReal+((u:ℝ).toNNReal+t)) 0 y=
    (anisotropicWhitenedDriftData D μ g).drift ((r:ℝ).toNNReal+t) 0 y
  rw [←add_assoc,hqu]

end QuantitativeFollowup
