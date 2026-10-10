module
public import QuantitativeFollowup.StandardSKOffDiagonalMarkedLaw
public import QuantitativeFollowup.AnisotropicRecordedFreshTerminalLaw
public import QuantitativePaper.VectorNoiseStatePathUniqueness

@[expose] public section

/-! Exact physical restart transport for the zero-diagonal SK model.
The Gaussian initial disorder is compressed; the entire fresh Wiener path
and arbitrary initial field are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem standardSKOffDiagonalNoiseMap (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (x : Field n) :
    anisotropicNoiseMap (standardSKOffDiagonalModel n β t hβ ht) x=
      Real.sqrt ((1-t)*β^2) • x := by
  ext i
  rfl

theorem standardSKOffDiagonalWhitenedDrift (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (g : AnisotropicDisorder n) (r : ℝ≥0)
    (p : Couplings n×ℝ) (y : Field n) :
    Real.sqrt ((1-t)*β^2) •
      (anisotropicWhitenedDriftData (standardSKOffDiagonalModel n β t hβ ht) μ g).drift r p y=
      (vectorMeasureDriftData μ β t ht.le).drift r
        (standardSKOffDiagonalCompression g) (Real.sqrt ((1-t)*β^2) • y) := by
  have hnn : 0≤(1-t)*β^2 := mul_nonneg (by linarith) (sq_nonneg β)
  dsimp only [anisotropicWhitenedDriftData,anisotropicWhitenedDrift]
  rw [anisotropicDisorderInjection_apply,←anisotropicParameterPoint_field,
    standardSKOffDiagonalNoiseMap,standardSKOffDiagonalMeasureMagnetization,
    standardSKOffDiagonalNoiseMap]
  change _=((1-t)*β^2*Paper.parisiCDF μ r) • _
  simp only [smul_smul]
  congr 1
  rw [show Real.sqrt ((1-t)*β^2)*(Paper.parisiCDF μ r*Real.sqrt ((1-t)*β^2))=
    (Real.sqrt ((1-t)*β^2)*Real.sqrt ((1-t)*β^2))*Paper.parisiCDF μ r by ring,
    Real.mul_self_sqrt hnn]

theorem standardSKOffDiagonalRestartNoiseState (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (q : Paper.Overlap)
    (g : AnisotropicDisorder n) (x : Field n) (W : VectorWienerPath n)
    (r : ℝ) (hr : r∈Icc (0:ℝ) (vectorRestartHorizon q)) :
    Real.sqrt ((1-t)*β^2) •
      anisotropicRestartNoiseStatePath (standardSKOffDiagonalModel n β t hβ ht) μ q ((g,x),W) r=
      vectorNoiseRestartStatePath (vectorMeasureDriftData μ β t ht.le)
        (Real.sqrt ((1-t)*β^2)) q
        ((standardSKOffDiagonalCompression g,Real.sqrt ((1-t)*β^2) • x),W) r := by
  let σ:=Real.sqrt ((1-t)*β^2)
  let D:=standardSKOffDiagonalModel n β t hβ ht
  let da:=vectorTimeShiftDriftData (anisotropicWhitenedDriftData D μ g) (q:ℝ).toNNReal
  let dv : VectorAdditiveDriftData n:=vectorTimeShiftDriftData (vectorMeasureDriftData μ β t ht.le) (q:ℝ).toNNReal
  let X : ℝ→Field n:=fun u=>σ • vectorNoiseStatePath da 1 (vectorRestartHorizon q) ((0,x),W) u
  have hX : Continuous X := (continuous_vectorNoiseStatePath da 1 _ _).const_smul σ
  have he (u : ℝ) (hu : u∈Icc (0:ℝ) (vectorRestartHorizon q)) :
      X u=σ • x+σ • vectorContinuousNoise W u+
        ∫v in 0..u,dv.drift v.toNNReal (standardSKOffDiagonalCompression g) (X v) := by
    have hh:=vectorNoiseStatePath_equation da 1 (vectorRestartHorizon q) ((0,x),W) u hu
    dsimp only [X]
    rw [hh,one_smul,smul_add,smul_add,←intervalIntegral.integral_smul]
    congr 1
    apply intervalIntegral.integral_congr
    intro v hv
    exact standardSKOffDiagonalWhitenedDrift μ β t hβ ht g
      ((q:ℝ).toNNReal+v.toNNReal) 0 _
  exact vectorNoiseStatePath_unique dv σ (vectorRestartHorizon q)
    ((standardSKOffDiagonalCompression g,σ • x),W) X hX he r hr

end QuantitativeFollowup
