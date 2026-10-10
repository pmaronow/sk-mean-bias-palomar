module
public import FourPapersCommon.WienerExponential
public import QuantitativePaper.VectorTerminal
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

@[expose] public section

/-! Genuine finite observations of a canonical continuous Wiener path.
Repeated, unordered and zero observation times are retained. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal ENNReal BigOperators
namespace HexagonPaper
open Paper FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {M : ℕ}

def pathHeatWienerClockSet (c : Fin M → Paper.Overlap) : Finset Paper.Overlap :=
  Finset.univ.image c

def pathHeatWienerClockSelector (c : Fin M → Paper.Overlap) :
    (pathHeatWienerClockSet c → ℝ) →L[ℝ] Field M :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin M => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin M => ContinuousLinearMap.proj
      ⟨c i,Finset.mem_image.2 ⟨i,Finset.mem_univ i,rfl⟩⟩)

def pathHeatWienerClockSample (c : Fin M → Paper.Overlap) (p : WienerPath) : Field M :=
  WithLp.toLp 2 (fun i => p (c i))

theorem measurable_pathHeatWienerClockSample (c : Fin M → Paper.Overlap) :
    Measurable (pathHeatWienerClockSample c) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin M => ℝ)).symm.toContinuousLinearMap.measurable.comp
  exact Measurable.of_eval (fun i => _root_.ContinuousMap.measurable_eval (c i))

theorem pathHeatWienerClock_hasGaussianLaw (c : Fin M → Paper.Overlap) :
    HasGaussianLaw (pathHeatWienerClockSample c) canonicalWienerMeasure := by
  let I := pathHeatWienerClockSet c
  let e := fun p : WienerPath => I.restrict (fun t => p t)
  have hm : Measurable e := measurable_wiener_finite_evaluations I
  have hG : IsGaussian (canonicalWienerMeasure.map e) := isGaussian_wiener_finite_evaluations I
  have hObs : HasGaussianLaw e canonicalWienerMeasure := IsGaussian.hasGaussianLaw hm.aemeasurable
  have hSel := hObs.map (pathHeatWienerClockSelector c)
  convert hSel using 1
  funext p
  ext i
  rfl

theorem hasLaw_pathHeatWiener_eval (t : Paper.Overlap) :
    HasLaw (fun p : WienerPath => p t) (gaussianReal 0 t.1.toNNReal) canonicalWienerMeasure := by
  refine ⟨(_root_.ContinuousMap.measurable_eval t).aemeasurable,?_⟩
  rw [canonicalWienerMeasure,Measure.map_map
    (_root_.ContinuousMap.measurable_eval t) measurable_canonicalBrownianPath]
  exact isBrownianReal_canonicalBrownian.toIsPreBrownianReal.hasLaw_eval t.1.toNNReal |>.map_eq

theorem integral_pathHeatWiener_eval (t : Paper.Overlap) :
    (∫ p : WienerPath, p t ∂canonicalWienerMeasure) = 0 := by
  rw [(hasLaw_pathHeatWiener_eval t).integral_eq,integral_id_gaussianReal]

theorem covariance_pathHeatWiener_eval (s t : Paper.Overlap) :
    covariance (fun p : WienerPath => p s) (fun p : WienerPath => p t)
      canonicalWienerMeasure = min (s : ℝ) (t : ℝ) := by
  rw [canonicalWienerMeasure,covariance_map_fun
    (_root_.ContinuousMap.measurable_eval s).aestronglyMeasurable
    (_root_.ContinuousMap.measurable_eval t).aestronglyMeasurable
    measurable_canonicalBrownianPath.aemeasurable]
  change covariance (canonicalBrownian s.1.toNNReal) (canonicalBrownian t.1.toNNReal)
    canonicalBrownianMeasure = _
  rw [isBrownianReal_canonicalBrownian.toIsPreBrownianReal.covariance_eval]
  simp only [NNReal.coe_min,Real.coe_toNNReal _ s.property.1,Real.coe_toNNReal _ t.property.1]

end HexagonPaper
