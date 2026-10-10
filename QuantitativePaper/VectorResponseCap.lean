module
public import QuantitativePaper.VectorResponseTestData
public import Paper.HJBVerification

@[expose] public section

/-! Genuine time localization of a weighted vector response below its
variance-zero boundary. The cap supplies a globally regular time test while
preserving the exact backward equation on the physical prefix. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 1000000
variable {n : ℕ}

def vectorResponseCapVariance (c Q b r : ℝ) : ℝ :=
  c*(Q-Paper.hjbTimeCap b ((Q-b)/2) r)

def vectorCappedResponse (f g : Field n → ℝ) (m c Q b r : ℝ) (x : Field n) : ℝ :=
  vectorStepResponse (vectorResponseCapVariance c Q b r) m f g x

def vectorCappedResponseTimeField (f g : Field n → ℝ) (m c Q b r : ℝ) (x : Field n) : ℝ :=
  -c*Paper.hjbTimeCapD b ((Q-b)/2) r*vectorLinearBackwardGenerator
    (vectorStepResponse (vectorResponseCapVariance c Q b r) m f g)
    (vectorColeHopfStep (vectorResponseCapVariance c Q b r) m f) m x

theorem vectorResponseCapVariance_pos {c Q b : ℝ} (hc : 0<c) (hb : b<Q) (r : ℝ) :
    0 < vectorResponseCapVariance c Q b r := by
  have hh := Paper.hjbTimeCap_lt b (show 0<(Q-b)/2 by linarith) r
  exact mul_pos hc (by linarith)

theorem vectorResponseCapVariance_of_le (c Q b r : ℝ) (hr : r≤b) :
    vectorResponseCapVariance c Q b r=c*(Q-r) := by
  simp only [vectorResponseCapVariance,Paper.hjbTimeCap_of_le b ((Q-b)/2) r hr]

theorem hasDerivAt_vectorResponseCapVariance {c Q b : ℝ} (hb : b<Q) (r : ℝ) :
    HasDerivAt (vectorResponseCapVariance c Q b)
      (-c*Paper.hjbTimeCapD b ((Q-b)/2) r) r := by
  have hd := ((Paper.hasDerivAt_hjbTimeCap b (show 0<(Q-b)/2 by linarith) r).const_sub Q).const_mul c
  convert hd using 1
  · rfl
  · ring

theorem hasDerivAt_vectorCappedResponse {f g : Field n → ℝ}
    (d : VectorResponseTestData f g) (m : ℝ) {c Q b : ℝ}
    (hc : 0<c) (hb : b<Q) (r : ℝ) (x : Field n) :
    HasDerivAt (fun s=>vectorCappedResponse f g m c Q b s x)
      (vectorCappedResponseTimeField f g m c Q b r x) r := by
  have hd := (hasDerivAt_vectorStepResponse_variance f g m (d.weightedDatum m) (d.expDatum m)
    (vectorResponseCapVariance_pos hc hb r) x).comp r (hasDerivAt_vectorResponseCapVariance hb r)
  convert hd using 1
  · rfl
  · unfold vectorCappedResponseTimeField vectorLinearBackwardGenerator
    ring

theorem VectorResponseTestData.continuous_cappedResponse {f g : Field n → ℝ}
    (d : VectorResponseTestData f g) (m c Q b : ℝ) :
    Continuous (fun p : ℝ×Field n=>vectorCappedResponse f g m c Q b p.1 p.2) := by
  have hg (x : Field n) : |g x| ≤ d.observableBounds 0 := by
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using d.observableJets 0 (by omega) x
  exact (continuous_vectorStepResponse_variance_field f g d.fieldLip d.lipschitz
    d.observableRegularity.continuous (d.observableBounds 0) hg m).comp
      (show Continuous (fun p : ℝ×Field n=>(vectorResponseCapVariance c Q b p.1,p.2)) from by
        unfold vectorResponseCapVariance
        fun_prop)

theorem VectorResponseTestData.continuous_cappedResponseTimeField {f g : Field n → ℝ}
    (d : VectorResponseTestData f g) (m c Q b : ℝ) :
    Continuous (fun p : ℝ×Field n=>vectorCappedResponseTimeField f g m c Q b p.1 p.2) := by
  have hg := (d.continuous_generator m).comp
    (show Continuous (fun p : ℝ×Field n=>(vectorResponseCapVariance c Q b p.1,p.2)) from by
      unfold vectorResponseCapVariance
      fun_prop)
  exact (continuous_const.mul ((Paper.continuous_hjbTimeCapD b ((Q-b)/2)).comp continuous_fst)).mul hg

theorem vectorCappedResponseTimeField_of_le (f g : Field n → ℝ) (m c Q b r : ℝ)
    (hr : r≤b) (x : Field n) :
    vectorCappedResponseTimeField f g m c Q b r x=
      -c*vectorLinearBackwardGenerator (vectorStepResponse (c*(Q-r)) m f g)
        (vectorColeHopfStep (c*(Q-r)) m f) m x := by
  simp only [vectorCappedResponseTimeField,vectorResponseCapVariance_of_le c Q b r hr,
    Paper.hjbTimeCapD,ite_eq_left hr,mul_one]

end QuantitativePaper
