module
public import QuantitativeFollowup.AnisotropicFiniteKernelTransport
public import FourPapersCommon.FiniteHistoryKernel

@[expose] public section

/-! The literal chronological history of the constructed anisotropic
 diffusion, for fixed physical disorder, equals the honest normalized
 finite Gaussian cascade history law. All past coordinates are retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper
open scoped NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def anisotropicFinitePhysicalHistory (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (j : ℕ) (sample : VectorDisorderBrownianSample n) :
    FiniteHistory (AnisotropicParameter n) j :=
  historySample (anisotropicFinitePhysicalParameter D s g) (fun i=>(s.q i).toNNReal) j sample

theorem measurable_anisotropicFinitePhysicalHistory (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (j : ℕ) :
    Measurable (anisotropicFinitePhysicalHistory D s g j) := by
  apply Measurable.of_eval
  intro i
  exact measurable_anisotropicFinitePhysicalParameter D s g (s.q i).toNNReal

@[simp] theorem anisotropicFinitePhysicalParameter_zero (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (sample : VectorDisorderBrownianSample n) :
    anisotropicFinitePhysicalParameter D s g 0 sample=anisotropicDisorderInjection n g := by
  simp [anisotropicFinitePhysicalParameter,anisotropicWhitenedParameterMap,
    anisotropicWhitenedFiniteJointState,anisotropicWhitenedFiniteState]

theorem anisotropicFinitePhysicalFixed_history_law (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (j : ℕ) (hj : j ≤ k+2) :
    (vectorDisorderBrownianMeasure n).map (anisotropicFinitePhysicalHistory D s g j)=
      finiteHistoryLaw (Measure.dirac (anisotropicDisorderInjection n g))
        (anisotropicFiniteTransition D s) j := by
  have he:=historySample_law_of_restricted_up_to
    (vectorDisorderBrownianMeasure n) (vectorBrownianFiltration n)
    (anisotropicFinitePhysicalParameter D s g) (adapted_anisotropicFinitePhysicalParameter D s g)
    (fun i=>(s.q i).toNNReal) (k+2)
    (fun i j hij hj=>Real.toNNReal_le_toNNReal (s.q_mono' j hj i hij))
    (anisotropicFiniteTransition D s) (fun _=>inferInstance)
    (fun i hi A hA=>anisotropicFinitePhysical_restricted_transition_law D s g i (by omega) A hA)
    j hj
  have h0 : (vectorDisorderBrownianMeasure n).map
      (anisotropicFinitePhysicalParameter D s g 0)=Measure.dirac (anisotropicDisorderInjection n g) := by
    simp only [show anisotropicFinitePhysicalParameter D s g 0=(fun _=>anisotropicDisorderInjection n g) from
      funext (anisotropicFinitePhysicalParameter_zero D s g),Measure.map_const,measure_univ,one_smul]
  change (vectorDisorderBrownianMeasure n).map
    (historySample (anisotropicFinitePhysicalParameter D s g) (fun i=>(s.q i).toNNReal) j)=_
  simpa only [s.q_zero,Real.toNNReal_zero,h0] using he

theorem anisotropicFinitePhysicalFixed_history_kernel (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (j : ℕ) (hj : j ≤ k+2) :
    (vectorDisorderBrownianMeasure n).map (anisotropicFinitePhysicalHistory D s g j)=
      finiteHistoryKernel (anisotropicFiniteTransition D s) j (anisotropicDisorderInjection n g) := by
  rw [anisotropicFinitePhysicalFixed_history_law D s g j hj,
    finiteHistoryKernel_apply _ (fun _=>inferInstance)]

end QuantitativeFollowup
