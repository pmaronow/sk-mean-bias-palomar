module
public import QuantitativeFollowup.AnisotropicVarianceRestartKernels
public import QuantitativeFollowup.AnisotropicFiniteKernelTransport
public import FourPapersCommon.FiniteHistoryKernel

@[expose] public section

/-! The actual restarted anisotropic diffusion retains every chronological
coordinate and has the genuine clamped Gaussian continuation history law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper
open scoped NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

def anisotropicFiniteRestartPhysicalParameter (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : AnisotropicParameter n :=
  anisotropicWhitenedParameterMap D g (sample.1,anisotropicFiniteRestartState D s g q x r sample)

theorem adapted_anisotropicFiniteRestartPhysicalParameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (r : ℝ≥0) :
    Measurable[vectorBrownianFiltration n r] (anisotropicFiniteRestartPhysicalParameter D s g q x r) :=
  (measurable_anisotropicWhitenedParameterMap D g).comp
    ((stronglyMeasurable_initialVectorDisorder n r).measurable.prodMk
      (stronglyAdapted_anisotropicFiniteRestartState D s g q x r).measurable)

theorem measurable_anisotropicFiniteRestartPhysicalParameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (r : ℝ≥0) :
    Measurable (anisotropicFiniteRestartPhysicalParameter D s g q x r) :=
  (adapted_anisotropicFiniteRestartPhysicalParameter D s g q x r).mono
    ((vectorBrownianFiltration n).le _) le_rfl

def anisotropicFiniteRestartPhysicalKernel (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : Paper.Overlap) (i : ℕ) : Kernel (AnisotropicParameter n) (AnisotropicParameter n) :=
  anisotropicFiniteTransition D (vectorClampedScheme s q q.property) (i+1)

instance anisotropicFiniteRestartPhysicalKernel_markov (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : Paper.Overlap) (i : ℕ) :
    IsMarkovKernel (anisotropicFiniteRestartPhysicalKernel D s q i) := by
  unfold anisotropicFiniteRestartPhysicalKernel
  infer_instance

theorem anisotropicFiniteRestartPhysical_restricted_transition_law (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (i : ℕ) (hi : i≤k+1) (A : Set (VectorDisorderBrownianSample n))
    (hA : MeasurableSet[vectorBrownianFiltration n (anisotropicRestartElapsed s q i)] A) :
    ((vectorDisorderBrownianMeasure n).restrict A).map
      (anisotropicFiniteRestartPhysicalParameter D s g q x (anisotropicRestartElapsed s q (i+1)))=
      (anisotropicFiniteRestartPhysicalKernel D s q i) ∘ₘ
        ((vectorDisorderBrownianMeasure n).restrict A).map
          (anisotropicFiniteRestartPhysicalParameter D s g q x (anisotropicRestartElapsed s q i)) := by
  let Φ:=anisotropicWhitenedParameterMap D g
  have hΦ : Measurable Φ:=measurable_anisotropicWhitenedParameterMap D g
  have hker : (anisotropicFiniteRestartKernel D s g q i).map Φ=
      (anisotropicFiniteRestartPhysicalKernel D s q i).comap Φ hΦ := by
    ext p t ht
    rw [Kernel.map_apply _ hΦ,Kernel.comap_apply]
    exact congrArg (fun μ : Measure (AnisotropicParameter n)=>μ t)
      (anisotropicWhitenedFiniteKernel_parameter_map D (vectorClampedScheme s q q.property)
        g (i+1) (by omega) p)
  change ((vectorDisorderBrownianMeasure n).restrict A).map
    (Φ ∘ anisotropicFiniteRestartJointState D s g q x (i+1))=_
  rw [←Measure.map_map hΦ (measurable_anisotropicFiniteRestartJointState D s g q x _),
    anisotropicFiniteRestart_restricted_transition_law D s g q x i hi A hA,
    Measure.map_comp _ _ hΦ,hker]
  rw [show ((vectorDisorderBrownianMeasure n).restrict A).map
      (anisotropicFiniteRestartPhysicalParameter D s g q x (anisotropicRestartElapsed s q i))=
      (((vectorDisorderBrownianMeasure n).restrict A).map
        (anisotropicFiniteRestartJointState D s g q x i)).map Φ from
      (Measure.map_map hΦ (measurable_anisotropicFiniteRestartJointState D s g q x _)).symm,
    ←Measure.deterministic_comp_eq_map hΦ,Measure.comp_assoc,Kernel.comp_deterministic_eq_comap _ hΦ]

def anisotropicFiniteRestartPhysicalHistory (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (N : ℕ)
    (sample : VectorDisorderBrownianSample n) : FiniteHistory (AnisotropicParameter n) N :=
  historySample (anisotropicFiniteRestartPhysicalParameter D s g q x) (anisotropicRestartElapsed s q) N sample

theorem measurable_anisotropicFiniteRestartPhysicalHistory (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (N : ℕ) :
    Measurable (anisotropicFiniteRestartPhysicalHistory D s g q x N) := by
  apply Measurable.of_eval
  intro i
  exact measurable_anisotropicFiniteRestartPhysicalParameter D s g q x _

@[simp] theorem anisotropicFiniteRestartPhysicalParameter_zero (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (sample : VectorDisorderBrownianSample n) :
    anisotropicFiniteRestartPhysicalParameter D s g q x 0 sample=
      anisotropicDisorderInjection n g+anisotropicUnitInput D x := by
  simp only [anisotropicFiniteRestartPhysicalParameter,anisotropicFiniteRestartState_zero,
    anisotropicWhitenedParameterMap]

theorem anisotropicFiniteRestartPhysical_history_law (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (N : ℕ) (hN : N≤k+2) :
    (vectorDisorderBrownianMeasure n).map (anisotropicFiniteRestartPhysicalHistory D s g q x N)=
      finiteHistoryLaw (Measure.dirac (anisotropicDisorderInjection n g+anisotropicUnitInput D x))
        (anisotropicFiniteRestartPhysicalKernel D s q) N := by
  have he:=historySample_law_of_restricted_up_to
    (vectorDisorderBrownianMeasure n) (vectorBrownianFiltration n)
    (anisotropicFiniteRestartPhysicalParameter D s g q x)
    (adapted_anisotropicFiniteRestartPhysicalParameter D s g q x)
    (anisotropicRestartElapsed s q) (k+2)
    (fun i j hij hj=>Real.toNNReal_le_toNNReal (sub_le_sub_right
      (max_le_max_left (q:ℝ) (s.q_mono' j hj i hij)) _))
    (anisotropicFiniteRestartPhysicalKernel D s q) (fun _=>inferInstance)
    (fun i hi A hA=>anisotropicFiniteRestartPhysical_restricted_transition_law D s g q x i
      (by omega) A hA) N hN
  have hzero : anisotropicRestartElapsed s q 0=0 := by
    simp only [anisotropicRestartElapsed,s.q_zero,max_eq_left q.property.1,sub_self,Real.toNNReal_zero]
  have hinit : (vectorDisorderBrownianMeasure n).map
      (anisotropicFiniteRestartPhysicalParameter D s g q x 0)=
        Measure.dirac (anisotropicDisorderInjection n g+anisotropicUnitInput D x) := by
    rw [show anisotropicFiniteRestartPhysicalParameter D s g q x 0=
      (fun _=>anisotropicDisorderInjection n g+anisotropicUnitInput D x) from
      funext (anisotropicFiniteRestartPhysicalParameter_zero D s g q x)]
    simp
  rw [hzero,hinit] at he
  exact he

theorem anisotropicFiniteRestartPhysical_history_kernel (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (N : ℕ) (hN : N≤k+2) :
    (vectorDisorderBrownianMeasure n).map (anisotropicFiniteRestartPhysicalHistory D s g q x N)=
      finiteHistoryKernel (anisotropicFiniteRestartPhysicalKernel D s q) N
        (anisotropicDisorderInjection n g+anisotropicUnitInput D x) := by
  rw [anisotropicFiniteRestartPhysical_history_law D s g q x N hN,
    finiteHistoryKernel_apply _ (fun _=>inferInstance)]

end QuantitativeFollowup
