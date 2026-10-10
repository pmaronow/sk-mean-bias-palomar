module
public import QuantitativeFollowup.AnisotropicWhitenedFiniteTransition
public import QuantitativePaper.VectorInterpolationKernelTransport
public import QuantitativePaper.VectorSharpMassBounds
public import FourPapersCommon.FiniteHistoryPrefix

@[expose] public section

/-! Exact affine transport of the actual whitened Gaussian diffusion kernel
 to the literal anisotropic parameter kernel. No physical covariance or
 kernel identification is supplied as a hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

def anisotropicWhitenedParameterMap (D : AnisotropicSpinModel n)
    (g : AnisotropicDisorder n) (p : VectorState n) : AnisotropicParameter n :=
  anisotropicDisorderInjection n g+anisotropicUnitInput D p.2

theorem measurable_anisotropicWhitenedParameterMap (D : AnisotropicSpinModel n)
    (g : AnisotropicDisorder n) : Measurable (anisotropicWhitenedParameterMap D g) := by
  unfold anisotropicWhitenedParameterMap
  fun_prop

theorem anisotropicWhitenedParameterMap_shift (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (i : ℕ) (hi : i ≤ k+1)
    (p : VectorState n) (z : Field n) :
    anisotropicWhitenedParameterMap D g (p.1,fieldShift (s.q (i+1)-s.q i) p.2 z)=
      anisotropicWhitenedParameterMap D g p+anisotropicSchemeInput D s (k+1-i) z := by
  have h1 : k+1-(k+1-i)=i := by omega
  have h2 : k+2-(k+1-i)=i+1 := by omega
  simp only [anisotropicWhitenedParameterMap,fieldShift,map_add,map_smul,
    anisotropicSchemeInput,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,h1,h2,
    anisotropicUnitInput]
  rw [add_assoc]

theorem anisotropicWhitenedFiniteKernel_parameter_map (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (i : ℕ) (hi : i ≤ k+1)
    (p : VectorState n) :
    (anisotropicWhitenedFiniteKernel D s g i p).map (anisotropicWhitenedParameterMap D g)=
      anisotropicFiniteTransition D s i (anisotropicWhitenedParameterMap D g p) := by
  have hmass : anisotropicSchemeMass s (k+1-i)=s.m i := by
    simp only [anisotropicSchemeMass,show k+1-(k+1-i)=i from by omega]
  rw [anisotropicWhitenedFiniteKernel,vectorStateKernel_eq_map_tilted _
      (measurable_anisotropicWhitenedFiniteJointPotential D s g _),
    Measure.map_map (measurable_anisotropicWhitenedParameterMap D g) (by unfold fieldShift;fun_prop),
    anisotropicFiniteTransition_law,hmass,fieldGaussian_eq_stdGaussian]
  have ht : (fun z : Field n=>s.m i*anisotropicWhitenedFinitePotential D s (k+1-i) g
      (fieldShift (s.q (i+1)-s.q i) p.2 z))=
      fun z=>s.m i*anisotropicFinitePotential D s (k+1-i)
        (anisotropicWhitenedParameterMap D g p+anisotropicSchemeInput D s (k+1-i) z) := by
    funext z
    congr 1
    exact congrArg (anisotropicFinitePotential D s (k+1-i))
      (anisotropicWhitenedParameterMap_shift D s g i hi p z)
  rw [ht]
  congr 1
  exact funext (anisotropicWhitenedParameterMap_shift D s g i hi p)

def anisotropicFinitePhysicalParameter (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    AnisotropicParameter n :=
  anisotropicWhitenedParameterMap D g (anisotropicWhitenedFiniteJointState D s g r sample)

theorem measurable_anisotropicFinitePhysicalParameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (r : ℝ≥0) :
    Measurable (anisotropicFinitePhysicalParameter D s g r) :=
  (measurable_anisotropicWhitenedParameterMap D g).comp
    (measurable_anisotropicWhitenedFiniteJointState D s g r)

theorem adapted_anisotropicFinitePhysicalParameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (r : ℝ≥0) :
    Measurable[vectorBrownianFiltration n r] (anisotropicFinitePhysicalParameter D s g r) := by
  have hX := (stronglyAdapted_vectorAdditiveState (anisotropicWhitenedFiniteDriftData D s g) 1 0 1 r).measurable
  have hp := (stronglyMeasurable_initialVectorDisorder n r).measurable.prodMk hX
  exact (measurable_anisotropicWhitenedParameterMap D g).comp hp

theorem anisotropicFinitePhysical_restricted_transition_law (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (i : ℕ) (hi : i ≤ k+1)
    (A : Set (VectorDisorderBrownianSample n))
    (hA : MeasurableSet[vectorBrownianFiltration n (s.q i).toNNReal] A) :
    ((vectorDisorderBrownianMeasure n).restrict A).map
      (anisotropicFinitePhysicalParameter D s g (s.q (i+1)).toNNReal)=
      (anisotropicFiniteTransition D s i) ∘ₘ
        ((vectorDisorderBrownianMeasure n).restrict A).map
          (anisotropicFinitePhysicalParameter D s g (s.q i).toNNReal) := by
  let Φ:=anisotropicWhitenedParameterMap D g
  have hΦ : Measurable Φ:=measurable_anisotropicWhitenedParameterMap D g
  have hker : (anisotropicWhitenedFiniteKernel D s g i).map Φ=
      (anisotropicFiniteTransition D s i).comap Φ hΦ := by
    ext p t ht
    rw [Kernel.map_apply _ hΦ,Kernel.comap_apply]
    exact congrArg (fun μ : Measure (AnisotropicParameter n)=>μ t)
      (anisotropicWhitenedFiniteKernel_parameter_map D s g i hi p)
  change ((vectorDisorderBrownianMeasure n).restrict A).map
    (Φ ∘ anisotropicWhitenedFiniteJointState D s g (s.q (i+1)).toNNReal)=_
  rw [←Measure.map_map hΦ (measurable_anisotropicWhitenedFiniteJointState D s g _),
    anisotropicWhitenedFinite_restricted_transition_law D s g i hi A hA,
    Measure.map_comp _ _ hΦ,hker]
  rw [show ((vectorDisorderBrownianMeasure n).restrict A).map
      (anisotropicFinitePhysicalParameter D s g (s.q i).toNNReal)=
      (((vectorDisorderBrownianMeasure n).restrict A).map
        (anisotropicWhitenedFiniteJointState D s g (s.q i).toNNReal)).map Φ from
      (Measure.map_map hΦ (measurable_anisotropicWhitenedFiniteJointState D s g _)).symm,
    ←Measure.deterministic_comp_eq_map hΦ,Measure.comp_assoc,Kernel.comp_deterministic_eq_comap _ hΦ]

end QuantitativeFollowup
