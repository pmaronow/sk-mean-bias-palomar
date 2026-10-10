module
public import QuantitativeFollowup.AnisotropicWhitenedIto
public import QuantitativeFollowup.AnisotropicWhitenedFiniteState
public import QuantitativePaper.VectorRestartState

@[expose] public section

/-! Honest whitened anisotropic diffusions restarted at a deterministic
physical time and arbitrary initial field. Both finite and arbitrary-profile
paths are constructed by the actual Picard solver on elapsed Wiener time. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000
variable {n k : ℕ}

def anisotropicRestartDriftData (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) : VectorAdditiveDriftData n :=
  vectorFixedRestartDriftData (anisotropicWhitenedDriftData D μ g) (q:ℝ).toNNReal 0

def anisotropicFiniteRestartDriftData (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) : VectorAdditiveDriftData n :=
  vectorFixedRestartDriftData (anisotropicWhitenedFiniteDriftData D s g) (q:ℝ).toNNReal 0

def anisotropicRestartState (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    ℝ≥0→VectorDisorderBrownianSample n→Field n :=
  vectorAdditiveState (anisotropicRestartDriftData D μ g q) 1 x (vectorRestartHorizon q)

def anisotropicFiniteRestartState (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    ℝ≥0→VectorDisorderBrownianSample n→Field n :=
  vectorAdditiveState (anisotropicFiniteRestartDriftData D s g q) 1 x (vectorRestartHorizon q)

theorem continuous_anisotropicRestartState (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r=>anisotropicRestartState D μ g q x r sample) :=
  continuous_vectorAdditiveState _ _ _ _ _

theorem continuous_anisotropicFiniteRestartState (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r=>anisotropicFiniteRestartState D s g q x r sample) :=
  continuous_vectorAdditiveState _ _ _ _ _

theorem measurable_uncurry_anisotropicRestartState (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    Measurable (Function.uncurry (anisotropicRestartState D μ g q x)) :=
  measurable_uncurry_vectorAdditiveState _ _ _ _

theorem measurable_uncurry_anisotropicFiniteRestartState (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    Measurable (Function.uncurry (anisotropicFiniteRestartState D s g q x)) :=
  measurable_uncurry_vectorAdditiveState _ _ _ _

theorem stronglyAdapted_anisotropicRestartState (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    StronglyAdapted (vectorBrownianFiltration n) (anisotropicRestartState D μ g q x) :=
  stronglyAdapted_vectorAdditiveState _ _ _ _

theorem stronglyAdapted_anisotropicFiniteRestartState (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    StronglyAdapted (vectorBrownianFiltration n) (anisotropicFiniteRestartState D s g q x) :=
  stronglyAdapted_vectorAdditiveState _ _ _ _

@[simp] theorem anisotropicRestartState_zero (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (sample : VectorDisorderBrownianSample n) :
    anisotropicRestartState D μ g q x 0 sample=x := vectorAdditiveState_zero _ _ _ _ _

@[simp] theorem anisotropicFiniteRestartState_zero (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) (sample : VectorDisorderBrownianSample n) :
    anisotropicFiniteRestartState D s g q x 0 sample=x := vectorAdditiveState_zero _ _ _ _ _

theorem vectorItoCharacteristics_anisotropicRestartState (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    VectorItoCharacteristics (anisotropicRestartState D μ g q x)
      (vectorAdditiveDrift (anisotropicRestartDriftData D μ g q) 1 x (vectorRestartHorizon q)) 1 :=
  vectorItoCharacteristics_vectorAdditiveState _ _ _ _

theorem vectorItoCharacteristics_anisotropicFiniteRestartState (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    VectorItoCharacteristics (anisotropicFiniteRestartState D s g q x)
      (vectorAdditiveDrift (anisotropicFiniteRestartDriftData D s g q) 1 x (vectorRestartHorizon q)) 1 :=
  vectorItoCharacteristics_vectorAdditiveState _ _ _ _

end QuantitativeFollowup
