module
public import QuantitativePaper.VectorWeightedControlRepresentation
public import QuantitativePaper.VectorConvexity
public import Paper.JTVariational

@[expose] public section

/-! The literal control state and cost are affine under probability mixing.
Consequently each actual fixed control has a convex payoff. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem integrableOn_vectorControlDrift (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (hA : IsVectorParisiControl A)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    IntegrableOn (fun s => vectorControlDrift c μ A s sample) (Ioc 0 r)
      nonnegativeLebesgueMeasure := by
  apply (integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 r)
    (C := |c| * Real.sqrt (n : ℝ))).mono'
    (measurable_vectorControlDrift c μ A hA).of_uncurry_right.aestronglyMeasurable
  exact Eventually.of_forall (fun s => norm_vectorControlDrift_le c μ A hA s sample)

theorem vectorControlDrift_mix (c : ℝ) (μ ν : Paper.ParisiMeasure) (lam : ℝ)
    (hlam : lam ∈ Icc (0 : ℝ) 1)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) :
    vectorControlDrift c (Paper.parisiMix μ ν lam) A r sample =
      (1-lam) • vectorControlDrift c μ A r sample +
        lam • vectorControlDrift c ν A r sample := by
  unfold vectorControlDrift
  rw [Paper.parisiCDF_mix μ ν lam r hlam]
  module

theorem vectorControlledState_mix (c : ℝ) (μ ν : Paper.ParisiMeasure) (lam : ℝ)
    (hlam : lam ∈ Icc (0 : ℝ) 1)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (hA : IsVectorParisiControl A)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    vectorControlledState c (Paper.parisiMix μ ν lam) A r sample =
      (1-lam) • vectorControlledState c μ A r sample +
        lam • vectorControlledState c ν A r sample := by
  have hμ := integrableOn_vectorControlDrift c μ A hA r sample
  have hν := integrableOn_vectorControlDrift c ν A hA r sample
  unfold vectorControlledState vectorIntegratedDrift
  simp_rw [vectorControlDrift_mix c μ ν lam hlam A]
  have he := integral_add (hμ.smul (1-lam)) (hν.smul lam)
  simp only [Pi.smul_apply] at he
  rw [he,integral_smul,integral_smul]
  module

theorem vectorParisiControlCost_mix (c : ℝ) (μ ν : Paper.ParisiMeasure) (lam : ℝ)
    (hlam : lam ∈ Icc (0 : ℝ) 1)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) :
    vectorParisiControlCost c (Paper.parisiMix μ ν lam) A r sample =
      (1-lam) * vectorParisiControlCost c μ A r sample +
        lam * vectorParisiControlCost c ν A r sample := by
  unfold vectorParisiControlCost
  rw [Paper.parisiCDF_mix μ ν lam r hlam]
  ring

theorem vectorParisiControlIntegratedCost_mix (c : ℝ) (μ ν : Paper.ParisiMeasure) (lam : ℝ)
    (hlam : lam ∈ Icc (0 : ℝ) 1)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (hA : IsVectorParisiControl A)
    (sample : VectorDisorderBrownianSample n) :
    vectorParisiControlIntegratedCost c (Paper.parisiMix μ ν lam) A sample =
      (1-lam) * vectorParisiControlIntegratedCost c μ A sample +
        lam * vectorParisiControlIntegratedCost c ν A sample := by
  unfold vectorParisiControlIntegratedCost
  simp_rw [vectorParisiControlCost_mix c μ ν lam hlam A]
  rw [integral_add ((integrableOn_vectorParisiControlCost c μ A hA sample).const_mul (1-lam))
    ((integrableOn_vectorParisiControlCost c ν A hA sample).const_mul lam),
    integral_const_mul,integral_const_mul]

theorem vectorTerminalPotential_convex_mix (β t : ℝ) (p : Couplings n × ℝ)
    (x y : Field n) (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1) :
    vectorTerminalPotential n β t p ((1-lam) • x + lam • y) ≤
      (1-lam)*vectorTerminalPotential n β t p x + lam*vectorTerminalPotential n β t p y := by
  have hh := (convexOn_vectorRecursion_joint (Paper.parisiGridRSBScheme
    (Paper.diracOverlap 0 (by simp)) 0) β t 0).2
    (mem_univ ((p,x) : VectorParameter n)) (mem_univ ((p,y) : VectorParameter n))
    (sub_nonneg.mpr hlam.2) hlam.1 (by ring : (1-lam)+lam=1)
  have he : ((1-lam) • p + lam • p : Couplings n × ℝ) = p := by module
  change vectorTerminalPotential n β t ((1-lam) • p + lam • p)
      ((1-lam) • x + lam • y) ≤
    (1-lam)*vectorTerminalPotential n β t p x + lam*vectorTerminalPotential n β t p y at hh
  rwa [he] at hh

theorem vectorParisiControlPayoff_mix_le (μ ν : Paper.ParisiMeasure) (β t lam : ℝ)
    (hlam : lam ∈ Icc (0 : ℝ) 1)
    (A : ℝ≥0 → VectorDisorderBrownianSample n → Field n) (hA : IsVectorParisiControl A)
    (sample : VectorDisorderBrownianSample n) :
    vectorTerminalPotential n β t sample.1
        (vectorControlledState ((1-t)*β^2) (Paper.parisiMix μ ν lam) A 1 sample) -
      vectorParisiControlIntegratedCost ((1-t)*β^2) (Paper.parisiMix μ ν lam) A sample ≤
      (1-lam)*(vectorTerminalPotential n β t sample.1
        (vectorControlledState ((1-t)*β^2) μ A 1 sample) -
          vectorParisiControlIntegratedCost ((1-t)*β^2) μ A sample) +
      lam*(vectorTerminalPotential n β t sample.1
        (vectorControlledState ((1-t)*β^2) ν A 1 sample) -
          vectorParisiControlIntegratedCost ((1-t)*β^2) ν A sample) := by
  rw [vectorControlledState_mix _ μ ν lam hlam A hA,
    vectorParisiControlIntegratedCost_mix _ μ ν lam hlam A hA]
  have hh := vectorTerminalPotential_convex_mix β t sample.1
    (vectorControlledState ((1-t)*β^2) μ A 1 sample)
    (vectorControlledState ((1-t)*β^2) ν A 1 sample) lam hlam
  linarith

end QuantitativePaper
