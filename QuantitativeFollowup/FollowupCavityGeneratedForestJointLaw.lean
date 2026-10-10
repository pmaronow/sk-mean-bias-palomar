module
public import QuantitativeFollowup.FollowupCavityGeneratedForestHistoryPrefactor
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-! The actual joint mark and terminal-spin law of a generated forest.
The terminal kernel is constructed from the native independent forest
probability. Its measurability is derived from genuine moving-clock
continuity, rather than supplied as a law hypothesis. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

theorem measurable_cavityGeneratedForestTerminalMeasure
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) :
    Measurable (fun h : CavityGeneratedHistory Paper.Overlap m=>
      (cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock h) : Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  let F : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree→ℝ :=
    E.indicator (fun _=>1)
  have hc : Continuous (fun h : CavityGeneratedHistory Paper.Overlap m=>
      ∫σ,F σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock h) : Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) :=
    continuous_integral_probability_family (fun z=>F z.2)
      ((continuous_of_discreteTopology (f:=F)).comp continuous_snd) _
      (continuous_cavityGeneratedNativeForestTerminalProbability_family D μ a W.depth W.tree
        W.clockTemplate.clock (fun i j _=>W.clockTemplate.clock_continuous i j)
        (fun h i j _=>W.clockTemplate.clock_step_le h i j))
  have he (h : CavityGeneratedHistory Paper.Overlap m) :
      ENNReal.ofReal (∫σ,F σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock h) : Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) =
      (cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock h) : Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)) E := by
    rw [show F=E.indicator (1 : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree→ℝ) from rfl,
      integral_indicator_one hE,ofReal_measureReal]
  exact (funext he) ▸ hc.measurable.ennreal_ofReal

def cavityGeneratedForestTerminalKernel
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) :
    Kernel (CavityGeneratedHistory Paper.Overlap m)
      (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) where
  toFun h := cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
    (W.clockTemplate.clock h)
  measurable' := measurable_cavityGeneratedForestTerminalMeasure D μ a W

instance cavityGeneratedForestTerminalKernel_markov
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) :
    IsMarkovKernel (cavityGeneratedForestTerminalKernel D μ a W) where
  isProbabilityMeasure h := inferInstanceAs (IsProbabilityMeasure
    (cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
      (W.clockTemplate.clock h) : Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)))

theorem cavityGeneratedForestTerminalKernel_apply
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (h : CavityGeneratedHistory Paper.Overlap m) :
    cavityGeneratedForestTerminalKernel D μ a W h=
      (cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock h) : Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)) := rfl

def cavityGeneratedForestJointLaw
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedForest m) :
    Measure (CavityGeneratedHistory Paper.Overlap m×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) :=
  (P.restrict W.clockTemplate.orderSet).measure (parisiFreeMeasure μ a) ⊗ₘ
    cavityGeneratedForestTerminalKernel D μ a W

theorem cavityGeneratedForestJointLaw_finite
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0≤a)
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedForest m) :
    IsFiniteMeasure (cavityGeneratedForestJointLaw D μ a P W) := by
  haveI := (P.restrict W.clockTemplate.orderSet).isFiniteMeasure_measure
    (parisiFreeMeasure μ a) (cavityGenerated_free_mass_le_one μ a ha)
  unfold cavityGeneratedForestJointLaw
  infer_instance

theorem integral_cavityGeneratedForestJointLaw_eq_iterated
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0≤a)
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedForest m)
    (F : CavityGeneratedHistory Paper.Overlap m×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree→ℝ)
    (hF : Measurable F) (K : ℝ) (hK : ∀z,‖F z‖≤K) :
    (∫z,F z ∂cavityGeneratedForestJointLaw D μ a P W)=
      ∫h,∫σ,F (h,σ) ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock h) : Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))
        ∂(P.restrict W.clockTemplate.orderSet).measure (parisiFreeMeasure μ a) := by
  haveI := cavityGeneratedForestJointLaw_finite D μ a ha P W
  haveI := (P.restrict W.clockTemplate.orderSet).isFiniteMeasure_measure
    (parisiFreeMeasure μ a) (cavityGenerated_free_mass_le_one μ a ha)
  have hi : Integrable F (cavityGeneratedForestJointLaw D μ a P W) :=
    (integrable_const K).mono' hF.aestronglyMeasurable (.of_forall hK)
  exact Measure.integral_compProd hi

end QuantitativeFollowup
