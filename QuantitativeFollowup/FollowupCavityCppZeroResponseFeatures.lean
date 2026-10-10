module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseKernels
public import QuantitativeFollowup.FollowupCavityCppZeroResponseTerminal
public import QuantitativeFollowup.FollowupCavityDecouplingSpinMoments
public import QuantitativeFollowup.ScalarFiniteMarkedDensity

@[expose] public section

/-! Every joint scalar/rest terminal feature is transported independently by
 the actual normalized finite transitions at zero incident coupling. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {k : ℕ}
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityScalarFiniteFeatureMean (s : RSBScheme k) (β : ℝ) (j : ℕ)
    (b : Bool → ℝ) : ℝ → ℝ :=
  OverlapPaper.sourceKernelExpectation (cavityScalarDepthKernel s β) j
    (fun x => ∫ e, b e ∂scalarSpinLaw x)

theorem measurable_cavityScalarFiniteFeatureMean (s : RSBScheme k) (β : ℝ)
    (j : ℕ) (b : Bool → ℝ) : Measurable (cavityScalarFiniteFeatureMean s β j b) := by
  apply OverlapPaper.sourceKernelExpectation_measurable
  have h : Measurable (fun x : ℝ => ∫ e, b e ∂scalarSpinMarkKernel id measurable_id x) :=
    (measurable_of_finite b).stronglyMeasurable.integral_kernel.measurable
  exact h

@[simp] theorem cavityScalarFiniteFeatureMean_zero (s : RSBScheme k) (β : ℝ)
    (b : Bool → ℝ) (x : ℝ) :
    cavityScalarFiniteFeatureMean s β 0 b x = ∫ e, b e ∂scalarSpinLaw x := rfl

theorem cavityScalarFiniteFeatureMean_succ (s : RSBScheme k) (β : ℝ) (j : ℕ)
    (b : Bool → ℝ) (x : ℝ) :
    cavityScalarFiniteFeatureMean s β (j+1) b x =
      ∫ y, cavityScalarFiniteFeatureMean s β j b y ∂cavityScalarDepthKernel s β j x := rfl

theorem cavityFiniteJointFeature_zero (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1) (j : ℕ)
    (f : Configuration n → ℝ) (b : Bool → ℝ) (P : AnisotropicParameter (n+1)) :
    anisotropicFiniteFeatureMean
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩) s j
        (fun σ => f (cavityRestConfiguration σ) * b (σ (Fin.last n))) P =
      anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s j f
        (cavityRestParameterProjection n P) *
      cavityScalarFiniteFeatureMean s (followupCavityScalarBeta n β ρ) j b (P (Sum.inr (Fin.last n))) := by
  let D := followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl, zero_le_one⟩
  let R := followupCavityRestSpinModel n β ρ hβ hρ
  let β0 := followupCavityScalarBeta n β ρ
  induction j generalizing P with
  | zero =>
      let g : AnisotropicDisorder (n+1) := WithLp.toLp 2 (fun e => P (Sum.inl e))
      let x : QuantitativePaper.Field (n+1) := WithLp.toLp 2 (fun i => P (Sum.inr i))
      have hid : anisotropicParameterPoint g x = P := by ext i; cases i <;> rfl
      rw [←hid, cavityRestParameterProjection_point, anisotropicFiniteFeatureMean_zero,
        anisotropicFiniteFeatureMean_zero, cavityScalarFiniteFeatureMean_zero]
      exact cavityTerminalJointFeature_zero n β ρ hβ hρ g x f b
  | succ j ih =>
      let g : AnisotropicDisorder (n+1) := WithLp.toLp 2 (fun e => P (Sum.inl e))
      let x : QuantitativePaper.Field (n+1) := WithLp.toLp 2 (fun i => P (Sum.inr i))
      have hid : anisotropicParameterPoint g x = P := by ext i; cases i <;> rfl
      rw [anisotropicFiniteFeatureMean_succ_kernel,
        anisotropicFiniteFeatureMean_succ_kernel, cavityScalarFiniteFeatureMean_succ]
      simp_rw [ih]
      have hm : Measurable (fun z : AnisotropicParameter n × ℝ =>
          anisotropicFiniteFeatureMean R s j f z.1 * cavityScalarFiniteFeatureMean s β0 j b z.2) :=
        ((measurable_anisotropicFiniteFeatureMean R s j f).comp measurable_fst).mul
          ((measurable_cavityScalarFiniteFeatureMean s β0 j b).comp measurable_snd)
      change (∫ Q, (fun z : AnisotropicParameter n × ℝ =>
        anisotropicFiniteFeatureMean R s j f z.1 * cavityScalarFiniteFeatureMean s β0 j b z.2)
          (cavityIndependentParameterSplit n Q) ∂anisotropicDepthKernel D s j P) = _
      rw [←integral_map (measurable_cavityIndependentParameterSplit n).aemeasurable hm.aestronglyMeasurable,
        ←hid, cavityDepthKernel_zero_product, integral_prod_mul, cavityRestParameterProjection_point]
      rfl

end QuantitativeFollowup
