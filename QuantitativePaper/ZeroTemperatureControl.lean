module
public import Paper.ParisiHJBValueFunction
public import Paper.ControlCostIntegrability

@[expose] public section

/-! Actual canonical Brownian control objectives with terminal datum |x|.
The coefficient is an integrable profile, not a supplied value function. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 500000

def zeroControlEndpoint (γ : ℝ→ℝ) (x : ℝ)
    (A : ℝ→BrownianSample→ℝ) (ω : BrownianSample) : ℝ :=
  x+canonicalBrownian 1 ω+∫q in (0:ℝ)..1,γ q*A q ω

def zeroControlCost (γ : ℝ→ℝ) (A : ℝ→BrownianSample→ℝ) (ω : BrownianSample) : ℝ :=
  (1/2:ℝ)*∫q in (0:ℝ)..1,γ q*(A q ω)^2

def zeroControlPayoff (γ : ℝ→ℝ) (x : ℝ)
    (A : ℝ→BrownianSample→ℝ) (ω : BrownianSample) : ℝ :=
  |zeroControlEndpoint γ x A ω|-zeroControlCost γ A ω

def zeroControlObjective (γ : ℝ→ℝ) (x : ℝ) (A : ℝ→BrownianSample→ℝ) : ℝ :=
  ∫ω,zeroControlPayoff γ x A ω ∂canonicalBrownianMeasure

def zeroControlValues (γ : ℝ→ℝ) (x : ℝ) : Set ℝ :=
  {v | ∃A,IsParisiAdmissibleControl A ∧ v=zeroControlObjective γ x A}

def zeroTemperatureValue (γ : ℝ→ℝ) (x : ℝ) : ℝ :=sSup (zeroControlValues γ x)

theorem intervalIntegrable_zeroControlProduct (γ : ℝ→ℝ) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume (0:ℝ) 1)
    (A : ℝ→BrownianSample→ℝ) (hA : IsParisiAdmissibleControl A) (j : ℕ)
    (ω : BrownianSample) :
    IntervalIntegrable (fun q=>γ q*(A q ω)^j) volume (0:ℝ) 1 := by
  have hm : Measurable (fun q=>γ q*(A q ω)^j) :=
    hγ.mul (((hA.measurable.comp (measurable_id.prodMk measurable_const))).pow_const j)
  apply hi.norm.mono_fun' hm.aestronglyMeasurable
  exact .of_forall fun q=>by
    change ‖γ q*(A q ω)^j‖≤‖γ q‖
    rw [norm_mul,norm_pow]
    have hh:=pow_le_one₀ (norm_nonneg (A q ω)) (hA.bounded q ω) (n:=j)
    exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (mul_one _)

theorem norm_zeroControlProduct_integral_le (γ : ℝ→ℝ)
    (hi : IntervalIntegrable γ volume (0:ℝ) 1)
    (A : ℝ→BrownianSample→ℝ) (hA : IsParisiAdmissibleControl A) (j : ℕ)
    (ω : BrownianSample) :
    ‖∫q in (0:ℝ)..1,γ q*(A q ω)^j‖≤∫q in (0:ℝ)..1,‖γ q‖ := by
  apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num) _ hi.norm
  exact .of_forall fun q _=>by
    rw [norm_mul,norm_pow]
    have hh:=pow_le_one₀ (norm_nonneg (A q ω)) (hA.bounded q ω) (n:=j)
    exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (mul_one _)

theorem integrable_zeroControlProduct_integral (γ : ℝ→ℝ) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume (0:ℝ) 1)
    (A : ℝ→BrownianSample→ℝ) (hA : IsParisiAdmissibleControl A) (j : ℕ) :
    Integrable (fun ω=>∫q in (0:ℝ)..1,γ q*(A q ω)^j) canonicalBrownianMeasure := by
  have hm : Measurable (fun p:ℝ×BrownianSample=>γ p.1*(A p.1 p.2)^j) :=
    (hγ.comp measurable_fst).mul (hA.measurable.pow_const j)
  have hms:=hm.stronglyMeasurable.integral_prod_left' (μ:=volume.restrict (Ioc (0:ℝ) 1))
  have hm' : StronglyMeasurable (fun ω=>∫q in (0:ℝ)..1,γ q*(A q ω)^j) := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] using hms
  exact (integrable_const (∫q in (0:ℝ)..1,‖γ q‖)).mono' hm'.aestronglyMeasurable
    (.of_forall fun ω=>norm_zeroControlProduct_integral_le γ hi A hA j ω)

theorem integrable_zeroControlEndpoint (γ : ℝ→ℝ) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume (0:ℝ) 1) (x : ℝ)
    (A : ℝ→BrownianSample→ℝ) (hA : IsParisiAdmissibleControl A) :
    Integrable (zeroControlEndpoint γ x A) canonicalBrownianMeasure := by
  have hp:=integrable_zeroControlProduct_integral γ hγ hi A hA 1
  convert! ((integrable_const x).add integrable_hjb_canonicalBrownian_one).add hp using 1
  funext ω
  simp only [zeroControlEndpoint,Pi.add_apply,pow_one]

theorem integrable_zeroControlCost (γ : ℝ→ℝ) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume (0:ℝ) 1)
    (A : ℝ→BrownianSample→ℝ) (hA : IsParisiAdmissibleControl A) :
    Integrable (zeroControlCost γ A) canonicalBrownianMeasure :=
  (integrable_zeroControlProduct_integral γ hγ hi A hA 2).const_mul (1/2:ℝ)

theorem integrable_zeroControlPayoff (γ : ℝ→ℝ) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume (0:ℝ) 1) (x : ℝ)
    (A : ℝ→BrownianSample→ℝ) (hA : IsParisiAdmissibleControl A) :
    Integrable (zeroControlPayoff γ x A) canonicalBrownianMeasure :=
  (integrable_zeroControlEndpoint γ hγ hi x A hA).abs.sub
    (integrable_zeroControlCost γ hγ hi A hA)

theorem admissible_zeroControl : IsParisiAdmissibleControl (fun _ _=>0) where
  continuous_paths :=fun _=>continuous_const
  adapted :=stronglyAdapted_const _ 0
  measurable :=measurable_const
  bounded :=fun _ _=>by norm_num

theorem zeroControlValues_nonempty (γ : ℝ→ℝ) (x : ℝ) :
    (zeroControlValues γ x).Nonempty :=
  ⟨_,fun _ _=>0,admissible_zeroControl,rfl⟩

end QuantitativePaper
