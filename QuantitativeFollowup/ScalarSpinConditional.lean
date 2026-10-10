module
public import QuantitativeFollowup.ScalarKernelBounds
public import FourPapersCommon.PullbackIndicatorIntegral

@[expose] public section

/-! The genuinely marked scalar spin has the actual magnetization as its
conditional mean in every whole Brownian past. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FRSB FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem measurable_scalarM_past (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    Measurable[canonicalBrownianFiltration (q : ℝ).toNNReal] (M β μ q) := by
  have he : M β μ q=fun ω => parisiGradient β μ (q,parisiPhysicalSplitState β 0 μ q ω) :=
    funext fun ω => (scalarGradient_physicalSplitState β hβ μ q ω).symm
  rw [he]
  exact (continuous_parisiGradient β μ).measurable.comp
    (measurable_const.prodMk (measurable_parisiPhysicalSplitState_past β 0 hβ μ q))

theorem scalarGradientProcess_physical (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (ω : Paper.BrownianSample) :
    selectedParisiGradientProcess β 0 hβ μ (q : ℝ).toNNReal ω=M β μ q ω := by
  have hq : (q : ℝ).toNNReal ≤ 1 := by
    rw [←NNReal.coe_le_coe,Real.coe_toNNReal _ q.property.1]
    exact q.property.2
  simpa only [stoppedMagnetization,min_eq_left hq,Real.coe_toNNReal _ q.property.1] using
    stoppedMagnetization_eq_physical β hβ μ hq ω

theorem scalarM_terminal_weighted_expectation (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (Z : Paper.BrownianSample → ℝ)
    (hZ : Measurable[canonicalBrownianFiltration (q : ℝ).toNNReal] Z)
    (hbZ : ∀ ω,‖Z ω‖ ≤ 1) :
    (∫ ω,Z ω*M β μ 1 ω ∂canonicalBrownianMeasure)=
      ∫ ω,Z ω*M β μ q ω ∂canonicalBrownianMeasure := by
  have he := selectedParisiGradient_terminal_weighted_expectation β 0 hβ μ
    (q : ℝ).toNNReal (by rw [Real.coe_toNNReal _ q.property.1];exact q.property.2)
      Z hZ.stronglyMeasurable hbZ
  change (∫ ω,Z ω*selectedParisiGradientProcess β 0 hβ μ 1 ω ∂canonicalBrownianMeasure)=
    ∫ ω,Z ω*selectedParisiGradientProcess β 0 hβ μ (q : ℝ).toNNReal ω
      ∂canonicalBrownianMeasure at he
  have hterm (ω : Paper.BrownianSample) :
      selectedParisiGradientProcess β 0 hβ μ 1 ω=M β μ 1 ω := by
    simpa only [stoppedMagnetization,min_self,NNReal.coe_one] using
      stoppedMagnetization_eq_physical β hβ μ (t := 1) le_rfl ω
  simpa only [hterm,scalarGradientProcess_physical β hβ μ q] using he

abbrev scalarSpinPast (q : ℝ≥0) : MeasurableSpace (Paper.BrownianSample×Bool) :=
  (canonicalBrownianFiltration q).comap Prod.fst

theorem scalarSpinPast_le (q : ℝ≥0) : scalarSpinPast q ≤
    (inferInstance : MeasurableSpace (Paper.BrownianSample×Bool)) :=
  (MeasurableSpace.comap_mono (canonicalBrownianFiltration.le q)).trans measurable_fst.comap_le

theorem integral_scalarMarkedSpinLaw_past_sign (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (Z : Paper.BrownianSample → ℝ)
    (hZ : Measurable[canonicalBrownianFiltration (q : ℝ).toNNReal] Z)
    (hbZ : ∀ ω,‖Z ω‖ ≤ 1) :
    (∫ z,Z z.1*Paper.spinSign z.2 ∂scalarMarkedSpinLaw β hβ μ)=
      ∫ z,Z z.1*M β μ q z.1 ∂scalarMarkedSpinLaw β hβ μ := by
  have hZm := hZ.mono (canonicalBrownianFiltration.le _) le_rfl
  calc
    _ = ∫ ω,Z ω*M β μ 1 ω ∂canonicalBrownianMeasure :=
      integral_scalarMarkedSpinLaw_terminal_sign β hβ μ Z hZm 1 hbZ
    _ = ∫ ω,Z ω*M β μ q ω ∂canonicalBrownianMeasure :=
      scalarM_terminal_weighted_expectation β hβ μ q Z hZ hbZ
    _ = _ := (integral_scalarMarkedSpinLaw_sample β hβ μ
      (fun ω => Z ω*M β μ q ω) (hZm.mul (measurable_M β μ q q.property))).symm

theorem scalarMarkedSpinLaw_sign_condExp (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    (scalarMarkedSpinLaw β hβ μ)[(fun z => Paper.spinSign z.2) |
      scalarSpinPast (q : ℝ).toNNReal]=ᵐ[scalarMarkedSpinLaw β hβ μ]
      fun z => M β μ q z.1 := by
  have hspin : Measurable (fun z : Paper.BrownianSample×Bool => Paper.spinSign z.2) :=
    (measurable_of_finite Paper.spinSign).comp measurable_snd
  have hi : Integrable (fun z : Paper.BrownianSample×Bool => Paper.spinSign z.2)
      (scalarMarkedSpinLaw β hβ μ) :=
    (integrable_const (1 : ℝ)).mono' hspin.aestronglyMeasurable (.of_forall fun z => by
      cases z.2 <;> norm_num [Paper.spinSign])
  have had : Measurable[scalarSpinPast (q : ℝ).toNNReal]
      (fun z : Paper.BrownianSample×Bool => M β μ q z.1) :=
    (measurable_scalarM_past β hβ μ q).comp (comap_measurable Prod.fst)
  have hci := (scalarMarkedSpinLaw_memLp_lift β hβ μ _
    (scalar_M_memLp_two β μ q q.property)).integrable (by norm_num)
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (scalarSpinPast_le _) hi
  · intro A hA hfinite
    exact hci.integrableOn
  · intro A hA hfinite
    obtain ⟨B,hB,rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
    have hBg := (canonicalBrownianFiltration.le (q : ℝ).toNNReal) B hB
    have he := integral_scalarMarkedSpinLaw_past_sign β hβ μ q
      (B.indicator (fun _ => 1)) (measurable_const.indicator hB)
      (fun ω => by by_cases hω : ω∈B <;> simp [hω])
    rw [integral_pullback_indicator_one_mul (scalarMarkedSpinLaw β hβ μ)
        Prod.fst measurable_fst B hBg,
      integral_pullback_indicator_one_mul (scalarMarkedSpinLaw β hβ μ)
        Prod.fst measurable_fst B hBg] at he
    exact he.symm
  · exact had.stronglyMeasurable.aestronglyMeasurable

end QuantitativeFollowup
