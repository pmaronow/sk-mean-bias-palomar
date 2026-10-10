module
public import QuantitativeFollowup.ScalarResponseRegrouping
public import QuantitativeFollowup.ScalarFiniteMarkedDensity
public import FRSB.GammaEndpoints

@[expose] public section

/-! The prescribed zero-overlap atom contributes nothing to the genuine
scalar transport response. The future kernel at the root is a deterministic
expectation, so its centered pairing vanishes; no independence premise is used. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FRSB FourPapersCommon QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem scalarM_root (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (ω : Paper.BrownianSample) : M β μ (0 : Paper.Overlap) ω = 0 := by
  change M β μ (0 : ℝ) ω = 0
  simp only [M,jetProcess,optimalState_initial,parisiSpatialJet_one]
  exact parisiGradient_at_zero β hβ μ 0 (by constructor <;> norm_num)

theorem scalarPhysicalState_root (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (ω : Paper.BrownianSample) : parisiPhysicalSplitState β 0 μ 0 ω = 0 := by
  rw [parisiPhysicalSplitState_eq_selected β hβ]
  rw [show ((0 : Paper.Overlap) : ℝ)=0 from rfl,Real.toNNReal_zero]
  rw [Paper.selectedParisiItoState_eq β 0 hβ μ (t:=0) (by norm_num) ω]
  rw [←optimalStateReal_eq_selected β hβ μ]
  exact optimalState_initial β μ ω

theorem integral_scalarCenteredSquare (β : ℝ) (μ : Paper.ParisiMeasure)
    (p : Paper.Overlap) :
    (∫ω,scalarCenteredSquare β μ p ω ∂canonicalBrownianMeasure) = 0 := by
  change (∫ω,M β μ p ω^2-Gamma β μ p ∂canonicalBrownianMeasure)=0
  rw [integral_sub (integrable_M_sq β μ p p.property) (integrable_const _),
    integral_const,probReal_univ,one_smul]
  change Gamma β μ p-Gamma β μ p=0
  ring

theorem scalarFutureSquare_root (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (ell : Paper.Overlap) : scalarFutureSquareExtended β μ 0 ell 0 = Gamma β μ ell := by
  have hr : ((0 : Paper.Overlap) : ℝ) ≤ ell := ell.property.1
  have he := integral_scalarFutureSquareProcess β hβ μ 0 ell hr
  simp only [scalarFutureSquareProcess,scalarPhysicalState_root β hβ μ,
    integral_const,probReal_univ,one_smul] at he
  rw [scalarFutureSquareExtended_eq β μ 0 ell hr]
  exact he

theorem scalarResponseKernel7_root (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (p ell : Paper.Overlap) : scalarResponseKernel7 β μ p 0 ell = 0 := by
  unfold scalarResponseKernel7
  simp_rw [scalarPhysicalState_root β hβ μ,scalarFutureSquare_root β hβ μ]
  rw [integral_mul_const,integral_scalarCenteredSquare,zero_mul]

theorem scalarResponsePsi1_root (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (_h0 : φ 0=0) (p : Paper.Overlap) :
    scalarResponsePsi1 β μ φ p 0 = 0 := by
  have hn : ¬p < (0 : Paper.Overlap) := not_lt.mpr p.property.1
  simp only [scalarResponsePsi1,ite_eq_right hn,scalarResponseKernel3,
    scalarResponseKernel4,scalarResponseKernel5,scalarM_root β hβ μ,
    mul_zero,zero_pow (by decide : 2 ≠ 0),integral_zero,zero_mul,sub_zero,
    add_zero]

theorem scalarResponsePsi2_first_root (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (_h0 : φ 0=0) (p ell : Paper.Overlap) :
    scalarResponsePsi2 β μ φ p 0 ell = 0 := by
  simp only [scalarResponsePsi2,scalarResponseKernel6,scalarResponseKernel5,
    scalarM_root β hβ μ,scalarResponseKernel7_root β hβ μ,
    mul_zero,zero_mul,zero_pow (by decide : 2 ≠ 0),integral_zero,sub_zero,
    ite_self,add_zero]

theorem scalarResponsePsi2_second_root (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (p r : Paper.Overlap) :
    scalarResponsePsi2 β μ φ p r 0 = 0 := by
  have hn : ¬r < (0 : Paper.Overlap) := not_lt.mpr r.property.1
  simp only [scalarResponsePsi2,ite_eq_right hn,scalarResponseKernel6,
    scalarM_root β hβ μ,mul_zero,integral_zero,zero_mul,add_zero]

theorem integral_scalarResponsePsi1_free_eq_full (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor s) (φ : C(Paper.Overlap,ℝ)) (h0 : φ 0=0)
    (p : Paper.Overlap) :
    (∫r,scalarResponsePsi1 β μ φ p r ∂parisiFreeMeasure μ s) =
      ∫r,scalarResponsePsi1 β μ φ p r ∂(μ : Measure Paper.Overlap) := by
  have hc : Continuous (fun r : Paper.Overlap=>scalarResponsePsi1 β μ φ p r) := by
    have ha : Continuous (fun r : Paper.Overlap=>(μ,(p,r))) := by fun_prop
    convert! (continuous_scalarResponsePsi1 β hβ φ).comp ha using 1
  rw [integral_parisiFreeMeasure_continuous μ s hs hμ _ hc]
  simp only [show zeroOverlap=(0 : Paper.Overlap) from rfl,
    scalarResponsePsi1_root β hβ μ φ h0,mul_zero,sub_zero]

theorem integral_scalarResponsePsi2_free_eq_full (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor s) (φ : C(Paper.Overlap,ℝ)) (h0 : φ 0=0)
    (p : Paper.Overlap) :
    (∫r,∫ell,scalarResponsePsi2 β μ φ p r ell ∂parisiFreeMeasure μ s
      ∂parisiFreeMeasure μ s) =
      ∫r,∫ell,scalarResponsePsi2 β μ φ p r ell ∂(μ : Measure Paper.Overlap)
      ∂(μ : Measure Paper.Overlap) := by
  have hc : Continuous (fun z : Paper.Overlap×Paper.Overlap=>scalarResponsePsi2 β μ φ p z.1 z.2) := by
    have ha : Continuous (fun z : Paper.Overlap×Paper.Overlap=>(μ,(p,(z.1,z.2)))) := by fun_prop
    convert! (continuous_scalarResponsePsi2 β hβ φ).comp ha using 1
  have he (r : Paper.Overlap) :
      (∫ell,scalarResponsePsi2 β μ φ p r ell ∂parisiFreeMeasure μ s) =
        ∫ell,scalarResponsePsi2 β μ φ p r ell ∂(μ : Measure Paper.Overlap) := by
    have hcr : Continuous (fun ell : Paper.Overlap=>scalarResponsePsi2 β μ φ p r ell) := by
      convert! hc.comp (continuous_const.prodMk continuous_id) using 1
    rw [integral_parisiFreeMeasure_continuous μ s hs hμ _ hcr]
    simp only [show zeroOverlap=(0 : Paper.Overlap) from rfl,
      scalarResponsePsi2_second_root β hβ μ φ,mul_zero,sub_zero]
  simp_rw [he]
  have hci : Continuous (fun r : Paper.Overlap=>
      ∫ell,scalarResponsePsi2 β μ φ p r ell ∂(μ : Measure Paper.Overlap)) := by
    exact continuous_integral_probability_family _ hc (fun _=>μ) continuous_const
  rw [integral_parisiFreeMeasure_continuous μ s hs hμ _ hci]
  simp only [show zeroOverlap=(0 : Paper.Overlap) from rfl,
    scalarResponsePsi2_first_root β hβ μ φ h0,integral_zero,mul_zero,sub_zero]

theorem scalarResponseOperator_eq_full_regrouped (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor s) (φ : C(Paper.Overlap,ℝ)) (h0 : φ 0=0)
    (p : Paper.Overlap) :
    scalarResponseOperator β hβ μ s φ p = β^2*(
      scalarResponseKernel0 β μ p 0 0*φ p+
      (∫r,scalarResponsePsi1 β μ φ p r ∂(μ : Measure Paper.Overlap))+
      (∫r,∫ell,scalarResponsePsi2 β μ φ p r ell ∂(μ : Measure Paper.Overlap)
        ∂(μ : Measure Paper.Overlap))) := by
  rw [scalarResponseOperator_eq_regrouped β hβ μ s hs hμ]
  unfold scalarRegroupedResponse
  rw [integral_scalarResponsePsi1_free_eq_full β hβ μ s hs hμ φ h0,
    integral_scalarResponsePsi2_free_eq_full β hβ μ s hs hμ φ h0]

end QuantitativeFollowup
