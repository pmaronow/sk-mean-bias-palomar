module
public import QuantitativeFollowup.FollowupCavitySignedResponseNativeDefinitions

@[expose] public section

/-! Joint weak-profile continuity of the literal isolated-spin kernels.
The marked-spin term is first transported through the genuine terminal
kernel; all subsequent limits use the fixed Wiener measure. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB Paper
open scoped Topology NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem scalar_C_norm (β : ℝ) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (ω : Paper.BrownianSample) : ‖C β μ q ω‖≤1 := by
  simp only [C,jetProcess,parisiSpatialJet_two]
  exact norm_parisiHessian_le_one_all _ _ _

theorem continuous_cavitySignedScalarKernelOne_profile (β : ℝ) (hβ : β≠0) :
    Continuous (fun z : Paper.ParisiMeasure×(Paper.Overlap×Paper.Overlap) =>
      cavitySignedScalarKernelOne β z.1 z.2.1 z.2.2) := by
  apply continuous_of_dominated (μ:=canonicalBrownianMeasure) (bound:=fun _=>(1:ℝ))
  · intro z
    exact (((measurable_M β z.1 z.2.2 z.2.2.property).mul
      (measurable_C β hβ z.1 z.2.2.property)).mul
      (measurable_M β z.1 z.2.1 z.2.1.property)).aestronglyMeasurable
  · intro z
    exact .of_forall fun ω=>by
      rw [norm_mul,norm_mul]
      exact (mul_le_mul (mul_le_mul (scalar_M_norm_le_one β z.1 z.2.2 ω)
        (scalar_C_norm β z.1 z.2.2 ω) (norm_nonneg _) zero_le_one)
        (scalar_M_norm_le_one β z.1 z.2.1 ω) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · exact integrable_const _
  · exact .of_forall fun ω=>by
      have hpmap : Continuous (fun z : Paper.ParisiMeasure×(Paper.Overlap×Paper.Overlap)=>(z.1,z.2.2)) :=
        continuous_fst.prodMk continuous_snd.snd
      have hrmap : Continuous (fun z : Paper.ParisiMeasure×(Paper.Overlap×Paper.Overlap)=>(z.1,z.2.1)) :=
        continuous_fst.prodMk continuous_snd.fst
      have hh := (((continuous_scalarM_parameter β hβ ω).comp hpmap).mul
        ((continuous_scalarC_parameter β hβ ω).comp hpmap)).mul
        ((continuous_scalarM_parameter β hβ ω).comp hrmap)
      exact hh.congr (fun z=>rfl)

theorem cavitySignedScalarKernelMarked_eq_unmarked (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (r p : Paper.Overlap) :
    cavitySignedScalarKernelMarked β hβ μ r p=
      ∫ω,scalarCenteredSquare β μ p ω*M β μ r ω*M β μ 1 ω ∂canonicalBrownianMeasure := by
  have hm : Measurable (fun ω=>scalarCenteredSquare β μ p ω*M β μ r ω) :=
    (((measurable_M β μ p p.property).pow_const 2).sub measurable_const).mul
      (measurable_M β μ r r.property)
  have hb (ω : Paper.BrownianSample) : ‖scalarCenteredSquare β μ p ω*M β μ r ω‖≤1 :=
    (norm_mul _ _).trans_le ((mul_le_mul
      (scalarCenteredSquare_norm_le_one β μ p ω) (scalar_M_norm_le_one β μ r ω)
      (norm_nonneg _) zero_le_one).trans_eq (by norm_num))
  have he := integral_scalarMarkedSpinLaw_terminal_sign β hβ μ _ hm 1 hb
  unfold cavitySignedScalarKernelMarked
  convert he using 1
  congr 1
  funext z
  ring

theorem continuous_cavitySignedScalarKernelMarked_profile (β : ℝ) (hβ : β≠0) :
    Continuous (fun z : Paper.ParisiMeasure×(Paper.Overlap×Paper.Overlap) =>
      cavitySignedScalarKernelMarked β hβ z.1 z.2.1 z.2.2) := by
  simp_rw [cavitySignedScalarKernelMarked_eq_unmarked]
  apply continuous_of_dominated (μ:=canonicalBrownianMeasure) (bound:=fun _=>(1:ℝ))
  · intro z
    exact (((((measurable_M β z.1 z.2.2 z.2.2.property).pow_const 2).sub measurable_const).mul
      (measurable_M β z.1 z.2.1 z.2.1.property)).mul
      (measurable_M β z.1 1 (by norm_num))).aestronglyMeasurable
  · intro z
    exact .of_forall fun ω=>by
      rw [norm_mul,norm_mul]
      exact (mul_le_mul (mul_le_mul (scalarCenteredSquare_norm_le_one β z.1 z.2.2 ω)
        (scalar_M_norm_le_one β z.1 z.2.1 ω) (norm_nonneg _) zero_le_one)
        (scalar_M_norm_le_one β z.1 1 ω) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · exact integrable_const _
  · exact .of_forall fun ω=>by
      have hpmap : Continuous (fun z : Paper.ParisiMeasure×(Paper.Overlap×Paper.Overlap)=>(z.1,z.2.2)) :=
        continuous_fst.prodMk continuous_snd.snd
      have hrmap : Continuous (fun z : Paper.ParisiMeasure×(Paper.Overlap×Paper.Overlap)=>(z.1,z.2.1)) :=
        continuous_fst.prodMk continuous_snd.fst
      have h1map : Continuous (fun z : Paper.ParisiMeasure×(Paper.Overlap×Paper.Overlap)=>(z.1,(1:Paper.Overlap))) :=
        continuous_fst.prodMk continuous_const
      have hh := (((continuous_scalarCenteredSquare_parameter β hβ ω).comp hpmap).mul
        ((continuous_scalarM_parameter β hβ ω).comp hrmap)).mul
        ((continuous_scalarM_parameter β hβ ω).comp h1map)
      exact hh.congr (fun z=>rfl)

theorem continuous_cavitySignedScalarKernelTriple_profile (β : ℝ) (hβ : β≠0) :
    Continuous (fun z : Paper.ParisiMeasure×((Paper.Overlap×Paper.Overlap)×Paper.Overlap) =>
      cavitySignedScalarKernelTriple β z.1 z.2.1 z.2.2) := by
  apply continuous_of_dominated (μ:=canonicalBrownianMeasure) (bound:=fun _=>(1:ℝ))
  · intro z
    exact (((((measurable_M β z.1 z.2.2 z.2.2.property).pow_const 2).sub measurable_const).mul
      (measurable_M β z.1 z.2.1.1 z.2.1.1.property)).mul
      (measurable_M β z.1 z.2.1.2 z.2.1.2.property)).aestronglyMeasurable
  · intro z
    exact .of_forall fun ω=>by
      rw [norm_mul,norm_mul]
      exact (mul_le_mul (mul_le_mul (scalarCenteredSquare_norm_le_one β z.1 z.2.2 ω)
        (scalar_M_norm_le_one β z.1 z.2.1.1 ω) (norm_nonneg _) zero_le_one)
        (scalar_M_norm_le_one β z.1 z.2.1.2 ω) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · exact integrable_const _
  · exact .of_forall fun ω=>by
      have hpmap : Continuous (fun z : Paper.ParisiMeasure×((Paper.Overlap×Paper.Overlap)×Paper.Overlap)=>(z.1,z.2.2)) :=
        continuous_fst.prodMk continuous_snd.snd
      have hrmap : Continuous (fun z : Paper.ParisiMeasure×((Paper.Overlap×Paper.Overlap)×Paper.Overlap)=>(z.1,z.2.1.1)) :=
        continuous_fst.prodMk continuous_snd.fst.fst
      have hsmap : Continuous (fun z : Paper.ParisiMeasure×((Paper.Overlap×Paper.Overlap)×Paper.Overlap)=>(z.1,z.2.1.2)) :=
        continuous_fst.prodMk continuous_snd.fst.snd
      have hh := (((continuous_scalarCenteredSquare_parameter β hβ ω).comp hpmap).mul
        ((continuous_scalarM_parameter β hβ ω).comp hrmap)).mul
        ((continuous_scalarM_parameter β hβ ω).comp hsmap)
      exact hh.congr (fun z=>rfl)

theorem continuous_cavitySignedScalarFutureCovarianceKernel_profile (β : ℝ) (hβ : β≠0) :
    Continuous (fun z : Paper.ParisiMeasure×(Paper.Overlap×Paper.Overlap) =>
      cavitySignedScalarFutureCovarianceKernel β z.1 z.2.1 z.2.2) := by
  apply continuous_of_dominated (μ:=canonicalBrownianMeasure) (bound:=fun _=>(1:ℝ))
  · intro z
    exact ((((measurable_M β z.1 z.2.1 z.2.1.property).pow_const 2).sub measurable_const).mul
      (((measurable_M β z.1 z.2.2 z.2.2.property).pow_const 2).sub measurable_const)).aestronglyMeasurable
  · intro z
    exact .of_forall fun ω=>(norm_mul _ _).trans_le ((mul_le_mul
      (scalarCenteredSquare_norm_le_one β z.1 z.2.1 ω)
      (scalarCenteredSquare_norm_le_one β z.1 z.2.2 ω)
      (norm_nonneg _) zero_le_one).trans_eq (by norm_num))
  · exact integrable_const _
  · exact .of_forall fun ω=>by
      have hpmap : Continuous (fun z : Paper.ParisiMeasure×(Paper.Overlap×Paper.Overlap)=>(z.1,z.2.1)) :=
        continuous_fst.prodMk continuous_snd.fst
      have hlmap : Continuous (fun z : Paper.ParisiMeasure×(Paper.Overlap×Paper.Overlap)=>(z.1,z.2.2)) :=
        continuous_fst.prodMk continuous_snd.snd
      have hh := ((continuous_scalarCenteredSquare_parameter β hβ ω).comp hpmap).mul
        ((continuous_scalarCenteredSquare_parameter β hβ ω).comp hlmap)
      exact hh.congr (fun z=>rfl)

theorem continuous_cavitySignedScalarVariance_profile (β : ℝ) (hβ : β≠0) :
    Continuous (fun z : Paper.ParisiMeasure×Paper.Overlap => cavitySignedScalarVariance β z.1 z.2) := by
  have he (μ : Paper.ParisiMeasure) (p : Paper.Overlap) :
      cavitySignedScalarVariance β μ p=cavitySignedScalarFutureCovarianceKernel β μ p p := by
    rw [cavitySignedScalarVariance,variance_eq_integral
      ((measurable_M β μ p p.property).pow_const 2).aemeasurable]
    simp only [cavitySignedScalarFutureCovarianceKernel,scalarCenteredSquare,Gamma,pow_two]
  simp_rw [he]
  have hd : Continuous (fun z : Paper.ParisiMeasure×Paper.Overlap=>(z.1,(z.2,z.2))) :=
    continuous_fst.prodMk (continuous_snd.prodMk continuous_snd)
  have hh := (continuous_cavitySignedScalarFutureCovarianceKernel_profile β hβ).comp hd
  exact hh.congr (fun z=>rfl)

end QuantitativeFollowup
