module
public import QuantitativeFollowup.ScalarFiniteResponseKernelLinear
public import QuantitativeFollowup.ScalarFiniteResponsePointwiseLinear
public import QuantitativeFollowup.ScalarTransportPhysicalScore

@[expose] public section

/-! Identification of the genuine transported Gaussian response with the
literal seven-term operator of the paper. All conditioning, density changes,
parameter derivatives and finite expectation passages are discharged. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper FRSB
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

theorem integrable_scalar_centered_terminal_score (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) :
    Integrable (fun z : Paper.BrownianSample×Bool=>M β μ p z.1*C β μ p z.1*
      (Paper.spinSign z.2-M β μ p z.1)) (scalarMarkedSpinLaw β hβ μ) := by
  have hM : Measurable (fun z : Paper.BrownianSample×Bool=>M β μ p z.1) :=
    (measurable_M β μ p p.property).comp measurable_fst
  have hC : Measurable (fun z : Paper.BrownianSample×Bool=>C β μ p z.1) :=
    (measurable_C β hβ μ p.property).comp measurable_fst
  have hs : Measurable (fun z : Paper.BrownianSample×Bool=>Paper.spinSign z.2) :=
    (measurable_of_finite Paper.spinSign).comp measurable_snd
  apply (integrable_const (2:ℝ)).mono' ((hM.mul hC).mul (hs.sub hM)).aestronglyMeasurable
  exact .of_forall fun z=>by
    change ‖M β μ p z.1*C β μ p z.1*(Paper.spinSign z.2-M β μ p z.1)‖≤2
    rw [norm_mul,norm_mul]
    have hA : ‖M β μ p z.1‖*‖C β μ p z.1‖≤1 :=
      (mul_le_mul (scalar_M_norm_le_one β μ p z.1) (norm_C_le_one β μ p z.1)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    have hB : ‖Paper.spinSign z.2-M β μ p z.1‖≤2 := by
      apply (norm_sub_le _ _).trans
      rw [show ‖Paper.spinSign z.2‖=1 by cases z.2 <;> norm_num [Paper.spinSign]]
      linarith [scalar_M_norm_le_one β μ p z.1]
    exact (mul_le_mul hA hB (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem scalarTransportGaussianResponse_eq_operator (s : RSBScheme k)
    (β : ℝ) (hβ : β≠0) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : Paper.parisiSchemeMeasure s∈scalarFloor a)
    (p : Fin (k+3)) :
    scalarTransportGaussianResponse s β φ p=
      scalarResponseOperator β hβ (Paper.parisiSchemeMeasure s) a φ (scalarSchemeTransportNode s p) := by
  let μ:=Paper.parisiSchemeMeasure s
  let qp:=scalarSchemeTransportNode s p
  let P:=scalarMarkedSpinLaw β hβ μ
  let R:=fun z : Paper.BrownianSample×Bool=>2*β^2*φ qp*
    scalarFiniteNodeGradient s β (WithLp.toLp 2 (scalarSelectedHistory s β hβ z.1)) p*
    scalarFiniteNodeHessian s β (WithLp.toLp 2 (scalarSelectedHistory s β hβ z.1)) p*
    (Paper.spinSign z.2-scalarFiniteNodeGradient s β
      (WithLp.toLp 2 (scalarSelectedHistory s β hβ z.1)) p)
  let A:=fun z : Paper.BrownianSample×Bool=>scalarFiniteResponseLinear s φ qp
    (fun j r ell=>scalarResponseSample j β μ qp r ell z)
  have hiA : Integrable A P := integrable_scalarFiniteResponseLinear s β hβ φ qp
  have hiR : Integrable R P := by
    have hi:=(integrable_scalar_centered_terminal_score β hβ μ qp).const_mul (2*β^2*φ qp)
    convert! hi using 1
    funext z
    dsimp only [R]
    rw [scalarFiniteNodeGradient_physical s β hβ,scalarFiniteNodeHessian_physical s β hβ]
    dsimp only [μ,qp]
    ring
  rw [scalarTransportGaussianResponse_eq_physical_score s β hβ]
  have he : (fun z : Paper.BrownianSample×Bool=>scalarTransportExplicitScore s β φ p z.2
      (WithLp.toLp 2 (scalarSelectedHistory s β hβ z.1)) (Gamma β μ qp))=
      (fun z=>β^2*A z+R z) := by
    funext z
    rw [scalarTransportExplicitScore_seven_terms s β hβ φ L hφ h0 h1,
      scalarFiniteSevenTermResponse_eq_linear s β hβ]
  change (∫z,_ ∂P)=_
  rw [he,integral_add (hiA.const_mul _) hiR,integral_const_mul]
  change β^2*(∫z,A z ∂P)+(∫z,R z ∂P)=_
  have hR : (∫z,R z ∂P)=0 := integral_scalarFinite_centered_terminal_score s β hβ φ p
  rw [hR,add_zero,integral_scalarFiniteResponseLinear]
  exact (scalarResponseOperator_eq_finite_linear s β hβ a ha hμ φ h0 qp).symm

end QuantitativeFollowup
