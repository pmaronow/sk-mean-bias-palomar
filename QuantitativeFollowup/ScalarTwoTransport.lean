module
public import QuantitativeFollowup.ScalarTransportHomeomorph
public import QuantitativeFollowup.ScalarTransportFunctionalDerivative

@[expose] public section

/-! Actual two-direction overlap transports and their exact relabelling at
a moved profile. All measures below are literal probability pushforwards. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def scalarTwoDirection (φ ψ : C(Paper.Overlap,ℝ)) (z : ℝ×ℝ) : C(Paper.Overlap,ℝ) :=
  z.1 • φ+z.2 • ψ

@[simp] theorem scalarTwoDirection_apply (φ ψ : C(Paper.Overlap,ℝ)) (z : ℝ×ℝ)
    (q : Paper.Overlap) : scalarTwoDirection φ ψ z q=z.1*φ q+z.2*ψ q := rfl

theorem lipschitzWith_scalarTwoDirection (φ ψ : C(Paper.Overlap,ℝ))
    (Lφ Lψ : ℝ≥0) (hφ : LipschitzWith Lφ φ) (hψ : LipschitzWith Lψ ψ) (z : ℝ×ℝ) :
    LipschitzWith (‖z.1‖₊*Lφ+‖z.2‖₊*Lψ) (scalarTwoDirection φ ψ z) := by
  exact ((lipschitzWith_smul z.1).comp hφ).add ((lipschitzWith_smul z.2).comp hψ)

theorem scalarTwoDirection_endpoints (φ ψ : C(Paper.Overlap,ℝ))
    (hφ0 : φ 0=0) (hφ1 : φ 1=0) (hψ0 : ψ 0=0) (hψ1 : ψ 1=0) (z : ℝ×ℝ) :
    scalarTwoDirection φ ψ z 0=0 ∧ scalarTwoDirection φ ψ z 1=0 := by
  simp only [scalarTwoDirection_apply,hφ0,hφ1,hψ0,hψ1,mul_zero,add_zero,and_self]

def scalarTwoTransportMeasure (μ : Paper.ParisiMeasure) (φ ψ : C(Paper.Overlap,ℝ))
    (z : ℝ×ℝ) : Paper.ParisiMeasure :=
  scalarTransportMeasure μ (scalarTwoDirection φ ψ z) 1

def scalarTwoTransportFunctional (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ ψ : C(Paper.Overlap,ℝ)) (z : ℝ×ℝ) : ℝ :=
  scalarParisiFunctional β (scalarTwoTransportMeasure μ φ ψ z)

theorem scalarTwoTransport_axis (μ : Paper.ParisiMeasure) (φ ψ : C(Paper.Overlap,ℝ)) (u : ℝ) :
    scalarTwoTransportMeasure μ φ ψ (0,u)=scalarTransportMeasure μ ψ u := by
  have he : scalarLevelTransport (scalarTwoDirection φ ψ (0,u)) 1=scalarLevelTransport ψ u := by
    funext q
    apply Subtype.ext
    simp only [scalarLevelTransport,scalarTwoDirection_apply,zero_mul,zero_add,one_mul]
  exact congrArg (fun f=>μ.map f) he

theorem scalarTwoLevelTransport_relabelled (φ ψ : C(Paper.Overlap,ℝ)) (Lψ : ℝ≥0)
    (hψ : LipschitzWith Lψ ψ) (hψ0 : ψ 0=0) (hψ1 : ψ 1=0)
    (u : ℝ) (hu : |u| *Lψ<1) (v : ℝ) (q : Paper.Overlap) :
    scalarLevelTransport (scalarTwoDirection φ ψ (v,u)) 1 q=
      scalarLevelTransport (scalarRelabelledDirection φ ψ Lψ hψ hψ0 hψ1 u hu) v
        (scalarLevelTransport ψ u q) := by
  change projIcc 0 1 zero_le_one ((q:ℝ)+1*scalarTwoDirection φ ψ (v,u) q)=
    projIcc 0 1 zero_le_one ((scalarLevelTransport ψ u q:ℝ)+
      v*scalarRelabelledDirection φ ψ Lψ hψ hψ0 hψ1 u hu (scalarLevelTransport ψ u q))
  rw [scalarRelabelledDirection_transport,
    scalarLevelTransport_eq_affine ψ Lψ hψ hψ0 hψ1 u hu.le]
  simp only [scalarTwoDirection_apply,one_mul]
  congr 1
  ring

theorem scalarTwoTransport_relabelled (μ : Paper.ParisiMeasure)
    (φ ψ : C(Paper.Overlap,ℝ)) (Lψ : ℝ≥0) (hψ : LipschitzWith Lψ ψ)
    (hψ0 : ψ 0=0) (hψ1 : ψ 1=0) (u : ℝ) (hu : |u| *Lψ<1) (v : ℝ) :
    scalarTwoTransportMeasure μ φ ψ (v,u)=
      scalarTransportMeasure (scalarTransportMeasure μ ψ u)
        (scalarRelabelledDirection φ ψ Lψ hψ hψ0 hψ1 u hu) v := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [scalarTwoTransportMeasure,scalarTransportMeasure,ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (continuous_scalarLevelTransport_parameter _ v).measurable
    (continuous_scalarLevelTransport_parameter ψ u).measurable]
  congr 1
  funext q
  exact scalarTwoLevelTransport_relabelled φ ψ Lψ hψ hψ0 hψ1 u hu v q

def scalarTwoTransportAxisDerivative (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ ψ : C(Paper.Overlap,ℝ)) (u : ℝ) : ℝ :=
  β^2/2*(∫q : Paper.Overlap,φ q*((scalarLevelTransport ψ u q:ℝ)-
    Gamma β (scalarTransportMeasure μ ψ u) (scalarLevelTransport ψ u q)) ∂(μ:Measure Paper.Overlap))

theorem scalarTwoTransport_relabelled_firstDerivative (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (φ ψ : C(Paper.Overlap,ℝ)) (Lψ : ℝ≥0) (hψ : LipschitzWith Lψ ψ)
    (hψ0 : ψ 0=0) (hψ1 : ψ 1=0) (u : ℝ) (hu : |u| *Lψ<1) :
    scalarTransportFirstDerivative β (scalarTransportMeasure μ ψ u)
      (scalarRelabelledDirection φ ψ Lψ hψ hψ0 hψ1 u hu) 0=
      scalarTwoTransportAxisDerivative β μ φ ψ u := by
  unfold scalarTransportFirstDerivative scalarTwoTransportAxisDerivative
  simp only [scalarTransportMeasure_zero,scalarLevelTransport_zero]
  congr 1
  rw [scalarTransportMeasure,ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_scalarLevelTransport_parameter ψ u).measurable.aemeasurable]
  · apply integral_congr_ae
    exact .of_forall fun q=>by
      change scalarRelabelledDirection φ ψ Lψ hψ hψ0 hψ1 u hu (scalarLevelTransport ψ u q)*_=φ q*_
      rw [scalarRelabelledDirection_transport]
  · apply Continuous.aestronglyMeasurable
    exact (scalarRelabelledDirection φ ψ Lψ hψ hψ0 hψ1 u hu).continuous.mul
      (continuous_subtype_val.sub ((continuousOn_Gamma β hβ _).comp_continuous
        continuous_subtype_val (fun q=>q.property)))

theorem hasDerivAt_scalarTwoTransportFunctional_first_axis {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (φ ψ : C(Paper.Overlap,ℝ)) (Lφ Lψ : ℝ≥0)
    (hφ : LipschitzWith Lφ φ) (hψ : LipschitzWith Lψ ψ)
    (hφ0 : φ 0=0) (hφ1 : φ 1=0) (hψ0 : ψ 0=0) (hψ1 : ψ 1=0)
    (u : ℝ) (hu : |u| *Lψ<1) :
    HasDerivAt (fun v=>scalarTwoTransportFunctional β (parisiSchemeMeasure s) φ ψ (v,u))
      (scalarTwoTransportAxisDerivative β (parisiSchemeMeasure s) φ ψ u) 0 := by
  let r := scalarTransportScheme s ψ Lψ hψ hψ0 hψ1 u hu
  let Φ := scalarRelabelledDirection φ ψ Lψ hψ hψ0 hψ1 u hu
  let K : ℝ≥0 := Lφ*Real.toNNReal ((1-|u| *Lψ)⁻¹)
  have hΦ : LipschitzWith K Φ := lipschitzWith_scalarRelabelledDirection φ ψ Lφ Lψ hφ hψ hψ0 hψ1 u hu
  obtain ⟨hΦ0,hΦ1⟩ := scalarRelabelledDirection_endpoints φ ψ Lψ hψ hφ0 hφ1 hψ0 hψ1 u hu
  let δ : ℝ := 1/(2*((K:ℝ)+1))
  have hδ : 0<δ := by dsimp only [δ];positivity
  have hsmall : δ*K<1 := by
    dsimp only [δ]
    rw [div_mul_eq_mul_div,one_mul]
    have hden : 0<2*((K:ℝ)+1) := by positivity
    apply (div_lt_iff₀ hden).mpr
    linarith [K.coe_nonneg]
  have hd := hasDerivAt_scalarTransportFunctional r β hβ Φ K hΦ hΦ0 hΦ1 δ 0
    hδ hsmall (by simpa using hδ)
  rw [scalarTransportScheme_measure] at hd
  rw [scalarTwoTransport_relabelled_firstDerivative β hβ.ne' _ φ ψ Lψ hψ hψ0 hψ1 u hu] at hd
  apply hd.congr_of_eventuallyEq
  exact .of_forall fun v=>by
    change scalarParisiFunctional β _=scalarParisiFunctional β _
    rw [scalarTwoTransport_relabelled]

theorem hasDerivAt_scalarTwoTransportAxisDerivative_zero {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (φ ψ : C(Paper.Overlap,ℝ)) (Lψ : ℝ≥0)
    (hψ : LipschitzWith Lψ ψ) (hψ0 : ψ 0=0) (hψ1 : ψ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*Lψ<1) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : parisiSchemeMeasure s∈scalarFloor a) :
    HasDerivAt (scalarTwoTransportAxisDerivative β (parisiSchemeMeasure s) φ ψ)
      (β^2/2*(∫q : Paper.Overlap,φ q*(ψ q-
        scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a ψ q)
        ∂(parisiSchemeMeasure s:Measure Paper.Overlap))) 0 := by
  have hT (q : Paper.Overlap) := hasDerivAt_scalarLevelTransport_coe ψ Lψ hψ hψ0 hψ1 0
    (by simp : |(0:ℝ)| *Lψ<1) q
  have hG (q : Paper.Overlap) := hasDerivAt_scalarTransportGamma_seven_terms s β hβ ψ Lψ hψ hψ0 hψ1
    δ hδ hsmall a ha hμ q
  exact (hasDerivAt_scalarScheme_integral s _ _ 0
    (fun q=>((hT q).sub (hG q)).const_mul (φ q))).const_mul (β^2/2)

end QuantitativeFollowup
