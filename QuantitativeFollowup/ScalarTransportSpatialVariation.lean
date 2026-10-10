module
public import QuantitativeFollowup.ScalarTransportVariationRegularity

@[expose] public section

/-! The literal spatial derivative of the actual transported-potential
variation. The future integral is differentiated using the actual Picard
flow derivative and its uniform bound, not a mixed-partial premise. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FRSB
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon
set_option maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def scalarTransportPotentialVariationSpatial (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) (q : Paper.Overlap) (x : ℝ) : ℝ :=
  -(β^2/2)*(
    φ q*(FRSB.parisiSpatialJet β (scalarTransportMeasure μ φ u) 3 (scalarLevelTransport φ u q) x+
      2*Paper.parisiCDF μ q*Paper.parisiGradient β (scalarTransportMeasure μ φ u)
        ((scalarLevelTransport φ u q:ℝ),x)*Paper.parisiHessian β (scalarTransportMeasure μ φ u)
        ((scalarLevelTransport φ u q:ℝ),x))+
    ∫r in Ioi q,φ r*scalarTransportFutureSquareSpatial β μ φ u q r x ∂(μ:Measure Paper.Overlap))

theorem continuous_scalarTransportPotentialVariationSpatial (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (φ : C(Paper.Overlap,ℝ)) (q : Paper.Overlap) :
    Continuous (fun z : ℝ×ℝ=>scalarTransportPotentialVariationSpatial β μ φ z.1 q z.2) := by
  have hμ : Continuous (fun z : ℝ×ℝ=>scalarTransportMeasure μ φ z.1) :=
    (continuous_scalarTransportMeasure φ).comp (continuous_const.prodMk continuous_fst)
  have hq : Continuous (fun z : ℝ×ℝ=>(scalarLevelTransport φ z.1 q:ℝ)) :=
    continuous_subtype_val.comp ((continuous_scalarLevelTransport φ).comp (continuous_fst.prodMk continuous_const))
  have harg : Continuous (fun z : ℝ×ℝ=>
      (scalarTransportMeasure μ φ z.1,((scalarLevelTransport φ z.1 q:ℝ),z.2))) :=
    hμ.prodMk (hq.prodMk continuous_snd)
  have h3 := (continuous_parisiSpatialJet_measure_joint_succ β 2).comp harg
  have hM := (continuous_parisiGradient_measure_joint β).comp harg
  have hH := (continuous_parisiHessian_measure_joint β hβ).comp harg
  have hi : Continuous (fun z : ℝ×ℝ=>
      ∫r in Ioi q,φ r*scalarTransportFutureSquareSpatial β μ φ z.1 q r z.2 ∂(μ:Measure Paper.Overlap)) := by
    have hf : Continuous (fun z : (ℝ×ℝ)×Paper.Overlap=>
        φ z.2*scalarTransportFutureSquareSpatial β μ φ z.1.1 q z.2 z.1.2) := by
      have ha : Continuous (fun z : (ℝ×ℝ)×Paper.Overlap=>(z.1,(q,z.2))) := by fun_prop
      have hg : Continuous (fun z : (ℝ×ℝ)×Paper.Overlap =>
          scalarTransportFutureSquareSpatial β μ φ z.1.1 q z.2 z.1.2) := by
        simpa only [Function.comp_def] using
          (continuous_scalarTransportFutureSquareSpatial_joint β hβ μ φ).comp ha
      exact (φ.continuous.comp continuous_snd).mul hg
    apply continuous_of_dominated (μ:=(μ:Measure Paper.Overlap).restrict (Ioi q))
      (bound:=fun _=>‖φ‖*(2*Real.exp (β^2)))
    · intro z
      exact (hf.comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable
    · intro z
      exact .of_forall fun r=>by
        rw [norm_mul]
        exact mul_le_mul (φ.norm_coe_le_norm r)
          (scalarTransportFutureSquareSpatial_norm_le β μ φ z.1 q r z.2)
          (norm_nonneg _) (norm_nonneg _)
    · exact integrable_const _
    · exact .of_forall fun r=>hf.comp (continuous_id.prodMk continuous_const)
  simpa only [scalarTransportPotentialVariationSpatial,Function.comp_def,Pi.add_apply,Pi.mul_apply,Nat.reduceAdd] using
    (((h3.add ((hM.const_mul (2*Paper.parisiCDF μ q)).mul hH)).const_mul (φ q)).add hi).const_mul (-(β^2/2))

theorem hasDerivAt_scalarTransportPotentialVariation_spatial (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| * L < 1) (q : Paper.Overlap) (x : ℝ) :
    HasDerivAt (scalarTransportPotentialVariation β μ φ u q)
      (scalarTransportPotentialVariationSpatial β μ φ u q x) x := by
  let ν:Measure Paper.Overlap:=(μ:Measure Paper.Overlap).restrict (Ioi q)
  let F:=fun y r=>φ r*scalarTransportFutureSquare β μ φ u q r y
  let E:=fun y r=>φ r*scalarTransportFutureSquareSpatial β μ φ u q r y
  have hFc (y : ℝ) : Continuous (F y) := by
    have ha : Continuous (fun r : Paper.Overlap=>((u,y),(q,r))) := by fun_prop
    have hg : Continuous (fun r : Paper.Overlap => scalarTransportFutureSquare β μ φ u q r y) := by
      simpa only [Function.comp_def] using (continuous_scalarTransportFutureSquare_joint β μ φ).comp ha
    exact φ.continuous.mul hg
  have hEc (y : ℝ) : Continuous (E y) := by
    have ha : Continuous (fun r : Paper.Overlap=>((u,y),(q,r))) := by fun_prop
    have hg : Continuous (fun r : Paper.Overlap => scalarTransportFutureSquareSpatial β μ φ u q r y) := by
      simpa only [Function.comp_def] using (continuous_scalarTransportFutureSquareSpatial_joint β hβ μ φ).comp ha
    exact φ.continuous.mul hg
  have hFi : Integrable (F x) ν :=
    (integrable_const ‖φ‖).mono' (hFc x).measurable.aestronglyMeasurable
      (.of_forall fun r=>by
        rw [norm_mul]
        exact (mul_le_mul (φ.norm_coe_le_norm r) (scalarTransportFutureSquare_norm_le β μ φ u q r x)
          (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _))
  have hdiff : ∀ᵐ r ∂ν,∀y∈(univ:Set ℝ),HasDerivAt (fun z=>F z r) (E y r) y := by
    filter_upwards [ae_restrict_mem isOpen_Ioi.measurableSet] with r hr
    intro y hy
    exact (hasDerivAt_scalarTransportFutureSquare_spatial β hβ μ φ L hφ h0 h1 u hu q r hr.le y).const_mul (φ r)
  have hi := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=F) (F':=E) (bound:=fun _=>‖φ‖*(2*Real.exp (β^2))) (s:=univ) (by simp)
    (.of_forall fun y=>(hFc y).measurable.aestronglyMeasurable) hFi
    (hEc x).measurable.aestronglyMeasurable
    (.of_forall fun r y hy=>by
      rw [norm_mul]
      exact mul_le_mul (φ.norm_coe_le_norm r)
        (scalarTransportFutureSquareSpatial_norm_le β μ φ u q r y)
          (norm_nonneg _) (norm_nonneg _)) (integrable_const _) hdiff).2
  have hH : HasDerivAt (fun y=>Paper.parisiHessian β (scalarTransportMeasure μ φ u)
      ((scalarLevelTransport φ u q:ℝ),y))
      (FRSB.parisiSpatialJet β (scalarTransportMeasure μ φ u) 3 (scalarLevelTransport φ u q) x) x := by
    simpa only [Nat.reduceAdd,FRSB.parisiSpatialJet_two] using FRSB.hasDerivAt_parisiSpatialJet_succ β
      (scalarTransportMeasure μ φ u) 1 (scalarLevelTransport φ u q) x
  have hM := (Paper.hasDerivAt_parisiGradient_spatial_all β (scalarTransportMeasure μ φ u)
    (scalarLevelTransport φ u q) x).pow 2
  have hd := ((hH.add (hM.const_mul (Paper.parisiCDF μ q))).const_mul (φ q)).add hi
  convert hd.const_mul (-(β^2/2)) using 1 <;>
    dsimp only [scalarTransportPotentialVariation,scalarTransportPotentialVariationSpatial,
      F,E,ν] <;> first | rfl | ring

end QuantitativeFollowup
