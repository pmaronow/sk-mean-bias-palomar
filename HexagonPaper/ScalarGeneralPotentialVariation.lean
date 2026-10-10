module
public import HexagonPaper.ScalarTransportCylinder
public import QuantitativeFollowup.ScalarTransportVariationRegularity
public import QuantitativeFollowup.ScalarObservationRefinement
public import Paper.ParisiCDFIntegral
public import FRSB.PotentialMeasureContinuity
public import FRSB.ParisiGridTopology
public import FRSB.GridMeasureIdentification
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

@[expose] public section

/-! The literal scalar node variation at every profile. The CDF jump at the
observed node is retained and cancels the strict-future kernel jump. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace HexagonPaper
open Paper FRSB QuantitativePaper FourPapersCommon SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

 def scalarPotentialVariationKernel (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) (q : Paper.Overlap) (x : ℝ) (r : Paper.Overlap) : ℝ :=
  if q<r then φ r*scalarTransportFutureSquare β μ φ u q r x
  else φ q*parisiGradient β (scalarTransportMeasure μ φ u) ((scalarLevelTransport φ u q:ℝ),x)^2

 theorem scalarPotentialVariationKernel_integral (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) (q : Paper.Overlap) (x : ℝ) :
    (∫r,scalarPotentialVariationKernel β μ φ u q x r ∂(μ:Measure Paper.Overlap))=
      parisiCDF μ q*(φ q*parisiGradient β (scalarTransportMeasure μ φ u)
        ((scalarLevelTransport φ u q:ℝ),x)^2)+
      ∫r in Ioi q,φ r*scalarTransportFutureSquare β μ φ u q r x ∂(μ:Measure Paper.Overlap) := by
  let A := φ q*parisiGradient β (scalarTransportMeasure μ φ u) ((scalarLevelTransport φ u q:ℝ),x)^2
  let F := fun r : Paper.Overlap => φ r*scalarTransportFutureSquare β μ φ u q r x
  have hF : Continuous F := by
    have hf : Continuous (fun r : Paper.Overlap=>scalarTransportFutureSquare β μ φ u q r x) := by
      convert! (continuous_scalarTransportFutureSquare_joint β μ φ).comp
        ((continuous_const (y:=u)).prodMk (continuous_const (y:=x)) |>.prodMk
          ((continuous_const (y:=q)).prodMk continuous_id)) using 1
    convert! φ.continuous.mul hf using 1
  have hiF := hF.integrable_of_hasCompactSupport (μ:= (μ:Measure Paper.Overlap)) (HasCompactSupport.of_compactSpace F)
  have hiA : Integrable (fun _ : Paper.Overlap => A) (μ:Measure Paper.Overlap) := integrable_const A
  have he : (fun r=>scalarPotentialVariationKernel β μ φ u q x r)=
      (Iic q).indicator (fun _=>A)+(Ioi q).indicator F := by
    funext r
    simp only [Pi.add_apply,scalarPotentialVariationKernel,indicator_apply,mem_Iic,mem_Ioi]
    by_cases hr : q<r
    · simp only [hr,not_le_of_gt hr,ite_false,ite_true,zero_add]
      rfl
    · simp only [hr,le_of_not_gt hr,ite_false,ite_true,add_zero]
      rfl
  rw [he]
  change (∫r,((Iic q).indicator (fun _=>A)) r+((Ioi q).indicator F) r ∂(μ:Measure Paper.Overlap))=_
  rw [integral_add (hiA.indicator measurableSet_Iic) (hiF.indicator measurableSet_Ioi),
    integral_indicator measurableSet_Iic,integral_indicator measurableSet_Ioi,setIntegral_const]
  congr 1

 theorem scalarTransportPotentialVariation_eq_regrouped (β : ℝ) (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (u : ℝ) (q : Paper.Overlap) (x : ℝ) :
    scalarTransportPotentialVariation β μ φ u q x=
      -(β^2/2)*(φ q*parisiHessian β (scalarTransportMeasure μ φ u)
        ((scalarLevelTransport φ u q:ℝ),x)+
        ∫r,scalarPotentialVariationKernel β μ φ u q x r ∂(μ:Measure Paper.Overlap)) := by
  rw [scalarPotentialVariationKernel_integral]
  unfold scalarTransportPotentialVariation
  ring

 theorem continuous_scalarTransportPotentialVariation_cylinder (β : ℝ) (hβ : β≠0)
    (φ : C(Paper.Overlap,ℝ)) (δ : ℝ) (q : Paper.Overlap) (x : ℝ) :
    Continuous (fun z : Paper.ParisiMeasure×ScalarTransportParameter δ =>
      scalarTransportPotentialVariation β z.1 φ z.2 q x) := by
  let A := Paper.ParisiMeasure×ScalarTransportParameter δ
  have hm : Continuous (fun z : A => scalarTransportMeasure z.1 φ z.2) :=
    (continuous_scalarTransportMeasure φ).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hq : Continuous (fun z : A => scalarLevelTransport φ z.2 q) :=
    (continuous_scalarLevelTransport φ).comp
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_const)
  have harg : Continuous (fun z : A =>
      (scalarTransportMeasure z.1 φ z.2,((scalarLevelTransport φ z.2 q:ℝ),x))) :=
    hm.prodMk ((continuous_subtype_val.comp hq).prodMk continuous_const)
  have hg := (continuous_parisiGradient_measure_joint β).comp harg
  have hh := (continuous_parisiHessian_measure_joint β hβ).comp harg
  have hFuture : Continuous (fun z : A×Paper.Overlap =>
      scalarTransportFutureSquare β z.1.1 φ z.1.2 q z.2 x) := by
    have hr : Continuous (fun z : A×Paper.Overlap => scalarLevelTransport φ z.1.2 z.2) :=
      (continuous_scalarLevelTransport φ).comp
        ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd)
    have ha : Continuous (fun z : A×Paper.Overlap =>
        (scalarTransportMeasure z.1.1 φ z.1.2,
          (scalarLevelTransport φ z.1.2 q,(scalarLevelTransport φ z.1.2 z.2,x)))) :=
      (hm.comp continuous_fst).prodMk ((hq.comp continuous_fst).prodMk (hr.prodMk continuous_const))
    convert! (continuous_scalarFutureSquareExtended β).comp ha using 1
  have hkernel : Continuous (fun z : A×Paper.Overlap =>
      scalarPotentialVariationKernel β z.1.1 φ z.1.2 q x z.2) := by
    apply Continuous.if _ ((φ.continuous.comp continuous_snd).mul hFuture)
      ((continuous_const.mul (hg.pow 2)).comp continuous_fst)
    intro z hz
    have he : q=z.2 := frontier_lt_subset_eq (f:=fun _ : A×Paper.Overlap => q)
      (g:=Prod.snd) continuous_const continuous_snd hz
    dsimp only [Function.comp_def,Pi.mul_apply,Pi.pow_apply]
    rw [←he,scalarTransportFutureSquare_self β hβ]
  have hI : Continuous (fun z : A => ∫r,
      scalarPotentialVariationKernel β z.1 φ z.2 q x r ∂(z.1:Measure Paper.Overlap)) :=
    continuous_integral_probability_family _ hkernel _ continuous_fst
  have hcont : Continuous (fun z : A=>-(β^2/2)*(φ q*parisiHessian β
      (scalarTransportMeasure z.1 φ z.2) ((scalarLevelTransport φ z.2 q:ℝ),x)+
      ∫r,scalarPotentialVariationKernel β z.1 φ z.2 q x r ∂(z.1:Measure Paper.Overlap))) :=
    continuous_const.mul ((continuous_const.mul hh).add hI)
  convert! hcont using 1
  funext z
  exact scalarTransportPotentialVariation_eq_regrouped β z.1 φ z.2 q x

 theorem hasDerivAt_scalarTransportPotential_finite_at {k : ℕ} (r : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (q : Paper.Overlap) (x u : ℝ)
    (hu : u∈Ioo (-δ) δ) :
    HasDerivAt (fun v=>parisiPotential β (scalarTransportMeasure (parisiSchemeMeasure r) φ v)
      ((scalarLevelTransport φ v q:ℝ),x))
      (scalarTransportPotentialVariation β (parisiSchemeMeasure r) φ u q x) u := by
  obtain ⟨K,t,j,hm,hq⟩ := exists_scalar_same_measure_scheme_node r q
  have hj : (j:ℕ)≤K+2 := by omega
  have he : K+2-(K+2-j)=j := by omega
  have hd := hasDerivAt_scalarTransportNodePotential_variation t β hβ φ L hφ h0 h1
    δ u x hδ hsmall (abs_lt.mpr hu) (K+2-j) (by omega)
  simp only [scalarTransportNodePotential,he,hm,hq] at hd
  exact hd

 theorem hasDerivAt_scalarTransportPotential_general_at (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (q : Paper.Overlap) (x u : ℝ)
    (hu : u∈Ioo (-δ) δ) :
    HasDerivAt (fun v=>parisiPotential β (scalarTransportMeasure μ φ v)
      ((scalarLevelTransport φ v q:ℝ),x))
      (scalarTransportPotentialVariation β μ φ u q x) u := by
  let D : Paper.ParisiMeasure→C(ScalarTransportParameter δ,ℝ) := fun ν =>
    ⟨fun v=>scalarTransportPotentialVariation β ν φ v q x,by
      convert! (continuous_scalarTransportPotentialVariation_cylinder β hβ.ne' φ δ q x).comp
        (continuous_const.prodMk continuous_id) using 1⟩
  have hD : Continuous D := ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_scalarTransportPotentialVariation_cylinder β hβ.ne' φ δ q x)
  have hDU := ContinuousMap.tendsto_iff_tendstoUniformly.mp
    ((hD.tendsto μ).comp (tendsto_parisiGridMeasure μ))
  have hU : TendstoUniformlyOn (fun n v=>scalarTransportPotentialVariation β (parisiGridMeasure μ n) φ v q x)
      (fun v=>scalarTransportPotentialVariation β μ φ v q x) atTop (Icc (-δ) δ) :=
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr hDU
  apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo (hU.mono (Ioo_subset_Icc_self))
    (f:=fun n v=>parisiPotential β (scalarTransportMeasure (parisiGridMeasure μ n) φ v)
      ((scalarLevelTransport φ v q:ℝ),x))
  · exact .of_forall fun n v hv => by
      have hd := hasDerivAt_scalarTransportPotential_finite_at (parisiGridRSBScheme μ n)
        β hβ φ L hφ h0 h1 δ hδ hsmall q x v hv
      simpa only [parisiSchemeMeasure_grid_eq] using hd
  · intro v hv
    have hm := ((continuous_scalarTransportMeasure φ).comp
      (continuous_id.prodMk (continuous_const (y:=v)))).tendsto μ |>.comp (tendsto_parisiGridMeasure μ)
    exact tendsto_parisiPotential_of_weak β (scalarTransportMeasure μ φ v)
      (fun n=>scalarTransportMeasure (parisiGridMeasure μ n) φ v) hm
      (scalarLevelTransport φ v q) x (scalarLevelTransport φ v q).property
  · exact hu

end HexagonPaper
