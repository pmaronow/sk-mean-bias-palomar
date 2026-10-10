module
public import FourPapersCommon.SmoothDirectionalCommutation
public import FourPapersCommon.PartialFDerivSmooth

@[expose] public section

/-! Commutation of actual parameter and spatial partial derivatives. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {A E F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

def partialParamDerivative (v : A) (U : A×E→F) (z : A×E) : F:=
  fderiv ℝ (fun a=>U (a,z.2)) z.1 v

def partialSpatialDerivative (w : E) (U : A×E→F) (z : A×E) : F:=
  fderiv ℝ (fun x=>U (z.1,x)) z.2 w

theorem partialParamDerivative_eq (v : A) (U : A×E→F) (z : A×E)
    (hU : DifferentiableAt ℝ U z) :
    partialParamDerivative v U z=directionDerivative (v,0) U z := by
  change DifferentiableAt ℝ U (z.1,z.2) at hU
  have hk : HasFDerivAt (fun a : A=>(a,z.2)) (ContinuousLinearMap.inl ℝ A E) z.1:=by
    convert (hasFDerivAt_id (𝕜 := ℝ) z.1).prodMk
      (hasFDerivAt_const z.2 z.1) using 1 <;> first | rfl | (ext w; simp)
  have hd : HasFDerivAt (fun a : A=>U (a,z.2))
      ((fderiv ℝ U (z.1,z.2)).comp (ContinuousLinearMap.inl ℝ A E)) z.1:=
    hU.hasFDerivAt.comp z.1 hk
  have he:=congrArg (fun L : A→L[ℝ]F=>L v) hd.fderiv
  simpa only [partialParamDerivative,directionDerivative,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply,ContinuousLinearMap.inl_apply,Prod.mk.eta] using he

theorem partialSpatialDerivative_eq (w : E) (U : A×E→F) (z : A×E)
    (hU : DifferentiableAt ℝ U z) :
    partialSpatialDerivative w U z=directionDerivative (0,w) U z := by
  rw [partialSpatialDerivative,partial_fderiv_eq U z.1 z.2 hU]
  rfl

theorem contDiffAt_partialParamDerivative (v : A) (U : A×E→F) (z : A×E)
    (hU : ContDiffAt ℝ ∞ U z) :
    ContDiffAt ℝ ∞ (partialParamDerivative v U) z := by
  apply (contDiffAt_directionDerivative U z (v,0) hU).congr_of_eventuallyEq
  filter_upwards [(hU.of_le (by norm_num : (1 : ℕ∞ω)≤∞)).eventually (by norm_num)] with y hy
  exact partialParamDerivative_eq v U y (hy.differentiableAt (by norm_num))

theorem contDiffAt_partialSpatialDerivative (w : E) (U : A×E→F) (z : A×E)
    (hU : ContDiffAt ℝ ∞ U z) :
    ContDiffAt ℝ ∞ (partialSpatialDerivative w U) z := by
  apply (contDiffAt_directionDerivative U z (0,w) hU).congr_of_eventuallyEq
  filter_upwards [(hU.of_le (by norm_num : (1 : ℕ∞ω)≤∞)).eventually (by norm_num)] with y hy
  exact partialSpatialDerivative_eq w U y (hy.differentiableAt (by norm_num))

theorem partialParamSpatialDerivative_commute_of_two (v : A) (w : E) (U : A×E→F)
    (z : A×E) (hU : ContDiffAt ℝ 2 U z) :
    partialParamDerivative v (partialSpatialDerivative w U) z=
      partialSpatialDerivative w (partialParamDerivative v U) z := by
  have hs : partialSpatialDerivative w U=ᶠ[𝓝 z]directionDerivative (0,w) U:=by
    filter_upwards [(hU.of_le (by norm_num : (1 : ℕ∞ω)≤2)).eventually (by norm_num)] with y hy
    exact partialSpatialDerivative_eq w U y (hy.differentiableAt (by norm_num))
  have hp : partialParamDerivative v U=ᶠ[𝓝 z]directionDerivative (v,0) U:=by
    filter_upwards [(hU.of_le (by norm_num : (1 : ℕ∞ω)≤2)).eventually (by norm_num)] with y hy
    exact partialParamDerivative_eq v U y (hy.differentiableAt (by norm_num))
  have hD := ((hU.fderiv_right (by norm_num : (1 : ℕ∞ω)+1≤2)).differentiableAt
    (by norm_num)).hasFDerivAt
  have hds := (hD.clm_apply (hasFDerivAt_const (0,w) z)).congr_of_eventuallyEq hs
  have hdp := (hD.clm_apply (hasFDerivAt_const (v,0) z)).congr_of_eventuallyEq hp
  rw [partialParamDerivative_eq v _ z hds.differentiableAt,
    partialSpatialDerivative_eq w _ z hdp.differentiableAt]
  unfold directionDerivative
  rw [hds.fderiv,hdp.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply,map_zero,zero_add,add_zero,ContinuousLinearMap.flip_apply]
  exact (hU.isSymmSndFDerivAt (by norm_num)).eq (v,0) (0,w)

theorem partialParamSpatialDerivative_commute (v : A) (w : E) (U : A×E→F)
    (z : A×E) (hU : ContDiffAt ℝ ∞ U z) :
    partialParamDerivative v (partialSpatialDerivative w U) z=
      partialSpatialDerivative w (partialParamDerivative v U) z :=
  partialParamSpatialDerivative_commute_of_two v w U z (hU.of_le (by norm_num))

theorem partialParamSpatialDerivative_commute_third (v : A) (w z' : E)
    (U : A×E→F) (z : A×E) (hU : ContDiffAt ℝ ∞ U z) :
    partialParamDerivative v (partialSpatialDerivative w (partialSpatialDerivative z' U)) z=
      partialSpatialDerivative w (partialSpatialDerivative z' (partialParamDerivative v U)) z := by
  rw [partialParamSpatialDerivative_commute v w _ z
    (contDiffAt_partialSpatialDerivative z' U z hU)]
  have he : partialParamDerivative v (partialSpatialDerivative z' U)=ᶠ[𝓝 z]
      partialSpatialDerivative z' (partialParamDerivative v U):=by
    filter_upwards [(hU.of_le (by norm_num : (3 : ℕ∞ω)≤∞)).eventually (by norm_num)] with y hy
    exact partialParamSpatialDerivative_commute_of_two v z' U y (hy.of_le (by norm_num))
  change fderiv ℝ (fun x=>partialParamDerivative v (partialSpatialDerivative z' U) (z.1,x)) z.2 w=_
  have he' : (fun x=>partialParamDerivative v (partialSpatialDerivative z' U) (z.1,x))=ᶠ[𝓝 z.2]
      (fun x=>partialSpatialDerivative z' (partialParamDerivative v U) (z.1,x)):=
    ((continuous_const.prodMk continuous_id).tendsto z.2).eventually he
  exact congrArg (fun L : E→L[ℝ]F=>L w) he'.fderiv_eq

end FourPapersCommon
