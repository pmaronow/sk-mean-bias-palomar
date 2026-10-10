module
public import QuantitativeFollowup.ScalarTransportHeatData

@[expose] public section

/-! Actual continuous spatial partials of the transported observable families.
Together with the genuine node parameter derivative these furnish joint first
differentiability, without a joint second parameter regularity assumption. -/
noncomputable section
open Set
open scoped NNReal ContDiff BigOperators
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarTransportNodeHessian (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (i : ℕ) (u x : ℝ) : ℝ :=
  Paper.parisiHessian β (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ u)
    ((scalarLevelTransport φ u (scalarSchemeTransportNode s i):ℝ),x)

theorem continuous_scalarTransportNodeGradient (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (i : ℕ) :
    Continuous (Function.uncurry (scalarTransportNodeGradient s β φ i)) := by
  have hμ : Continuous (fun z : ℝ×ℝ=>scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ z.1) :=
    (continuous_scalarTransportMeasure φ).comp (continuous_const.prodMk continuous_fst)
  have hq : Continuous (fun z : ℝ×ℝ=>(scalarLevelTransport φ z.1 (scalarSchemeTransportNode s i):ℝ)) :=
    continuous_subtype_val.comp ((continuous_scalarLevelTransport φ).comp
      (continuous_fst.prodMk continuous_const))
  change Continuous (fun z : ℝ×ℝ=>Paper.parisiGradient β
    (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ z.1)
    ((scalarLevelTransport φ z.1 (scalarSchemeTransportNode s i):ℝ),z.2))
  let F : ℝ×ℝ→Paper.ParisiMeasure×(ℝ×ℝ) := fun z=>
    (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ z.1,
      ((scalarLevelTransport φ z.1 (scalarSchemeTransportNode s i):ℝ),z.2))
  have hF : Continuous F := hμ.prodMk (hq.prodMk continuous_snd)
  have hc := (continuous_parisiGradient_measure_joint β).comp hF
  convert! hc using 1

theorem continuous_scalarTransportNodeHessian (s : RSBScheme k) (β : ℝ)
    (hβ : β≠0) (φ : C(Paper.Overlap,ℝ)) (i : ℕ) :
    Continuous (Function.uncurry (scalarTransportNodeHessian s β φ i)) := by
  have hμ : Continuous (fun z : ℝ×ℝ=>scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ z.1) :=
    (continuous_scalarTransportMeasure φ).comp (continuous_const.prodMk continuous_fst)
  have hq : Continuous (fun z : ℝ×ℝ=>(scalarLevelTransport φ z.1 (scalarSchemeTransportNode s i):ℝ)) :=
    continuous_subtype_val.comp ((continuous_scalarLevelTransport φ).comp
      (continuous_fst.prodMk continuous_const))
  change Continuous (fun z : ℝ×ℝ=>Paper.parisiHessian β
    (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ z.1)
    ((scalarLevelTransport φ z.1 (scalarSchemeTransportNode s i):ℝ),z.2))
  let F : ℝ×ℝ→Paper.ParisiMeasure×(ℝ×ℝ) := fun z=>
    (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ z.1,
      ((scalarLevelTransport φ z.1 (scalarSchemeTransportNode s i):ℝ),z.2))
  have hF : Continuous F := hμ.prodMk (hq.prodMk continuous_snd)
  have hc := (continuous_parisiHessian_measure_joint β hβ).comp hF
  convert! hc using 1

theorem hasDerivAt_scalarTransportNodePotential_spatial (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (i : ℕ) (u x : ℝ) :
    HasDerivAt (scalarTransportNodePotential s β φ i u)
      (scalarTransportNodeGradient s β φ i u x) x :=
  Paper.hasDerivAt_parisiPotential_spatial_all β _ _ x
    (scalarLevelTransport φ u (scalarSchemeTransportNode s i)).property

theorem hasDerivAt_scalarTransportNodeGradient_spatial (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (i : ℕ) (u x : ℝ) :
    HasDerivAt (scalarTransportNodeGradient s β φ i u)
      (scalarTransportNodeHessian s β φ i u x) x :=
  Paper.hasDerivAt_parisiGradient_spatial_all β _ _ x

theorem scalarTransportEuclideanExponent_fderiv (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (e : Bool) (u : ℝ) (x : QuantitativePaper.Field (k+3)) :
    fderiv ℝ (scalarTransportEuclideanExponent s β φ e u) x=
      Paper.spinSign e • PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) (Fin.last (k+2))-
        ∑i : Fin (k+1),((s.m (i+1)-s.m i)*scalarTransportNodeGradient s β φ (i+1) u (x ⟨i+1,by omega⟩)) •
          PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) ⟨i+1,by omega⟩ := by
  have hnode (i : Fin (k+1)) := ((hasDerivAt_scalarTransportNodePotential_spatial s β φ (i+1) u
    (x ⟨i+1,by omega⟩)).hasFDerivAt.comp x
      (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) ⟨i+1,by omega⟩).hasFDerivAt).const_mul (s.m (i+1)-s.m i)
  have hd := ((PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) (Fin.last (k+2))).hasFDerivAt.const_mul
    (Paper.spinSign e)).sub (HasFDerivAt.fun_sum (u:=Finset.univ) fun i _=>hnode i)
  convert! hd.fderiv using 1
  ext v
  simp only [sub_apply,sum_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,PiLp.proj_apply]
  exact congrArg (fun z : ℝ=>Paper.spinSign e*v (Fin.last (k+2))-z)
    (Finset.sum_congr rfl fun i _=>by ring)

theorem continuous_scalarTransportEuclideanExponent_fderiv (s : RSBScheme k)
    (β : ℝ) (φ : C(Paper.Overlap,ℝ)) (e : Bool) :
    Continuous (fun z : ℝ×QuantitativePaper.Field (k+3)=>
      fderiv ℝ (scalarTransportEuclideanExponent s β φ e z.1) z.2) := by
  simp_rw [scalarTransportEuclideanExponent_fderiv]
  apply continuous_const.sub
  apply continuous_finset_sum
  intro (i : Fin (k+1)) _
  have harg : Continuous (fun z : ℝ×QuantitativePaper.Field (k+3)=>(z.1,z.2 ⟨i+1,by omega⟩)) :=
    continuous_fst.prodMk ((PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) ⟨i+1,by omega⟩).continuous.comp continuous_snd)
  exact (continuous_const.mul ((continuous_scalarTransportNodeGradient s β φ (i+1)).comp harg)).smul continuous_const

theorem scalarTransportGradientSquare_fderiv (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (p : Fin (k+3)) (u : ℝ) (x : QuantitativePaper.Field (k+3)) :
    fderiv ℝ (scalarTransportGradientSquare s β φ p u) x=
      (2*scalarTransportNodeGradient s β φ p u (x p)*scalarTransportNodeHessian s β φ p u (x p)) •
        PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) p := by
  have hd := ((hasDerivAt_scalarTransportNodeGradient_spatial s β φ p u (x p)).hasFDerivAt.comp x
    (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) p).hasFDerivAt).pow 2
  convert! hd.fderiv using 1
  ext v
  simp only [smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,PiLp.proj_apply,pow_one,Function.comp_def]
  ring

theorem continuous_scalarTransportGradientSquare_fderiv (s : RSBScheme k)
    (β : ℝ) (hβ : β≠0) (φ : C(Paper.Overlap,ℝ)) (p : Fin (k+3)) :
    Continuous (fun z : ℝ×QuantitativePaper.Field (k+3)=>
      fderiv ℝ (scalarTransportGradientSquare s β φ p z.1) z.2) := by
  simp_rw [scalarTransportGradientSquare_fderiv]
  have harg : Continuous (fun z : ℝ×QuantitativePaper.Field (k+3)=>(z.1,z.2 p)) :=
    continuous_fst.prodMk ((PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) p).continuous.comp continuous_snd)
  exact ((continuous_const.mul ((continuous_scalarTransportNodeGradient s β φ p).comp harg)).mul
    ((continuous_scalarTransportNodeHessian s β hβ φ p).comp harg)).smul continuous_const

end QuantitativeFollowup
