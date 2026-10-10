module
public import QuantitativeFollowup.ScalarTransportObservableFamily

@[expose] public section

/-! Actual spatial Gaussian data for the whole clamped transport family.
Static heat data are proved even outside the increasing neighborhood; the
uniform first envelopes hold on that neighborhood by the exact finite-profile
identification. No joint second parameter differentiability is assumed. -/
noncomputable section
open Set
open scoped BigOperators NNReal ContDiff
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

theorem boundedJets_parisiGradient_spatial (β : ℝ) (μ : Paper.ParisiMeasure)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    BoundedJets (fun x : ℝ=>Paper.parisiGradient β μ (t,x)) := by
  have hh := (boundedPositiveJets_scalarPotential β μ t ht).boundedJets_fderiv_apply (1:ℝ)
  have he : (fun x : ℝ=>fderiv ℝ (fun y=>Paper.parisiPotential β μ (t,y)) x 1)=
      (fun x=>Paper.parisiGradient β μ (t,x)) := by
    funext x
    rw [(Paper.hasDerivAt_parisiPotential_spatial_all β μ t x ht).hasFDerivAt.fderiv]
    simp only [ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,one_mul]
  rwa [he] at hh

theorem boundedPositiveJets_scalarTransportEuclideanExponent (s : RSBScheme k)
    (β : ℝ) (φ : C(Paper.Overlap,ℝ)) (e : Bool) (u : ℝ) :
    BoundedPositiveJets (scalarTransportEuclideanExponent s β φ e u) := by
  have hlin := (boundedPositiveJets_linear
    (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) (Fin.last (k+2)))).const_mul (Paper.spinSign e)
  have hsum := boundedPositiveJets_finite_sum Finset.univ
    (fun i : Fin (k+1)=>fun x : QuantitativePaper.Field (k+3)=>
      (s.m (i+1)-s.m i)*scalarTransportNodePotential s β φ (i+1) u (x ⟨i+1,by omega⟩))
    (fun i _=>((boundedPositiveJets_scalarPotential β
      (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ u)
      (scalarLevelTransport φ u (scalarSchemeTransportNode s (i+1)))
      (scalarLevelTransport φ u (scalarSchemeTransportNode s (i+1))).property).comp_linear
        (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) ⟨i+1,by omega⟩)).const_mul _)
  exact hlin.add hsum.neg

theorem boundedJets_scalarTransportGradientSquare (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (p : Fin (k+3)) (u : ℝ) :
    BoundedJets (scalarTransportGradientSquare s β φ p u) := by
  have h := (boundedJets_parisiGradient_spatial β
    (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ u)
    (scalarLevelTransport φ u (scalarSchemeTransportNode s p))
    (scalarLevelTransport φ u (scalarSchemeTransportNode s p)).property).comp_linear
      (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) p)
  change BoundedJets (fun x : QuantitativePaper.Field (k+3)=>Paper.parisiGradient β
    (scalarTransportMeasure (Paper.parisiSchemeMeasure s) φ u)
    (scalarLevelTransport φ u (scalarSchemeTransportNode s p),x p)^2)
  simpa only [pow_two,Function.comp_def,PiLp.proj_apply] using h.mul h

theorem scalarTransportGaussianWeight_heatData (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (e : Bool) (u : ℝ) :
    Nonempty (VectorHeatDatum (fun x=>Real.exp (scalarTransportEuclideanExponent s β φ e u x))) := by
  simpa only [mul_one] using vectorHeatDatum_of_boundedJets (scalarTransportEuclideanExponent s β φ e u)
    (fun _=>1) (boundedPositiveJets_scalarTransportEuclideanExponent s β φ e u) (boundedJets_const 1)

theorem scalarTransportGaussianSquare_heatData (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (e : Bool) (p : Fin (k+3)) (u : ℝ) :
    Nonempty (VectorHeatDatum (fun x=>Real.exp (scalarTransportEuclideanExponent s β φ e u x)*
      scalarTransportGradientSquare s β φ p u x)) :=
  vectorHeatDatum_of_boundedJets _ _ (boundedPositiveJets_scalarTransportEuclideanExponent s β φ e u)
    (boundedJets_scalarTransportGradientSquare s β φ p u)

theorem norm_scalarTransportGaussianWeight_first_le (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) (e : Bool) (x : QuantitativePaper.Field (k+3)) :
    ‖fderiv ℝ (fun y=>Real.exp (scalarTransportEuclideanExponent s β φ e u y)) x‖≤
      2*Real.exp ‖x‖ := by
  rw [scalarTransportEuclideanExponent_eq_actual s β φ L hφ h0 h1 u hu]
  exact norm_scalarFiniteGaussianWeight_first_le _ _ _ _

theorem norm_scalarTransportGaussianSquare_first_le (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (u : ℝ) (hu : |u| *L<1) (e : Bool) (p : Fin (k+3)) (x : QuantitativePaper.Field (k+3)) :
    ‖fderiv ℝ (fun y=>Real.exp (scalarTransportEuclideanExponent s β φ e u y)*
      scalarTransportGradientSquare s β φ p u y) x‖≤4*Real.exp ‖x‖ := by
  rw [scalarTransportEuclideanExponent_eq_actual s β φ L hφ h0 h1 u hu,
    scalarTransportGradientSquare_eq_actual s β φ L hφ h0 h1 u hu]
  exact norm_scalarFiniteGaussianSquare_first_le _ _ _ _ _

end QuantitativeFollowup
