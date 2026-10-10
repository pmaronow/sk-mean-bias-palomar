module
public import QuantitativeFollowup.IntegralFlowDerivative
public import QuantitativeFollowup.ScalarRestartKernel
public import Paper.ParisiCurvature

@[expose] public section

/-! The actual scalar restart has its genuine initial-field derivative,
including arbitrary atomic or continuous Parisi measures. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

def scalarRestartDriftField (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (r x : ℝ) : ℝ :=
  β^2*parisiCDF (parisiRestartMeasure μ a ha) r*parisiGradient β μ (a+r,x)

def scalarRestartDriftDerivative (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (r x : ℝ) : ℝ :=
  β^2*parisiCDF (parisiRestartMeasure μ a ha) r*parisiHessian β μ (a+r,x)

theorem scalarRestartDriftField_data (β : ℝ) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) :
    Paper.IsBoundedMeasurableDrift (scalarRestartDriftField β μ a ha)
      (parisiDriftConstant β) (parisiDriftConstant β) := by
  have he : parisiNoiseDrift β (parisiRestartMeasure μ a ha)
      (parisiRestartGradient β μ a) (fun _ => 0) = scalarRestartDriftField β μ a ha := by
    funext r x
    simp only [parisiNoiseDrift,mul_zero,add_zero,parisiRestartGradient,scalarRestartDriftField]
  rw [← he]
  exact isBoundedMeasurableDrift_parisiNoiseDrift β (parisiRestartMeasure μ a ha)
      (parisiRestartGradient β μ a) (continuous_parisiRestartGradient β μ a)
      (norm_parisiRestartGradient_le_one β μ a) (lipschitzWith_parisiRestartGradient β μ a)
      (fun _ => 0) continuous_const

theorem measurable_scalarRestartDriftDerivative (β : ℝ) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) :
    Measurable (Function.uncurry (scalarRestartDriftDerivative β μ a ha)) :=
  (measurable_const.mul ((parisiCDF_measurable _).comp measurable_fst)).mul
    ((continuous_parisiHessian_all β μ).measurable.comp
      ((measurable_const.add measurable_fst).prodMk measurable_snd))

theorem norm_scalarRestartDriftDerivative_le (β : ℝ) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) (r x : ℝ) :
    ‖scalarRestartDriftDerivative β μ a ha r x‖ ≤ parisiDriftConstant β := by
  change ‖β^2*parisiCDF (parisiRestartMeasure μ a ha) r*parisiHessian β μ (a+r,x)‖ ≤ β^2
  rw [norm_mul,Real.norm_of_nonneg (mul_nonneg (sq_nonneg β) (parisiCDF_nonneg _ _))]
  exact (mul_le_mul_of_nonneg_left (norm_parisiHessian_le_one_all β μ _)
    (mul_nonneg (sq_nonneg β) (parisiCDF_nonneg _ _))).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (parisiCDF_le_one _ _) (sq_nonneg β))

theorem hasDerivAt_scalarRestartDriftField (β : ℝ) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) (r x : ℝ) :
    HasDerivAt (scalarRestartDriftField β μ a ha r)
      (scalarRestartDriftDerivative β μ a ha r x) x :=
  (hasDerivAt_parisiGradient_spatial_all β μ (a+r) x).const_mul _

theorem scalarRestartDriftDerivative_lipschitz (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a) (r : ℝ) :
    LipschitzWith (14*parisiDriftConstant β) (scalarRestartDriftDerivative β μ a ha r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (β^2*parisiCDF (parisiRestartMeasure μ a ha) r*parisiHessian β μ (a+r,x))
    (β^2*parisiCDF (parisiRestartMeasure μ a ha) r*parisiHessian β μ (a+r,y)) ≤ _
  rw [dist_eq_norm,←mul_sub,norm_mul,
    Real.norm_of_nonneg (mul_nonneg (sq_nonneg β) (parisiCDF_nonneg _ _))]
  have hl := (lipschitzWith_parisiHessian β hβ μ (a+r)).dist_le_mul x y
  rw [dist_eq_norm] at hl
  have hc : β^2*parisiCDF (parisiRestartMeasure μ a ha) r ≤ β^2 :=
    (mul_le_mul_of_nonneg_left (parisiCDF_le_one _ _) (sq_nonneg β)).trans_eq (mul_one _)
  exact (mul_le_mul hc hl (norm_nonneg _) (sq_nonneg β)).trans_eq (by
    change β^2*((14 : ℝ)*dist x y)=(14 : ℝ)*β^2*dist x y
    ring)

def scalarRestartFlow (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (x : ℝ) (W : C(Paper.Overlap,ℝ)) : ℝ → ℝ :=
  parisiStateReal β x (parisiRestartMeasure μ a ha) (parisiRestartGradient β μ a)
    (continuous_parisiRestartGradient β μ a) (norm_parisiRestartGradient_le_one β μ a)
    (lipschitzWith_parisiRestartGradient β μ a) 1 zero_le_one
      (parisiNoiseExtension zero_le_one W) (continuous_parisiNoiseExtension zero_le_one W)

def scalarRestartFlowJacobian (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (x : ℝ) (W : C(Paper.Overlap,ℝ)) (t : ℝ) : ℝ :=
  Real.exp (∫ s in 0..t,scalarRestartDriftDerivative β μ a ha s
    (scalarRestartFlow β μ a ha x W s))

theorem continuous_scalarRestartFlow (β : ℝ) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) (x : ℝ) (W : C(Paper.Overlap,ℝ)) :
    Continuous (scalarRestartFlow β μ a ha x W) :=
  continuous_parisiStateReal β x _ _ _ _ _ _ _ _ _

theorem scalarRestartFlow_equation (β : ℝ) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) (x : ℝ) (W : C(Paper.Overlap,ℝ))
    (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) :
    scalarRestartFlow β μ a ha x W t=x+β*parisiNoiseExtension zero_le_one W t+
      ∫ s in 0..t,scalarRestartDriftField β μ a ha s (scalarRestartFlow β μ a ha x W s) :=
  parisiStateReal_integral_equation β x _ _ _ _ _ _ _ _ _ ht

theorem hasDerivAt_scalarRestartFlow_initial (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a) (x : ℝ)
    (W : C(Paper.Overlap,ℝ)) (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) :
    HasDerivAt (fun y => scalarRestartFlow β μ a ha y W t)
      (scalarRestartFlowJacobian β μ a ha x W t) x :=
  hasDerivAt_integral_flow_initial (scalarRestartDriftField β μ a ha)
    (scalarRestartDriftDerivative β μ a ha) (parisiDriftConstant β) (parisiDriftConstant β)
    (14*parisiDriftConstant β) (scalarRestartDriftField_data β μ a ha)
    (measurable_scalarRestartDriftDerivative β μ a ha) (norm_scalarRestartDriftDerivative_le β μ a ha)
    (hasDerivAt_scalarRestartDriftField β μ a ha) (scalarRestartDriftDerivative_lipschitz β hβ μ a ha)
    1 zero_le_one (fun s => β*parisiNoiseExtension zero_le_one W s)
    (fun y => scalarRestartFlow β μ a ha y W) (fun y => continuous_scalarRestartFlow β μ a ha y W)
    (fun y s hs => scalarRestartFlow_equation β μ a ha y W s hs) x t ht

theorem scalarRestartFlowJacobian_pos_le (β : ℝ) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) (x : ℝ) (W : C(Paper.Overlap,ℝ))
    (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) :
    0 < scalarRestartFlowJacobian β μ a ha x W t ∧
      scalarRestartFlowJacobian β μ a ha x W t ≤ Real.exp (β^2) := by
  refine ⟨Real.exp_pos _,Real.exp_le_exp.mpr ?_⟩
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := t) (C := β^2)
    (fun s _ => norm_scalarRestartDriftDerivative_le β μ a ha s (scalarRestartFlow β μ a ha x W s))
  simp only [sub_zero,abs_of_nonneg ht.1,Real.norm_eq_abs] at hi
  exact (le_abs_self _).trans (hi.trans (by nlinarith [sq_nonneg β,ht.2]))

theorem scalarPhysicalRestartEndpoint_eq_flow (β : ℝ) (μ : Paper.ParisiMeasure)
    (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q) (x : ℝ) (W : C(Paper.Overlap,ℝ)) :
    parisiPhysicalRestartEndpoint β μ r q hrq (x,W)=
      scalarRestartFlow β μ r r.property.1 x W ((q : ℝ)-r) := by
  simp only [parisiPhysicalRestartEndpoint,parisiRestartNoiseStatePath,parisiStatePath_apply,
    scalarRestartFlow,parisiElapsedOverlap]

theorem hasDerivAt_scalarPhysicalRestartEndpoint_initial (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (r q : Paper.Overlap) (hrq : (r : ℝ) ≤ q)
    (x : ℝ) (W : C(Paper.Overlap,ℝ)) :
    HasDerivAt (fun y => parisiPhysicalRestartEndpoint β μ r q hrq (y,W))
      (scalarRestartFlowJacobian β μ r r.property.1 x W ((q : ℝ)-r)) x := by
  have ht : (q : ℝ)-r∈Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr hrq,by linarith [q.property.2,r.property.1]⟩
  simpa only [scalarPhysicalRestartEndpoint_eq_flow] using
    hasDerivAt_scalarRestartFlow_initial β hβ μ r r.property.1 x W ((q : ℝ)-r) ht

end QuantitativeFollowup
