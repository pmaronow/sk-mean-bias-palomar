module
public import HexagonPaper.CavityMovingCoefficientVarianceMixedNative
public import HexagonPaper.CavityMovingCoefficientIntegral

@[expose] public section

/-! Actual mixed last-coefficient/field differentiation of the native
tail potential. Finite-interval FTC interchanges the two genuine partials;
the response and its spatial differential are constructed internally. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology ContDiff NNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

theorem cavityNativeVarianceResponse_fderiv_field_norm_bound
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (i : Fin n) (x : Field n) :
    ‖fderiv ℝ (fun y=>anisotropicRestartVarianceResponse D μ g q y i) x‖≤
      (1/2 : ℝ)*(4*‖cavityCoordinateFeature i‖^2*‖anisotropicRestartFieldEnergyMap D‖) := by
  let K : ℝ:=(1/2 : ℝ)*(4*‖cavityCoordinateFeature i‖^2*‖anisotropicRestartFieldEnergyMap D‖)
  have hK : 0≤K := by dsimp only [K]; positivity
  have hL : LipschitzWith K.toNNReal (fun y=>anisotropicRestartVarianceResponse D μ g q y i) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [dist_eq_norm,dist_eq_norm,Real.coe_toNNReal _ hK]
    exact cavityNativeVarianceResponse_field_difference_bound D μ g q i y z
  simpa only [Real.coe_toNNReal _ hK] using norm_fderiv_le_of_lipschitz ℝ hL

theorem cavityNativeTailPotential_field_partial_hasDerivAt_variance
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i : Fin n)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x v : Field n)
    (b : ℝ) (hb : 0<b) :
    HasDerivAt (fun u=>fderiv ℝ (anisotropicMeasureTailPotential (anisotropicReplaceVariance D i u) μ q)
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n x) (anisotropicFieldInjection n v))
      (fderiv ℝ (fun y=>anisotropicRestartVarianceResponse (anisotropicReplaceVariance D i b) μ g q y i) x v) b := by
  let F:=fun (u s : ℝ)=>anisotropicMeasureTailPotential (anisotropicReplaceVariance D i u) μ q
    (anisotropicDisorderInjection n g+anisotropicFieldInjection n (x+s • v))
  let P:=fun (u s : ℝ)=>fderiv ℝ (anisotropicMeasureTailPotential (anisotropicReplaceVariance D i u) μ q)
    (anisotropicDisorderInjection n g+anisotropicFieldInjection n (x+s • v)) (anisotropicFieldInjection n v)
  let R:=fun (u s : ℝ)=>anisotropicRestartVarianceResponse (anisotropicReplaceVariance D i u) μ g q (x+s • v) i
  let E:=fun (u s : ℝ)=>fderiv ℝ (fun y=>anisotropicRestartVarianceResponse
    (anisotropicReplaceVariance D i u) μ g q y i) (x+s • v) v
  let K : ℝ:=(1/2 : ℝ)*(4*‖cavityCoordinateFeature i‖^2*‖anisotropicRestartFieldEnergyMap D‖)*‖v‖
  have harg : Continuous (fun z : ℝ×ℝ=>(cavityMovingPositiveExtension b hb z.1,x+z.2 • v)) :=
    ((continuous_cavityMovingPositiveExtension b hb).comp continuous_fst).prodMk
      (continuous_const.add (continuous_snd.smul continuous_const))
  have hR0:= (cavityNativeVarianceResponse_coefficient_field_joint_continuous D μ i g q).comp harg
  have hE0:= ((cavityNativeVarianceResponse_fderiv_coefficient_field_joint_continuous D μ i g q).comp harg).clm_apply
    (continuous_const (y:=v))
  have hR : ContinuousOn (Function.uncurry R) (Ioo (b/2) (b+1)×ˢ(univ : Set ℝ)) := by
    apply hR0.continuousOn.congr
    intro z hz
    simp only [R,Function.uncurry,Function.comp_def,cavityMovingPositiveExtension,max_eq_left hz.1.1.le]
  have hE : ContinuousOn (Function.uncurry E) (Ioo (b/2) (b+1)×ˢ(univ : Set ℝ)) := by
    apply hE0.continuousOn.congr
    intro z hz
    simp only [E,Function.uncurry,Function.comp_def,cavityMovingPositiveExtension,max_eq_left hz.1.1.le]
  have hd:=hasDerivAt_spatialDerivative_of_parameterPartials F P R E (b/2) (b+1) b 0 K
    (by constructor <;> linarith) hR hE
    (fun u hu y=>hasDerivAt_anisotropicMeasureTailPotential_variance_restart D μ i g q (x+y • v) u (by linarith [hu.1]))
    (fun u hu y=>by
      have hpoint : HasDerivAt (fun s=>anisotropicDisorderInjection n g+anisotropicFieldInjection n (x+s • v))
          (anisotropicFieldInjection n v) y := by
        convert ((anisotropicFieldInjection n).hasFDerivAt.comp_hasDerivAt y
          (((hasDerivAt_id y).smul_const v).const_add x)).const_add (anisotropicDisorderInjection n g) using 1
        all_goals first | rfl | simp only [Function.comp_def,id_eq,one_smul]
      exact (((anisotropicMeasureTailPotential_derivative_limit (anisotropicReplaceVariance D i u) μ q).2.differentiable_one _).hasFDerivAt).comp_hasDerivAt y hpoint)
    (fun u hu y=>by
      have hpoint : HasDerivAt (fun s : ℝ=>x+s • v) v y := by
        convert ((hasDerivAt_id y).smul_const v).const_add x using 1
        all_goals first | rfl | simp only [id_eq,one_smul]
      exact (((cavityNativeVarianceResponse_contDiff_one_field (anisotropicReplaceVariance D i u) μ g q i).differentiable_one _).hasFDerivAt).comp_hasDerivAt y hpoint)
    (fun u hu y=>by
      apply ((fderiv ℝ (fun z=>anisotropicRestartVarianceResponse (anisotropicReplaceVariance D i u) μ g q z i) (x+y • v)).le_opNorm v).trans
      have hnorm:=cavityNativeVarianceResponse_fderiv_field_norm_bound (anisotropicReplaceVariance D i u) μ g q i (x+y • v)
      simp only [anisotropicRestartFieldEnergyMap,anisotropicReplaceVariance_energyMap] at hnorm
      exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg v))
  simpa only [P,E,zero_smul,add_zero] using hd

end HexagonPaper
