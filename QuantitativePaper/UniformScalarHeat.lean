module
public import Paper.GaussianConvolution
public import Paper.HeatGradient
public import Paper.GaussianIBP

@[expose] public section

/-! Two genuine heat-gradient estimates used by time cutoffs. The second
estimate moves both derivatives onto independent Gaussian kernels, so its
constant depends on the observable bound and not on its derivative bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativePaper
open Paper
set_option maxHeartbeats 1800000

theorem hasDerivAt_scalar_heat_by_data (v : ℝ) (f df : ℝ→ℝ) (M K x : ℝ)
    (hf : Continuous f) (hdf : Continuous df) (hd : ∀y,HasDerivAt f (df y) y)
    (hb : ∀y,‖f y‖≤M) (hdb : ∀y,‖df y‖≤K) :
    HasDerivAt (heatSemigroup v f) (heatSemigroup v df x) x := by
  exact hasDerivAt_gaussian_shift f df (Real.sqrt v) x K hf hdf
    (integrable_heatSemigroup_integrand v f hf.measurable M hb x) hd hdb

theorem hasDerivAt_scalar_heatGradient_by_data (v : ℝ) (f df : ℝ→ℝ) (M K x : ℝ)
    (hf : Continuous f) (hdf : Continuous df) (hd : ∀y,HasDerivAt f (df y) y)
    (hb : ∀y,‖f y‖≤M) (hdb : ∀y,‖df y‖≤K) :
    HasDerivAt (heatGradient v f) (heatGradient v df x) x := by
  have hc (b : ℝ) : Continuous (fun z : ℝ=>b+Real.sqrt v*z) := by fun_prop
  have hi := integrable_heatGradient_integrand v f hf.measurable M hb x
  have hD := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=gaussianReal 0 1) (F:=fun b z : ℝ=>z*f (b+Real.sqrt v*z))
    (F':=fun b z : ℝ=>z*df (b+Real.sqrt v*z))
    (bound:=fun z : ℝ=>‖z‖*K) (s:=univ) (by simp)
    (.of_forall fun b=>(continuous_id.mul (hf.comp (hc b))).aestronglyMeasurable) hi
    (continuous_id.mul (hdf.comp (hc x))).aestronglyMeasurable
    (.of_forall fun z b _=>by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hdb _) (norm_nonneg z))
    (integrable_standardGaussian_id.norm.mul_const K)
    (.of_forall fun z b _=>(hd (b+Real.sqrt v*z)).comp_add_const b
      (Real.sqrt v*z) |>.const_mul z)).2
  exact hD.const_mul (Real.sqrt v)⁻¹

theorem scalar_heat_derivative_eq (v : ℝ) (hv : 0<v)
    (f df : ℝ → ℝ) (M K : ℝ) (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀x,HasDerivAt f (df x) x)
    (hb : ∀x,‖f x‖≤M) (hdb : ∀x,‖df x‖≤K) (x : ℝ) :
    heatSemigroup v df x=heatGradient v f x := by
  have he:=gaussian_affine_stein f df x (Real.sqrt v) M K hf hdf hd hb hdb
  unfold heatGradient heatSemigroup
  rw [he]
  rw [← mul_assoc,inv_mul_cancel₀ (Real.sqrt_pos.mpr hv).ne',one_mul]

theorem scalar_heat_second_derivative_bound (v : ℝ) (hv : 0<v)
    (f df : ℝ → ℝ) (M K : ℝ) (hf : Continuous f) (hdf : Continuous df)
    (hd : ∀x,HasDerivAt f (df x) x)
    (hb : ∀x,‖f x‖≤M) (hdb : ∀x,‖df x‖≤K) (x : ℝ) :
    ‖heatGradient v df x‖≤2*gaussianAbsMoment^2*M/v := by
  have hvh : 0<v/2:=half_pos hv
  have hM : 0≤M :=(norm_nonneg (f 0)).trans (hb 0)
  have hinner : ∀y,‖heatSemigroup (v/2) df y‖≤K :=
    fun y=>norm_heatSemigroup_le _ _ _ hdb y
  have hsemi : (fun y=>heatSemigroup v df y)=
      (fun y=>heatSemigroup (v/2) (heatSemigroup (v/2) df) y) := by
    funext y
    simpa only [add_halves] using
      (heatSemigroup_add (v/2) (v/2) hvh.le hvh.le df hdf.measurable K hdb y).symm
  have hD1:=hasDerivAt_heatSemigroup_spatial v hv df hdf.measurable K hdb x
  have hD2:=hasDerivAt_heatSemigroup_spatial (v/2) hvh
    (heatSemigroup (v/2) df)
    (show Measurable (heatSemigroup (v/2) df) from
      (continuous_iff_continuousAt.mpr (fun y=>
        (hasDerivAt_heatSemigroup_spatial (v/2) hvh df hdf.measurable K hdb y).continuousAt)).measurable)
    K hinner x
  have hD2' : HasDerivAt (fun y=>heatSemigroup v df y)
      (heatGradient (v/2) (heatSemigroup (v/2) df) x) x := by
    rw [hsemi]
    exact hD2
  have he : heatGradient v df x=
      heatGradient (v/2) (heatSemigroup (v/2) df) x :=
    HasDerivAt.unique hD1 hD2'
  have hm : ∀y,‖heatSemigroup (v/2) df y‖≤
      (Real.sqrt (v/2))⁻¹*gaussianAbsMoment*M := by
    intro y
    rw [scalar_heat_derivative_eq (v/2) hvh f df M K hf hdf hd hb hdb y]
    exact norm_heatGradient_le _ _ _ hb y
  rw [he]
  have hbound:=norm_heatGradient_le (v/2) (heatSemigroup (v/2) df)
    ((Real.sqrt (v/2))⁻¹*gaussianAbsMoment*M) hm x
  have hs : (Real.sqrt (v/2))^2=v/2:=Real.sq_sqrt hvh.le
  have hsn : Real.sqrt (v/2)≠0:=(Real.sqrt_pos.mpr hvh).ne'
  apply hbound.trans_eq
  calc
    (Real.sqrt (v/2))⁻¹*gaussianAbsMoment*
        ((Real.sqrt (v/2))⁻¹*gaussianAbsMoment*M)=
        gaussianAbsMoment^2*M/(Real.sqrt (v/2))^2 := by field_simp
    _ = _ := by rw [hs]; field_simp

end QuantitativePaper
