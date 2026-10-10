module
public import FourPapersCommon.GaussianLocalizedCurvature

@[expose] public section

/-! Genuine normalized Gaussian tilt version of the localization bound.
Every Gaussian exponential moment and normalization is proved here. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 1600000
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "P" => SYK.standardGaussianMeasureOnEuclidean ι

theorem gaussian_tilted_curvature_lower (V m H : E→ℝ)
    (hV : ContDiff ℝ 1 V) (hm : ContDiff ℝ 1 m) (hH : Continuous H)
    (K B : ℝ) (hK : 0<K) (hHbound : ∀x,|H x|≤B)
    (hDV : ∀x,‖fderiv ℝ V x‖≤K) (hDm : ∀x,‖fderiv ℝ m x‖≤H x)
    (hmb : ∀x,|m x|≤1) (hdiag : ∀x,1-|m x|≤H x)
    (heven : ∀x,V (-x)=V x) (hodd : ∀x,m (-x)= -m x) :
    Real.exp (-8*Real.sqrt (Real.pi/2)*K-K^2/2)/(2*(1+Real.sqrt (Real.pi/2))) ≤
      (∫x,Real.exp (V x-∫y,V y ∂P)*H x ∂P)/(∫x,Real.exp (V x-∫y,V y∂P)∂P) := by
  let c:=Real.sqrt (Real.pi/2)
  let R:=4*c*K
  let chi:=gaussianCurvatureLocalization V K
  let W:=fun x:E=>Real.exp (V x-∫y,V y∂P)
  let Z:=∫x,W x∂P
  have hc : 0<c := Real.sqrt_pos.2 (by positivity)
  have hR : 0<R := by dsimp [R];positivity
  have hLip : LipschitzWith K.toNNReal V := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hV.differentiable (by norm_num))
    intro x
    rw [←NNReal.coe_le_coe,coe_nnnorm,Real.coe_toNNReal K hK.le]
    exact hDV x
  have hWi : Integrable W P := by
    simpa only [one_mul] using
      (SYK.product_standardGaussian_hasSubgaussianMGF V K hK hLip).integrable_exp_mul 1
  have hZpos : 0<Z := integral_exp_pos hWi
  have hZbound : Z≤Real.exp (K^2/2) := by
    have hh:=SYK.product_standardGaussian_mgf_le V K hK hLip 1
    simpa only [ProbabilityTheory.mgf,one_mul,one_pow,mul_one] using hh
  have hH0 (x:E) : 0≤H x := (norm_nonneg _).trans (hDm x)
  have hB0 : 0≤B := (abs_nonneg (H 0)).trans (hHbound 0)
  have hchic := (gaussianCurvatureLocalization_contDiff V hV K).continuous
  have hchib (x:E) : 0≤chi x ∧ chi x≤1 := curvatureCutoff_bounds _ _
  have hchiHi : Integrable (fun x=>chi x*H x) P := by
    apply (integrable_const B).mono' (hchic.mul hH).aestronglyMeasurable
    filter_upwards with x
    change ‖chi x*H x‖≤B
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hchib x).1]
    exact (mul_le_mul_of_nonneg_left (hHbound x) (hchib x).1).trans
      (by nlinarith [(hchib x).2])
  have hWH : Integrable (fun x=>W x*H x) P := by
    apply (hWi.mul_const B).mono'
      ((Real.continuous_exp.comp (hV.continuous.sub continuous_const)).mul hH).aestronglyMeasurable
    filter_upwards with x
    change |Real.exp (V x-∫y,V y∂P)*H x|≤Real.exp (V x-∫y,V y∂P)*B
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hHbound x) (Real.exp_pos _).le
  have hpoint (x:E) : Real.exp (-2*R)*(chi x*H x)≤W x*H x := by
    by_cases hchi : chi x=0
    · simp only [hchi,zero_mul,mul_zero]
      exact mul_nonneg (Real.exp_pos _).le (hH0 x)
    · have hs := curvatureCutoff_support hR hchi
      have hcent : -2*R≤V x-∫y,V y∂P := by
        simpa only [neg_mul] using (neg_abs_le _).trans' (neg_le_neg hs)
      have hW : Real.exp (-2*R)≤W x := Real.exp_le_exp.mpr hcent
      have hh : Real.exp (-2*R)*chi x≤W x :=
        (mul_le_mul_of_nonneg_left (hchib x).2 (Real.exp_pos _).le).trans (by simpa using hW)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (hH0 x)
  have hI := integral_mono (hchiHi.const_mul (Real.exp (-2*R))) hWH hpoint
  rw [integral_const_mul] at hI
  have hlocal:=gaussian_localized_curvature_lower V m H hV hm hH K B hK hHbound hDV hDm
    hmb hdiag heven hodd
  have hnum : Real.exp (-2*R)/(2*(1+c))≤∫x,W x*H x∂P := by
    have hh:=mul_le_mul_of_nonneg_left hlocal (Real.exp_pos (-2*R)).le
    have hn : Real.exp (-2*R)/(2*(1+c))≤Real.exp (-2*R)*(∫x,chi x*H x∂P) := by
      simpa only [div_eq_mul_inv,one_mul,c,chi] using hh
    exact hn.trans hI
  have heq : Real.exp (-8*c*K-K^2/2)/(2*(1+c))*Real.exp (K^2/2)=
      Real.exp (-2*R)/(2*(1+c)) := by
    rw [div_mul_eq_mul_div,←Real.exp_add]
    congr 2
    dsimp [R]
    ring
  apply (le_div_iff₀ hZpos).mpr
  exact ((mul_le_mul_of_nonneg_left hZbound (by positivity)).trans_eq heq).trans hnum

end FourPapersCommon
