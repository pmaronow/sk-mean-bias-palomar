module
public import FourPapersCommon.GaussianL1Poincare
public import FourPapersCommon.GaussianCurvatureCutoff

@[expose] public section

/-! The genuine Gaussian localization step used after conditioning on one
site. These are reusable analytic inequalities, not an assertion that the
physical spin-response hypotheses have already been instantiated. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace
namespace FourPapersCommon
set_option maxHeartbeats 1600000
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "P" => SYK.standardGaussianMeasureOnEuclidean ι

theorem gaussian_integral_odd_zero (f : E→ℝ) (hf : StronglyMeasurable f)
    (hodd : ∀x,f (-x)= -f x) : (∫x,f x ∂P)=0 := by
  have hn : (P).map (fun x : E => -x)=P := by
    rw [SYK_standardGaussian_eq_stdGaussian]
    exact stdGaussian_map (LinearIsometryEquiv.neg ℝ : E≃ₗᵢ[ℝ]E)
  have hh := integral_map_of_stronglyMeasurable (μ:=P) measurable_neg hf
  rw [hn] at hh
  simp_rw [hodd,integral_neg] at hh
  linarith

private theorem norm_gradient_eq_fderiv (f : E→ℝ) (x : E) :
    ‖gradient f x‖=‖fderiv ℝ f x‖ := by
  exact (InnerProductSpace.toDual ℝ E).symm.norm_map _

private theorem integrable_bounded_continuous (f : E→ℝ) (hf : Continuous f)
    (B : ℝ) (hB : ∀x,‖f x‖≤B) : Integrable f P :=
  integrable_const B |>.mono' hf.aestronglyMeasurable (.of_forall hB)

def gaussianCurvatureLocalization (V : E→ℝ) (K : ℝ) (x : E) : ℝ :=
  curvatureCutoff (4*Real.sqrt (Real.pi/2)*K) (V x-∫y,V y ∂P)

theorem gaussianCurvatureLocalization_contDiff (V : E→ℝ) (hV : ContDiff ℝ 1 V)
    (K : ℝ) : ContDiff ℝ 1 (gaussianCurvatureLocalization V K) := by
  exact (contDiff_curvatureCutoff _).comp (hV.sub contDiff_const)

theorem gaussianCurvatureLocalization_mean (V : E→ℝ) (hV : ContDiff ℝ 1 V)
    (K : ℝ) (hK : 0<K) (hD : ∀x,‖fderiv ℝ V x‖≤K) :
    (3/4:ℝ) ≤ ∫x,gaussianCurvatureLocalization V K x ∂P := by
  let c:=Real.sqrt (Real.pi/2)
  let R:=4*c*K
  have hc : 0<c := Real.sqrt_pos.2 (by positivity)
  have hR : 0<R := by dsimp [R];positivity
  have hgrad : Continuous (gradient V) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hV.continuous_fderiv (by simp))
  have hgi : Integrable (fun x=>‖gradient V x‖) P :=
    integrable_bounded_continuous _ hgrad.norm K (fun x=>by rw [norm_norm,norm_gradient_eq_fderiv];exact hD x)
  have hgInt : (∫x,‖gradient V x‖∂P)≤K := by
    have hh := integral_mono hgi (integrable_const K) (fun x=>by
      rw [norm_gradient_eq_fderiv];exact hD x)
    simpa using hh
  have hL := gaussian_L1_poincare V hV K (fun x=>by rw [norm_gradient_eq_fderiv];exact hD x)
  have hbound : (∫x,|V x-(∫y,V y ∂P)|∂P)≤c*K :=
    hL.trans (mul_le_mul_of_nonneg_left hgInt hc.le)
  have hVInt : Integrable V P := by
    apply ((integrable_const |V 0|).add ((IsGaussian.integrable_id (μ:=P)).norm.const_mul K)).mono'
      hV.continuous.aestronglyMeasurable
    filter_upwards with x
    simpa only [Real.norm_eq_abs,Pi.add_apply,id_eq] using
      SYK.contDiff_abs_le_of_gradient_le V K hK.le hV
        (fun y=>by rw [norm_gradient_eq_fderiv];exact hD y) x
  have hdiff : Integrable (fun x=>|V x-(∫y,V y ∂P)|) P :=
    (hVInt.sub (integrable_const _)).abs
  have hchi : Integrable (gaussianCurvatureLocalization V K) P :=
    integrable_bounded_continuous _ (gaussianCurvatureLocalization_contDiff V hV K).continuous 1
      (fun x=>by
        let z:=V x-∫y,V y∂P
        change ‖curvatureCutoff (4*Real.sqrt (Real.pi/2)*K) z‖≤1
        have hb:=curvatureCutoff_bounds (4*Real.sqrt (Real.pi/2)*K) z
        rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
        exact hb.2)
  have hh := integral_mono ((integrable_const (1:ℝ)).sub (hdiff.div_const R)) hchi
    (fun x=>curvatureCutoff_lower hR (V x-∫y,V y ∂P))
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (integrable_const _) (hdiff.div_const R),integral_div,
    integral_const,probReal_univ,one_smul] at hh
  have hdiv := div_le_div_of_nonneg_right hbound hR.le
  have hq : c*K/R=(1/4:ℝ) := by dsimp [R];field_simp
  rw [hq] at hdiv
  linarith

theorem gaussian_localized_curvature_lower (V m H : E→ℝ)
    (hV : ContDiff ℝ 1 V) (hm : ContDiff ℝ 1 m) (hH : Continuous H)
    (K B : ℝ) (hK : 0<K) (hHbound : ∀x,|H x|≤B)
    (hDV : ∀x,‖fderiv ℝ V x‖≤K) (hDm : ∀x,‖fderiv ℝ m x‖≤H x)
    (hmb : ∀x,|m x|≤1) (hdiag : ∀x,1-|m x|≤H x)
    (heven : ∀x,V (-x)=V x) (hodd : ∀x,m (-x)= -m x) :
    1/(2*(1+Real.sqrt (Real.pi/2))) ≤
      ∫x,gaussianCurvatureLocalization V K x*H x ∂P := by
  let c:=Real.sqrt (Real.pi/2)
  let R:=4*c*K
  let chi:=gaussianCurvatureLocalization V K
  have hc : 0<c := Real.sqrt_pos.2 (by positivity)
  have hR : 0<R := by dsimp [R];positivity
  have hchic : ContDiff ℝ 1 chi := gaussianCurvatureLocalization_contDiff V hV K
  have hchib (x : E) : 0≤chi x ∧ chi x≤1 := curvatureCutoff_bounds _ _
  have hH0 (x : E) : 0≤H x := (norm_nonneg _).trans (hDm x)
  have hHi : Integrable H P := integrable_bounded_continuous H hH B
    (fun x=>by rw [Real.norm_eq_abs];exact hHbound x)
  have hchii : Integrable chi P := integrable_bounded_continuous chi hchic.continuous 1
    (fun x=>by rw [Real.norm_eq_abs,abs_of_nonneg (hchib x).1];exact (hchib x).2)
  have hproduct : ContDiff ℝ 1 (fun x=>chi x*m x) := hchic.mul hm
  have hDchi (x : E) : ‖fderiv ℝ chi x‖≤K/R := by
    have hd := ((contDiff_curvatureCutoff R).differentiable (by simp) _).hasDerivAt.comp_hasFDerivAt x
      (((hV.differentiable (by simp) x).hasFDerivAt).sub_const (∫y,V y ∂P))
    change HasFDerivAt chi (deriv (curvatureCutoff R) (V x-∫y,V y∂P) • fderiv ℝ V x) x at hd
    rw [hd.fderiv,norm_smul,Real.norm_eq_abs]
    apply (mul_le_mul (curvatureCutoff_derivative_bound hR _) (hDV x) (norm_nonneg _) (by positivity)).trans_eq
    ring
  have hpoint (x : E) : ‖gradient (fun y=>chi y*m y) x‖≤chi x*H x+K/R := by
    rw [norm_gradient_eq_fderiv]
    have hd := (hchic.differentiable (by simp) x).hasFDerivAt.mul
      (hm.differentiable (by simp) x).hasFDerivAt
    change HasFDerivAt (fun y=>chi y*m y) (chi x • fderiv ℝ m x+m x • fderiv ℝ chi x) x at hd
    rw [hd.fderiv]
    apply (norm_add_le _ _).trans
    simp only [norm_smul,Real.norm_eq_abs]
    apply add_le_add
    · rw [abs_of_nonneg (hchib x).1]
      exact mul_le_mul_of_nonneg_left (hDm x) (hchib x).1
    · exact (mul_le_mul (hmb x) (hDchi x) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hgradB (x : E) : ‖gradient (fun y=>chi y*m y) x‖≤B+K/R := by
    apply (hpoint x).trans
    have hHH := (le_abs_self (H x)).trans (hHbound x)
    have hz := mul_le_mul_of_nonneg_right (hchib x).2 (hH0 x)
    linarith
  have hzero : (∫x,chi x*m x∂P)=0 := gaussian_integral_odd_zero _ hproduct.continuous.stronglyMeasurable
    (fun x=>by dsimp [chi,gaussianCurvatureLocalization];rw [heven,hodd];ring)
  have hL := gaussian_L1_poincare (fun x=>chi x*m x) hproduct (B+K/R) hgradB
  simp only [hzero,sub_zero] at hL
  have hchiHi : Integrable (fun x=>chi x*H x) P :=
    integrable_bounded_continuous _ (hchic.continuous.mul hH) B (fun x=>by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hchib x).1]
      exact (mul_le_mul_of_nonneg_left (hHbound x) (hchib x).1).trans
        (by have hb:0≤B:=(abs_nonneg (H x)).trans (hHbound x);nlinarith [(hchib x).2]))
  have hgradc : Continuous (gradient (fun x=>chi x*m x)) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hproduct.continuous_fderiv (by simp))
  have hgradI := integrable_bounded_continuous _ hgradc.norm (B+K/R) (fun x=>by simpa only [norm_norm] using hgradB x)
  have hgradInt := integral_mono hgradI (hchiHi.add (integrable_const (K/R))) hpoint
  simp only [Pi.add_apply] at hgradInt
  rw [integral_add hchiHi (integrable_const _),integral_const,probReal_univ,one_smul] at hgradInt
  have habsI : Integrable (fun x=>|chi x*m x|) P :=
    integrable_bounded_continuous _ hproduct.continuous.abs 1 (fun x=>by
      rw [Real.norm_eq_abs,abs_abs,abs_mul,abs_of_nonneg (hchib x).1]
      nlinarith [(hchib x).1,(hchib x).2,abs_nonneg (m x),hmb x])
  have hsum := integral_mono hchii (hchiHi.add habsI) (fun x=>by
    change chi x≤chi x*H x+|chi x*m x|
    rw [abs_mul,abs_of_nonneg (hchib x).1]
    nlinarith [(hchib x).1,hdiag x])
  simp only [Pi.add_apply] at hsum
  rw [integral_add hchiHi habsI] at hsum
  have hmean := gaussianCurvatureLocalization_mean V hV K hK hDV
  have hcdiv : c*(K/R)=(1/4:ℝ) := by dsimp [R];field_simp
  have hLL := hL.trans (mul_le_mul_of_nonneg_left hgradInt hc.le)
  have hfin : (1/2:ℝ)≤(1+c)*(∫x,chi x*H x∂P) := by
    rw [mul_add,hcdiv] at hLL
    dsimp only [chi] at hsum ⊢
    nlinarith
  exact (div_le_iff₀ (by positivity : 0<2*(1+c))).mpr (by nlinarith)

end FourPapersCommon
