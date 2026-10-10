module
public import FourPapersCommon.FiniteCascadeTreeGaussianRowBounds
public import Mathlib.Analysis.ODE.Gronwall

@[expose] public section

/-! Relative response and comparison for nonnegative observables under
the actual normalized Gaussian-row law. The response includes its true
normalizer; no lower bound on the observable is required. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy FRSB
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
variable (V : S→ℝ) (K : FiniteStateField S) (a : ℕ→ℝ)
  (ha : ∀j,0≤a j) (hanti : Antitone a) (h0 : a 0≤1)
  (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (s : ℝ)
  {j : ℕ} (T : FiniteTerminalGenealogy j) (hs : s≤finiteCascadeTreeRootCoefficient a T)
  (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S) (H : FiniteStateField S)
  (C : ℝ) (hC : 0≤C) (hK : ∀σ,|K σ|≤C)
  (F : FiniteStateField S×Records (FiniteStateField S) S T→ℝ)
  (hF : Measurable F) (CF : ℝ) (hCF : 0≤CF) (hFb : ∀z,|F z|≤CF)
  (hFn : ∀z,0≤F z)

include ha hanti h0 hs hC hK hF hCF hFb hFn

theorem finiteCascadeTreeGaussianRowVarianceResponse_abs_le_mean (v : ℝ) :
    |finiteCascadeTreeGaussianRowVarianceResponse V K a L s v T R H F|≤
      (|(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C|^2+
        |((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C^2|)*
      (∫z,F z.2 ∂finiteCascadeTreeGaussianRowLaw V K a L s v T R H) := by
  let P:=finiteCascadeTreeGaussianRowLaw V K a L s v T R H
  let A:=|(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C|^2+
    |((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C^2|
  let Q:=finiteCascadeTreeGaussianRowCurvature V K a L s T
  letI:=finiteCascadeTreeGaussianRowLaw_probability V K a ha hanti h0 L s v T hs R H C hC hK
  have hQ (z) : |Q z|≤A:=finiteCascadeTreeGaussianRowCurvature_abs_le
    V K a ha hanti h0 L s T hs C hC hK z
  have hiF : Integrable (fun z=>F z.2) P :=
    (integrable_const CF).mono' (hF.comp measurable_snd).aestronglyMeasurable
      (.of_forall fun z=>by simpa only [Real.norm_eq_abs] using hFb z.2)
  have hiQ : Integrable Q P := (integrable_const A).mono'
    (measurable_finiteCascadeTreeGaussianRowCurvature V K a ha L s T).aestronglyMeasurable
    (.of_forall fun z=>by simpa only [Real.norm_eq_abs] using hQ z)
  have hiFQ : Integrable (fun z=>F z.2*Q z) P :=
    (hiF.mul_const A).mono'
      (((hF.comp measurable_snd).mul
        (measurable_finiteCascadeTreeGaussianRowCurvature V K a ha L s T)).aestronglyMeasurable)
      (.of_forall fun z=>by
        rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hFn z.2)]
        exact mul_le_mul_of_nonneg_left (hQ z) (hFn z.2))
  have hEF : 0≤∫z,F z.2∂P:=integral_nonneg (fun z=>hFn z.2)
  have hEQ : |∫z,Q z∂P|≤A := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=P) (f:=Q)
        (.of_forall fun z=>by simpa only [Real.norm_eq_abs] using hQ z)
  have hEFQ : |∫z,F z.2*Q z∂P|≤(∫z,F z.2∂P)*A := by
    calc
      |∫z,F z.2*Q z∂P| ≤ ∫z,‖F z.2*Q z‖∂P := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z=>F z.2*Q z)
      _ ≤ ∫z,F z.2*A∂P := integral_mono_ae hiFQ.norm (hiF.mul_const A)
        (.of_forall fun z=>by
          change ‖F z.2*Q z‖≤F z.2*A
          rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hFn z.2)]
          exact mul_le_mul_of_nonneg_left (hQ z) (hFn z.2))
      _ = (∫z,F z.2∂P)*A := integral_mul_const A _
  have hprod : |(∫z,F z.2∂P)*(∫z,Q z∂P)|≤(∫z,F z.2∂P)*A := by
    rw [abs_mul,abs_of_nonneg hEF]
    exact mul_le_mul_of_nonneg_left hEQ hEF
  change |(1/2:ℝ)*((∫z,F z.2*Q z∂P)-(∫z,F z.2∂P)*(∫z,Q z∂P))|≤A*(∫z,F z.2∂P)
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  have hd:=abs_sub (∫z,F z.2*Q z∂P) ((∫z,F z.2∂P)*(∫z,Q z∂P))
  nlinarith

theorem finiteCascadeTreeGaussianRowExpectation_le_exp_forward
    (v w : ℝ) (hv : 0≤v) (hvw : v≤w) :
    (∫z,F z.2 ∂finiteCascadeTreeGaussianRowLaw V K a L s w T R H)≤
      (∫z,F z.2 ∂finiteCascadeTreeGaussianRowLaw V K a L s v T R H)*
        Real.exp ((|(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C|^2+
          |((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C^2|)*(w-v)) := by
  let f:=fun x=>∫z,F z.2∂finiteCascadeTreeGaussianRowLaw V K a L s x T R H
  let Q:=fun x=>finiteCascadeTreeGaussianRowVarianceResponse V K a L s x T R H F
  let A:=|(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C|^2+
    |((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C^2|
  have hf:=continuous_finiteCascadeTreeGaussianRowExpectation_variance
    V K a ha hanti h0 L s T hs R H C hC hK F hF CF hCF hFb
  have hder (x) (hx : x∈Ico v w) : HasDerivWithinAt f (Q x) (Ici x) x := by
    have hx0:=hv.trans hx.1
    rcases hx0.eq_or_lt with he|hp
    · subst x
      exact hasDerivWithinAt_finiteCascadeTreeGaussianRowExpectation_variance_zero
        V K a ha hanti h0 L s T hs R H C hC hK F hF CF hCF hFb
    · exact (hasDerivAt_finiteCascadeTreeGaussianRowExpectation_variance
        V K a ha hanti h0 L s x hp T hs R H C hC hK F hF CF hCF hFb).hasDerivWithinAt
  have hn (x) : 0≤f x := integral_nonneg (fun z=>hFn z.2)
  have hg:=norm_le_gronwallBound_of_norm_deriv_right_le hf.continuousOn hder
    (δ:=f v) (K:=A) (ε:=0) (by rw [Real.norm_of_nonneg (hn v)])
    (by
      intro x hx
      rw [Real.norm_eq_abs,Real.norm_of_nonneg (hn x),add_zero]
      exact finiteCascadeTreeGaussianRowVarianceResponse_abs_le_mean
        V K a ha hanti h0 L s T hs R H C hC hK F hF CF hCF hFb hFn x)
  have hgw:=hg w ⟨hvw,le_rfl⟩
  change ‖f w‖≤gronwallBound (f v) A 0 (w-v) at hgw
  rw [Real.norm_of_nonneg (hn w),gronwallBound_ε0] at hgw
  exact hgw

theorem finiteCascadeTreeGaussianRowExpectation_le_exp_backward
    (v w : ℝ) (hw : 0≤w) (hwv : w≤v) :
    (∫z,F z.2 ∂finiteCascadeTreeGaussianRowLaw V K a L s w T R H)≤
      (∫z,F z.2 ∂finiteCascadeTreeGaussianRowLaw V K a L s v T R H)*
        Real.exp ((|(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C|^2+
          |((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C^2|)*(v-w)) := by
  let f:=fun x=>∫z,F z.2∂finiteCascadeTreeGaussianRowLaw V K a L s x T R H
  let Q:=fun x=>finiteCascadeTreeGaussianRowVarianceResponse V K a L s x T R H F
  let A:=|(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C|^2+
    |((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C^2|
  have hf:=continuous_finiteCascadeTreeGaussianRowExpectation_variance
    V K a ha hanti h0 L s T hs R H C hC hK F hF CF hCF hFb
  have hder (x) (hx : x∈Ico w v) :
      HasDerivWithinAt (fun x=>f (v+w-x)) (-Q (v+w-x)) (Ici x) x := by
    have hy : 0<v+w-x := by linarith [hx.2]
    have hd:=hasDerivAt_finiteCascadeTreeGaussianRowExpectation_variance
      V K a ha hanti h0 L s (v+w-x) hy T hs R H C hC hK F hF CF hCF hFb
    have hc:=hd.comp x ((hasDerivAt_const x (v+w)).sub (hasDerivAt_id x))
    simpa only [f,Q,finiteCascadeTreeGaussianRowVarianceResponse,Function.comp_def,
      zero_sub,mul_neg_one] using hc.hasDerivWithinAt (s:=Ici x)
  have hn (x) : 0≤f x := integral_nonneg (fun z=>hFn z.2)
  have hg:=norm_le_gronwallBound_of_norm_deriv_right_le
    (f:=fun x=>f (v+w-x)) (f':=fun x=>-Q (v+w-x))
    ((hf.comp (continuous_const.sub continuous_id)).continuousOn) hder
    (δ:=f v) (K:=A) (ε:=0) (by
      change ‖f (v+w-w)‖≤f v
      simp only [add_sub_cancel_right,Real.norm_of_nonneg (hn v)]
      exact le_rfl)
    (by
      intro x hx
      change ‖-Q (v+w-x)‖≤A*‖f (v+w-x)‖+0
      rw [norm_neg,Real.norm_eq_abs,Real.norm_of_nonneg (hn (v+w-x)),add_zero]
      exact finiteCascadeTreeGaussianRowVarianceResponse_abs_le_mean
        V K a ha hanti h0 L s T hs R H C hC hK F hF CF hCF hFb hFn (v+w-x))
  have hgw:=hg v ⟨hwv,le_rfl⟩
  change ‖f (v+w-v)‖≤gronwallBound (f v) A 0 (v-w) at hgw
  have he : v+w-v=w := by ring
  rw [he,Real.norm_of_nonneg (hn w),gronwallBound_ε0] at hgw
  exact hgw

theorem finiteCascadeTreeGaussianRowExpectation_le_exp
    (v w : ℝ) (hv : 0≤v) (hw : 0≤w) :
    (∫z,F z.2 ∂finiteCascadeTreeGaussianRowLaw V K a L s w T R H)≤
      (∫z,F z.2 ∂finiteCascadeTreeGaussianRowLaw V K a L s v T R H)*
        Real.exp ((|(2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C|^2+
          |((FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)-s)*C^2|)*|w-v|) := by
  rcases le_total v w with he|he
  · rw [abs_of_nonneg (sub_nonneg.mpr he)]
    exact finiteCascadeTreeGaussianRowExpectation_le_exp_forward
      V K a ha hanti h0 L s T hs R H C hC hK F hF CF hCF hFb hFn v w hv he
  · rw [abs_of_nonpos (sub_nonpos.mpr he),neg_sub]
    exact finiteCascadeTreeGaussianRowExpectation_le_exp_backward
      V K a ha hanti h0 L s T hs R H C hC hK F hF CF hCF hFb hFn v w hw he

end FourPapersCommon
