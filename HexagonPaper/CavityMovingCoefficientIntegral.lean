module
public import HexagonPaper.CavityFixedRowHeatDataIntegral
public import HexagonPaper.CavityFixedRowJetMeasurableSections
public import FourPapersCommon.GaussianSelectedMovingZeroHeat

@[expose] public section

/-! Moving Gaussian endpoint differentiation after integration on a fixed
finite driving space. No derivative in the positive coefficient is needed. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology ContDiff BigOperators
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ} {Ω : Type} [MeasurableSpace Ω]

theorem cavityMovingIntegral_diagonal_continuous
    (ν : Measure Ω) [IsFiniteMeasure ν]
    (F : {b : ℝ // 0<b}→Field n→Ω→ℝ)
    (hs : ∀b w,ContDiff ℝ ∞ (fun y=>F b y w))
    (hm : ∀b θ,Measurable (F b θ))
    (B R : ℝ) (hB : 0≤B) (hR : 0≤R)
    (hb : ∀b r,r≤2→∀θ w,‖iteratedFDeriv ℝ r (fun y=>F b y w) θ‖≤B*Real.exp (R*‖θ‖))
    (e : Field n)
    (hc : ∀w,Continuous (fun z : {b : ℝ // 0<b}×Field n=>
      fderiv ℝ (fderiv ℝ (fun y=>F z.1 y w)) z.2 e e)) :
    Continuous (fun z : {b : ℝ // 0<b}×Field n=>
      fderiv ℝ (fderiv ℝ (fun y=>∫w,F z.1 y w∂ν)) z.2 e e) := by
  have hjm (b : {b : ℝ // 0<b}) (r : ℕ) (θ : Field n) :
      AEStronglyMeasurable (fun w=>iteratedFDeriv ℝ r (fun y=>F b y w) θ) ν :=
    aestronglyMeasurable_cavityFiniteIteratedFDeriv_sections
      (fun z : Ω×Field n=>F b z.2 z.1) (hm b) (hs b) r θ ν
  have hi (b : {b : ℝ // 0<b}) (θ : Field n) :
      Integrable (fun w=>iteratedFDeriv ℝ 2 (fun y=>F b y w) θ) ν :=
    (integrable_const (B*Real.exp (R*‖θ‖))).mono' (hjm b 2 θ)
      (.of_forall fun w=>hb b 2 le_rfl θ w)
  have he (z : {b : ℝ // 0<b}×Field n) :
      fderiv ℝ (fderiv ℝ (fun y=>∫w,F z.1 y w∂ν)) z.2 e e=
      ∫w,fderiv ℝ (fderiv ℝ (fun y=>F z.1 y w)) z.2 e e∂ν := by
    rw [←iteratedFDeriv_two_apply (fun y=>∫w,F z.1 y w∂ν) z.2 (fun _=>e),
      cavityIntegral_iterated_derivative_of_uniform_jets ν (F z.1)
        (fun w=>(hs z.1 w).of_le (by simp))
        (fun r _ θ=>hjm z.1 r θ) B R hB hR (hb z.1) 2 le_rfl z.2,
      ContinuousMultilinearMap.integral_apply (hi z.1 z.2)]
    simp only [iteratedFDeriv_two_apply]
  have hbound (z : {b : ℝ // 0<b}×Field n) (w : Ω) :
      ‖fderiv ℝ (fderiv ℝ (fun y=>F z.1 y w)) z.2 e e‖≤
        B*Real.exp (R*‖z.2‖)*‖e‖^2 := by
    apply ((fderiv ℝ (fderiv ℝ (fun y=>F z.1 y w)) z.2 e).le_opNorm e).trans
    apply (mul_le_mul_of_nonneg_right
      ((fderiv ℝ (fderiv ℝ (fun y=>F z.1 y w)) z.2).le_opNorm e) (norm_nonneg e)).trans
    have hh : ‖fderiv ℝ (fderiv ℝ (fun y=>F z.1 y w)) z.2‖≤B*Real.exp (R*‖z.2‖) := by
      rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
      exact hb z.1 2 le_rfl z.2 w
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (norm_nonneg e))
      (norm_nonneg e)).trans_eq (by ring)
  have hint : Continuous (fun z : {b : ℝ // 0<b}×Field n=>
      ∫w,fderiv ℝ (fderiv ℝ (fun y=>F z.1 y w)) z.2 e e∂ν) := by
    rw [continuous_iff_continuousAt]
    intro z0
    apply continuousAt_of_dominated (bound:=fun _=>B*Real.exp (R*(‖z0.2‖+1))*‖e‖^2)
    · exact .of_forall fun z=>by
        have hh:=(ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2=>Field n) ℝ (fun _=>e)).continuous
          |>.comp_aestronglyMeasurable (hjm z.1 2 z.2)
        simpa only [ContinuousMultilinearMap.apply_apply,iteratedFDeriv_two_apply] using hh
    · filter_upwards [(continuous_snd.norm.tendsto z0).eventually
        (gt_mem_nhds (show ‖z0.2‖<‖z0.2‖+1 by linarith))] with z hz
      exact .of_forall fun w=>(hbound z w).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hz.le hR)) hB) (sq_nonneg _))
    · exact integrable_const _
    · exact .of_forall fun w=>(hc w).continuousAt
  exact hint.congr fun z=>(he z).symm

def cavityMovingPositiveExtension (d : ℝ) (hd : 0<d) (b : ℝ) : {b : ℝ // 0<b} :=
  ⟨max b (d/2),(half_pos hd).trans_le (le_max_right _ _)⟩

theorem continuous_cavityMovingPositiveExtension (d : ℝ) (hd : 0<d) :
    Continuous (cavityMovingPositiveExtension d hd) :=
  (continuous_id.max continuous_const).subtype_mk _

theorem cavityMovingIntegral_heat_increment_derivative
    (ν : Measure Ω) [IsFiniteMeasure ν]
    (F : {b : ℝ // 0<b}→Field n→Ω→ℝ)
    (hs : ∀b w,ContDiff ℝ ∞ (fun y=>F b y w))
    (hm : ∀b θ,Measurable (F b θ))
    (B R : ℝ) (hB : 0≤B) (hR : 0≤R)
    (hb : ∀b r,r≤2→∀θ w,‖iteratedFDeriv ℝ r (fun y=>F b y w) θ‖≤B*Real.exp (R*‖θ‖))
    (hc : ∀w e,Continuous (fun z : {b : ℝ // 0<b}×Field n=>
      fderiv ℝ (fderiv ℝ (fun y=>F z.1 y w)) z.2 e e))
    (d α : ℝ) (hd : 0<d) :
    HasDerivWithinAt (fun v=>∫z : Field n,
      ((∫w,F (cavityMovingPositiveExtension d hd (d-α*v))
          (gaussianSelectedScale (fun _ : Fin n=>true) v z) w∂ν)-
       (∫w,F (cavityMovingPositiveExtension d hd (d-α*v))
          (gaussianSelectedScale (fun _ : Fin n=>true) 0 z) w∂ν))∂stdGaussian (Field n))
      ((1/2 : ℝ)*∫z : Field n,
        gaussianSelectedSpatialTrace (fun _ : Fin n=>true)
          (fun x : ℝ×Field n=>∫w,F (cavityMovingPositiveExtension d hd x.1) x.2 w∂ν)
          d (gaussianSelectedScale (fun _ : Fin n=>true) 0 z)∂stdGaussian (Field n)) (Ici (0 : ℝ)) 0 := by
  have hjm (b : {b : ℝ // 0<b}) (r : ℕ) (θ : Field n) :
      AEStronglyMeasurable (fun w=>iteratedFDeriv ℝ r (fun y=>F b y w) θ) ν :=
    aestronglyMeasurable_cavityFiniteIteratedFDeriv_sections
      (fun z : Ω×Field n=>F b z.2 z.1) (hm b) (hs b) r θ ν
  have hsI (b : {b : ℝ // 0<b}) : ContDiff ℝ 2 (fun θ=>∫w,F b θ w∂ν) :=
    cavityIntegral_contDiff_two_of_uniform_jets ν (F b) (fun w=>(hs b w).of_le (by simp))
      (fun r _ θ=>hjm b r θ) B R hB hR (hb b)
  have hjI (b : {b : ℝ // 0<b}) (r : ℕ) (hr : r≤2) (θ : Field n) :
      ‖iteratedFDeriv ℝ r (fun y=>∫w,F b y w∂ν) θ‖≤
        (ν.real univ*B)*Real.exp (R*‖θ‖) :=
    cavityIntegral_jet_bound_of_uniform_jets ν (F b) (fun w=>(hs b w).of_le (by simp))
      (fun r _ θ=>hjm b r θ) B R hB hR (hb b) r hr θ
  apply hasDerivWithinAt_gaussianSelected_moving_heat_zero (fun _ : Fin n=>true)
    (fun x : ℝ×Field n=>∫w,F (cavityMovingPositiveExtension d hd x.1) x.2 w∂ν)
    (d/2) (2*d) d α (ν.real univ*B) R
    ⟨by linarith,by linarith⟩ (mul_nonneg measureReal_nonneg hB) hR
    (fun b _=>hsI (cavityMovingPositiveExtension d hd b))
  · intro i _
    exact ((cavityMovingIntegral_diagonal_continuous ν F hs hm B R hB hR hb
      (EuclideanSpace.basisFun (Fin n) ℝ i) (fun w=>hc w _)).comp
      ((continuous_cavityMovingPositiveExtension d hd).comp continuous_fst |>.prodMk continuous_snd)).continuousOn
  · intro b _ θ
    simpa only [norm_iteratedFDeriv_zero] using hjI (cavityMovingPositiveExtension d hd b) 0 (by omega) θ
  · intro b _ θ
    simpa only [norm_iteratedFDeriv_one] using hjI (cavityMovingPositiveExtension d hd b) 1 (by omega) θ
  · intro b _ θ
    rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
    exact hjI (cavityMovingPositiveExtension d hd b) 2 le_rfl θ

end HexagonPaper
