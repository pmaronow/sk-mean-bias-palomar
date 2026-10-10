module
public import FourPapersCommon.ExponentialSmoothBounds
public import QuantitativePaper.GaussianColeHopfCoordinateJets
public import QuantitativePaper.LocalSmoothIntegral
public import OverlapPaper.CavityGaussianIBP

@[expose] public section

/-! Smoothness of a genuine Gaussian integral with a smooth, possibly
singular, parameter-dependent linear noise map. Zero noise directions cause
no loss of smoothness in the signed amplitude parameter. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff
namespace FourPapersCommon
open QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {ι : Type} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

private def parameterEvaluation (z : E) : (ℝ×(E→L[ℝ]E))→L[ℝ](ℝ×E) :=
  (ContinuousLinearMap.fst ℝ ℝ (E→L[ℝ]E)).prod
    ((ContinuousLinearMap.apply ℝ E z).comp (ContinuousLinearMap.snd ℝ ℝ (E→L[ℝ]E)))

private theorem parameterEvaluation_norm_le (z : E) : ‖parameterEvaluation z‖≤1+‖z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  change ‖(w.1,w.2 z)‖≤(1+‖z‖)*‖w‖
  rw [Prod.norm_def]
  apply max_le
  · exact (norm_fst_le w).trans (by nlinarith [norm_nonneg w,norm_nonneg z])
  · exact (w.2.le_opNorm z).trans (by nlinarith [norm_snd_le w,norm_nonneg z,norm_nonneg w])

/-- Actual local all-order Gaussian differentiation with bounded parameter
jets on the chosen open domain. These are analytic input bounds, not
hypotheses supplying any derivative of the integral. -/
theorem contDiffOn_gaussian_operator_parameter
    (F : ℝ×E→ℝ) (l u : ℝ)
    (hF : ExponentialSmoothOn F ((Ioo l u)×ˢ(univ : Set E)))
    (g : ℝ→ℝ×(E→L[ℝ]E)) (U : Set ℝ) (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (hmap : ∀x∈U,(g x).1∈Ioo l u)
    (hjets : ∀N:ℕ,∃K:ℝ,1≤K ∧ ∀j,j≤N→∀x∈U,‖iteratedFDeriv ℝ j g x‖≤K) :
    ContDiffOn ℝ ∞ (fun x=>∫z:E,F ((g x).1,(g x).2 z)∂stdGaussian E) U := by
  let H : E×ℝ→ℝ:=fun w=>F ((g w.2).1,(g w.2).2 w.1)
  have hH : ContDiffOn ℝ ∞ H ((univ:Set E)×ˢU) := by
    intro w hw
    apply ((hF.smooth _ ⟨hmap w.2 hw.2,mem_univ _⟩).comp w ?_).contDiffWithinAt
    have hgw := (hg.contDiffAt (hU.mem_nhds hw.2)).comp w contDiffAt_snd
    exact hgw.fst.prodMk (hgw.snd.clm_apply contDiffAt_fst)
  rw [contDiffOn_infty]
  intro N
  apply contDiffOn_integral_of_dominated_derivatives N (stdGaussian E)
    (fun x z=>F ((g x).1,(g x).2 z)) U hU
  · intro z x hx
    exact (((hF.smooth _ ⟨hmap x hx,mem_univ _⟩).comp x
      ((parameterEvaluation z).contDiff.contDiffAt.comp x
        (hg.contDiffAt (hU.mem_nhds hx)))).of_le (by simp)).contDiffWithinAt
  · intro j hj x hx
    have hc:=continuousOn_fieldSlice_iteratedFDeriv_on_open H ((univ:Set E)×ˢU)
      (isOpen_univ.prod hU) (hH.of_le (by simp)) hj
    have hcx : Continuous (fun z:E=>iteratedFDeriv ℝ j
        (fun y=>F ((g y).1,(g y).2 z)) x) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      exact (hc.continuousAt ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ _,hx⟩)).comp
        (continuous_id.prodMk continuous_const).continuousAt
    exact hcx.aestronglyMeasurable
  · intro x hx
    obtain ⟨K,hK,hgb⟩:=hjets N
    obtain ⟨C,R,hC,hR,hFb⟩:=hF.common_bound N
    let B : ℕ→E→ℝ:=fun j z=>(j.factorial:ℝ)*C*Real.exp (R*K)*K^j*
      Real.exp ((R*K+(j:ℝ))*‖z‖)
    refine ⟨U,hU.mem_nhds hx,Subset.rfl,B,?_,?_⟩
    · intro j _
      exact (integrable_exp_mul_norm_gaussian (stdGaussian E) (R*K+(j:ℝ))).const_mul _
    · intro j hj y hy z
      let L:=parameterEvaluation z
      have hgs:=hg.contDiffAt (hU.mem_nhds hy)
      have hG : ContDiffAt ℝ ∞ (L∘g) y:=L.contDiff.contDiffAt.comp y hgs
      have hGnorm : ‖L (g y)‖≤K*(1+‖z‖) := by
        apply (L.le_opNorm (g y)).trans
        have h0 : ‖g y‖≤K:=by simpa only [norm_iteratedFDeriv_zero] using hgb 0 (Nat.zero_le _) y hy
        exact (mul_le_mul (parameterEvaluation_norm_le z) h0 (norm_nonneg _) (by positivity)).trans_eq (by ring)
      have hGjet (r:ℕ) (hr:1≤r) (hrj:r≤j) :
          ‖iteratedFDeriv ℝ r (L∘g) y‖≤(K*Real.exp ‖z‖)^r := by
        have hh:=L.norm_iteratedFDeriv_comp_left hgs (by simp : (r:ℕ∞ω)≤∞)
        apply (hh.trans (mul_le_mul (parameterEvaluation_norm_le z)
          (hgb r (hrj.trans hj) y hy) (norm_nonneg _) (by positivity))).trans
        have hz : 1+‖z‖≤Real.exp ‖z‖:=by linarith [Real.add_one_le_exp ‖z‖]
        have hbase : 1≤K*Real.exp ‖z‖:=one_le_mul_of_one_le_of_one_le hK
          (Real.one_le_exp_iff.mpr (norm_nonneg _))
        exact ((mul_le_mul_of_nonneg_right hz (zero_le_one.trans hK)).trans_eq (by ring)).trans
          (le_self_pow₀ hbase (by omega))
      have hFc (r:ℕ) (hr:r≤j) : ‖iteratedFDeriv ℝ r F (L (g y))‖≤
          C*Real.exp (R*K)*Real.exp ((R*K)*‖z‖) := by
        apply (hFb r (hr.trans hj) _ ⟨hmap y hy,mem_univ _⟩).trans
        calc
          _≤C*Real.exp (R*(K*(1+‖z‖))) := by gcongr
          _=_:=by rw [show R*(K*(1+‖z‖))=R*K+(R*K)*‖z‖ by ring,Real.exp_add];ring
      have hh:=DepthPaper.norm_iteratedFDeriv_comp_le_at
        (hF.smooth _ ⟨hmap y hy,mem_univ _⟩) hG j
        (C*Real.exp (R*K)*Real.exp ((R*K)*‖z‖)) (K*Real.exp ‖z‖) hFc hGjet
      change ‖iteratedFDeriv ℝ j (F∘(L∘g)) y‖≤_
      apply hh.trans_eq
      dsimp only [B]
      rw [mul_pow,←Real.exp_nat_mul,show (R*K+(j:ℝ))*‖z‖=R*K*‖z‖+(j:ℝ)*‖z‖ by ring,Real.exp_add]
      ring

end FourPapersCommon
