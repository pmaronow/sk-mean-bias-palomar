module
public import QuantitativePaper.NormalizedExponentialObservableJets

@[expose] public section

/-! Literal differentiation under an exponentially weighted integral.
The local envelope follows from the actual log-density Lipschitz bound
and the base exponential moment. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff NNReal
namespace FourPapersCommon
open QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {E F Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [MeasurableSpace Ω]

theorem exponentialObservable_integral_iteratedFDeriv (N : ℕ) (P : Measure Ω)
    (L : E → Ω → ℝ) (v : E → Ω → F) (K : ℝ) (A : Ω → ℝ)
    (hK : 0 ≤ K) (hA : ∀z, 0 ≤ A z)
    (hL : ∀z, ContDiff ℝ N (fun x => L x z))
    (hv : ∀z, ContDiff ℝ N (fun x => v x z))
    (hLip : ∃ M : ℝ≥0, ∀z, LipschitzWith M (fun x => L x z))
    (hB : ∀i, 1 ≤ i → i ≤ N → ∀x z, ‖iteratedFDeriv ℝ i (fun y => L y z) x‖ ≤ K^i)
    (hV : ∀i, i ≤ N → ∀x z, ‖iteratedFDeriv ℝ i (fun y => v y z) x‖ ≤ A z*K^i)
    (hMeas : ∀i, i ≤ N → ∀x, AEStronglyMeasurable
      (fun z => iteratedFDeriv ℝ i (fun y => Real.exp (L y z) • v y z) x) P)
    (hi : ∀x, Integrable (fun z => Real.exp (L x z)*A z) P) :
    ∀j, j ≤ N → ∀x,
      Integrable (fun z=>iteratedFDeriv ℝ j (fun y=>Real.exp (L y z) • v y z) x) P ∧
      iteratedFDeriv ℝ j (fun y=>∫z,Real.exp (L y z) • v y z∂P) x=
        ∫z,iteratedFDeriv ℝ j (fun y=>Real.exp (L y z) • v y z) x∂P := by
  obtain ⟨M,hM⟩:=hLip
  have hSmooth(z):ContDiff ℝ N (fun x=>Real.exp (L x z) • v x z):=(hL z).exp.smul (hv z)
  have hDom(x:E):∃s∈𝓝 x,∃B:ℕ→Ω→ℝ,
      (∀j,j≤N→Integrable (B j) P) ∧
      ∀j,j≤N→∀y∈s,∀z,‖iteratedFDeriv ℝ j (fun u=>Real.exp (L u z) • v u z) y‖≤B j z:=by
    let B:=fun j z=>(exponentialObservableJetCoefficient j K*Real.exp M)*(Real.exp (L x z)*A z)
    refine ⟨Metric.ball x 1,Metric.ball_mem_nhds x (by norm_num),B,
      fun j _=>(hi x).const_mul _,?_⟩
    intro j hj y hy z
    have hb:=norm_iteratedFDeriv_exp_smul_observable_le N j (fun u=>L u z) (fun u=>v u z)
      (hL z) (hv z) hj K (A z) hK (hA z)
      (fun i hi hij u=>hB i hi hij u z) (fun i hij u=>hV i hij u z) y
    have he:Real.exp (L y z)≤Real.exp M*Real.exp (L x z):=by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh:=(hM z).dist_le_mul y x
      rw [Real.dist_eq] at hh
      have hm:=mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le M.coe_nonneg
      have hh':L y z-L x z≤M:=(le_abs_self _).trans (hh.trans (by simpa only [mul_one] using hm))
      linarith
    exact hb.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (hA z))
      (exponentialObservableJetCoefficient_nonneg j K hK)).trans_eq (by dsimp only [B];ring))
  intro j hj x
  refine ⟨?_,iteratedFDeriv_integral_of_dominated_derivatives N P _ hSmooth hMeas hDom j hj x⟩
  apply ((hi x).const_mul (exponentialObservableJetCoefficient j K)).mono' (hMeas j hj x)
  exact .of_forall fun z=>by
    exact norm_iteratedFDeriv_exp_smul_observable_le N j _ _ (hL z) (hv z) hj K (A z) hK (hA z)
      (fun i hi hij y=>hB i hi hij y z) (fun i hij y=>hV i hij y z) x

end FourPapersCommon
