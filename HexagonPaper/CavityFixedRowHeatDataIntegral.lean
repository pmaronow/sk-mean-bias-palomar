module
public import QuantitativeFollowup.FollowupCavityMixtureHeatZero
public import QuantitativePaper.SmoothIntegral

@[expose] public section

/-! Gaussian row heat data obtained by differentiating an actual finite-measure
parameter integral. Inputs concern the integrand's genuine spatial jets;
no derivative, smoothness or heat formula for the resulting integral is a premise. -/
noncomputable section
open Set Filter MeasureTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped ContDiff Topology
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Ω : Type} [MeasurableSpace Ω] {n : ℕ}

private theorem integral_jet_local_envelope
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Field n→Ω→ℝ)
    (B R : ℝ) (hB : 0≤B) (hR : 0≤R)
    (hb : ∀r,r≤2→∀θ w,‖iteratedFDeriv ℝ r (fun y=>F y w) θ‖≤B*Real.exp (R*‖θ‖))
    (θ : Field n) :
    ∃s∈𝓝 θ,∃C : ℕ→Ω→ℝ,
      (∀r,r≤2→Integrable (C r) μ) ∧
      ∀r,r≤2→∀y∈s,∀w,‖iteratedFDeriv ℝ r (fun u=>F u w) y‖≤C r w := by
  let D:=B*Real.exp (R*(‖θ‖+1))
  refine ⟨Metric.ball θ 1,Metric.ball_mem_nhds θ (by norm_num),fun _ _=>D,
    fun _ _=>integrable_const D,?_⟩
  intro r hr y hy w
  apply (hb r hr y w).trans
  apply mul_le_mul_of_nonneg_left _ hB
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hR
  have hd : ‖y-θ‖<1:=by simpa only [Metric.mem_ball,dist_eq_norm] using hy
  have hh : ‖y‖≤‖y-θ‖+‖θ‖:=by simpa only [sub_add_cancel] using norm_add_le (y-θ) θ
  linarith

 theorem cavityIntegral_contDiff_two_of_uniform_jets
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Field n→Ω→ℝ)
    (hf : ∀w,ContDiff ℝ 2 (fun θ=>F θ w))
    (hm : ∀r,r≤2→∀θ,AEStronglyMeasurable
      (fun w=>iteratedFDeriv ℝ r (fun y=>F y w) θ) μ)
    (B R : ℝ) (hB : 0≤B) (hR : 0≤R)
    (hb : ∀r,r≤2→∀θ w,‖iteratedFDeriv ℝ r (fun y=>F y w) θ‖≤B*Real.exp (R*‖θ‖)) :
    ContDiff ℝ 2 (fun θ=>∫w,F θ w∂μ) :=
  contDiff_integral_of_dominated_derivatives 2 μ F hf hm
    (integral_jet_local_envelope μ F B R hB hR hb)

 theorem cavityIntegral_iterated_derivative_of_uniform_jets
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Field n→Ω→ℝ)
    (hf : ∀w,ContDiff ℝ 2 (fun θ=>F θ w))
    (hm : ∀r,r≤2→∀θ,AEStronglyMeasurable
      (fun w=>iteratedFDeriv ℝ r (fun y=>F y w) θ) μ)
    (B R : ℝ) (hB : 0≤B) (hR : 0≤R)
    (hb : ∀r,r≤2→∀θ w,‖iteratedFDeriv ℝ r (fun y=>F y w) θ‖≤B*Real.exp (R*‖θ‖))
    (r : ℕ) (hr : r≤2) (θ : Field n) :
    iteratedFDeriv ℝ r (fun y=>∫w,F y w∂μ) θ=
      ∫w,iteratedFDeriv ℝ r (fun y=>F y w) θ∂μ :=
  iteratedFDeriv_integral_of_dominated_derivatives 2 μ F hf hm
    (integral_jet_local_envelope μ F B R hB hR hb) r hr θ

 theorem cavityIntegral_jet_bound_of_uniform_jets
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Field n→Ω→ℝ)
    (hf : ∀w,ContDiff ℝ 2 (fun θ=>F θ w))
    (hm : ∀r,r≤2→∀θ,AEStronglyMeasurable
      (fun w=>iteratedFDeriv ℝ r (fun y=>F y w) θ) μ)
    (B R : ℝ) (hB : 0≤B) (hR : 0≤R)
    (hb : ∀r,r≤2→∀θ w,‖iteratedFDeriv ℝ r (fun y=>F y w) θ‖≤B*Real.exp (R*‖θ‖))
    (r : ℕ) (hr : r≤2) (θ : Field n) :
    ‖iteratedFDeriv ℝ r (fun y=>∫w,F y w∂μ) θ‖≤
      (μ.real univ*B)*Real.exp (R*‖θ‖) := by
  rw [cavityIntegral_iterated_derivative_of_uniform_jets μ F hf hm B R hB hR hb r hr θ]
  have hn:=norm_integral_le_of_norm_le_const (μ:=μ)
    (.of_forall fun w=>hb r hr θ w)
  exact hn.trans_eq (by ring)

 theorem cavityRowHeatData_integral_of_uniform_jets
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Field n→Ω→ℝ)
    (hf : ∀w,ContDiff ℝ 2 (fun θ=>F θ w))
    (hm : ∀r,r≤2→∀θ,AEStronglyMeasurable
      (fun w=>iteratedFDeriv ℝ r (fun y=>F y w) θ) μ)
    (B R : ℝ) (hB : 0≤B) (hR : 0≤R)
    (hb : ∀r,r≤2→∀θ w,‖iteratedFDeriv ℝ r (fun y=>F y w) θ‖≤B*Real.exp (R*‖θ‖)) :
    Nonempty (CavityRowHeatData (fun θ=>∫w,F θ w∂μ)) := by
  refine ⟨⟨cavityIntegral_contDiff_two_of_uniform_jets μ F hf hm B R hB hR hb,
    μ.real univ*B,R,mul_nonneg (measureReal_nonneg) hB,hR,?_,?_,?_⟩⟩
  · intro θ
    simpa only [norm_iteratedFDeriv_zero] using
      cavityIntegral_jet_bound_of_uniform_jets μ F hf hm B R hB hR hb 0 (by omega) θ
  · intro θ
    simpa only [norm_iteratedFDeriv_one] using
      cavityIntegral_jet_bound_of_uniform_jets μ F hf hm B R hB hR hb 1 (by omega) θ
  · intro θ
    rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
    exact cavityIntegral_jet_bound_of_uniform_jets μ F hf hm B R hB hR hb 2 (by omega) θ

end HexagonPaper
