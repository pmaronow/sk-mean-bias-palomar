module
public import HexagonPaper.PathHeatSectionwiseAnalyticSource

@[expose] public section

/-! Freeze true auxiliary coordinates only for conditional finite Price.
This construction is not used as a common auxiliary growth envelope. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal unitInterval
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PathHeatSectionwiseSignedSource
variable {Z E K X : Type*} [TopologicalSpace Z] [TopologicalSpace E] [TopologicalSpace K]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [CompactSpace X] [SecondCountableTopology X]
theorem pathHeatSectionwise_projection_tv {V : Type*} [MeasurableSpace V]
    (F : Z×C(X,ℝ)→SignedMeasure V)
    (hF : ∀u,Tendsto (fun w=>signedTV (F w-F u)) (𝓝 u) (𝓝 0))
    (v : Z×((E×K)×C(X,ℝ))) :
    Tendsto (fun w : Z×((E×K)×C(X,ℝ))=>signedTV (F (w.1,w.2.2)-F (v.1,v.2.2)))
      (𝓝 v) (𝓝 0) := by
  have hv : Tendsto (fun w : Z×((E×K)×C(X,ℝ))=>(w.1,w.2.2))
      (𝓝 v) (𝓝 (v.1,v.2.2)) :=
    (continuous_fst.prodMk continuous_snd.snd).continuousAt.tendsto
  exact (hF (v.1,v.2.2)).comp hv

def fixedAuxiliary (d : PathHeatSectionwiseSignedSource Z E K X) (aux : E×K) :
    PathHeatContinuousSignedSource (Z×((E×K)×C(X,ℝ))) X where
  ell v := d.ell (v.1,(aux,v.2.2))
  phi v := d.phi (v.1,(aux,v.2.2))
  dotell v := d.dotell (v.1,(aux,v.2.2))
  dotphi v := d.dotphi (v.1,(aux,v.2.2))
  S v := d.S (v.1,(aux,v.2.2))
  P v := d.P (v.1,(aux,v.2.2))
  M v := d.M (v.1,(aux,v.2.2))
  Q v := d.Q (v.1,(aux,v.2.2))
  B := d.B
  Ds := d.Ds
  Dm := d.Dm
  Dp := d.Dp
  Dq := d.Dq
  Dt := d.Dt
  Dphi := d.Dphi
  continuous_ell := (d.section aux).continuous_ell.comp (continuous_fst.prodMk continuous_snd.snd)
  continuous_phi := (d.section aux).continuous_phi.comp (continuous_fst.prodMk continuous_snd.snd)
  continuous_dotell := (d.section aux).continuous_dotell.comp (continuous_fst.prodMk continuous_snd.snd)
  continuous_dotphi := (d.section aux).continuous_dotphi.comp (continuous_fst.prodMk continuous_snd.snd)
  continuous_S v := pathHeatSectionwise_projection_tv
    (fun u : Z×C(X,ℝ)=>d.S (u.1,(aux,u.2))) (d.continuous_S aux) v
  continuous_P v := pathHeatSectionwise_projection_tv
    (fun u : Z×C(X,ℝ)=>d.P (u.1,(aux,u.2))) (d.continuous_P aux) v
  continuous_M v := pathHeatSectionwise_projection_tv
    (fun u : Z×C(X,ℝ)=>d.M (u.1,(aux,u.2))) (d.continuous_M aux) v
  continuous_Q v := pathHeatSectionwise_projection_tv
    (fun u : Z×C(X,ℝ)=>d.Q (u.1,(aux,u.2))) (d.continuous_Q aux) v
  bound_phi v := d.bound_phi _
  bound_dotell v := d.bound_dotell _
  bound_dotphi v := d.bound_dotphi _
  bound_S v := d.bound_S _
  bound_P v := d.bound_P _
  bound_M v := d.bound_M _
  bound_Q v := d.bound_Q _



end PathHeatSectionwiseSignedSource
variable {E K X : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {a b : ℝ}
theorem pathHeatSectionwise_fixedAuxiliary_analytic
    (hab : a≤b) (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (C : ℝ≥0) (h : PathHeatSectionwiseAnalyticSource a b hab d C) (aux : E×K) :
    PathHeatNativeAnalyticSource a b hab (d.fixedAuxiliary aux)
      (pathHeatWienerAuxGrowthConstant C aux) := by
  constructor
  · intro z ω p
    exact h.ell_derivative z aux p
  · intro z ω p
    exact h.phi_derivative z aux p
  · intro z ω p
    exact h.score_derivative z aux p
  · intro z ω p
    exact h.phi_score_derivative z aux p
  · intro ω z hz p
    exact h.ell_parameter aux z hz p
  · intro ω z hz p
    exact h.phi_parameter aux z hz p
  · intro z ω p
    change |d.ell (z,(aux,p))|≤(pathHeatWienerAuxGrowthConstant C aux:ℝ)*(1+‖ω.1‖+‖p‖)
    have hc : (C:ℝ)≤pathHeatWienerAuxGrowthConstant C aux := by
      simp only [pathHeatWienerAuxGrowthConstant,NNReal.coe_mul,NNReal.coe_add,
        NNReal.coe_one,coe_nnnorm]
      nlinarith [mul_nonneg C.coe_nonneg (norm_nonneg aux.1)]
    calc
      _ ≤ C*(1+‖aux.1‖+‖p‖) := h.ell_growth z aux p
      _ = (pathHeatWienerAuxGrowthConstant C aux:ℝ)+C*‖p‖ := by
        simp only [pathHeatWienerAuxGrowthConstant,NNReal.coe_mul,NNReal.coe_add,
          NNReal.coe_one,coe_nnnorm]
        ring
      _ ≤ (pathHeatWienerAuxGrowthConstant C aux:ℝ)+pathHeatWienerAuxGrowthConstant C aux*‖p‖ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hc (norm_nonneg p))
      _ ≤ _ := by nlinarith [mul_nonneg (pathHeatWienerAuxGrowthConstant C aux).coe_nonneg (norm_nonneg ω.1)]

theorem pathHeatSectionwise_fixedAuxiliary_wiener_analytic {L : ℕ}
    (hab : a≤b) (d : PathHeatSectionwiseSignedSource (Icc a b) E K (Fin L×I))
    (C : ℝ≥0) (h : PathHeatSectionwiseAnalyticSource a b hab d C) (aux : E×K) :
    PathHeatWienerAnalyticSource a b hab (d.fixedAuxiliary aux)
      (pathHeatWienerAuxGrowthConstant C aux) := by
  have hd := pathHeatSectionwise_fixedAuxiliary_analytic hab d C h aux
  exact ⟨hd.ell_derivative,hd.phi_derivative,hd.score_derivative,hd.phi_score_derivative,
    hd.ell_parameter,hd.phi_parameter,hd.ell_growth⟩

end HexagonPaper
