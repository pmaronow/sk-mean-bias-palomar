module
public import QuantitativePaper.LocalSmoothIntegralJets
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

/-! Scalar derivatives of actual locally dominated parameter integrals. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuantitativePaper
variable {α : Type} [MeasurableSpace α]
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

structure ScalarDominatedJets (N : ℕ) (μ : Measure α) (f : ℝ→α→ℝ) (U : Set ℝ) : Prop where
  smooth : ∀z,ContDiffOn ℝ N (fun x=>f x z) U
  measurable : ∀r,r≤N→∀x∈U,AEStronglyMeasurable
    (fun z=>iteratedFDeriv ℝ r (fun y=>f y z) x) μ
  localBound : ∀x∈U,∃s∈𝓝 x,s⊆U ∧ ∃B : ℕ→α→ℝ,
    (∀r,r≤N→Integrable (B r) μ) ∧
    ∀r,r≤N→∀y∈s,∀z,‖iteratedFDeriv ℝ r (fun u=>f u z) y‖≤B r z

theorem ScalarDominatedJets.integrable_iteratedDeriv {N : ℕ} {μ : Measure α}
    {f : ℝ→α→ℝ} {U : Set ℝ} (h : ScalarDominatedJets N μ f U)
    {r : ℕ} (hr : r≤N) {x : ℝ} (hx : x∈U) :
    Integrable (fun z=>iteratedDeriv r (fun y=>f y z) x) μ := by
  obtain ⟨s,hs,hsu,B,hBi,hB⟩:=h.localBound x hx
  have hi : Integrable (fun z=>iteratedFDeriv ℝ r (fun y=>f y z) x) μ:=
    (hBi r hr).mono' (h.measurable r hr x hx)
      (.of_forall fun z=>hB r hr x (mem_of_mem_nhds hs) z)
  exact
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r=>ℝ) ℝ
      (fun _ : Fin r=>(1:ℝ))).integrable_comp hi

theorem ScalarDominatedJets.contDiffOn {N : ℕ} {μ : Measure α}
    {f : ℝ→α→ℝ} {U : Set ℝ} (h : ScalarDominatedJets N μ f U) (hU : IsOpen U) :
    ContDiffOn ℝ N (fun x=>∫z,f x z ∂μ) U :=
  contDiffOn_integral_of_dominated_derivatives N μ f U hU h.smooth h.measurable h.localBound

theorem ScalarDominatedJets.iteratedDeriv_integral {N : ℕ} {μ : Measure α}
    {f : ℝ→α→ℝ} {U : Set ℝ} (h : ScalarDominatedJets N μ f U) (hU : IsOpen U)
    {r : ℕ} (hr : r≤N) {x : ℝ} (hx : x∈U) :
    iteratedDeriv r (fun y=>∫z,f y z ∂μ) x=
      ∫z,iteratedDeriv r (fun y=>f y z) x ∂μ := by
  have he:=iteratedFDeriv_integral_of_locally_dominated_derivatives N μ f U hU
    h.smooth h.measurable h.localBound r hr x hx
  obtain ⟨s,hs,hsu,B,hBi,hB⟩:=h.localBound x hx
  have hi : Integrable (fun z=>iteratedFDeriv ℝ r (fun y=>f y z) x) μ:=
    (hBi r hr).mono' (h.measurable r hr x hx)
      (.of_forall fun z=>hB r hr x (mem_of_mem_nhds hs) z)
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  rw [he,ContinuousMultilinearMap.integral_apply hi]

theorem ScalarDominatedJets.hasDerivAt_integral {N : ℕ} {μ : Measure α}
    {f : ℝ→α→ℝ} {U : Set ℝ} (h : ScalarDominatedJets N μ f U) (hU : IsOpen U)
    (hN : 1≤N) {x : ℝ} (hx : x∈U) :
    HasDerivAt (fun y=>∫z,f y z ∂μ) (∫z,deriv (fun y=>f y z) x ∂μ) x := by
  have hs:=(h.contDiffOn hU x hx).contDiffAt (hU.mem_nhds hx)
  have hd:=(hs.differentiableAt (by norm_cast;omega)).hasDerivAt
  have he:=h.iteratedDeriv_integral hU hN hx
  simp only [iteratedDeriv_one] at he
  rw [he] at hd
  exact hd

end QuantitativePaper
