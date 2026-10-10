module
public import QuantitativePaper.VectorJointResponse

@[expose] public section

/-! A single family of genuine response and potential bounds, uniform in
the initial disorder as well as the variance and field. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

structure VectorJointBackwardBounds (F G : VectorParameter n → ℝ) (m : ℝ) where
  responseBounds : ℕ → ℝ
  responseBounds_nonneg : ∀ j,0≤responseBounds j
  responseRegularity : ∀ v,ContDiff ℝ 3 (vectorJointResponse F G v m)
  responseJets : ∀ v j,j≤3 → ∀ p,
    ‖iteratedFDeriv ℝ j (vectorJointResponse F G v m) p‖≤responseBounds j
  potentialPower : ℝ≥0
  potentialPower_ge_one : 1≤potentialPower
  potentialRegularity : ∀ v,ContDiff ℝ 3 (vectorJointColeHopf F v m)
  potentialJets : ∀ v j,1≤j → j≤3 → ∀ p,
    ‖iteratedFDeriv ℝ j (vectorJointColeHopf F v m) p‖≤(potentialPower : ℝ)^j

theorem VectorJointResponseTestData.exists_jointBounds {F G : VectorParameter n → ℝ}
    (d : VectorJointResponseTestData F G) (m : ℝ) :
    Nonempty (VectorJointBackwardBounds F G m) := by
  obtain ⟨B,hB,hR⟩ := d.response_uniform_jets m
  obtain ⟨hU,D,hD,hUB⟩ := d.coleHopf_uniform_jets m
  exact ⟨{
    responseBounds := B
    responseBounds_nonneg := hB
    responseRegularity := fun v=>(hR v).1
    responseJets := fun v=>(hR v).2
    potentialPower := ⟨D,zero_le_one.trans hD⟩
    potentialPower_ge_one := hD
    potentialRegularity := hU
    potentialJets := hUB }⟩

def VectorJointResponseTestData.jointBounds {F G : VectorParameter n → ℝ}
    (d : VectorJointResponseTestData F G) (m : ℝ) : VectorJointBackwardBounds F G m :=
  Classical.choice (d.exists_jointBounds m)

def VectorJointBackwardBounds.responsePower {F G : VectorParameter n → ℝ} {m : ℝ}
    (h : VectorJointBackwardBounds F G m) : ℝ≥0 :=
  ⟨finiteJetPowerBound h.responseBounds 3,
    zero_le_one.trans (finiteJetPowerBound_ge_one h.responseBounds 3)⟩

theorem VectorJointBackwardBounds.responsePower_ge_one {F G : VectorParameter n → ℝ} {m : ℝ}
    (h : VectorJointBackwardBounds F G m) : 1≤h.responsePower :=
  finiteJetPowerBound_ge_one h.responseBounds 3

def VectorJointBackwardBounds.fieldBounds {F G : VectorParameter n → ℝ} {m : ℝ}
    (h : VectorJointBackwardBounds F G m) (p : Couplings n×ℝ) :
    VectorBackwardUniformBounds (fun x=>F (p,x)) (fun x=>G (p,x)) m where
  responsePower := h.responsePower
  responsePower_ge_one := h.responsePower_ge_one
  potentialPower := h.potentialPower
  potentialPower_ge_one := h.potentialPower_ge_one
  responseRegularity := fun v=>(h.responseRegularity v).comp (contDiff_const.prodMk contDiff_id)
  potentialRegularity := fun v=>(h.potentialRegularity v).comp (contDiff_const.prodMk contDiff_id)
  responseJets := by
    intro v j hj hjN x
    have hh := norm_iteratedFDeriv_fieldSlice_le (vectorJointResponse F G v m)
      (h.responseRegularity v) hjN p x (h.responseBounds j) (h.responseBounds_nonneg j)
      (h.responseJets v j hjN)
    exact hh.trans (finite_jet_bound_le_power h.responseBounds 3 j hj hjN)
  potentialJets := by
    intro v j hj hjN x
    exact norm_iteratedFDeriv_fieldSlice_le (vectorJointColeHopf F v m)
      (h.potentialRegularity v) hjN p x ((h.potentialPower : ℝ)^j)
      (pow_nonneg h.potentialPower.coe_nonneg _) (h.potentialJets v j hj hjN)

end QuantitativePaper
