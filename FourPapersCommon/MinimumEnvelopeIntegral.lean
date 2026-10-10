module
public import FourPapersCommon.CompactLipschitzEnvelope

@[expose] public section

/-! The optimized endpoint integral is derived from Lipschitz absolute
continuity and the genuine almost-everywhere derivative. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace FourPapersCommon
set_option maxHeartbeats 500000

def minimumEnvelopeDefect {ι : Type*} (S : Set ι) (F : ℝ→ι→ℝ) (c t : ℝ) : ℝ:=
  -deriv (compactMinimumValue S F) t/c

theorem minimumEnvelopeDefect_integral {ι : Type*}
    (S : Set ι) (F : ℝ→ι→ℝ) (a b c : ℝ) (hc : c≠0) (K : NNReal)
    (hf : LipschitzOnWith K (compactMinimumValue S F) (uIcc a b)) :
    IntervalIntegrable (minimumEnvelopeDefect S F c) volume a b ∧
      compactMinimumValue S F a-compactMinimumValue S F b=
        c*(∫t in a..b,minimumEnvelopeDefect S F c t) := by
  obtain ⟨hi,_,he⟩:=lipschitz_envelope_endpoint_integral (compactMinimumValue S F) a b K hf
  refine ⟨hi.neg.div_const c,?_⟩
  unfold minimumEnvelopeDefect
  rw [intervalIntegral.integral_div,intervalIntegral.integral_neg,he]
  field_simp
  ring

theorem compactMinimumValue_endpoint_integral {ι : Type*} [TopologicalSpace ι]
    (S : Set ι) (hS : IsCompact S) (hne : S.Nonempty) (F G : ℝ→ι→ℝ)
    (a b : ℝ) (hab : a≤b) (K : NNReal)
    (hcμ : ∀t∈Icc a b,ContinuousOn (F t) S)
    (hct : ∀i∈S,ContinuousOn (fun t=>F t i) (Icc a b))
    (hd : ∀i∈S,∀t∈Ioo a b,HasDerivAt (fun r=>F r i) (G t i) t)
    (hb : ∀i∈S,∀t∈Ioo a b,|G t i|≤(K : ℝ)) :
    IntervalIntegrable (deriv (compactMinimumValue S F)) volume a b ∧
      (∀ᵐ t : ℝ,t∈Icc a b→DifferentiableAt ℝ (compactMinimumValue S F) t) ∧
      (∫t in a..b,deriv (compactMinimumValue S F) t)=
        compactMinimumValue S F b-compactMinimumValue S F a := by
  have hl:=compactMinimumValue_lipschitz S hS hne F G a b K hcμ hct hd hb
  rw [←uIcc_of_le hab] at hl ⊢
  exact lipschitz_envelope_endpoint_integral (compactMinimumValue S F) a b K hl

end FourPapersCommon
