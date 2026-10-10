module
public import QuantitativeFollowup.FollowupCavityMixtureUniformWeightedJets
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! Compact positive-parameter families have actual common exponential
bounds, obtained from the continuous value of their genuine normalizer. -/
noncomputable section
open Set FourPapersCommon QuantitativePaper
open scoped ContDiff Topology BigOperators
namespace QuantitativeFollowup
variable {S P J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  [TopologicalSpace P] [FirstCountableTopology P] [CompactSpace P] {n : ℕ}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem cavityOuterPosterior_family_common_exponential_bound
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀i,0≤a i)
    (L : P→ℕ→Field n→L[ℝ]FiniteStateField S) (hL : ∀i,Continuous (fun p=>L p i))
    (s : ℝ) (N r : ℕ) (R : FiniteStateGaussianInput J→L[ℝ]FiniteStateField S)
    (F : P→FiniteStateField S→ℝ) (C : ℕ→ℝ) (hC : ∀i,0≤C i)
    (hrel : ∀p i,i≤r → ∀H,‖iteratedFDeriv ℝ i (F p) H‖≤
      C i*cavityOuterPosteriorNormalizer V a (L p) s N R H) :
    ∃B:ℝ,0≤B ∧ ∀p i,i≤r → ∀H,
      ‖iteratedFDeriv ℝ i (F p) H‖≤B*Real.exp (|s| * ‖H‖) :=by
  have hc:Continuous (fun p:P=>cavityOuterPosteriorNormalizer V a (L p) s N R 0):=
    (continuous_cavityOuterPosteriorNormalizer_input_family V a ha L hL s N R).comp
      (continuous_id.prodMk continuous_const)
  obtain ⟨Z,hZ⟩:BddAbove (range (fun p:P=>cavityOuterPosteriorNormalizer V a (L p) s N R 0)):=
    (isCompact_range hc).bddAbove
  let Z0:=max Z 0
  have hZ0:0≤Z0:=le_max_right _ _
  let B:=Z0*(∑i∈Finset.range (r+1),C i)
  have hB:0≤B:=mul_nonneg hZ0 (Finset.sum_nonneg fun i _=>hC i)
  refine ⟨B,hB,?_⟩
  intro p i hi H
  have hzi:cavityOuterPosteriorNormalizer V a (L p) s N R 0≤Z0:=
    (hZ (mem_range_self p)).trans (le_max_left _ _)
  have hz:=cavityOuterPosteriorNormalizer_shift_bound V a ha (L p) s N R H 0
  simp only [sub_zero] at hz
  have hci:C i≤∑j∈Finset.range (r+1),C j:=Finset.single_le_sum
    (fun j _=>hC j) (Finset.mem_range.mpr (by omega))
  apply (hrel p i hi H).trans
  have h1:=mul_le_mul_of_nonneg_left hz (hC i)
  have h2:=mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hzi (Real.exp_pos (|s| * ‖H‖)).le) (hC i)
  have h3:=mul_le_mul_of_nonneg_right hci
    (mul_nonneg hZ0 (Real.exp_pos (|s| * ‖H‖)).le)
  exact h1.trans (h2.trans (by simpa only [B,mul_comm,mul_left_comm,mul_assoc] using h3))

end QuantitativeFollowup
