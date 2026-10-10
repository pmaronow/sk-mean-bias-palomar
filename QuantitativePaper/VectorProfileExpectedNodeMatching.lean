module
public import QuantitativePaper.VectorProfileActualClosedWeightedSource
public import QuantitativePaper.VectorProfileRetainedNodeMatching
public import QuantitativePaper.VectorProfileClosedCurvaturePairing
public import QuantitativePaper.VectorProfileClosedLegendreVariations

@[expose] public section

/-! True closed-node matching of expected profile variations and the
literal trace-reaction jump under the same constructed fractional law. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem vectorProfileRetainedSecondVariation_match
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (i j : ℕ) (hi : i≤k+1) (hj : j≤k+1)
    (q : ℝ) (hqi : q∈Icc (s₀.q i) (s₀.q (i+1)))
    (hqj : q∈Icc (s₀.q j) (s₀.q (j+1)))
    (z : VectorProfileParameter n×Field n) (hθ : z.1.1∈Ioo (0:ℝ) 1) :
    vectorProfileRetainedSecondVariation s₀ s₁ β t j q z=
      vectorProfileRetainedSecondVariation s₀ s₁ β t i q z := by
  rw [vectorProfileRetainedSecondVariation_eq_field_closed s₀ s₁ β t ht j hj q hqj z hθ,
    vectorProfileRetainedSecondVariation_eq_field_closed s₀ s₁ β t ht i hi q hqi z hθ]
  exact vectorProfileCellFieldSecondVariation_match s₀ s₁ β t i j hi hj (q,z.1) hqi hqj
    ⟨hθ.1.le,hθ.2.le⟩ z.2

theorem vectorProfileRetainedCurvaturePairing_match
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i j : ℕ) (hi : i≤k+1) (hj : j≤k+1)
    (q : ℝ) (hqi : q∈Icc (s₀.q i) (s₀.q (i+1)))
    (hqj : q∈Icc (s₀.q j) (s₀.q (j+1)))
    (z : VectorProfileParameter n×Field n) (hθ : z.1.1∈Ioo (0:ℝ) 1) :
    vectorProfileRetainedCurvaturePairing s₀ s₁ β t j q z=
      vectorProfileRetainedCurvaturePairing s₀ s₁ β t i q z := by
  unfold vectorProfileRetainedCurvaturePairing
  rw [←vectorProfileCellCurvaturePairing_retained_formula_closed s₀ s₁ β t hβ ht j hj
    (q,z.1) hqj hθ z.2,
    ←vectorProfileCellCurvaturePairing_retained_formula_closed s₀ s₁ β t hβ ht i hi
    (q,z.1) hqi hθ z.2]
  exact vectorProfileCellFieldCurvaturePairing_match s₀ s₁ β t i j hi hj (q,z.1) hqi hqj
    ⟨hθ.1.le,hθ.2.le⟩ z.2

theorem vectorProfileRetainedTraceSquare_match
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (i j : ℕ) (hi : i≤k+1) (hj : j≤k+1)
    (q : ℝ) (hqi : q∈Icc (s₀.q i) (s₀.q (i+1)))
    (hqj : q∈Icc (s₀.q j) (s₀.q (j+1)))
    (z : VectorProfileParameter n×Field n) (hθ : z.1.1∈Icc (0:ℝ) 1) :
    vectorProfileRetainedTraceSquare s₀ s₁ β t j q z=
      vectorProfileRetainedTraceSquare s₀ s₁ β t i q z := by
  unfold vectorProfileRetainedTraceSquare
  rw [vectorProfileCell_potential_function_match s₀ s₁ β t i j hi hj (q,z.1) hqi hqj hθ]

theorem vectorProfile_retained_second_variation_expected_match
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (hθ : θ∈Ioo (0:ℝ) 1) (i j : ℕ) (hi : i≤k+1) (hj : j≤k+1)
    (q : ℝ) (hqi : q∈Icc (s₀.q i) (s₀.q (i+1)))
    (hqj : q∈Icc (s₀.q j) (s₀.q (j+1))) :
    vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedSecondVariation (n:=n) s₀ s₁ β t j) q=
    vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedSecondVariation (n:=n) s₀ s₁ β t i) q := by
  unfold vectorProfileRetainedExpectation
  exact integral_congr_ae (.of_forall fun sample=>
    vectorProfileRetainedSecondVariation_match s₀ s₁ β t ht i j hi hj q hqi hqj _ hθ)

theorem vectorProfile_retained_pairing_expected_match
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : β≠0) (ht : t<1)
    (hθ : θ∈Ioo (0:ℝ) 1) (i j : ℕ) (hi : i≤k+1) (hj : j≤k+1)
    (q : ℝ) (hqi : q∈Icc (s₀.q i) (s₀.q (i+1)))
    (hqj : q∈Icc (s₀.q j) (s₀.q (j+1))) :
    vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedCurvaturePairing (n:=n) s₀ s₁ β t j) q=
    vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedCurvaturePairing (n:=n) s₀ s₁ β t i) q := by
  unfold vectorProfileRetainedExpectation
  exact integral_congr_ae (.of_forall fun sample=>
    vectorProfileRetainedCurvaturePairing_match s₀ s₁ β t hβ ht i j hi hj q hqi hqj _ hθ)

theorem vectorProfile_retained_reaction_expected_jump (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (hθ : θ∈Ioo (0:ℝ) 1) (i j : ℕ) (hi : i≤k+1) (hj : j≤k+1)
    (q : ℝ) (hqi : q∈Icc (s₀.q i) (s₀.q (i+1)))
    (hqj : q∈Icc (s₀.q j) (s₀.q (j+1))) :
    vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedTraceReaction (n:=n) s₀ s₁ β t j) q-
    vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedTraceReaction (n:=n) s₀ s₁ β t i) q=
      -(1-t)*β*(vectorProfileMass s₀ s₁ θ j-vectorProfileMass s₀ s₁ θ i)*
        vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht ⟨hθ.1.le,hθ.2.le⟩
          (vectorProfileRetainedTraceSquare (n:=n) s₀ s₁ β t i) q := by
  let s:=vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩
  have hq0 : 0≤q:=(s₀.q_nonneg (by omega)).trans hqi.1
  have hqni : (q.toNNReal:ℝ)∈Icc (s₀.q i) (s₀.q (i+1)):=by simpa only [Real.coe_toNNReal _ hq0] using hqi
  have hqnj : (q.toNNReal:ℝ)∈Icc (s₀.q j) (s₀.q (j+1)):=by simpa only [Real.coe_toNNReal _ hq0] using hqj
  have hIi:=integrable_vectorProfile_retained_reaction hn s₀ s₁ β t outer θ ht i hi hθ q.toNNReal hqni
  have hIj:=integrable_vectorProfile_retained_reaction hn s₀ s₁ β t outer θ ht j hj hθ q.toNNReal hqnj
  simp only [Real.coe_toNNReal _ hq0] at hIi hIj
  unfold vectorProfileRetainedExpectation
  rw [←integral_sub hIj hIi]
  have he : (fun sample : VectorDisorderBrownianSample n=>
      vectorProfileRetainedTraceReaction s₀ s₁ β t j q
        ((θ,sample.1),vectorFiniteState s β t ht q.toNNReal sample)-
      vectorProfileRetainedTraceReaction s₀ s₁ β t i q
        ((θ,sample.1),vectorFiniteState s β t ht q.toNNReal sample))=
    (fun sample=> (-(1-t)*β*(vectorProfileMass s₀ s₁ θ j-vectorProfileMass s₀ s₁ θ i))*
      vectorProfileRetainedTraceSquare s₀ s₁ β t i q
        ((θ,sample.1),vectorFiniteState s β t ht q.toNNReal sample)):=by
    funext sample
    rw [vectorProfileRetainedTraceReaction_jump s₀ s₁ β t i j hi hj q hqi hqj _ ⟨hθ.1.le,hθ.2.le⟩]
    unfold vectorProfileRetainedTraceSquare
    ring
  simp only [Pi.sub_apply]
  rw [he,integral_const_mul]

end QuantitativePaper
