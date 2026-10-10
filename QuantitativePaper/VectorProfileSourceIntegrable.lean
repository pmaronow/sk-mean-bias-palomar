module
public import QuantitativePaper.VectorProfileGeneratorExponential

@[expose] public section

/-! Fixed strict-time generator sources are genuinely integrable under
 the actual fractional diffusion law, from the proved exponential jets. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem integrable_vectorProfile_cell_source
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (F H : VectorProfileCellParameter n×Field n→ℝ)
    (hGrowth : ∀ l u A B : ℝ,s₀.q i<l→u<s₀.q (i+1)→0<A→B<1→
      ExponentialSmoothOn F (vectorProfileJointCylinder l u A B))
    (he : ∀q∈Ioo (s₀.q i) (s₀.q (i+1)),∀p : Couplings n×ℝ,∀x : Field n,
      vectorProfileCellFieldGenerator s₀ s₁ β t i F (q,θ,p) x=H ((q,θ,p),x))
    (q : ℝ≥0) (hq : (q:ℝ)∈Ioo (s₀.q i) (s₀.q (i+1))) :
    Integrable (fun sample : VectorDisorderBrownianSample n=>
      H ((q,θ,sample.1),vectorFiniteState (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩)
        β t ht.le q sample))
      (vectorFiniteDisorderTilt (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t outer) := by
  let l:=(s₀.q i+(q:ℝ))/2
  let u:=((q:ℝ)+s₀.q (i+1))/2
  let A:=θ/2
  let B:=(θ+1)/2
  have hl : s₀.q i<l:=by dsimp [l]; linarith [hq.1]
  have hu : u<s₀.q (i+1):=by dsimp [u]; linarith [hq.2]
  have hA : 0<A:=by dsimp [A]; linarith [hθ.1]
  have hB : B<1:=by dsimp [B]; linarith [hθ.2]
  have hqu : (q:ℝ)∈Ioo l u:=by dsimp [l,u]; constructor <;> linarith [hq.1,hq.2]
  have hθAB : θ∈Ioo A B:=by dsimp [A,B]; constructor <;> linarith [hθ.1,hθ.2]
  have hG:=exponentialSmoothOn_vectorProfileCellFieldGenerator s₀ s₁ β t hβ ht i hi
    l u A B hu hA hB F (hGrowth l u A B hl hu hA hB)
  have hg:=integrable_vectorProfile_cell_observable s₀ s₁ β t outer θ ht.le l u A B
    ((s₀.q_nonneg (by omega)).trans hl.le)
    (hu.le.trans (s₀.q_le_one (by omega))) hA hB hθAB
    (fun z=>vectorProfileCellFieldGenerator s₀ s₁ β t i F z.1 z.2) hG q hqu
  apply hg.congr
  exact .of_forall fun sample=>he q hq sample.1 _

theorem integrable_vectorProfile_second_variation_source (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (q : ℝ≥0) (hq : (q:ℝ)∈Ioo (s₀.q i) (s₀.q (i+1))) :
    Integrable (fun sample : VectorDisorderBrownianSample n=>
      vectorProfileFieldSecondVariationSource s₀ s₁ β t i
        ((q,θ,sample.1),vectorFiniteState (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩)
          β t ht.le q sample))
      (vectorFiniteDisorderTilt (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t outer) := by
  exact integrable_vectorProfile_cell_source s₀ s₁ β t outer θ hβ.ne' ht i hi hθ
    (vectorProfileCellFieldSecondVariation s₀ s₁ β t i) _
    (fun l u A B hl hu hA hB=>exponentialSmoothOn_vectorProfileCellFieldSecondVariation
      hn s₀ s₁ β t hβ.ne' ht i hi l u A B hl.le hu hA hB)
    (fun q hq p x=>vectorProfileCellFieldSecondVariation_generator
      s₀ s₁ β t hβ ht i hi (q,θ,p) hq hθ x) q hq

theorem integrable_vectorProfile_curvature_pairing_source (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (q : ℝ≥0) (hq : (q:ℝ)∈Ioo (s₀.q i) (s₀.q (i+1))) :
    Integrable (fun sample : VectorDisorderBrownianSample n=>
      vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i
        ((q,θ,sample.1),vectorFiniteState (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩)
          β t ht.le q sample))
      (vectorFiniteDisorderTilt (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t outer) := by
  exact integrable_vectorProfile_cell_source s₀ s₁ β t outer θ hβ ht i hi hθ
    (vectorProfileCellFieldCurvaturePairing s₀ s₁ β t i) _
    (fun l u A B hl hu hA hB=>exponentialSmoothOn_vectorProfileCellFieldCurvaturePairing
      hn s₀ s₁ β t hβ ht i hi l u A B hl.le hu hA hB)
    (fun q hq p x=>vectorProfileCellFieldCurvaturePairing_generator
      s₀ s₁ β t hβ ht i hi (q,θ,p) hq hθ x) q hq

theorem integrable_vectorProfile_trace_time_source (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (q : ℝ≥0) (hq : (q:ℝ)∈Ioo (s₀.q i) (s₀.q (i+1))) :
    Integrable (fun sample : VectorDisorderBrownianSample n=>
      vectorProfileFieldTraceTimeSource s₀ s₁ β t i
        ((q,θ,sample.1),vectorFiniteState (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩)
          β t ht.le q sample))
      (vectorFiniteDisorderTilt (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t outer) := by
  exact integrable_vectorProfile_cell_source s₀ s₁ β t outer θ hβ.ne' ht i hi hθ
    (vectorProfileCellFieldTraceTime s₀ s₁ β t i) _
    (fun l u A B hl hu hA hB=>exponentialSmoothOn_vectorProfileCellFieldTraceTime
      hn s₀ s₁ β t hβ.ne' ht i hi l u A B hl.le hu hA hB)
    (fun q hq p x=>vectorProfileCellFieldTraceTime_generator
      s₀ s₁ β t hβ ht i hi (q,θ,p) hq hθ x) q hq

end QuantitativePaper
