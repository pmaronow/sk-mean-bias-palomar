module
public import QuantitativePaper.VectorProfileExpectedXi

@[expose] public section

/-! The literal expected Xi square is nonnegative. The formula is a
genuine integral of the actual matrix square under the constructed law. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology MatrixOrder
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem vectorProfile_expected_Xi_energy_nonneg (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1)
    (q : ℝ≥0) (hq : (q:ℝ)∈Ioo (s₀.q i) (s₀.q (i+1))) (φ δ : ℝ) :
    let E:=vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
    let R:=vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
    0≤δ^2*R (vectorProfileRetainedPhysicalTrace s₀ s₁ β t i) q+
      2*(2*δ*φ*R (vectorProfileRetainedTraceReaction s₀ s₁ β t i) q+
        φ^2*E (vectorProfileFieldTraceTimeSource s₀ s₁ β t i) q) := by
  let hθ01 : θ∈Icc (0:ℝ) 1:=⟨hθ.1.le,hθ.2.le⟩
  let s:=vectorProfileScheme s₀ s₁ θ hθ01
  let P:=vectorFiniteDisorderTilt (n:=n) s β t outer
  let X:=vectorFiniteState (n:=n) s β t ht.le
  let V:=fun ω : VectorDisorderBrownianSample n=>vectorProfileRetainedPhysicalTrace s₀ s₁ β t i q ((θ,ω.1),X q ω)
  let J:=fun ω : VectorDisorderBrownianSample n=>vectorProfileRetainedTraceReaction s₀ s₁ β t i q ((θ,ω.1),X q ω)
  let N:=fun ω : VectorDisorderBrownianSample n=>vectorProfileFieldTraceTimeSource s₀ s₁ β t i ((q,θ,ω.1),X q ω)
  have hV : Integrable V P:=integrable_vectorProfile_retained_physical_trace s₀ s₁ β t outer θ ht.le i hi hθ q ⟨hq.1.le,hq.2.le⟩
  have hJ : Integrable J P:=integrable_vectorProfile_retained_reaction hn s₀ s₁ β t outer θ ht.le i hi hθ q ⟨hq.1.le,hq.2.le⟩
  have hN : Integrable N P:=integrable_vectorProfile_trace_time_source hn s₀ s₁ β t outer θ hβ ht i hi hθ q hq
  have hh : 0≤∫ω,δ^2*V ω+2*(2*δ*φ*J ω+φ^2*N ω)∂P:=by
    apply integral_nonneg
    intro ω
    have he:=vectorProfileCellFieldXi_energy s₀ s₁ β t hβ ht i hi (q,θ,ω.1) hq hθ (X q ω) φ δ
    have hV':=vectorProfileRetainedPhysicalTrace_eq_physical s₀ s₁ β t hβ.ne' i hi q ⟨hq.1.le,hq.2.le⟩ ((θ,ω.1),X q ω) hθ01
    have hJ':=(vectorProfileRetainedTraceReaction_eq_field s₀ s₁ β t hβ.ne' ht i hi q hq ((θ,ω.1),X q ω) hθ).trans
      (vectorProfileCellFieldTraceTimeExtension_eq_time s₀ s₁ β t hβ.ne' ht i hi (q,θ,ω.1) hq hθ (X q ω)).symm
    dsimp only at he hV' hJ'
    rw [←hV',←hJ'] at he
    change 0≤δ^2*V ω+2*(2*δ*φ*J ω+φ^2*N ω)
    rw [←he]
    exact responseMatrixFrobeniusSquare_nonneg _
  have e₁:=integral_add (hV.const_mul (δ^2)) (((hJ.const_mul (2*δ*φ)).add (hN.const_mul (φ^2))).const_mul 2)
  have e₂:=integral_add (hJ.const_mul (2*δ*φ)) (hN.const_mul (φ^2))
  simp only [Pi.add_apply] at e₁ e₂
  rw [e₁,integral_const_mul,integral_const_mul,e₂,integral_const_mul,integral_const_mul] at hh
  dsimp only
  unfold vectorProfileRetainedExpectation
  simp only [Real.toNNReal_coe]
  exact hh

end QuantitativePaper
