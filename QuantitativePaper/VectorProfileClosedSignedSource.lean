module
public import QuantitativePaper.VectorProfileClosedPositiveSource
public import QuantitativePaper.VectorProfileExpectedSourceDomination
public import FourPapersCommon.ClosedSignedSourceFTC

@[expose] public section

/-! The true signed curvature-pairing source extends to closed cells
under the proved positive-energy domination; no endpoint derivative is
supplied as a hypothesis. -/
noncomputable section
open MeasureTheory Set Filter StochasticCalculus
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem vectorProfile_closed_dominated_source_interval
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1) (hθ : θ∈Icc (0:ℝ) 1)
    (i : ℕ) (hi : i≤k+1)
    (F : ℝ→VectorProfileParameter n×Field n→ℝ)
    (G H : VectorProfileCellParameter n×Field n→ℝ)
    (hF : ContinuousOn (vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht hθ F)
      (Icc (s₀.q i) (s₀.q (i+1))))
    (he : ∀q∈Ioo (s₀.q i) (s₀.q (i+1)),∀p : Couplings n×ℝ,∀x : Field n,
      F q ((θ,p),x)=G ((q,θ,p),x))
    (L : ℝ→ℝ) (hL : IntegrableOn L (Ioc (s₀.q i) (s₀.q (i+1))) volume)
    (hbound : ∀q∈Ioo (s₀.q i) (s₀.q (i+1)),
      |vectorProfileCellExpectation s₀ s₁ β t outer θ ht hθ H q.toNNReal|≤L q)
    (hc : ∀a b : ℝ≥0,a≤b→s₀.q i<(a:ℝ)→(b:ℝ)<s₀.q (i+1)→
      VectorProfileExpectedIntervalIdentity s₀ s₁ β t outer θ ht hθ G H a b) :
    let E:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht hθ
    IntegrableOn (fun r : ℝ=>E H r.toNNReal) (Ioc (s₀.q i) (s₀.q (i+1))) volume ∧
      vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht hθ F (s₀.q (i+1))-
        vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht hθ F (s₀.q i)=
        ∫r in (s₀.q i)..(s₀.q (i+1)),E H r.toNNReal := by
  apply closed_dominated_source_ftc _ _ L _ _ (s₀.q_mono i (by omega)) hF hL hbound
  · intro l hl u hu hlu
    have hl0 : 0≤l:=(s₀.q_nonneg (by omega)).trans hl.1.le
    have hu0 : 0≤u:=(s₀.q_nonneg (by omega)).trans hu.1.le
    let a : ℝ≥0:=⟨l,hl0⟩
    let b : ℝ≥0:=⟨u,hu0⟩
    have hab : a≤b:=hlu
    have hc':=hc a b hab hl.1 hu.2
    obtain ⟨hg,heq⟩:=hc'
    obtain ⟨hi',hiEq⟩:=nnreal_source_interval_to_real _ a b hab hg
    refine ⟨hi',?_⟩
    have hlEq:=vectorProfileRetainedExpectation_eq_cell s₀ s₁ β t outer θ ht hθ F G a
      (he l hl)
    have huEq:=vectorProfileRetainedExpectation_eq_cell s₀ s₁ β t outer θ ht hθ F G b
      (he u hu)
    change vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht hθ F (b:ℝ)-
      vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht hθ F (a:ℝ)=
      ∫r in (a:ℝ)..(b:ℝ),vectorProfileCellExpectation s₀ s₁ β t outer θ ht hθ H r.toNNReal
    rw [huEq,hlEq,heq,hiEq]

theorem vectorProfile_curvature_pairing_closed_source (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1) :
    let E:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
    IntegrableOn (fun r : ℝ=>E (vectorProfileFieldCurvaturePairingSource (n:=n) s₀ s₁ β t i) r.toNNReal)
      (Ioc (s₀.q i) (s₀.q (i+1))) volume ∧
      vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
        (vectorProfileRetainedCurvaturePairing (n:=n) s₀ s₁ β t i) (s₀.q (i+1))-
      vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
        (vectorProfileRetainedCurvaturePairing (n:=n) s₀ s₁ β t i) (s₀.q i)=
        ∫r in (s₀.q i)..(s₀.q (i+1)),E (vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i) r.toNNReal := by
  let E:=vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
  let T:=vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
    (fun q z=>‖vectorProfileRetainedTraceSquare s₀ s₁ β t i q z‖)
  let L : ℝ→ℝ:=fun q=>|(1-t)*(β*(s₁.m i-s₀.m i))| *T q+
    E (vectorProfileFieldSecondVariationSource s₀ s₁ β t i) q.toNNReal/(2*(1-t))+
    E (vectorProfileFieldTraceTimeSource s₀ s₁ β t i) q.toNNReal
  have hT : IntegrableOn T (Ioc (s₀.q i) (s₀.q (i+1))) volume:=
    (continuousOn_vectorProfileRetainedTraceSquare_abs_expectation (n:=n)
      s₀ s₁ β t outer θ ht.le hθ i hi).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hZ:=(vectorProfile_second_variation_closed_source hn s₀ s₁ β t outer θ hβ ht i hi hθ).1
  have hN:=(vectorProfile_trace_reaction_closed_source hn s₀ s₁ β t outer θ hβ ht i hi hθ).1
  have hL : IntegrableOn L (Ioc (s₀.q i) (s₀.q (i+1))) volume:=
    ((hT.const_mul _).add (hZ.div_const _)).add hN
  refine vectorProfile_closed_dominated_source_interval s₀ s₁ β t outer θ ht.le
    ⟨hθ.1.le,hθ.2.le⟩ i hi
    (vectorProfileRetainedCurvaturePairing s₀ s₁ β t i)
    (vectorProfileCellFieldCurvaturePairing s₀ s₁ β t i)
    (vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i)
    (continuousOn_vectorProfileRetainedCurvaturePairing_expectation hn s₀ s₁ β t outer θ ht.le hθ i hi)
    ?_ L hL ?_ ?_
  · intro q hq p x
    exact vectorProfileRetainedCurvaturePairing_eq_field s₀ s₁ β t hβ.ne' ht i hi q hq ((θ,p),x) hθ
  · intro q hq
    have hq0 : 0≤q:=(s₀.q_nonneg (by omega)).trans hq.1.le
    have hqn : (q.toNNReal:ℝ)∈Ioo (s₀.q i) (s₀.q (i+1)):=by
      simpa only [Real.coe_toNNReal _ hq0] using hq
    have he:=vectorProfile_expected_curvature_source_abs_bound hn s₀ s₁ β t outer θ hβ ht
      i hi hθ q.toNNReal hqn
    simpa only [Real.coe_toNNReal _ hq0,L,T,E] using he
  · intro a b hab ha hb
    exact vectorProfile_curvature_pairing_expected_source_interval hn s₀ s₁ β t outer θ hβ.ne' ht i hi hθ a b hab ha hb

end QuantitativePaper
