module
public import QuantitativePaper.VectorProfileRetainedExpectedContinuity
public import QuantitativePaper.VectorProfileActualWeightedSource
public import FourPapersCommon.ClosedNonnegativeSourceFTC
public import FourPapersCommon.BoundedTimeInterval

@[expose] public section

/-! Actual nonnegative profile energies are integrable to closed cell
endpoints, even when their pointwise source jets have no endpoint bound. -/
noncomputable section
open MeasureTheory Set Filter StochasticCalculus
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem nnreal_source_interval_to_real (g : ℝ≥0→ℝ) (a b : ℝ≥0) (hab : a≤b)
    (hg : IntegrableOn g (Ioc a b) nonnegativeLebesgueMeasure) :
    IntegrableOn (fun r : ℝ=>g r.toNNReal) (Ioc (a:ℝ) (b:ℝ)) volume ∧
      (∫r in Ioc a b,g r∂nonnegativeLebesgueMeasure)=
        ∫r in (a:ℝ)..(b:ℝ),g r.toNNReal := by
  have hp : MeasurePreserving ((↑):ℝ≥0→ℝ)
      (nonnegativeLebesgueMeasure.restrict (Ioc a b))
      (volume.restrict (Ioc (a:ℝ) (b:ℝ))):=
    ⟨NNReal.continuous_coe.measurable,map_nonnegativeLebesgueMeasure_restrict_interval a b⟩
  have hi : IntegrableOn (fun r : ℝ=>g r.toNNReal) (Ioc (a:ℝ) (b:ℝ)) volume:=by
    apply (hp.integrable_comp_emb measurableEmbedding_nnrealCoe_iterated).mp
    simpa only [Function.comp_def,Real.toNNReal_coe,IntegrableOn] using hg
  refine ⟨hi,?_⟩
  have he:=hp.integral_comp measurableEmbedding_nnrealCoe_iterated (fun r : ℝ=>g r.toNNReal)
  rw [intervalIntegral.integral_of_le (NNReal.coe_le_coe.mpr hab)]
  simpa only [Function.comp_def,Real.toNNReal_coe] using he

theorem vectorProfileRetainedExpectation_eq_cell
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1) (hθ : θ∈Icc (0:ℝ) 1)
    (F : ℝ→VectorProfileParameter n×Field n→ℝ) (G : VectorProfileCellParameter n×Field n→ℝ)
    (q : ℝ≥0) (he : ∀p : Couplings n×ℝ,∀x : Field n,F q ((θ,p),x)=G ((q,θ,p),x)) :
    vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht hθ F q=
      vectorProfileCellExpectation s₀ s₁ β t outer θ ht hθ G q := by
  unfold vectorProfileRetainedExpectation vectorProfileCellExpectation
  simp only [Real.toNNReal_coe]
  exact integral_congr_ae (.of_forall fun sample=>he sample.1 _)

theorem vectorProfile_closed_nonnegative_source_interval
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1) (hθ : θ∈Icc (0:ℝ) 1)
    (i : ℕ) (hi : i≤k+1)
    (F : ℝ→VectorProfileParameter n×Field n→ℝ)
    (G H : VectorProfileCellParameter n×Field n→ℝ)
    (hF : ContinuousOn (vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht hθ F)
      (Icc (s₀.q i) (s₀.q (i+1))))
    (he : ∀q∈Ioo (s₀.q i) (s₀.q (i+1)),∀p : Couplings n×ℝ,∀x : Field n,
      F q ((θ,p),x)=G ((q,θ,p),x))
    (hH : ∀z,0≤H z)
    (hc : ∀a b : ℝ≥0,a≤b→s₀.q i<(a:ℝ)→(b:ℝ)<s₀.q (i+1)→
      VectorProfileExpectedIntervalIdentity s₀ s₁ β t outer θ ht hθ G H a b) :
    let E:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht hθ
    IntegrableOn (fun r : ℝ=>E H r.toNNReal) (Ioc (s₀.q i) (s₀.q (i+1))) volume ∧
      vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht hθ F (s₀.q (i+1))-
        vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht hθ F (s₀.q i)=
        ∫r in (s₀.q i)..(s₀.q (i+1)),E H r.toNNReal := by
  apply closed_nonnegative_source_ftc _ _ _ _ (s₀.q_mono i (by omega)) hF
  · intro r hr
    exact integral_nonneg (fun sample=>hH _)
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

theorem vectorProfile_second_variation_closed_source (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1) :
    let E:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
    IntegrableOn (fun r : ℝ=>E (vectorProfileFieldSecondVariationSource (n:=n) s₀ s₁ β t i) r.toNNReal)
      (Ioc (s₀.q i) (s₀.q (i+1))) volume ∧
      vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
        (vectorProfileRetainedSecondVariation (n:=n) s₀ s₁ β t i) (s₀.q (i+1))-
      vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
        (vectorProfileRetainedSecondVariation (n:=n) s₀ s₁ β t i) (s₀.q i)=
        ∫r in (s₀.q i)..(s₀.q (i+1)),E (vectorProfileFieldSecondVariationSource s₀ s₁ β t i) r.toNNReal := by
  apply vectorProfile_closed_nonnegative_source_interval s₀ s₁ β t outer θ ht.le
    ⟨hθ.1.le,hθ.2.le⟩ i hi _ _ _
    (continuousOn_vectorProfileRetainedSecondVariation_expectation hn s₀ s₁ β t outer θ ht.le hθ i hi)
  · intro q hq p x
    exact vectorProfileRetainedSecondVariation_eq_field s₀ s₁ β t hβ.ne' ht i hi q hq ((θ,p),x) hθ
  · intro z
    exact mul_nonneg (sub_nonneg.mpr ht.le) (responseMatrixFrobeniusSquare_nonneg _)
  · intro a b hab ha hb
    exact vectorProfile_second_variation_expected_source_interval hn s₀ s₁ β t outer θ hβ ht i hi hθ a b hab ha hb

theorem vectorProfile_trace_reaction_closed_source (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (hθ : θ∈Ioo (0:ℝ) 1) :
    let E:=vectorProfileCellExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
    IntegrableOn (fun r : ℝ=>E (vectorProfileFieldTraceTimeSource (n:=n) s₀ s₁ β t i) r.toNNReal)
      (Ioc (s₀.q i) (s₀.q (i+1))) volume ∧
      vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
        (vectorProfileRetainedTraceReaction (n:=n) s₀ s₁ β t i) (s₀.q (i+1))-
      vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
        (vectorProfileRetainedTraceReaction (n:=n) s₀ s₁ β t i) (s₀.q i)=
        ∫r in (s₀.q i)..(s₀.q (i+1)),E (vectorProfileFieldTraceTimeSource s₀ s₁ β t i) r.toNNReal := by
  apply vectorProfile_closed_nonnegative_source_interval s₀ s₁ β t outer θ ht.le
    ⟨hθ.1.le,hθ.2.le⟩ i hi _ _ _
    (continuousOn_vectorProfileRetainedTraceReaction_expectation hn s₀ s₁ β t outer θ ht.le hθ i hi)
  · intro q hq p x
    exact (vectorProfileRetainedTraceReaction_eq_field s₀ s₁ β t hβ.ne' ht i hi q hq ((θ,p),x) hθ).trans
      (vectorProfileCellFieldTraceTimeExtension_eq_time s₀ s₁ β t hβ.ne' ht i hi
        (q,θ,p) hq hθ x).symm
  · intro z
    exact mul_nonneg (by norm_num : (0:ℝ)≤2) (responseMatrixFrobeniusSquare_nonneg _)
  · intro a b hab ha hb
    exact vectorProfile_trace_time_extension_expected_source_interval hn s₀ s₁ β t outer θ hβ ht i hi hθ a b hab ha hb

end QuantitativePaper
