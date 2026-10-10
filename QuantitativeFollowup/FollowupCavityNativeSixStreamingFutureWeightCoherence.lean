module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceBracket
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingMarkCoherence
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingMovingTerminalMoments

@[expose] public section

/-! Actual shared-future marked expectations have the fork-root coherence
needed for attachment charge regrouping. The old record is integrated
against its genuine law, with no coherence or integrability premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingFutureTerminalMoment_eq_integral
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) (r : Paper.Overlap)
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    (∫z,G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
      ∂nativeStreamingFuturePairLaw D μ a q T v r) =
      ∫z,∫σ,G (finiteCascadeRecordTerminalSpins T z.2,σ)
        ∂((anisotropicObservationTerminalSpinKernel D μ r ×ₖ
          anisotropicObservationTerminalSpinKernel D μ r) ∘ₖ
            anisotropicObservationTransition D μ (q v.depth) r)
              (nativeStreamingVertexState v z.1 z.2)
                ∂anisotropicRecordedProfileTreeLaw D μ a q T := by
  classical
  let P := nativeStreamingFuturePairLaw D μ a q T v r
  haveI : IsProbabilityMeasure P := by
    dsimp only [P,nativeStreamingFuturePairLaw]
    infer_instance
  let C := ∑σ : TerminalSpins (Configuration n) T × (Configuration n × Configuration n),|G σ|
  have hG : Measurable (fun z : (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) ×
      (Configuration n × Configuration n) =>
    G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) :=
    (measurable_of_finite G).comp
      (((measurable_finiteCascadeRecordTerminalSpins T).comp
        (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  have hi : Integrable (fun z=>G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) P := by
    apply (integrable_const C).mono' hG.aestronglyMeasurable
    exact .of_forall fun z=>by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f:=fun σ=>|G σ|) (fun _ _=>abs_nonneg _)
        (Finset.mem_univ _)
  dsimp only [P,nativeStreamingFuturePairLaw] at hi
  unfold nativeStreamingFuturePairLaw
  rw [Measure.integral_compProd hi]
  rfl

theorem nativeStreamingFutureMaskedMoment_vertex_root_coherent
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (r : Paper.Overlap) :
    nativeStreamingRootCoherent T (fun v=>if q v.depth<r then
      (∫z,nativeStreamingDefectSpinTest T F r (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
        ∂nativeStreamingFuturePairLaw D μ a q T v r) else 0) := by
  classical
  have h := nativeStreamingVertexState_integral_root_coherent T
    (anisotropicRecordedProfileTreeLaw D μ a q T)
    (fun z d x=>if q d<r then
      ∫σ,nativeStreamingDefectSpinTest T F r (finiteCascadeRecordTerminalSpins T z.2,σ)
        ∂((anisotropicObservationTerminalSpinKernel D μ r ×ₖ
          anisotropicObservationTerminalSpinKernel D μ r) ∘ₖ
            anisotropicObservationTransition D μ (q d) r) x else 0)
  convert h using 1
  funext v
  by_cases hv : q v.depth<r
  · simp only [hv,ite_true]
    exact nativeStreamingFutureTerminalMoment_eq_integral D μ a q T v r
      (nativeStreamingDefectSpinTest T F r)
  · simp only [hv,ite_false,integral_zero]

theorem nativeStreamingRootCoherent_finset_sum {A : Type} (I : Finset A)
    (T : FiniteTerminalGenealogy J)
    (φ : A → FiniteCascadeRecordVertex T → ℝ)
    (hφ : ∀i∈I,nativeStreamingRootCoherent T (φ i)) :
    nativeStreamingRootCoherent T (fun v=>∑i∈I,φ i v) := by
  induction T with
  | leaf => trivial
  | advance T ih => exact ih (fun i v=>φ i (.child v)) hφ
  | fork T U ihT ihU =>
      refine ⟨?_,?_,?_,?_⟩
      · exact Finset.sum_congr rfl (fun i hi=>(hφ i hi).1)
      · exact Finset.sum_congr rfl (fun i hi=>(hφ i hi).2.1)
      · exact ihT (fun i v=>φ i (.left v)) (fun i hi=>(hφ i hi).2.2.1)
      · exact ihU (fun i v=>φ i (.right v)) (fun i hi=>(hφ i hi).2.2.2)

theorem nativeStreamingPatternFutureIntegral_vertex_root_coherent
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0=1)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    nativeStreamingRootCoherent T (fun v=>
      nativeStreamingPatternFutureIntegral D μ a q T F (.vertex v)) := by
  classical
  unfold nativeStreamingPatternFutureIntegral
  refine nativeStreamingRootCoherent_finset_sum (Finset.range J) T _ ?_
  intro j hj
  have h := nativeStreamingRootCoherent_integral
    ((parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j))) T
    (fun r v=>if q v.depth<r then
      (∫z,nativeStreamingDefectSpinTest T F r (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
        ∂nativeStreamingFuturePairLaw D μ a q T v r) else 0)
    (fun r=>nativeStreamingFutureMaskedMoment_vertex_root_coherent D μ a q T F r)
  convert h using 1
  funext v
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  change (if q v.depth<r then nativeStreamingPatternMoment D μ a q T F
    (.future (.vertex v) j r) else 0)=_
  by_cases hv : q v.depth<r
  · have hvj : j<v.depth := by
      by_contra hh
      have hle := hq (show v.depth≤j by omega)
      exact (not_lt_of_ge (hr.2.trans hle)) hv
    simp only [hv,ite_true,nativeStreamingPatternMoment,nativeStreamingTerminalMarkMoment]
    rw [nativeStreamingOriginFutureProbability_vertex_eq_law D μ a q hq hzero T v j hvj r
      ⟨hr.1.le,hr.2⟩]
  · simp only [hv,ite_false]

end QuantitativeFollowup
