module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingMarkedLaw

@[expose] public section

/-! An edge at equal physical times has the actual identity transition.
The complete old record is retained: its initial state and child root
agree almost everywhere, as do their genuine conditional mark laws. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n j : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingRecordedKernel_zeroEdge_eq
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy j)
    (hq : q (j+1)=q j) :
    anisotropicRecordedProfileTreeKernel D μ q T.advance=
      Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ q T := by
  simp only [anisotropicRecordedProfileTreeKernel]
  rw [hq,anisotropicObservationTransition_same_time,Kernel.comp_id]

theorem nativeStreamingRecordedKernel_zeroEdge_coherent
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy j)
    (hq : q (j+1)=q j) (x : AnisotropicObservationState n) :
    ∀ᵐ y ∂anisotropicRecordedProfileTreeKernel D μ q T.advance x, x=y.1 := by
  rw [nativeStreamingRecordedKernel_zeroEdge_eq D μ q T hq]
  have hk : (Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ q T) x=
      (anisotropicRecordedProfileTreeKernel D μ q T x).map (fun y=>(x,y)) := by
    ext u hu
    rw [Kernel.id_prod_apply' _ x hu]
    have hm : Measurable (fun y : Records (AnisotropicObservationState n)
        (Configuration n) T => (x,y)) := measurable_const.prodMk measurable_id
    exact (Measure.map_apply (f := fun y => (x,y))
      (μ := anisotropicRecordedProfileTreeKernel D μ q T x) hm hu).symm
  rw [hk]
  exact (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable
    (measurableSet_eq_fun measurable_const measurable_fst)).mpr (.of_forall fun _ => rfl)

theorem nativeStreamingRecordedLaw_zeroEdge_coherent_of_measure
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy j)
    (hq : q (j+1)=q j) (P : Measure (AnisotropicObservationState n)) :
    ∀ᵐ z ∂(P ⊗ₘ anisotropicRecordedProfileTreeKernel D μ q T.advance), z.1=z.2.1 :=
  Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun measurable_fst measurable_snd.fst)
    (.of_forall (nativeStreamingRecordedKernel_zeroEdge_coherent D μ q T hq))

theorem nativeStreamingRecordedLaw_zeroEdge_coherent
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy j)
    (hq : q (j+1)=q j) :
    ∀ᵐ z ∂anisotropicRecordedProfileTreeLaw D μ a q T.advance, z.1=z.2.1 :=
  nativeStreamingRecordedLaw_zeroEdge_coherent_of_measure D μ q T hq
    (anisotropicObservationInitialLaw D μ a)

theorem nativeStreamingSingleVertexKernel_zeroEdge_eq
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy j)
    (hq : q (j+1)=q j) :
    nativeStreamingSingleVertexKernel D μ q T.advance (.root T.advance) =ᵐ[
      anisotropicRecordedProfileTreeLaw D μ a q T.advance]
        nativeStreamingSingleVertexKernel D μ q T.advance (.child (.root T)) := by
  filter_upwards [nativeStreamingRecordedLaw_zeroEdge_coherent D μ a q T hq] with z hz
  change anisotropicObservationTerminalSpinKernel D μ (q (j+1)) z.1=
    anisotropicObservationTerminalSpinKernel D μ (q j) z.2.1
  rw [hq,hz]

theorem nativeStreamingSingleVertexLaw_zeroEdge_eq
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy j)
    (hq : q (j+1)=q j) :
    nativeStreamingSingleVertexLaw D μ a q T.advance (.root T.advance)=
      nativeStreamingSingleVertexLaw D μ a q T.advance (.child (.root T)) := by
  haveI : IsMarkovKernel
      (nativeStreamingSingleVertexKernel D μ q T.advance (.root T.advance)) :=
    nativeStreamingSingleVertexKernel_markov D μ q T.advance (.root T.advance)
  haveI : IsMarkovKernel
      (nativeStreamingSingleVertexKernel D μ q T.advance (.child (.root T))) :=
    nativeStreamingSingleVertexKernel_markov D μ q T.advance (.child (.root T))
  exact Measure.compProd_congr (nativeStreamingSingleVertexKernel_zeroEdge_eq D μ a q T hq)

theorem nativeStreamingConditionalMark_zeroEdge_eq
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy j)
    (hq : q (j+1)=q j)
    (F : (AnisotropicObservationState n × Records (AnisotropicObservationState n)
      (Configuration n) T.advance) → Configuration n → ℝ) :
    (fun z => ∫σ, F z σ ∂nativeStreamingSingleVertexKernel D μ q T.advance
      (.root T.advance) z) =ᵐ[anisotropicRecordedProfileTreeLaw D μ a q T.advance]
    (fun z => ∫σ, F z σ ∂nativeStreamingSingleVertexKernel D μ q T.advance
      (.child (.root T)) z) := by
  filter_upwards [nativeStreamingSingleVertexKernel_zeroEdge_eq D μ a q T hq] with z hz
  rw [hz]

theorem nativeStreamingConditionalMark_zeroEdge_integral_eq
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy j)
    (hq : q (j+1)=q j)
    (F : (AnisotropicObservationState n × Records (AnisotropicObservationState n)
      (Configuration n) T.advance) → Configuration n → ℝ) :
    (∫z, ∫σ, F z σ ∂nativeStreamingSingleVertexKernel D μ q T.advance (.root T.advance) z
      ∂anisotropicRecordedProfileTreeLaw D μ a q T.advance)=
    ∫z, ∫σ, F z σ ∂nativeStreamingSingleVertexKernel D μ q T.advance (.child (.root T)) z
      ∂anisotropicRecordedProfileTreeLaw D μ a q T.advance :=
  integral_congr_ae (nativeStreamingConditionalMark_zeroEdge_eq D μ a q T hq F)

end QuantitativeFollowup
