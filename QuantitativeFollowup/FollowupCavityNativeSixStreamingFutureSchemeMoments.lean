module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginalNormalizerSchemeMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginFuture
public import QuantitativeFollowup.FollowupCavityFutureDepthLevels
public import QuantitativeFollowup.FollowupCavityFutureGraftResponseGeometry

@[expose] public section

/-! The physical finite future mark agrees with the genuine native shared
future pair. Both laws are compared through their actual enlarged tree,
so every old record and every independent terminal mark is retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingFutureLawTerminalMoment_scheme_trimmed
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1)) (v : FiniteCascadeRecordVertex T)
    (r : Paper.Overlap)
    (hr : cavityProfileLevel s (cavityFiniteFutureDepth s v.depth r)=r)
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :
    (∫z,G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
      ∂nativeStreamingFuturePairLaw D (Paper.parisiSchemeMeasure s) a
        (anisotropicRecordedSchemeSchedule s) T v r) =
      ∫z,G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
        ∂anisotropicFutureVertexMarkedLaw D s a T.advance v r := by
  let p := cavityFiniteFutureDepth s v.depth r
  have hp : p≤v.depth := cavityFiniteFutureDepth_le s v.depth r
  have hclock : anisotropicRecordedSchemeSchedule s p=r :=
    (nativeStreamingSchemeSchedule_eq_profileLevel s p).trans hr
  have hN := nativeStreamingFuturePairLaw_eq_graft D (Paper.parisiSchemeMeasure s) a
    (anisotropicRecordedSchemeSchedule s) (anisotropicRecordedSchemeSchedule_antitone s)
    (nativeStreamingSchemeSchedule_zero s) T v p hp
  rw [hclock] at hN
  have hF := anisotropicFutureVertexMarkedLaw_eq_graft D s a T.advance v r
  let exN := fun z : AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) (finiteCascadeFutureVertexGraft v p) =>
    ((z.1,(finiteCascadeFutureGraftExtract v p z.2).1),
      (finiteCascadeFutureGraftExtract v p z.2).2)
  let exF := fun z : FiniteStateField (Configuration n) ×
      Records (FiniteStateField (Configuration n)) (Configuration n) (finiteCascadeFutureVertexGraft v p) =>
    ((z.1,(finiteCascadeFutureGraftExtract v p z.2).1),
      (finiteCascadeFutureGraftExtract v p z.2).2)
  have hmN : Measurable exN :=
    (measurable_fst.prodMk ((measurable_finiteCascadeFutureGraftExtract v p).comp
      measurable_snd).fst).prodMk
        ((measurable_finiteCascadeFutureGraftExtract v p).comp measurable_snd).snd
  have hmF : Measurable exF :=
    (measurable_fst.prodMk ((measurable_finiteCascadeFutureGraftExtract v p).comp
      measurable_snd).fst).prodMk
        ((measurable_finiteCascadeFutureGraftExtract v p).comp measurable_snd).snd
  have hGN : Measurable (fun z : (AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) ×
      (Configuration n × Configuration n) =>
    G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) :=
    (measurable_of_finite G).comp
      (((measurable_finiteCascadeRecordTerminalSpins T).comp
        (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  have hGF : Measurable (fun z : (FiniteStateField (Configuration n) ×
      Records (FiniteStateField (Configuration n)) (Configuration n) T) ×
      (Configuration n × Configuration n) =>
    G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) :=
    (measurable_of_finite G).comp
      (((measurable_finiteCascadeRecordTerminalSpins T).comp
        (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  rw [←hN,←hF,integral_map hmN.aemeasurable hGN.aestronglyMeasurable,
    integral_map hmF.aemeasurable hGF.aestronglyMeasurable]
  simp only [exN,exF]
  simp_rw [←cavityFutureGraftTerminalExtract_record]
  exact nativeStreamingOldTerminalMoment_scheme_trimmed D s a hq
    (finiteCascadeFutureVertexGraft v p) (fun σ=>G (cavityFutureGraftTerminalExtract v p σ))

theorem nativeStreamingFutureLawTerminalMoment_scheme_trimmed_ae
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ)
    (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+1)) (v : FiniteCascadeRecordVertex T)
    (G : Paper.Overlap → TerminalSpins (Configuration n) T ×
      (Configuration n × Configuration n) → ℝ) :
    ∀ᵐr∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a,
      cavityProfileLevel s v.depth<r →
      (∫z,G r (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
        ∂nativeStreamingFuturePairLaw D (Paper.parisiSchemeMeasure s) a
          (anisotropicRecordedSchemeSchedule s) T v r) =
        ∫z,G r (finiteCascadeRecordTerminalSpins T z.1.2,z.2)
          ∂anisotropicFutureVertexMarkedLaw D s a T.advance v r := by
  filter_upwards [ae_cavityFiniteFutureDepth_level s a ha has hq v.depth
    (by have hh:=v.depth_le;omega)] with r hr
  exact fun hfuture=>nativeStreamingFutureLawTerminalMoment_scheme_trimmed
    D s a hq T v r (hr hfuture) (G r)

end QuantitativeFollowup
