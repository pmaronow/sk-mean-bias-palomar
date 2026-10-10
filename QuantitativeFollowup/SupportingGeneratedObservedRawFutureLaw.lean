module
public import QuantitativeFollowup.SupportingGeneratedObservedRawFutureGeometry
public import QuantitativeFollowup.SupportingGeneratedInitialSiblingSelectedEdgeLaw

@[expose] public section

/-! The computed raw future graft has the genuine original selected-origin
future probability. The complete old record and ordered pair of fresh
spins survive the projection; no law or response identity is an input. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {J n : ℕ}

def cavityGeneratedObservedRawFutureRecordProject {E S : Type}
    (T : FiniteTerminalGenealogy J) (γ : CavityGeneratedObservedRawOriginChart T) (j : Fin J) :
    E × Records E S (cavityGeneratedObservedRawFutureTree T γ j) →
      (E × Records E S T) × (S × S) :=
  fun z =>
    let x := finiteCascadeFutureGraftExtract (cavityGeneratedObservedRawFutureAnchor T γ j)
      (cavityGeneratedObservedRawFutureSplit T γ j) z.2
    ((z.1,observationRefinementProject (cavityGeneratedObservedRawFutureSubdivision T γ j) T x.1),x.2)

theorem measurable_cavityGeneratedObservedRawFutureRecordProject {E S : Type}
    [MeasurableSpace E] [MeasurableSpace S]
    (T : FiniteTerminalGenealogy J) (γ : CavityGeneratedObservedRawOriginChart T) (j : Fin J) :
    Measurable (cavityGeneratedObservedRawFutureRecordProject (E:=E) (S:=S) T γ j) := by
  let hx := measurable_finiteCascadeFutureGraftExtract
    (E:=E) (S:=S) (cavityGeneratedObservedRawFutureAnchor T γ j)
    (cavityGeneratedObservedRawFutureSplit T γ j)
  exact (measurable_fst.prodMk
    ((measurable_observationRefinementProject _ T).comp (hx.fst.comp measurable_snd))).prodMk
      (hx.snd.comp measurable_snd)

def cavityGeneratedObservedRawFutureProbability (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (γ : CavityGeneratedObservedRawOriginChart T)
    (j : Fin J) (r l : Paper.Overlap) :
    ProbabilityMeasure ((AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n) T) ×
        (Configuration n × Configuration n)) :=
  (nativeStreamingActualContinuationProbability D μ a
    (cavityGeneratedObservedRawFutureClock q T γ j r l)
    (fun d => (finiteCascadeFuturePairTree (cavityGeneratedObservedRawFutureSplit T γ j) d).tree)
    (fun d => (finiteCascadeFuturePairTree (cavityGeneratedObservedRawFutureSplit T γ j) d).spins)
    (observationRefineTree (cavityGeneratedObservedRawFutureSubdivision T γ j) T)
    (cavityGeneratedObservedRawFutureAnchor T γ j)).map
      (fun z => ((z.1.1,observationRefinementProject
        (cavityGeneratedObservedRawFutureSubdivision T γ j) T z.1.2),z.2))

theorem cavityGeneratedObservedRawFutureProbability_eq_origin (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (γ : CavityGeneratedObservedRawOriginChart T)
    (j : Fin J) (r l : Paper.Overlap) (hrl : r < l) :
    cavityGeneratedObservedRawFutureProbability D μ a q T γ j r l =
      nativeStreamingOriginFutureProbability D μ a q T
        (cavityGeneratedObservedRawFutureOrigin T γ r) j l := by
  rcases γ with i | (i | u)
  · rfl
  · let e := (cavityGeneratedOriginEdges T).get i
    have hi : nativeStreamingPairObservationIndex e.depth j r l =
        (if e.depth = j then 1 else 0) := by
      simp only [nativeStreamingPairObservationIndex,if_pos hrl]
    have hk : nativeStreamingPairObservationIndex j e.depth l r = 0 := by
      simp only [nativeStreamingPairObservationIndex,if_neg (not_lt_of_ge hrl.le),ite_self]
    change _ = nativeStreamingEdgeFutureProbabilityFixed D μ a q T e j
      (nativeStreamingPairObservationIndex e.depth j r l)
      (nativeStreamingPairObservationIndex j e.depth l r) r l
    rw [hi,hk]
    simp only [nativeStreamingEdgeFutureProbabilityFixed,Nat.add_zero]
    rfl
  · rfl

private theorem rawFuture_map_graft_project {E S B : Type}
    [MeasurableSpace E] [MeasurableSpace S] [MeasurableSpace B]
    {K : ℕ} {T : FiniteTerminalGenealogy K}
    (v : FiniteCascadeRecordVertex T) (p : ℕ) (f : Records E S T → B) (hf : Measurable f)
    (Q : Measure (E × Records E S (finiteCascadeFutureVertexGraft v p))) :
    Q.map (fun z => ((z.1,f (finiteCascadeFutureGraftExtract v p z.2).1),
      (finiteCascadeFutureGraftExtract v p z.2).2)) =
      (Q.map (fun z => ((z.1,(finiteCascadeFutureGraftExtract v p z.2).1),
        (finiteCascadeFutureGraftExtract v p z.2).2))).map
          (fun z => ((z.1.1,f z.1.2),z.2)) := by
  have hx : Measurable (fun z : E × Records E S (finiteCascadeFutureVertexGraft v p) =>
      ((z.1,(finiteCascadeFutureGraftExtract v p z.2).1),
        (finiteCascadeFutureGraftExtract v p z.2).2)) :=
    (measurable_fst.prodMk ((measurable_finiteCascadeFutureGraftExtract v p).fst.comp
      measurable_snd)).prodMk ((measurable_finiteCascadeFutureGraftExtract v p).snd.comp measurable_snd)
  have hp : Measurable (fun z : (E × Records E S T) × (S × S) =>
      ((z.1.1,f z.1.2),z.2)) :=
    (measurable_fst.fst.prodMk (hf.comp measurable_fst.snd)).prodMk measurable_snd
  simpa only [Function.comp_def] using (Measure.map_map (μ:=Q) hp hx).symm

theorem cavityGeneratedObservedRawFuture_record_law (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (γ : CavityGeneratedObservedRawOriginChart T)
    (j : Fin J) (r l : Paper.Overlap) (hrl : r < l) :
    (anisotropicRecordedProfileTreeLaw D μ a (cavityGeneratedObservedRawFutureClock q T γ j r l)
      (cavityGeneratedObservedRawFutureTree T γ j)).map
        (cavityGeneratedObservedRawFutureRecordProject T γ j) =
      (nativeStreamingOriginFutureProbability D μ a q T
        (cavityGeneratedObservedRawFutureOrigin T γ r) j l : Measure _) := by
  rw [←cavityGeneratedObservedRawFutureProbability_eq_origin D μ a q T γ j r l hrl]
  exact rawFuture_map_graft_project (cavityGeneratedObservedRawFutureAnchor T γ j)
    (cavityGeneratedObservedRawFutureSplit T γ j)
    (observationRefinementProject (cavityGeneratedObservedRawFutureSubdivision T γ j) T)
    (measurable_observationRefinementProject _ T) _

theorem cavityGeneratedObservedRawFutureTerminalProject_record {E S : Type}
    (T : FiniteTerminalGenealogy J) (γ : CavityGeneratedObservedRawOriginChart T) (j : Fin J)
    (z : E × Records E S (cavityGeneratedObservedRawFutureTree T γ j)) :
    cavityGeneratedObservedRawFutureTerminalProject T γ j (finiteCascadeRecordTerminalSpins _ z.2) =
      (finiteCascadeRecordTerminalSpins T
        (cavityGeneratedObservedRawFutureRecordProject T γ j z).1.2,
        (cavityGeneratedObservedRawFutureRecordProject T γ j z).2) :=
  printedGeneratedRefinedFutureTerminalProject_record _ T _ _ z.2

theorem cavityGeneratedObservedRawFuture_terminal_law (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (γ : CavityGeneratedObservedRawOriginChart T)
    (j : Fin J) (r l : Paper.Overlap) (hrl : r < l) :
    (anisotropicRecordedProfileTreeLaw D μ a (cavityGeneratedObservedRawFutureClock q T γ j r l)
      (cavityGeneratedObservedRawFutureTree T γ j)).map
        (fun z => ((z.1,(cavityGeneratedObservedRawFutureTerminalProject T γ j
          (finiteCascadeRecordTerminalSpins _ z.2)).1),
            (cavityGeneratedObservedRawFutureTerminalProject T γ j
              (finiteCascadeRecordTerminalSpins _ z.2)).2)) =
      (nativeStreamingOriginFutureProbability D μ a q T
        (cavityGeneratedObservedRawFutureOrigin T γ r) j l : Measure _).map
          (printedGeneratedInitialMarkedTerminalMap T) := by
  rw [←cavityGeneratedObservedRawFuture_record_law D μ a q T γ j r l hrl,
    Measure.map_map (measurable_printedGeneratedInitialMarkedTerminalMap T)
      (measurable_cavityGeneratedObservedRawFutureRecordProject T γ j)]
  congr 1
  funext z
  have he := cavityGeneratedObservedRawFutureTerminalProject_record T γ j z
  simp only [Function.comp_def,printedGeneratedInitialMarkedTerminalMap]
  rw [he]
  rfl

end QuantitativeFollowup
