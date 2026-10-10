module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFuturePairLaw

@[expose] public section

/-! Insert a genuine future time into the observation clock, retain the
entire old genealogy, and attach the actual shared future two-spin
continuation there.  Moving future times and weak profiles converge as
whole marked laws, including both endpoints of an original clock cell. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J:ℕ}
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingFuturePairLaw_refinement (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q Q:ℕ→Paper.Overlap) (d:ℕ→ℕ)
    (hQ:Antitone Q) (hlevels:∀j,Q (observationRefinementDepth d j)=q j)
    (T:FiniteTerminalGenealogy J) (v:FiniteCascadeRecordVertex T) (r:Paper.Overlap) :
    (nativeStreamingFuturePairLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingRefinementVertexEmbed d T v) r).map
        (fun z=>((z.1.1,observationRefinementProject d T z.1.2),z.2))=
      nativeStreamingFuturePairLaw D μ a q T v r := by
  unfold nativeStreamingFuturePairLaw
  rw [nativeStreamingFuturePairKernel_refinement D μ q Q d hlevels T v r]
  have he:=compProd_comap_map_history
    (anisotropicRecordedProfileTreeLaw D μ a Q (observationRefineTree d T))
    (Prod.map id (observationRefinementProject d T))
    (measurable_id.prodMap (measurable_observationRefinementProject d T))
    (nativeStreamingFuturePairKernel D μ q T v r)
  rw [anisotropicRecordedProfileTreeLaw_refinement D μ a q Q d hQ hlevels T] at he
  exact he

def nativeStreamingInsertedFuturePairProbability (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q:ℕ→Paper.Overlap)
    (T:FiniteTerminalGenealogy J) (v:FiniteCascadeRecordVertex T) (j:ℕ) (r:Paper.Overlap) :
    ProbabilityMeasure ((AnisotropicObservationState n×
      Records (AnisotropicObservationState n) (Configuration n) T)×(Configuration n×Configuration n)) :=
  (nativeStreamingActualContinuationProbability D μ a (nativeStreamingEdgeSchedule q j r)
    (fun d=>(finiteCascadeFuturePairTree (j+1) d).tree)
    (fun d=>(finiteCascadeFuturePairTree (j+1) d).spins)
    (observationRefineTree (nativeStreamingEdgeSubdivision j) T)
    (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision j) T v)).map
      (fun z=>((z.1.1,observationRefinementProject (nativeStreamingEdgeSubdivision j) T z.1.2),z.2))

theorem nativeStreamingInsertedFuturePairProbability_eq_law (D:AnisotropicSpinModel n)
    (μ:Paper.ParisiMeasure) (a:ℝ) (q:ℕ→Paper.Overlap) (hq:Antitone q) (hzero:q 0=1)
    (T:FiniteTerminalGenealogy J) (v:FiniteCascadeRecordVertex T)
    (j:ℕ) (hj:j<v.depth) (r:Paper.Overlap) (hr:q (j+1)≤r ∧ r≤q j) :
    (nativeStreamingInsertedFuturePairProbability D μ a q T v j r:Measure _)=
      nativeStreamingFuturePairLaw D μ a q T v r := by
  let Q:=nativeStreamingEdgeSchedule q j r
  let d:=nativeStreamingEdgeSubdivision j
  let V:=nativeStreamingRefinementVertexEmbed d T v
  have hQ:Antitone Q:=nativeStreamingEdgeSchedule_antitone q hq j r hr
  have hQzero:Q 0=1:=by simpa [Q,nativeStreamingEdgeSchedule] using hzero
  have hp:j+1≤V.depth:=by
    rw [nativeStreamingRefinementVertexEmbed_depth,nativeStreamingEdgeSubdivision_depth]
    simp only [not_le.mpr hj,ite_false]
    omega
  have hg:=nativeStreamingFuturePairLaw_eq_graft D μ a Q hQ hQzero
    (observationRefineTree d T) V (j+1) hp
  rw [show Q (j+1)=r from nativeStreamingEdgeSchedule_inserted q j r] at hg
  change (Measure.map _ ((anisotropicRecordedProfileTreeLaw D μ a Q _).map _))=_
  rw [hg]
  exact nativeStreamingFuturePairLaw_refinement D μ a q Q d hQ
    (nativeStreamingEdgeSchedule_refinement q j r) T v r

theorem tendsto_nativeStreamingInsertedFuturePairProbability
    {L:Type*} {l:Filter L} [l.IsCountablyGenerated] (D:AnisotropicSpinModel n)
    {μj:L→Paper.ParisiMeasure} {μ:Paper.ParisiMeasure} (hμ:Tendsto μj l (𝓝 μ))
    (a:ℝ) (q:ℕ→Paper.Overlap) (hq:Antitone q)
    (T:FiniteTerminalGenealogy J) (v:FiniteCascadeRecordVertex T) (j:ℕ)
    {rj:L→Paper.Overlap} {r:Paper.Overlap} (hr:Tendsto rj l (𝓝 r))
    (hrj:∀N,q (j+1)≤rj N ∧ rj N≤q j) (hrr:q (j+1)≤r ∧ r≤q j) :
    Tendsto (fun N=>nativeStreamingInsertedFuturePairProbability D (μj N) a q T v j (rj N)) l
      (𝓝 (nativeStreamingInsertedFuturePairProbability D μ a q T v j r)) := by
  haveI : BorelSpace (Records (AnisotropicObservationState n) (Configuration n) T) :=
    anisotropicObservationRecords_borel T
  haveI : SecondCountableTopology (Records (AnisotropicObservationState n) (Configuration n) T) :=
    inferInstance
  apply ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_nativeStreamingActualContinuationProbability D hμ a
      (fun N=>nativeStreamingEdgeSchedule q j (rj N)) (nativeStreamingEdgeSchedule q j r)
      (fun d=>(finiteCascadeFuturePairTree (j+1) d).tree)
      (fun d=>(finiteCascadeFuturePairTree (j+1) d).spins)
      (fun d=>nativeStreamingObservationPairSpins_continuous (finiteCascadeFuturePairTree (j+1) d))
      (observationRefineTree (nativeStreamingEdgeSubdivision j) T)
      (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision j) T v)
      ?_ ?_ ?_)
  · exact (continuous_fst.fst.prodMk
      ((continuous_observationRefinementProject (nativeStreamingEdgeSubdivision j) T).comp
        continuous_fst.snd)).prodMk continuous_snd
  · intro p _
    unfold nativeStreamingEdgeSchedule
    by_cases hp:p≤j
    · simp only [hp,ite_true]
      exact tendsto_const_nhds
    · simp only [hp,ite_false]
      by_cases he:p=j+1
      · simp only [he,ite_true]
        exact hr
      · simp only [he,ite_false]
        exact tendsto_const_nhds
  · intro N p _
    exact nativeStreamingEdgeSchedule_antitone q hq j (rj N) (hrj N) (Nat.le_succ p)
  · intro p _
    exact nativeStreamingEdgeSchedule_antitone q hq j r hrr (Nat.le_succ p)

end QuantitativeFollowup
